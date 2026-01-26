//! Async network worker for gossip and fact replication.
//! Uses Tokio for TCP (facts) and UDP (gossip).
//!
//! ## Zero-Copy Architecture
//!
//! The `ZeroCopyNetworkWorker` integrates with `WALArena` to broadcast facts
//! without heap allocation:
//! 1. Kernel admits fact, acquires arena slot with refcount=2 (persist + network)
//! 2. Kernel pushes `ZeroCopyBroadcastEntry` to network SPSC
//! 3. Network worker reads payload directly from arena using slot index
//! 4. After broadcast, worker calls `arena.complete_broadcast(slot_idx)`
//! 5. When refcount hits 0, slot is auto-released

use std::collections::HashMap;
use std::net::SocketAddr;
use std::sync::Arc;
use std::time::Duration;

use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::{TcpListener, TcpStream, UdpSocket};
use tokio::sync::mpsc;
use tokio::time::interval;

use crate::core::topology::{CausalClock, FactId};
use crate::core::persistence::WALArena;

use super::protocol::{NetworkMessage, WireHeader};

/// Peer address (IP:port).
pub type PeerAddr = SocketAddr;

/// Network configuration.
#[derive(Debug, Clone)]
pub struct NetworkConfig {
    /// Local TCP bind address for fact transfers.
    pub tcp_bind: SocketAddr,
    /// Local UDP bind address for gossip.
    pub udp_bind: SocketAddr,
    /// Known peers for gossip.
    pub peers: Vec<PeerAddr>,
    /// Gossip interval in milliseconds.
    pub gossip_interval_ms: u64,
}

impl Default for NetworkConfig {
    fn default() -> Self {
        Self {
            tcp_bind: "0.0.0.0:9100".parse().unwrap(),
            udp_bind: "0.0.0.0:9101".parse().unwrap(),
            peers: Vec::new(),
            gossip_interval_ms: 100,
        }
    }
}

/// Commands sent to the network worker.
#[derive(Debug)]
pub enum NetworkCommand {
    /// Broadcast a new fact to peers.
    BroadcastFact { fact_id: FactId, payload: Vec<u8> },
    /// Request facts from peers.
    PullFacts { fact_ids: Vec<FactId> },
    /// Shutdown the worker.
    Shutdown,
}

/// Events received from the network.
#[derive(Debug)]
pub enum NetworkEvent {
    /// Received a gossip clock from peer.
    GossipReceived { peer: PeerAddr, clock: CausalClock },
    /// Received a fact from peer.
    FactReceived { fact_id: FactId, payload: Vec<u8> },
    /// Peer requested facts.
    PullRequested { peer: PeerAddr, fact_ids: Vec<FactId> },
    /// Network error.
    Error { message: String },
}

/// Async network worker handle.
pub struct NetworkWorker {
    command_tx: mpsc::Sender<NetworkCommand>,
    event_rx: mpsc::Receiver<NetworkEvent>,
}

impl NetworkWorker {
    /// Spawn the network worker on the Tokio runtime.
    pub async fn spawn(
        config: NetworkConfig,
        local_clock: Arc<tokio::sync::RwLock<CausalClock>>,
    ) -> std::io::Result<Self> {
        let (command_tx, command_rx) = mpsc::channel(1024);
        let (event_tx, event_rx) = mpsc::channel(1024);

        let worker = WorkerInner {
            config: config.clone(),
            local_clock,
            command_rx,
            event_tx,
            peer_clocks: HashMap::new(),
        };

        tokio::spawn(worker.run());

        Ok(Self { command_tx, event_rx })
    }

    /// Send a command to the worker.
    pub async fn send(&self, cmd: NetworkCommand) -> Result<(), mpsc::error::SendError<NetworkCommand>> {
        self.command_tx.send(cmd).await
    }

    /// Receive next event from the network.
    pub async fn recv(&mut self) -> Option<NetworkEvent> {
        self.event_rx.recv().await
    }

    /// Broadcast a fact to all peers.
    pub async fn broadcast_fact(&self, fact_id: FactId, payload: Vec<u8>) -> Result<(), mpsc::error::SendError<NetworkCommand>> {
        self.send(NetworkCommand::BroadcastFact { fact_id, payload }).await
    }

    /// Shutdown the worker.
    pub async fn shutdown(&self) -> Result<(), mpsc::error::SendError<NetworkCommand>> {
        self.send(NetworkCommand::Shutdown).await
    }
}

struct WorkerInner {
    config: NetworkConfig,
    local_clock: Arc<tokio::sync::RwLock<CausalClock>>,
    command_rx: mpsc::Receiver<NetworkCommand>,
    event_tx: mpsc::Sender<NetworkEvent>,
    peer_clocks: HashMap<PeerAddr, CausalClock>,
}

impl WorkerInner {
    async fn run(mut self) {
        let tcp_listener = match TcpListener::bind(self.config.tcp_bind).await {
            Ok(l) => l,
            Err(e) => {
                let _ = self.event_tx.send(NetworkEvent::Error {
                    message: format!("TCP bind failed: {}", e),
                }).await;
                return;
            }
        };

        let udp_socket = match UdpSocket::bind(self.config.udp_bind).await {
            Ok(s) => Arc::new(s),
            Err(e) => {
                let _ = self.event_tx.send(NetworkEvent::Error {
                    message: format!("UDP bind failed: {}", e),
                }).await;
                return;
            }
        };

        let mut gossip_timer = interval(Duration::from_millis(self.config.gossip_interval_ms));
        let mut udp_buf = vec![0u8; 1500];

        loop {
            tokio::select! {
                // Handle incoming TCP connections
                accept_result = tcp_listener.accept() => {
                    if let Ok((stream, peer)) = accept_result {
                        let event_tx = self.event_tx.clone();
                        tokio::spawn(Self::handle_tcp_connection(stream, peer, event_tx));
                    }
                }

                // Handle incoming UDP gossip
                recv_result = udp_socket.recv_from(&mut udp_buf) => {
                    if let Ok((len, peer)) = recv_result {
                        self.handle_udp_message(&udp_buf[..len], peer).await;
                    }
                }

                // Handle commands from kernel
                Some(cmd) = self.command_rx.recv() => {
                    match cmd {
                        NetworkCommand::BroadcastFact { fact_id, payload } => {
                            self.broadcast_fact_to_peers(fact_id, payload).await;
                        }
                        NetworkCommand::PullFacts { fact_ids } => {
                            self.pull_facts_from_peers(fact_ids).await;
                        }
                        NetworkCommand::Shutdown => {
                            break;
                        }
                    }
                }

                // Periodic gossip
                _ = gossip_timer.tick() => {
                    self.send_gossip(&udp_socket).await;
                }
            }
        }
    }

    async fn handle_tcp_connection(
        mut stream: TcpStream,
        peer: PeerAddr,
        event_tx: mpsc::Sender<NetworkEvent>,
    ) {
        let mut header_buf = [0u8; WireHeader::SIZE];

        loop {
            // Read header
            if stream.read_exact(&mut header_buf).await.is_err() {
                break;
            }

            let header = match WireHeader::from_bytes(&header_buf) {
                Some(h) => h,
                None => break,
            };

            if header.validate().is_err() {
                break;
            }

            // Read payload
            let mut payload = vec![0u8; header.payload_len as usize];
            if stream.read_exact(&mut payload).await.is_err() {
                break;
            }

            // Reconstruct full message for decoding
            let mut full_msg = Vec::with_capacity(WireHeader::SIZE + payload.len());
            full_msg.extend_from_slice(&header_buf);
            full_msg.extend_from_slice(&payload);

            match NetworkMessage::decode(&full_msg) {
                Ok(NetworkMessage::PushFact { fact_id, payload }) => {
                    let _ = event_tx.send(NetworkEvent::FactReceived { fact_id, payload }).await;
                }
                Ok(NetworkMessage::PullRequest { fact_ids }) => {
                    let _ = event_tx.send(NetworkEvent::PullRequested { peer, fact_ids }).await;
                }
                _ => {}
            }
        }
    }

    async fn handle_udp_message(&mut self, data: &[u8], peer: PeerAddr) {
        match NetworkMessage::decode(data) {
            Ok(NetworkMessage::GossipClock(clock)) => {
                self.peer_clocks.insert(peer, clock);
                let _ = self.event_tx.send(NetworkEvent::GossipReceived { peer, clock }).await;
            }
            _ => {}
        }
    }

    async fn send_gossip(&self, socket: &UdpSocket) {
        let clock = self.local_clock.read().await;
        let msg = NetworkMessage::GossipClock(*clock);
        let data = msg.encode();

        for peer in &self.config.peers {
            // Use UDP port (peer's gossip port)
            let gossip_addr = SocketAddr::new(peer.ip(), self.config.udp_bind.port());
            let _ = socket.send_to(&data, gossip_addr).await;
        }
    }

    async fn broadcast_fact_to_peers(&self, fact_id: FactId, payload: Vec<u8>) {
        let msg = NetworkMessage::PushFact { fact_id, payload };
        let data = msg.encode();

        for peer in &self.config.peers {
            if let Ok(mut stream) = TcpStream::connect(peer).await {
                let _ = stream.write_all(&data).await;
            }
        }
    }

    async fn pull_facts_from_peers(&self, fact_ids: Vec<FactId>) {
        let msg = NetworkMessage::PullRequest { fact_ids };
        let data = msg.encode();

        for peer in &self.config.peers {
            if let Ok(mut stream) = TcpStream::connect(peer).await {
                let _ = stream.write_all(&data).await;
            }
        }
    }
}

/// Zero-copy network worker that reads directly from WALArena.
///
/// This worker integrates with the Two-Lane architecture:
/// - Receives `ZeroCopyBroadcastEntry` via SPSC channel
/// - Reads payload directly from WALArena using slot index
/// - Uses fixed-size `SendBuffer` to avoid heap allocation
/// - Calls `arena.complete_broadcast()` after transmission
pub struct ZeroCopyNetworkWorker {
    config: NetworkConfig,
    arena: Arc<WALArena>,
    local_clock: Arc<tokio::sync::RwLock<CausalClock>>,
    broadcast_rx: mpsc::Receiver<ZeroCopyBroadcastEntry>,
    event_tx: mpsc::Sender<NetworkEvent>,
    peer_connections: HashMap<PeerAddr, TcpStream>,
}

impl ZeroCopyNetworkWorker {
    /// Create a new zero-copy network worker.
    pub fn new(
        config: NetworkConfig,
        arena: Arc<WALArena>,
        local_clock: Arc<tokio::sync::RwLock<CausalClock>>,
        broadcast_rx: mpsc::Receiver<ZeroCopyBroadcastEntry>,
        event_tx: mpsc::Sender<NetworkEvent>,
    ) -> Self {
        Self {
            config,
            arena,
            local_clock,
            broadcast_rx,
            event_tx,
            peer_connections: HashMap::new(),
        }
    }

    /// Run the zero-copy worker loop.
    pub async fn run(mut self) {
        let udp_socket = match UdpSocket::bind(self.config.udp_bind).await {
            Ok(s) => Arc::new(s),
            Err(e) => {
                let _ = self.event_tx.send(NetworkEvent::Error {
                    message: format!("UDP bind failed: {}", e),
                }).await;
                return;
            }
        };

        let mut gossip_timer = interval(Duration::from_millis(self.config.gossip_interval_ms));
        let mut send_buffer = SendBuffer::new();

        loop {
            tokio::select! {
                // Handle broadcast entries from kernel
                Some(entry) = self.broadcast_rx.recv() => {
                    self.broadcast_from_arena(&entry, &mut send_buffer).await;
                }

                // Periodic gossip
                _ = gossip_timer.tick() => {
                    self.send_gossip(&udp_socket).await;
                }
            }
        }
    }

    /// Broadcast a fact directly from the arena (zero-copy).
    async fn broadcast_from_arena(
        &mut self,
        entry: &ZeroCopyBroadcastEntry,
        send_buffer: &mut SendBuffer,
    ) {
        // Read payload directly from arena
        let payload_result = self.arena.read_slot(entry.slot_index);

        if let Ok((fact_id, payload)) = payload_result {
            send_buffer.clear();

            // Encode frame into fixed buffer (no heap allocation)
            if send_buffer.append_frame(fact_id, payload) {
                // Send to all peers
                for peer in &self.config.peers {
                    // Get or create connection
                    if !self.peer_connections.contains_key(peer) {
                        if let Ok(stream) = TcpStream::connect(peer).await {
                            self.peer_connections.insert(*peer, stream);
                        }
                    }

                    if let Some(stream) = self.peer_connections.get_mut(peer) {
                        let _ = stream.write_all(send_buffer.as_slice()).await;
                    }
                }
            }
        }

        // Decrement refcount - slot auto-releases when count hits 0
        let _ = self.arena.complete_broadcast(entry.slot_index);
    }

    /// Send gossip clock to peers.
    async fn send_gossip(&self, socket: &UdpSocket) {
        let clock = self.local_clock.read().await;
        let msg = NetworkMessage::GossipClock(*clock);
        let data = msg.encode();

        for peer in &self.config.peers {
            let gossip_addr = SocketAddr::new(peer.ip(), self.config.udp_bind.port());
            let _ = socket.send_to(&data, gossip_addr).await;
        }
    }
}

/// Handle for spawning and communicating with ZeroCopyNetworkWorker.
pub struct ZeroCopyNetworkHandle {
    broadcast_tx: mpsc::Sender<ZeroCopyBroadcastEntry>,
    event_rx: mpsc::Receiver<NetworkEvent>,
}

impl ZeroCopyNetworkHandle {
    /// Spawn a zero-copy network worker.
    pub fn spawn(
        config: NetworkConfig,
        arena: Arc<WALArena>,
        local_clock: Arc<tokio::sync::RwLock<CausalClock>>,
    ) -> Self {
        let (broadcast_tx, broadcast_rx) = mpsc::channel(4096);
        let (event_tx, event_rx) = mpsc::channel(1024);

        let worker = ZeroCopyNetworkWorker::new(
            config,
            arena,
            local_clock,
            broadcast_rx,
            event_tx,
        );

        tokio::spawn(worker.run());

        Self {
            broadcast_tx,
            event_rx,
        }
    }

    /// Queue a fact for zero-copy broadcast.
    /// The entry contains a slot index into the WALArena.
    #[inline]
    pub async fn broadcast(&self, entry: ZeroCopyBroadcastEntry) -> Result<(), mpsc::error::SendError<ZeroCopyBroadcastEntry>> {
        self.broadcast_tx.send(entry).await
    }

    /// Try to queue a fact for broadcast (non-blocking).
    #[inline]
    pub fn try_broadcast(&self, entry: ZeroCopyBroadcastEntry) -> Result<(), mpsc::error::TrySendError<ZeroCopyBroadcastEntry>> {
        self.broadcast_tx.try_send(entry)
    }

    /// Receive next event from the network.
    pub async fn recv(&mut self) -> Option<NetworkEvent> {
        self.event_rx.recv().await
    }
}

/// Broadcast buffer entry for kernel integration (legacy, heap-based).
#[derive(Clone, Copy, Debug)]
#[repr(C)]
pub struct BroadcastEntry {
    pub fact_id: FactId,
    pub payload_ptr: usize,
    pub payload_len: u32,
    _pad: [u8; 4],
}

impl BroadcastEntry {
    pub const fn empty() -> Self {
        Self {
            fact_id: [0u8; 32],
            payload_ptr: 0,
            payload_len: 0,
            _pad: [0u8; 4],
        }
    }
}

const _: () = {
    assert!(core::mem::size_of::<BroadcastEntry>() == 48);
};

/// Zero-copy broadcast entry using arena slot index.
/// The network worker reads directly from WALArena using this index.
#[derive(Clone, Copy, Debug)]
#[repr(C)]
pub struct ZeroCopyBroadcastEntry {
    /// Fact ID for routing/dedup.
    pub fact_id: FactId,
    /// Slot index into WALArena (zero-copy reference).
    pub slot_index: u32,
    /// Payload length (for frame sizing).
    pub payload_len: u32,
}

impl ZeroCopyBroadcastEntry {
    pub const fn empty() -> Self {
        Self {
            fact_id: [0u8; 32],
            slot_index: u32::MAX,
            payload_len: 0,
        }
    }

    #[inline(always)]
    pub const fn is_valid(&self) -> bool {
        self.slot_index != u32::MAX
    }
}

const _: () = {
    assert!(core::mem::size_of::<ZeroCopyBroadcastEntry>() == 40);
};

/// Fixed-format wire frame for zero-copy broadcast.
/// Layout: [FactId:32][PayloadLen:4][Payload:N][Padding to 8-byte boundary]
#[derive(Debug)]
#[repr(C, align(8))]
pub struct BroadcastFrame {
    pub fact_id: FactId,
    pub payload_len: u32,
    _reserved: u32,
    // Payload follows inline (variable length)
}

impl BroadcastFrame {
    pub const HEADER_SIZE: usize = 40;

    /// Encode a frame into a fixed buffer (no heap allocation).
    /// Returns the number of bytes written.
    #[inline]
    pub fn encode_into(
        buffer: &mut [u8],
        fact_id: &FactId,
        payload: &[u8],
    ) -> Option<usize> {
        let total_len = Self::HEADER_SIZE + payload.len();
        let padded_len = (total_len + 7) & !7; // Round up to 8-byte boundary

        if buffer.len() < padded_len {
            return None;
        }

        // Write header
        buffer[..32].copy_from_slice(fact_id);
        buffer[32..36].copy_from_slice(&(payload.len() as u32).to_le_bytes());
        buffer[36..40].fill(0); // Reserved

        // Write payload
        buffer[40..40 + payload.len()].copy_from_slice(payload);

        // Zero padding
        buffer[40 + payload.len()..padded_len].fill(0);

        Some(padded_len)
    }

    /// Decode a frame from a buffer.
    #[inline]
    pub fn decode(buffer: &[u8]) -> Option<(FactId, &[u8])> {
        if buffer.len() < Self::HEADER_SIZE {
            return None;
        }

        let mut fact_id = [0u8; 32];
        fact_id.copy_from_slice(&buffer[..32]);

        let payload_len = u32::from_le_bytes([
            buffer[32], buffer[33], buffer[34], buffer[35],
        ]) as usize;

        if buffer.len() < Self::HEADER_SIZE + payload_len {
            return None;
        }

        let payload = &buffer[40..40 + payload_len];
        Some((fact_id, payload))
    }
}

/// Zero-copy broadcast command using arena reference.
#[derive(Debug, Clone, Copy)]
pub enum ZeroCopyCommand {
    /// Broadcast fact using arena slot (zero-copy).
    BroadcastFromArena {
        fact_id: FactId,
        slot_index: u32,
        payload_len: u32,
    },
    /// Shutdown the worker.
    Shutdown,
}

/// Fixed-size send buffer for zero-copy networking.
/// Avoids heap allocation in the broadcast path.
#[repr(C, align(4096))]
pub struct SendBuffer {
    data: [u8; 4096],
    len: usize,
}

impl SendBuffer {
    pub const fn new() -> Self {
        Self {
            data: [0u8; 4096],
            len: 0,
        }
    }

    #[inline]
    pub fn clear(&mut self) {
        self.len = 0;
    }

    #[inline]
    pub fn as_slice(&self) -> &[u8] {
        &self.data[..self.len]
    }

    #[inline]
    pub fn remaining_capacity(&self) -> usize {
        4096 - self.len
    }

    /// Append a broadcast frame to the buffer.
    /// Returns true if successful, false if buffer full.
    #[inline]
    pub fn append_frame(&mut self, fact_id: &FactId, payload: &[u8]) -> bool {
        if let Some(written) = BroadcastFrame::encode_into(
            &mut self.data[self.len..],
            fact_id,
            payload,
        ) {
            self.len += written;
            true
        } else {
            false
        }
    }
}

impl Default for SendBuffer {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_broadcast_entry_size() {
        assert_eq!(core::mem::size_of::<BroadcastEntry>(), 48);
    }

    #[test]
    fn test_zero_copy_broadcast_entry_size() {
        assert_eq!(core::mem::size_of::<ZeroCopyBroadcastEntry>(), 40);
    }

    #[test]
    fn test_broadcast_frame_encode_decode() {
        let fact_id: FactId = [0xAB; 32];
        let payload = b"test payload data";

        let mut buffer = [0u8; 256];
        let written = BroadcastFrame::encode_into(&mut buffer, &fact_id, payload).unwrap();

        assert!(written >= BroadcastFrame::HEADER_SIZE + payload.len());
        assert_eq!(written % 8, 0); // 8-byte aligned

        let (decoded_id, decoded_payload) = BroadcastFrame::decode(&buffer[..written]).unwrap();
        assert_eq!(decoded_id, fact_id);
        assert_eq!(decoded_payload, payload);
    }

    #[test]
    fn test_send_buffer_append() {
        let mut buffer = SendBuffer::new();

        let fact1: FactId = [1u8; 32];
        let payload1 = b"first";
        assert!(buffer.append_frame(&fact1, payload1));

        let fact2: FactId = [2u8; 32];
        let payload2 = b"second";
        assert!(buffer.append_frame(&fact2, payload2));

        assert!(buffer.len > 0);
        assert!(buffer.remaining_capacity() < 4096);
    }

    #[test]
    fn test_send_buffer_overflow() {
        let mut buffer = SendBuffer::new();

        // Fill buffer with large payloads until it can't fit more
        let fact_id: FactId = [0xAB; 32];
        let large_payload = [0u8; 200];

        let mut count = 0;
        while buffer.append_frame(&fact_id, &large_payload) {
            count += 1;
            if count > 100 {
                break; // Safety limit
            }
        }

        // Should have fit multiple frames
        assert!(count > 1);
        assert!(count < 20); // But not too many
    }

    #[test]
    fn test_network_config_default() {
        let config = NetworkConfig::default();
        assert_eq!(config.gossip_interval_ms, 100);
    }
}
