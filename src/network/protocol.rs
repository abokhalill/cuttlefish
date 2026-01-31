//! Wire protocol for network messages.
//! Format: [Magic:4][Version:1][Type:1][Len:4][CRC32:4][Payload]

use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout};

use crate::core::topology::{CausalClock, FactId};

/// Magic bytes identifying Cuttlefish protocol.
pub const WIRE_MAGIC: [u8; 4] = [0xCF, 0x15, 0xFA, 0xCE];

/// Current protocol version.
pub const WIRE_VERSION: u8 = 1;

/// Maximum payload size (1MB).
pub const MAX_PAYLOAD_SIZE: u32 = 1024 * 1024;

/// Message types.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum MessageType {
    /// Gossip clock exchange (UDP).
    GossipClock = 1,
    /// Push a fact to peer (TCP).
    PushFact = 2,
    /// Request specific facts by ID (TCP).
    PullRequest = 3,
    /// Response with requested facts (TCP).
    PullResponse = 4,
}

impl MessageType {
    pub fn from_u8(v: u8) -> Option<Self> {
        match v {
            1 => Some(Self::GossipClock),
            2 => Some(Self::PushFact),
            3 => Some(Self::PullRequest),
            4 => Some(Self::PullResponse),
            _ => None,
        }
    }
}

/// Wire header for all messages.
#[derive(Debug, Clone, Copy, FromBytes, IntoBytes, KnownLayout, Immutable)]
#[repr(C, packed)]
pub struct WireHeader {
    pub magic: [u8; 4],
    pub version: u8,
    pub msg_type: u8,
    pub payload_len: u32,
    pub crc32: u32,
}

const _: () = {
    assert!(core::mem::size_of::<WireHeader>() == 14);
};

impl WireHeader {
    pub const SIZE: usize = 14;

    pub fn new(msg_type: MessageType, payload_len: u32, crc32: u32) -> Self {
        Self {
            magic: WIRE_MAGIC,
            version: WIRE_VERSION,
            msg_type: msg_type as u8,
            payload_len,
            crc32,
        }
    }

    pub fn validate(&self) -> Result<MessageType, ProtocolError> {
        if self.magic != WIRE_MAGIC {
            return Err(ProtocolError::InvalidMagic);
        }
        if self.version != WIRE_VERSION {
            return Err(ProtocolError::UnsupportedVersion);
        }
        if self.payload_len > MAX_PAYLOAD_SIZE {
            return Err(ProtocolError::PayloadTooLarge);
        }
        MessageType::from_u8(self.msg_type).ok_or(ProtocolError::InvalidMessageType)
    }

    pub fn to_bytes(&self) -> [u8; Self::SIZE] {
        let mut buf = [0u8; Self::SIZE];
        buf.copy_from_slice(self.as_bytes());
        buf
    }

    pub fn from_bytes(buf: &[u8; Self::SIZE]) -> Option<Self> {
        Self::read_from_bytes(buf).ok()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProtocolError {
    InvalidMagic,
    UnsupportedVersion,
    InvalidMessageType,
    PayloadTooLarge,
    CrcMismatch,
    InsufficientData,
    MalformedPayload,
}

/// Gossip clock payload (just the BFVC).
#[derive(Debug, Clone, Copy, FromBytes, IntoBytes, KnownLayout, Immutable)]
#[repr(C)]
pub struct GossipClockPayload {
    pub clock: CausalClock,
}

const _: () = {
    assert!(core::mem::size_of::<GossipClockPayload>() == 64);
};

/// Pull request payload (list of FactIds we want).
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct PullRequestPayload {
    pub count: u32,
    _pad: [u8; 4],
}

impl PullRequestPayload {
    pub const HEADER_SIZE: usize = 8;

    pub fn new(count: u32) -> Self {
        Self {
            count,
            _pad: [0u8; 4],
        }
    }
}

/// High-level network message enum.
#[derive(Debug, Clone)]
pub enum NetworkMessage {
    GossipClock(CausalClock),
    PushFact { fact_id: FactId, payload: Vec<u8> },
    PullRequest { fact_ids: Vec<FactId> },
    PullResponse { facts: Vec<(FactId, Vec<u8>)> },
}

impl NetworkMessage {
    /// Serialize message to bytes with header.
    pub fn encode(&self) -> Vec<u8> {
        match self {
            NetworkMessage::GossipClock(clock) => {
                let payload = clock.as_bytes();
                let crc = crc32fast::hash(payload);
                let header = WireHeader::new(MessageType::GossipClock, payload.len() as u32, crc);
                let mut buf = Vec::with_capacity(WireHeader::SIZE + payload.len());
                buf.extend_from_slice(&header.to_bytes());
                buf.extend_from_slice(payload);
                buf
            }
            NetworkMessage::PushFact { fact_id, payload } => {
                let mut data = Vec::with_capacity(32 + payload.len());
                data.extend_from_slice(fact_id);
                data.extend_from_slice(payload);
                let crc = crc32fast::hash(&data);
                let header = WireHeader::new(MessageType::PushFact, data.len() as u32, crc);
                let mut buf = Vec::with_capacity(WireHeader::SIZE + data.len());
                buf.extend_from_slice(&header.to_bytes());
                buf.extend_from_slice(&data);
                buf
            }
            NetworkMessage::PullRequest { fact_ids } => {
                let mut data = Vec::with_capacity(4 + fact_ids.len() * 32);
                data.extend_from_slice(&(fact_ids.len() as u32).to_le_bytes());
                for id in fact_ids {
                    data.extend_from_slice(id);
                }
                let crc = crc32fast::hash(&data);
                let header = WireHeader::new(MessageType::PullRequest, data.len() as u32, crc);
                let mut buf = Vec::with_capacity(WireHeader::SIZE + data.len());
                buf.extend_from_slice(&header.to_bytes());
                buf.extend_from_slice(&data);
                buf
            }
            NetworkMessage::PullResponse { facts } => {
                let mut data = Vec::new();
                data.extend_from_slice(&(facts.len() as u32).to_le_bytes());
                for (id, payload) in facts {
                    data.extend_from_slice(id);
                    data.extend_from_slice(&(payload.len() as u32).to_le_bytes());
                    data.extend_from_slice(payload);
                }
                let crc = crc32fast::hash(&data);
                let header = WireHeader::new(MessageType::PullResponse, data.len() as u32, crc);
                let mut buf = Vec::with_capacity(WireHeader::SIZE + data.len());
                buf.extend_from_slice(&header.to_bytes());
                buf.extend_from_slice(&data);
                buf
            }
        }
    }

    /// Decode message from bytes (header + payload).
    pub fn decode(data: &[u8]) -> Result<Self, ProtocolError> {
        if data.len() < WireHeader::SIZE {
            return Err(ProtocolError::InsufficientData);
        }

        let header_bytes: [u8; WireHeader::SIZE] = data[..WireHeader::SIZE]
            .try_into()
            .map_err(|_| ProtocolError::InsufficientData)?;

        let header =
            WireHeader::from_bytes(&header_bytes).ok_or(ProtocolError::MalformedPayload)?;

        let msg_type = header.validate()?;
        let payload_len = header.payload_len as usize;

        if data.len() < WireHeader::SIZE + payload_len {
            return Err(ProtocolError::InsufficientData);
        }

        let payload = &data[WireHeader::SIZE..WireHeader::SIZE + payload_len];

        // Verify CRC
        let computed_crc = crc32fast::hash(payload);
        if computed_crc != header.crc32 {
            return Err(ProtocolError::CrcMismatch);
        }

        match msg_type {
            MessageType::GossipClock => {
                if payload.len() != 64 {
                    return Err(ProtocolError::MalformedPayload);
                }
                let clock = CausalClock::read_from_bytes(payload)
                    .map_err(|_| ProtocolError::MalformedPayload)?;
                Ok(NetworkMessage::GossipClock(clock))
            }
            MessageType::PushFact => {
                if payload.len() < 32 {
                    return Err(ProtocolError::MalformedPayload);
                }
                let mut fact_id = [0u8; 32];
                fact_id.copy_from_slice(&payload[..32]);
                let fact_payload = payload[32..].to_vec();
                Ok(NetworkMessage::PushFact {
                    fact_id,
                    payload: fact_payload,
                })
            }
            MessageType::PullRequest => {
                if payload.len() < 4 {
                    return Err(ProtocolError::MalformedPayload);
                }
                let count = u32::from_le_bytes(payload[..4].try_into().unwrap()) as usize;
                if payload.len() != 4 + count * 32 {
                    return Err(ProtocolError::MalformedPayload);
                }
                let mut fact_ids = Vec::with_capacity(count);
                for i in 0..count {
                    let mut id = [0u8; 32];
                    id.copy_from_slice(&payload[4 + i * 32..4 + (i + 1) * 32]);
                    fact_ids.push(id);
                }
                Ok(NetworkMessage::PullRequest { fact_ids })
            }
            MessageType::PullResponse => {
                if payload.len() < 4 {
                    return Err(ProtocolError::MalformedPayload);
                }
                let count = u32::from_le_bytes(payload[..4].try_into().unwrap()) as usize;
                let mut facts = Vec::with_capacity(count);
                let mut offset = 4;
                for _ in 0..count {
                    if offset + 36 > payload.len() {
                        return Err(ProtocolError::MalformedPayload);
                    }
                    let mut id = [0u8; 32];
                    id.copy_from_slice(&payload[offset..offset + 32]);
                    offset += 32;
                    let len = u32::from_le_bytes(payload[offset..offset + 4].try_into().unwrap())
                        as usize;
                    offset += 4;
                    if offset + len > payload.len() {
                        return Err(ProtocolError::MalformedPayload);
                    }
                    let data = payload[offset..offset + len].to_vec();
                    offset += len;
                    facts.push((id, data));
                }
                Ok(NetworkMessage::PullResponse { facts })
            }
        }
    }
}

/// Reconcile two clocks: returns FactIds that remote has but local doesn't.
/// This is approximate due to Bloom filter nature—may include false positives.
pub fn reconcile_clocks(local: &CausalClock, remote: &CausalClock) -> bool {
    // If remote has bits we don't, they have facts we're missing
    !local.dominates(remote)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_wire_header_size() {
        assert_eq!(core::mem::size_of::<WireHeader>(), 14);
    }

    #[test]
    fn test_gossip_clock_roundtrip() {
        let mut clock = CausalClock::new();
        clock.observe(&[1u8; 32]);
        clock.observe(&[2u8; 32]);

        let msg = NetworkMessage::GossipClock(clock);
        let encoded = msg.encode();
        let decoded = NetworkMessage::decode(&encoded).unwrap();

        match decoded {
            NetworkMessage::GossipClock(c) => {
                assert!(c.might_contain(&[1u8; 32]));
                assert!(c.might_contain(&[2u8; 32]));
            }
            _ => panic!("wrong message type"),
        }
    }

    #[test]
    fn test_push_fact_roundtrip() {
        let fact_id = [0xAB; 32];
        let payload = vec![1, 2, 3, 4, 5];

        let msg = NetworkMessage::PushFact {
            fact_id,
            payload: payload.clone(),
        };
        let encoded = msg.encode();
        let decoded = NetworkMessage::decode(&encoded).unwrap();

        match decoded {
            NetworkMessage::PushFact {
                fact_id: id,
                payload: p,
            } => {
                assert_eq!(id, fact_id);
                assert_eq!(p, payload);
            }
            _ => panic!("wrong message type"),
        }
    }

    #[test]
    fn test_pull_request_roundtrip() {
        let fact_ids = vec![[1u8; 32], [2u8; 32], [3u8; 32]];

        let msg = NetworkMessage::PullRequest {
            fact_ids: fact_ids.clone(),
        };
        let encoded = msg.encode();
        let decoded = NetworkMessage::decode(&encoded).unwrap();

        match decoded {
            NetworkMessage::PullRequest { fact_ids: ids } => {
                assert_eq!(ids, fact_ids);
            }
            _ => panic!("wrong message type"),
        }
    }

    #[test]
    fn test_crc_mismatch() {
        let clock = CausalClock::new();
        let msg = NetworkMessage::GossipClock(clock);
        let mut encoded = msg.encode();

        // Corrupt payload
        if encoded.len() > WireHeader::SIZE {
            encoded[WireHeader::SIZE] ^= 0xFF;
        }

        let result = NetworkMessage::decode(&encoded);
        assert_eq!(result.unwrap_err(), ProtocolError::CrcMismatch);
    }
}
