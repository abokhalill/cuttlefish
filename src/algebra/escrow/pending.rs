//! Pending quota request state machine. Retry with exponential backoff.

use std::collections::HashMap;
use std::net::SocketAddr;
use std::time::{Duration, Instant};

/// Request state for tracking in-flight quota requests.
#[derive(Debug, Clone)]
pub struct PendingRequest {
    pub request_id: u64,
    pub invariant_id: u64,
    pub amount: i128,
    pub submitted_at: Instant,
    pub retry_count: u32,
    pub last_attempt: Instant,
    pub peers_tried: Vec<SocketAddr>,
}

impl PendingRequest {
    pub fn new(request_id: u64, invariant_id: u64, amount: i128) -> Self {
        let now = Instant::now();
        Self {
            request_id,
            invariant_id,
            amount,
            submitted_at: now,
            retry_count: 0,
            last_attempt: now,
            peers_tried: Vec::new(),
        }
    }

    /// Check if request has timed out (no response within timeout).
    pub fn is_timed_out(&self, timeout: Duration) -> bool {
        self.last_attempt.elapsed() > timeout
    }

    /// Get backoff duration for next retry. Exponential: 500ms, 1s, 2s, 4s cap.
    pub fn backoff_duration(&self) -> Duration {
        let base_ms = 500u64;
        let max_ms = 4000u64;
        let backoff_ms = base_ms.saturating_mul(1u64 << self.retry_count.min(3));
        Duration::from_millis(backoff_ms.min(max_ms))
    }

    /// Record a retry attempt.
    pub fn record_retry(&mut self, peer: SocketAddr) {
        self.retry_count += 1;
        self.last_attempt = Instant::now();
        if !self.peers_tried.contains(&peer) {
            self.peers_tried.push(peer);
        }
    }

    /// Check if we should retry now.
    pub fn should_retry(&self, timeout: Duration) -> bool {
        self.is_timed_out(timeout) && self.last_attempt.elapsed() >= self.backoff_duration()
    }

    /// Total time since request was first submitted.
    pub fn age(&self) -> Duration {
        self.submitted_at.elapsed()
    }
}

/// Manages pending quota requests with retry logic.
#[derive(Debug)]
pub struct PendingRequestMap {
    requests: HashMap<u64, PendingRequest>,
    timeout: Duration,
    max_retries: u32,
    max_age: Duration,
}

impl PendingRequestMap {
    pub const DEFAULT_TIMEOUT_MS: u64 = 500;
    pub const DEFAULT_MAX_RETRIES: u32 = 5;
    pub const DEFAULT_MAX_AGE_MS: u64 = 30_000;

    pub fn new() -> Self {
        Self {
            requests: HashMap::new(),
            timeout: Duration::from_millis(Self::DEFAULT_TIMEOUT_MS),
            max_retries: Self::DEFAULT_MAX_RETRIES,
            max_age: Duration::from_millis(Self::DEFAULT_MAX_AGE_MS),
        }
    }

    pub fn with_config(timeout_ms: u64, max_retries: u32, max_age_ms: u64) -> Self {
        Self {
            requests: HashMap::new(),
            timeout: Duration::from_millis(timeout_ms),
            max_retries,
            max_age: Duration::from_millis(max_age_ms),
        }
    }

    /// Insert a new pending request.
    pub fn insert(&mut self, request: PendingRequest) {
        self.requests.insert(request.request_id, request);
    }

    /// Remove a request (on success or permanent failure).
    pub fn remove(&mut self, request_id: u64) -> Option<PendingRequest> {
        self.requests.remove(&request_id)
    }

    /// Get a request by ID.
    pub fn get(&self, request_id: u64) -> Option<&PendingRequest> {
        self.requests.get(&request_id)
    }

    /// Get mutable request by ID.
    pub fn get_mut(&mut self, request_id: u64) -> Option<&mut PendingRequest> {
        self.requests.get_mut(&request_id)
    }

    /// Get all requests that need retry.
    pub fn get_retry_candidates(&self) -> Vec<u64> {
        self.requests
            .iter()
            .filter(|(_, req)| {
                req.should_retry(self.timeout)
                    && req.retry_count < self.max_retries
                    && req.age() < self.max_age
            })
            .map(|(id, _)| *id)
            .collect()
    }

    /// Get all requests that have permanently failed (max retries or too old).
    pub fn get_failed_requests(&self) -> Vec<u64> {
        self.requests
            .iter()
            .filter(|(_, req)| req.retry_count >= self.max_retries || req.age() >= self.max_age)
            .map(|(id, _)| *id)
            .collect()
    }

    /// Prune failed requests, returning them.
    pub fn prune_failed(&mut self) -> Vec<PendingRequest> {
        let failed_ids = self.get_failed_requests();
        failed_ids
            .into_iter()
            .filter_map(|id| self.requests.remove(&id))
            .collect()
    }

    /// Number of pending requests.
    pub fn len(&self) -> usize {
        self.requests.len()
    }

    pub fn is_empty(&self) -> bool {
        self.requests.is_empty()
    }

    /// Select next peer to try, avoiding already-tried peers if possible.
    pub fn select_peer<'a>(
        &self,
        request_id: u64,
        available_peers: &'a [SocketAddr],
    ) -> Option<&'a SocketAddr> {
        let req = self.requests.get(&request_id)?;

        // Prefer peers we haven't tried yet
        for peer in available_peers {
            if !req.peers_tried.contains(peer) {
                return Some(peer);
            }
        }

        // Fall back to any peer (round-robin based on retry count)
        if !available_peers.is_empty() {
            let idx = req.retry_count as usize % available_peers.len();
            return Some(&available_peers[idx]);
        }

        None
    }
}

impl Default for PendingRequestMap {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pending_request_backoff() {
        let mut req = PendingRequest::new(1, 100, 50);

        assert_eq!(req.backoff_duration(), Duration::from_millis(500));

        req.retry_count = 1;
        assert_eq!(req.backoff_duration(), Duration::from_millis(1000));

        req.retry_count = 2;
        assert_eq!(req.backoff_duration(), Duration::from_millis(2000));

        req.retry_count = 3;
        assert_eq!(req.backoff_duration(), Duration::from_millis(4000));

        // Capped at 4s
        req.retry_count = 10;
        assert_eq!(req.backoff_duration(), Duration::from_millis(4000));
    }

    #[test]
    fn test_pending_request_map() {
        let mut map = PendingRequestMap::new();

        let req = PendingRequest::new(1, 100, 50);
        map.insert(req);

        assert_eq!(map.len(), 1);
        assert!(map.get(1).is_some());

        map.remove(1);
        assert!(map.is_empty());
    }

    #[test]
    fn test_peer_selection() {
        let mut map = PendingRequestMap::new();
        let mut req = PendingRequest::new(1, 100, 50);

        let peer1: SocketAddr = "127.0.0.1:9000".parse().unwrap();
        let peer2: SocketAddr = "127.0.0.1:9001".parse().unwrap();
        let peers = vec![peer1, peer2];

        map.insert(req.clone());

        // First selection: peer1 (not tried)
        let selected = map.select_peer(1, &peers);
        assert_eq!(selected, Some(&peer1));

        // Mark peer1 as tried
        req.peers_tried.push(peer1);
        map.requests.insert(1, req.clone());

        // Second selection: peer2 (not tried)
        let selected = map.select_peer(1, &peers);
        assert_eq!(selected, Some(&peer2));

        // Mark peer2 as tried
        req.peers_tried.push(peer2);
        map.requests.insert(1, req);

        // Third selection: round-robin (all tried)
        let selected = map.select_peer(1, &peers);
        assert!(selected.is_some());
    }
}
