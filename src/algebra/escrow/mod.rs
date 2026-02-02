//! Escrow for BoundedCommutative. Partition headroom → local ops stay coordination-free.

#[cfg(feature = "std")]
pub mod pending;

#[cfg(feature = "std")]
pub use pending::{PendingRequest, PendingRequestMap};

use crate::core::topology::FactId;

pub type NodeId = u64;

/// Per-node quota. Consume locally, transfer when short.
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct EscrowAllocation {
    pub node_id: NodeId,
    pub quota: i128,
    pub used: i128,
}

impl EscrowAllocation {
    pub const fn new(node_id: NodeId, quota: i128) -> Self {
        Self {
            node_id,
            quota,
            used: 0,
        }
    }

    #[inline(always)]
    pub const fn available(&self) -> i128 {
        self.quota - self.used
    }

    #[inline(always)]
    pub fn can_consume(&self, amount: i128) -> bool {
        amount <= self.available()
    }

    #[inline(always)]
    pub fn consume(&mut self, amount: i128) -> Result<(), EscrowError> {
        if amount > self.available() {
            return Err(EscrowError::InsufficientEscrow {
                requested: amount,
                available: self.available(),
            });
        }
        self.used += amount;
        Ok(())
    }

    #[inline(always)]
    pub fn release(&mut self, amount: i128) {
        self.used = self.used.saturating_sub(amount);
    }

    #[inline(always)]
    pub fn transfer_to(&mut self, other: &mut Self, amount: i128) -> Result<(), EscrowError> {
        if amount > self.available() {
            return Err(EscrowError::InsufficientEscrow {
                requested: amount,
                available: self.available(),
            });
        }
        self.quota -= amount;
        other.quota += amount;
        Ok(())
    }
}

/// The usual suspects.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EscrowError {
    InsufficientEscrow { requested: i128, available: i128 },
    NodeNotFound,
    InvalidTransfer,
    QuotaExhausted,
}

/// Orchestrates the whole escrow dance.
#[derive(Debug)]
pub struct EscrowManager {
    total_headroom: i128,
    allocations: [Option<EscrowAllocation>; 16],
    node_count: usize,
}

impl EscrowManager {
    pub const MAX_NODES: usize = 16;

    pub const fn new(total_headroom: i128) -> Self {
        Self {
            total_headroom,
            allocations: [None; 16],
            node_count: 0,
        }
    }

    /// Initialize escrow with equal distribution across nodes.
    pub fn initialize(&mut self, node_ids: &[NodeId]) -> Result<(), EscrowError> {
        if node_ids.len() > Self::MAX_NODES {
            return Err(EscrowError::InvalidTransfer);
        }

        let n = node_ids.len() as i128;
        let base_quota = self.total_headroom / n;
        let remainder = self.total_headroom % n;

        for (i, &node_id) in node_ids.iter().enumerate() {
            let extra = if (i as i128) < remainder { 1 } else { 0 };
            self.allocations[i] = Some(EscrowAllocation::new(node_id, base_quota + extra));
        }
        self.node_count = node_ids.len();

        Ok(())
    }

    /// Get allocation for a node.
    pub fn get(&self, node_id: NodeId) -> Option<&EscrowAllocation> {
        self.allocations[..self.node_count]
            .iter()
            .flatten()
            .find(|a| a.node_id == node_id)
    }

    /// Get mutable allocation for a node.
    pub fn get_mut(&mut self, node_id: NodeId) -> Option<&mut EscrowAllocation> {
        self.allocations[..self.node_count]
            .iter_mut()
            .flatten()
            .find(|a| a.node_id == node_id)
    }

    /// Try to consume escrow for a local operation.
    pub fn try_consume(&mut self, node_id: NodeId, amount: i128) -> Result<(), EscrowError> {
        self.get_mut(node_id)
            .ok_or(EscrowError::NodeNotFound)?
            .consume(amount)
    }

    /// Release escrow after operation completion or rollback.
    pub fn release(&mut self, node_id: NodeId, amount: i128) -> Result<(), EscrowError> {
        self.get_mut(node_id)
            .ok_or(EscrowError::NodeNotFound)
            .map(|a| a.release(amount))
    }

    /// Transfer escrow between nodes.
    pub fn transfer(
        &mut self,
        from_node: NodeId,
        to_node: NodeId,
        amount: i128,
    ) -> Result<(), EscrowError> {
        // Find indices
        let from_idx = self.allocations[..self.node_count]
            .iter()
            .position(|a| a.map(|x| x.node_id) == Some(from_node))
            .ok_or(EscrowError::NodeNotFound)?;

        let to_idx = self.allocations[..self.node_count]
            .iter()
            .position(|a| a.map(|x| x.node_id) == Some(to_node))
            .ok_or(EscrowError::NodeNotFound)?;

        if from_idx == to_idx {
            return Err(EscrowError::InvalidTransfer);
        }

        // Check source has enough
        let from_available = self.allocations[from_idx]
            .as_ref()
            .map(|a| a.available())
            .unwrap_or(0);

        if amount > from_available {
            return Err(EscrowError::InsufficientEscrow {
                requested: amount,
                available: from_available,
            });
        }

        // Perform transfer
        if let Some(ref mut from) = self.allocations[from_idx] {
            from.quota -= amount;
        }
        if let Some(ref mut to) = self.allocations[to_idx] {
            to.quota += amount;
        }

        Ok(())
    }

    /// Get total allocated escrow (should equal total_headroom).
    pub fn total_allocated(&self) -> i128 {
        self.allocations[..self.node_count]
            .iter()
            .flatten()
            .map(|a| a.quota)
            .sum()
    }

    /// Get total used escrow across all nodes.
    pub fn total_used(&self) -> i128 {
        self.allocations[..self.node_count]
            .iter()
            .flatten()
            .map(|a| a.used)
            .sum()
    }

    /// Rebalance escrow across nodes (called periodically by coordinator).
    pub fn rebalance(&mut self) {
        if self.node_count == 0 {
            return;
        }

        // Collect unused escrow
        let total_unused: i128 = self.allocations[..self.node_count]
            .iter()
            .flatten()
            .map(|a| a.available())
            .sum();

        // Redistribute equally
        let n = self.node_count as i128;
        let base = total_unused / n;
        let remainder = total_unused % n;

        for (i, alloc) in self.allocations[..self.node_count].iter_mut().enumerate() {
            if let Some(ref mut a) = alloc {
                let extra = if (i as i128) < remainder { 1 } else { 0 };
                a.quota = a.used + base + extra;
            }
        }
    }
}

/// Wire format for "gimme some headroom".
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct EscrowTransferRequest {
    pub request_id: FactId,
    pub from_node: NodeId,
    pub to_node: NodeId,
    pub amount: i128,
}

/// Wire format for "here you go" (or not).
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct EscrowTransferResponse {
    pub request_id: FactId,
    pub granted: i128,
    pub success: bool,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_escrow_allocation_basic() {
        let mut alloc = EscrowAllocation::new(1, 100);
        assert_eq!(alloc.available(), 100);

        alloc.consume(30).unwrap();
        assert_eq!(alloc.available(), 70);
        assert_eq!(alloc.used, 30);

        alloc.release(10);
        assert_eq!(alloc.available(), 80);
        assert_eq!(alloc.used, 20);
    }

    #[test]
    fn test_escrow_allocation_insufficient() {
        let mut alloc = EscrowAllocation::new(1, 100);
        alloc.consume(50).unwrap();

        let result = alloc.consume(60);
        assert!(matches!(
            result,
            Err(EscrowError::InsufficientEscrow {
                requested: 60,
                available: 50
            })
        ));
    }

    #[test]
    fn test_escrow_manager_initialize() {
        let mut mgr = EscrowManager::new(1000);
        mgr.initialize(&[1, 2, 3]).unwrap();

        // Should distribute 333, 333, 334
        assert_eq!(mgr.get(1).unwrap().quota, 334);
        assert_eq!(mgr.get(2).unwrap().quota, 333);
        assert_eq!(mgr.get(3).unwrap().quota, 333);
        assert_eq!(mgr.total_allocated(), 1000);
    }

    #[test]
    fn test_escrow_manager_consume_release() {
        let mut mgr = EscrowManager::new(1000);
        mgr.initialize(&[1, 2]).unwrap();

        mgr.try_consume(1, 200).unwrap();
        assert_eq!(mgr.get(1).unwrap().available(), 300);

        mgr.release(1, 50).unwrap();
        assert_eq!(mgr.get(1).unwrap().available(), 350);
    }

    #[test]
    fn test_escrow_manager_transfer() {
        let mut mgr = EscrowManager::new(1000);
        mgr.initialize(&[1, 2]).unwrap();

        let initial_1 = mgr.get(1).unwrap().quota;
        let initial_2 = mgr.get(2).unwrap().quota;

        mgr.transfer(1, 2, 100).unwrap();

        assert_eq!(mgr.get(1).unwrap().quota, initial_1 - 100);
        assert_eq!(mgr.get(2).unwrap().quota, initial_2 + 100);
        assert_eq!(mgr.total_allocated(), 1000);
    }

    #[test]
    fn test_escrow_manager_rebalance() {
        let mut mgr = EscrowManager::new(1000);
        mgr.initialize(&[1, 2]).unwrap();

        // Node 1 uses 400, node 2 uses 100
        mgr.try_consume(1, 400).unwrap();
        mgr.try_consume(2, 100).unwrap();

        // Before rebalance: node 1 has 100 available, node 2 has 400 available
        assert_eq!(mgr.get(1).unwrap().available(), 100);
        assert_eq!(mgr.get(2).unwrap().available(), 400);

        mgr.rebalance();

        // After rebalance: 500 total unused, split 250/250
        // Node 1: used=400, quota=400+250=650
        // Node 2: used=100, quota=100+250=350
        assert_eq!(mgr.get(1).unwrap().available(), 250);
        assert_eq!(mgr.get(2).unwrap().available(), 250);
        assert_eq!(mgr.total_allocated(), 1000);
    }
}
