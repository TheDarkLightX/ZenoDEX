//! Bounded proof-neutral chaining of 1..=64 single-cell witnesses.
//!
//! V1 carries every full 256-sibling path. It establishes deterministic root
//! continuity and exact write equality only; it supplies no proof receipt,
//! atomic persistence, settlement, or ledger authority. A future compressed
//! multiproof must preserve this canonical write order and root-chain result.

mod batch;
mod bounded;
mod codec;
mod entry;
mod error;

pub use batch::{SparseMerkleBatchTransitionInputV1, ValidatedSparseMerkleBatchTransitionV1};
pub use codec::{
    decode_exact_sparse_merkle_batch_transition_v1, encode_sparse_merkle_batch_transition_v1,
    expected_sparse_merkle_batch_transition_bytes_v1,
};
pub use entry::{SparseMerkleBatchEntryInputV1, SparseMerkleBatchEntryV1};
pub use error::SparseMerkleBatchTransitionErrorV1;

use crate::SPARSE_MERKLE_CELL_TRANSITION_WITNESS_BYTES_V1;

pub const SPARSE_MERKLE_BATCH_VERSION_V1: u16 = 1;
pub const MAX_SPARSE_MERKLE_BATCH_ENTRIES_V1: usize = 64;

/// One fixed `LedgerCellWriteV2` plus one fixed single-cell witness.
pub const SPARSE_MERKLE_BATCH_ENTRY_BYTES_V1: usize =
    (4 * 32) + SPARSE_MERKLE_CELL_TRANSITION_WITNESS_BYTES_V1;

/// One-byte version, one-byte bounded count, and two 32-byte batch roots.
pub const SPARSE_MERKLE_BATCH_FIXED_BYTES_V1: usize = 66;

pub const MAX_SPARSE_MERKLE_BATCH_TRANSITION_BYTES_V1: usize = SPARSE_MERKLE_BATCH_FIXED_BYTES_V1
    + (MAX_SPARSE_MERKLE_BATCH_ENTRIES_V1 * SPARSE_MERKLE_BATCH_ENTRY_BYTES_V1);
