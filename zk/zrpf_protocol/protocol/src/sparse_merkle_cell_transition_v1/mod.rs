mod binding;
mod codec;
mod error;
mod hash;
mod path;
mod witness;

pub use binding::{bind_sparse_merkle_cell_transition_v1, ValidatedSparseMerkleCellTransitionV1};
pub use codec::{
    decode_exact_sparse_merkle_cell_transition_witness_v1,
    encode_sparse_merkle_cell_transition_witness_v1,
};
pub use error::SparseMerkleCellTransitionErrorV1;
pub use hash::{
    derive_sparse_merkle_internal_commitment_v1, derive_sparse_merkle_leaf_commitment_v1,
    derive_sparse_merkle_root_v1,
};
pub use path::SparseMerkleSiblingPathV1;
pub use witness::{SparseMerkleCellTransitionWitnessInputV1, SparseMerkleCellTransitionWitnessV1};

/// One binary sparse-Merkle path bit for every bit in a 32-byte cell key.
pub const SPARSE_MERKLE_TREE_DEPTH_V1: usize = 256;
pub const SPARSE_MERKLE_WITNESS_VERSION_V1: u16 = 1;

/// Exact canonical Postcard size for the fixed-field V1 witness.
pub const SPARSE_MERKLE_CELL_TRANSITION_WITNESS_BYTES_V1: usize = 8_385;

/// Fixed witness fields require 8,385 canonical Postcard bytes in V1.
///
/// The slightly larger ceiling keeps malformed-input classification stable
/// while preserving a small hard bound before decoding.
pub const MAX_SPARSE_MERKLE_CELL_TRANSITION_WITNESS_BYTES_V1: usize = 8_512;
