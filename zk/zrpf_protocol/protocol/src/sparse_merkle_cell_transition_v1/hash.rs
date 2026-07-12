use sha2::{Digest, Sha256};

use super::{
    SparseMerkleCellTransitionErrorV1, SparseMerkleSiblingPathV1, SPARSE_MERKLE_TREE_DEPTH_V1,
};
use crate::{CommitmentV3, ValueHashV2};

const SPARSE_MERKLE_LEAF_DOMAIN_V1: &[u8] = b"zenodex.zrpf.sparse_merkle_leaf.v1";
const SPARSE_MERKLE_INTERNAL_DOMAIN_V1: &[u8] = b"zenodex.zrpf.sparse_merkle_internal.v1";

/// Hashes the V1 leaf preimage `domain || cell_key || value_hash`.
///
/// This deterministic helper authenticates bytes only. It grants no proof or
/// ledger authority.
pub fn derive_sparse_merkle_leaf_commitment_v1(
    cell_key: CommitmentV3,
    value_hash: ValueHashV2,
) -> Result<CommitmentV3, SparseMerkleCellTransitionErrorV1> {
    let mut hasher = domain_hasher(SPARSE_MERKLE_LEAF_DOMAIN_V1)?;
    hasher.update(cell_key.as_bytes());
    hasher.update(value_hash.as_bytes());
    finalize_commitment(hasher, "leaf")
}

/// Hashes one ordered V1 internal-node preimage at a root-indexed depth.
pub fn derive_sparse_merkle_internal_commitment_v1(
    depth: usize,
    left_child: CommitmentV3,
    right_child: CommitmentV3,
) -> Result<CommitmentV3, SparseMerkleCellTransitionErrorV1> {
    if depth >= SPARSE_MERKLE_TREE_DEPTH_V1 {
        return Err(SparseMerkleCellTransitionErrorV1::DepthOutOfRange(depth));
    }
    let depth = u16::try_from(depth)
        .map_err(|_| SparseMerkleCellTransitionErrorV1::ArithmeticOverflow("depth"))?;
    let mut hasher = domain_hasher(SPARSE_MERKLE_INTERNAL_DOMAIN_V1)?;
    hasher.update(depth.to_be_bytes());
    hasher.update(left_child.as_bytes());
    hasher.update(right_child.as_bytes());
    finalize_commitment(hasher, "internal_node")
}

/// Derives one fixed-depth root using MSB-first key bits.
///
/// Siblings are indexed from root depth zero to leaf-parent depth 255. Root
/// derivation therefore consumes them in reverse order.
pub fn derive_sparse_merkle_root_v1(
    cell_key: CommitmentV3,
    value_hash: ValueHashV2,
    siblings: &SparseMerkleSiblingPathV1,
) -> Result<CommitmentV3, SparseMerkleCellTransitionErrorV1> {
    let mut current = derive_sparse_merkle_leaf_commitment_v1(cell_key, value_hash)?;
    for depth in (0..SPARSE_MERKLE_TREE_DEPTH_V1).rev() {
        let path_byte = cell_key.as_bytes()[depth / 8];
        let path_bit = (path_byte >> (7 - (depth % 8))) & 1;
        let sibling = siblings.as_array()[depth];
        current = if path_bit == 0 {
            derive_sparse_merkle_internal_commitment_v1(depth, current, sibling)?
        } else {
            derive_sparse_merkle_internal_commitment_v1(depth, sibling, current)?
        };
    }
    Ok(current)
}

fn domain_hasher(domain: &[u8]) -> Result<Sha256, SparseMerkleCellTransitionErrorV1> {
    let length = u16::try_from(domain.len())
        .map_err(|_| SparseMerkleCellTransitionErrorV1::ArithmeticOverflow("hash_domain"))?;
    let mut hasher = Sha256::new();
    hasher.update(length.to_be_bytes());
    hasher.update(domain);
    Ok(hasher)
}

fn finalize_commitment(
    hasher: Sha256,
    field: &'static str,
) -> Result<CommitmentV3, SparseMerkleCellTransitionErrorV1> {
    CommitmentV3::new(hasher.finalize().into())
        .map_err(|_| SparseMerkleCellTransitionErrorV1::DerivedZeroCommitment(field))
}
