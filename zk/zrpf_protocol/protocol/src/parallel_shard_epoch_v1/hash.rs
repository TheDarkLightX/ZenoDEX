use sha2::{Digest, Sha256};

use super::{
    CanonicalShardStateMapV1, DeclaredShardSetV1, ParallelShardEpochErrorV1, ShardIdV1,
    ShardTransitionV1, PARALLEL_SHARD_COUNT_V1, PARALLEL_SHARD_EPOCH_VERSION_V1,
};
use crate::{CommitmentV3, NodeScopeV3, ProfileIdV3};

const EMPTY_CROSS_SHARD_OUTBOX_DOMAIN_V1: &[u8] = b"zenodex.zrpf.parallel_shard.empty_outbox.v1";
const EMPTY_CROSS_SHARD_INBOX_DOMAIN_V1: &[u8] = b"zenodex.zrpf.parallel_shard.empty_inbox.v1";
const EMPTY_CARRY_QUEUE_DOMAIN_V1: &[u8] = b"zenodex.zrpf.parallel_shard.empty_carry_queue.v1";
const DECLARED_SHARD_SET_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.parallel_shard.declared_set.v1";
const GLOBAL_PRE_STATE_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.parallel_shard.global_pre_state.v1";
const GLOBAL_POST_STATE_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.parallel_shard.global_post_state.v1";
const SHARD_SEMANTIC_VALUES_ROOT_DOMAIN_V1: &[u8] =
    b"zenodex.zrpf.parallel_shard.semantic_values.v1";
const SHARD_ACTION_NULLIFIERS_ROOT_DOMAIN_V1: &[u8] =
    b"zenodex.zrpf.parallel_shard.action_nullifiers.v1";
const GLOBAL_OUTBOX_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.parallel_shard.global_outbox.v1";
const GLOBAL_INBOX_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.parallel_shard.global_inbox.v1";
const GLOBAL_CARRY_PRE_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.parallel_shard.global_carry_pre.v1";
const GLOBAL_CARRY_POST_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.parallel_shard.global_carry_post.v1";
const SEMANTIC_EPOCH_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.parallel_shard.semantic_epoch_root.v1";
const PROPOSAL_HASH_DOMAIN_V1: &[u8] = b"zenodex.zrpf.parallel_shard.proposal_hash.v1";

pub fn canonical_empty_cross_shard_outbox_root_v1(
) -> Result<CommitmentV3, ParallelShardEpochErrorV1> {
    empty_list_root(EMPTY_CROSS_SHARD_OUTBOX_DOMAIN_V1)
}

pub fn canonical_empty_cross_shard_inbox_root_v1() -> Result<CommitmentV3, ParallelShardEpochErrorV1>
{
    empty_list_root(EMPTY_CROSS_SHARD_INBOX_DOMAIN_V1)
}

pub fn canonical_empty_carry_queue_root_v1() -> Result<CommitmentV3, ParallelShardEpochErrorV1> {
    empty_list_root(EMPTY_CARRY_QUEUE_DOMAIN_V1)
}

pub(super) fn derive_declared_shard_set_root_v1(
    shard_ids: &[ShardIdV1; PARALLEL_SHARD_COUNT_V1],
) -> Result<CommitmentV3, ParallelShardEpochErrorV1> {
    let mut hasher = domain_hasher(DECLARED_SHARD_SET_ROOT_DOMAIN_V1)?;
    write_len(&mut hasher, shard_ids.len())?;
    for shard_id in shard_ids {
        hasher.update(shard_id.as_bytes());
    }
    commitment(hasher, "declared_shard_set_root")
}

pub(super) fn derive_global_pre_state_root_v1(
    state_map: &CanonicalShardStateMapV1,
) -> Result<CommitmentV3, ParallelShardEpochErrorV1> {
    derive_keyed_map_root(GLOBAL_PRE_STATE_ROOT_DOMAIN_V1, state_map, |entry| {
        entry.local_pre_state_root()
    })
}

pub(super) fn derive_global_post_state_root_v1(
    state_map: &CanonicalShardStateMapV1,
) -> Result<CommitmentV3, ParallelShardEpochErrorV1> {
    derive_keyed_map_root(GLOBAL_POST_STATE_ROOT_DOMAIN_V1, state_map, |entry| {
        entry.local_post_state_root()
    })
}

pub(super) fn derive_shard_semantic_values_root_v1(
    state_map: &CanonicalShardStateMapV1,
) -> Result<CommitmentV3, ParallelShardEpochErrorV1> {
    derive_keyed_map_root(SHARD_SEMANTIC_VALUES_ROOT_DOMAIN_V1, state_map, |entry| {
        entry.semantic_value_root()
    })
}

pub(super) fn derive_shard_action_nullifiers_root_v1(
    state_map: &CanonicalShardStateMapV1,
) -> Result<CommitmentV3, ParallelShardEpochErrorV1> {
    derive_keyed_map_root(SHARD_ACTION_NULLIFIERS_ROOT_DOMAIN_V1, state_map, |entry| {
        entry.shard_action_nullifiers_root()
    })
}

pub(super) fn derive_global_outbox_root_v1(
    state_map: &CanonicalShardStateMapV1,
) -> Result<CommitmentV3, ParallelShardEpochErrorV1> {
    derive_keyed_map_root(GLOBAL_OUTBOX_ROOT_DOMAIN_V1, state_map, |entry| {
        entry.cross_shard_outbox_root()
    })
}

pub(super) fn derive_global_inbox_root_v1(
    state_map: &CanonicalShardStateMapV1,
) -> Result<CommitmentV3, ParallelShardEpochErrorV1> {
    derive_keyed_map_root(GLOBAL_INBOX_ROOT_DOMAIN_V1, state_map, |entry| {
        entry.cross_shard_inbox_root()
    })
}

pub(super) fn derive_global_carry_pre_root_v1(
    state_map: &CanonicalShardStateMapV1,
) -> Result<CommitmentV3, ParallelShardEpochErrorV1> {
    derive_keyed_map_root(GLOBAL_CARRY_PRE_ROOT_DOMAIN_V1, state_map, |entry| {
        entry.carry_queue_pre_root()
    })
}

pub(super) fn derive_global_carry_post_root_v1(
    state_map: &CanonicalShardStateMapV1,
) -> Result<CommitmentV3, ParallelShardEpochErrorV1> {
    derive_keyed_map_root(GLOBAL_CARRY_POST_ROOT_DOMAIN_V1, state_map, |entry| {
        entry.carry_queue_post_root()
    })
}

pub(super) struct SemanticEpochRootInputV1<'a> {
    pub scope: &'a NodeScopeV3,
    pub semantic_profile_id: ProfileIdV3,
    pub state_root_scheme_id: CommitmentV3,
    pub declared_shard_set: &'a DeclaredShardSetV1,
    pub state_map: &'a CanonicalShardStateMapV1,
}

pub(super) fn derive_semantic_epoch_root_v1(
    input: SemanticEpochRootInputV1<'_>,
) -> Result<CommitmentV3, ParallelShardEpochErrorV1> {
    let mut hasher = domain_hasher(SEMANTIC_EPOCH_ROOT_DOMAIN_V1)?;
    hasher.update(PARALLEL_SHARD_EPOCH_VERSION_V1.to_be_bytes());
    hasher.update(input.scope.canonical_hash()?.as_bytes());
    hasher.update(input.semantic_profile_id.as_bytes());
    hasher.update(input.state_root_scheme_id.as_bytes());
    hasher.update(input.declared_shard_set.canonical_root()?.as_bytes());
    for root in input.state_map.semantic_roots()? {
        hasher.update(root.as_bytes());
    }
    commitment(hasher, "semantic_epoch_root")
}

pub(super) fn derive_proposal_hash_v1(
    semantic_epoch_root: CommitmentV3,
    proof_tree_root: CommitmentV3,
) -> Result<CommitmentV3, ParallelShardEpochErrorV1> {
    let mut hasher = domain_hasher(PROPOSAL_HASH_DOMAIN_V1)?;
    hasher.update(PARALLEL_SHARD_EPOCH_VERSION_V1.to_be_bytes());
    hasher.update(semantic_epoch_root.as_bytes());
    hasher.update(proof_tree_root.as_bytes());
    commitment(hasher, "proposal_hash")
}

fn derive_keyed_map_root(
    domain: &[u8],
    state_map: &CanonicalShardStateMapV1,
    value: impl Fn(&ShardTransitionV1) -> CommitmentV3,
) -> Result<CommitmentV3, ParallelShardEpochErrorV1> {
    let entries = state_map.entries();
    let mut hasher = domain_hasher(domain)?;
    write_len(&mut hasher, entries.len())?;
    for entry in entries {
        hasher.update(entry.shard_id().as_bytes());
        hasher.update(value(entry).as_bytes());
    }
    commitment(hasher, "keyed_map_root")
}

fn empty_list_root(domain: &[u8]) -> Result<CommitmentV3, ParallelShardEpochErrorV1> {
    let mut hasher = domain_hasher(domain)?;
    hasher.update(0_u32.to_be_bytes());
    commitment(hasher, "empty_list_root")
}

fn domain_hasher(domain: &[u8]) -> Result<Sha256, ParallelShardEpochErrorV1> {
    let length = u16::try_from(domain.len())
        .map_err(|_| ParallelShardEpochErrorV1::ArithmeticOverflow("hash_domain_length"))?;
    let mut hasher = Sha256::new();
    hasher.update(length.to_be_bytes());
    hasher.update(domain);
    Ok(hasher)
}

fn write_len(hasher: &mut Sha256, length: usize) -> Result<(), ParallelShardEpochErrorV1> {
    let length = u32::try_from(length)
        .map_err(|_| ParallelShardEpochErrorV1::ArithmeticOverflow("map_length"))?;
    hasher.update(length.to_be_bytes());
    Ok(())
}

fn commitment(
    hasher: Sha256,
    field: &'static str,
) -> Result<CommitmentV3, ParallelShardEpochErrorV1> {
    CommitmentV3::new(hasher.finalize().into())
        .map_err(|_| ParallelShardEpochErrorV1::DerivedRootMismatch(field))
}
