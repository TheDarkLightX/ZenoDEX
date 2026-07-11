use alloc::vec::Vec;
use core::cmp::Ordering;

use super::super::{
    CommitmentV3, NodeCommitmentsInputV3, NodeScopeV3, TaskIdV3, MAX_LEAF_COUNT_V3,
};
use super::hash::{
    commitment_root, task_ids_root, ASSET_DELTA_ROOTS_DOMAIN_V1, EFFECT_ROOTS_DOMAIN_V1,
    LEAF_RECORDS_ROOT_DOMAIN_V1, POST_STATE_ROOTS_DOMAIN_V1, PRE_STATE_ROOTS_DOMAIN_V1,
    SEMANTIC_SOURCES_ROOT_DOMAIN_V1, SOURCE_CLAIMS_ROOT_DOMAIN_V1, TASK_IDS_ROOT_DOMAIN_V1,
    TRANSACTION_ROOTS_DOMAIN_V1,
};
use super::proposal::SemanticEpochCommitmentsV1;
use super::{ProposedSemanticLeafV1, SemanticEpochErrorV1, SemanticSourceIdV1, SourceClaimIdV1};

pub(super) fn validate_leaf_set(
    leaves: &[ProposedSemanticLeafV1],
    scope: &NodeScopeV3,
) -> Result<(), SemanticEpochErrorV1> {
    if leaves.is_empty() {
        return Err(SemanticEpochErrorV1::EmptyLeaves);
    }
    let maximum = usize::try_from(MAX_LEAF_COUNT_V3)
        .map_err(|_| SemanticEpochErrorV1::ArithmeticOverflow("maximum_leaf_count"))?;
    if leaves.len() > maximum {
        return Err(SemanticEpochErrorV1::TooManyLeaves {
            actual: leaves.len(),
            maximum,
        });
    }
    validate_each_leaf(leaves, scope)?;
    validate_dense_leaf_order(leaves)?;
    validate_shared_leaf_policy(leaves)?;
    reject_duplicate_source_claims(leaves)?;
    reject_duplicate_semantic_sources(leaves)?;
    reject_duplicate_tasks(leaves)?;
    Ok(())
}

fn validate_each_leaf(
    leaves: &[ProposedSemanticLeafV1],
    scope: &NodeScopeV3,
) -> Result<(), SemanticEpochErrorV1> {
    for leaf in leaves {
        leaf.validate_profile_projection()?;
        if leaf.scope() != scope {
            return Err(SemanticEpochErrorV1::ScopeMismatch);
        }
    }
    Ok(())
}

fn validate_dense_leaf_order(
    leaves: &[ProposedSemanticLeafV1],
) -> Result<(), SemanticEpochErrorV1> {
    if leaves
        .windows(2)
        .any(|pair| leaf_order(&pair[0], &pair[1]) != Ordering::Less)
    {
        return Err(SemanticEpochErrorV1::NonCanonicalLeafOrder);
    }
    if leaves[0].partition().start() != 0 {
        return Err(SemanticEpochErrorV1::PartitionMustStartAtZero);
    }
    if leaves
        .windows(2)
        .any(|pair| pair[0].partition().end_exclusive() != pair[1].partition().start())
    {
        return Err(SemanticEpochErrorV1::NonContiguousLeafPartitions);
    }
    Ok(())
}

fn validate_shared_leaf_policy(
    leaves: &[ProposedSemanticLeafV1],
) -> Result<(), SemanticEpochErrorV1> {
    let expected_count_unit = leaves[0].count_unit_id();
    if leaves
        .iter()
        .any(|leaf| leaf.count_unit_id() != expected_count_unit)
    {
        return Err(SemanticEpochErrorV1::CountUnitMismatch);
    }
    let expected_program = leaves[0].leaf_program_id();
    if leaves
        .iter()
        .any(|leaf| leaf.leaf_program_id() != expected_program)
    {
        return Err(SemanticEpochErrorV1::LeafProgramMismatch);
    }
    Ok(())
}

fn leaf_order(left: &ProposedSemanticLeafV1, right: &ProposedSemanticLeafV1) -> Ordering {
    left.partition()
        .start()
        .cmp(&right.partition().start())
        .then_with(|| {
            left.partition()
                .end_exclusive()
                .cmp(&right.partition().end_exclusive())
        })
        .then_with(|| left.task_id().cmp(&right.task_id()))
}

fn reject_duplicate_source_claims(
    leaves: &[ProposedSemanticLeafV1],
) -> Result<(), SemanticEpochErrorV1> {
    let mut values: Vec<SourceClaimIdV1> = leaves
        .iter()
        .map(ProposedSemanticLeafV1::source_claim_id)
        .collect();
    values.sort_unstable();
    if values.windows(2).any(|pair| pair[0] == pair[1]) {
        return Err(SemanticEpochErrorV1::DuplicateSourceClaim);
    }
    Ok(())
}

fn reject_duplicate_semantic_sources(
    leaves: &[ProposedSemanticLeafV1],
) -> Result<(), SemanticEpochErrorV1> {
    let mut values: Vec<SemanticSourceIdV1> = leaves
        .iter()
        .map(ProposedSemanticLeafV1::semantic_source_id)
        .collect();
    values.sort_unstable();
    if values.windows(2).any(|pair| pair[0] == pair[1]) {
        return Err(SemanticEpochErrorV1::DuplicateSemanticSource);
    }
    Ok(())
}

fn reject_duplicate_tasks(leaves: &[ProposedSemanticLeafV1]) -> Result<(), SemanticEpochErrorV1> {
    let mut values: Vec<TaskIdV3> = leaves.iter().map(ProposedSemanticLeafV1::task_id).collect();
    values.sort_unstable();
    if values.windows(2).any(|pair| pair[0] == pair[1]) {
        return Err(SemanticEpochErrorV1::DuplicateTask);
    }
    Ok(())
}

struct LeafAlignedRootsV1 {
    leaf_records: CommitmentV3,
    pre_states: CommitmentV3,
    post_states: CommitmentV3,
    transactions: CommitmentV3,
    effects: CommitmentV3,
    asset_deltas: CommitmentV3,
}

pub(super) fn derive_epoch_commitments(
    leaves: &[ProposedSemanticLeafV1],
) -> Result<SemanticEpochCommitmentsV1, SemanticEpochErrorV1> {
    let aligned = derive_leaf_aligned_roots(leaves)?;
    let mut source_claims: Vec<CommitmentV3> = leaves
        .iter()
        .map(|leaf| leaf.source_claim_id().into_commitment())
        .collect();
    let mut semantic_sources: Vec<CommitmentV3> = leaves
        .iter()
        .map(|leaf| leaf.semantic_source_id().into_commitment())
        .collect();
    let mut task_ids: Vec<TaskIdV3> = leaves.iter().map(ProposedSemanticLeafV1::task_id).collect();
    source_claims.sort_unstable();
    semantic_sources.sort_unstable();
    task_ids.sort_unstable();
    Ok(SemanticEpochCommitmentsV1 {
        leaf_records_root: aligned.leaf_records,
        pre_state_roots_root: aligned.pre_states,
        post_state_roots_root: aligned.post_states,
        transaction_roots_root: aligned.transactions,
        effect_roots_root: aligned.effects,
        asset_delta_roots_root: aligned.asset_deltas,
        source_claim_ids_root: commitment_root(SOURCE_CLAIMS_ROOT_DOMAIN_V1, &source_claims)?,
        semantic_source_ids_root: commitment_root(
            SEMANTIC_SOURCES_ROOT_DOMAIN_V1,
            &semantic_sources,
        )?,
        task_ids_root: task_ids_root(TASK_IDS_ROOT_DOMAIN_V1, &task_ids)?,
    })
}

fn derive_leaf_aligned_roots(
    leaves: &[ProposedSemanticLeafV1],
) -> Result<LeafAlignedRootsV1, SemanticEpochErrorV1> {
    let leaf_hashes = leaves
        .iter()
        .map(ProposedSemanticLeafV1::canonical_hash)
        .collect::<Result<Vec<_>, _>>()?;
    let commitments: Vec<_> = leaves
        .iter()
        .map(|leaf| leaf.commitments().to_input())
        .collect();
    Ok(LeafAlignedRootsV1 {
        leaf_records: commitment_root(LEAF_RECORDS_ROOT_DOMAIN_V1, &leaf_hashes)?,
        pre_states: field_root(&commitments, PRE_STATE_ROOTS_DOMAIN_V1, |value| {
            value.pre_state_vector_root
        })?,
        post_states: field_root(&commitments, POST_STATE_ROOTS_DOMAIN_V1, |value| {
            value.post_state_vector_root
        })?,
        transactions: field_root(&commitments, TRANSACTION_ROOTS_DOMAIN_V1, |value| {
            value.transaction_root
        })?,
        effects: field_root(&commitments, EFFECT_ROOTS_DOMAIN_V1, |value| {
            value.effect_root
        })?,
        asset_deltas: field_root(&commitments, ASSET_DELTA_ROOTS_DOMAIN_V1, |value| {
            value.asset_delta_root
        })?,
    })
}

fn field_root(
    commitments: &[NodeCommitmentsInputV3],
    domain: &[u8],
    select: fn(&NodeCommitmentsInputV3) -> CommitmentV3,
) -> Result<CommitmentV3, SemanticEpochErrorV1> {
    let values = commitments.iter().map(select).collect::<Vec<_>>();
    commitment_root(domain, &values)
}
