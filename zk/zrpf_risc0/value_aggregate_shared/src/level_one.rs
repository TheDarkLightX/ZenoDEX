use alloc::vec::Vec;

use zenodex_zrpf_protocol_v3::{
    merge_semantic_subtrees_v2, ProposedValueAggregateV5, ValueAggregateProposalInputV5,
};

use crate::child::{level_one_children, reject_duplicate_children};
use crate::{
    ValueAggregateLevelOneInputV5, ValueAggregateRecompositionErrorV5,
    ValueAggregateRecompositionPolicyV5,
};

/// Recompose the exact level-one proposal implied by canonical V4 child
/// journal bytes and governed child identities.
///
/// This function verifies no receipt. Its result is a proof-neutral expected
/// statement and carries no ledger or settlement authority.
pub fn recompose_expected_value_aggregate_level_one_v5(
    input: &ValueAggregateLevelOneInputV5,
    policy: &ValueAggregateRecompositionPolicyV5,
) -> Result<ProposedValueAggregateV5, ValueAggregateRecompositionErrorV5> {
    let children = level_one_children(input.child_journal_bytes(), policy)?;
    reject_duplicate_children(&children)?;
    let subtrees = children
        .iter()
        .map(|child| child.subtree.clone())
        .collect::<Vec<_>>();
    let semantic_subtree = merge_semantic_subtrees_v2(&subtrees)
        .map_err(ValueAggregateRecompositionErrorV5::SemanticMerge)?;
    let descriptors = children.into_iter().map(|child| child.descriptor).collect();
    ProposedValueAggregateV5::derive(ValueAggregateProposalInputV5 {
        aggregate_level: 1,
        scope: policy.expected_scope().clone(),
        semantic_subtree,
        children: descriptors,
    })
    .map_err(Into::into)
}

/// Enter level-one composition only after the caller has verified each exact
/// child receipt under the corresponding governed image ID.
///
/// The wrapper deliberately carries no receipt typestate and grants no proof
/// authority. A future guest must enforce the precondition before calling it.
pub fn compose_value_aggregate_level_one_after_receipt_verification_v5(
    input: &ValueAggregateLevelOneInputV5,
    policy: &ValueAggregateRecompositionPolicyV5,
) -> Result<ProposedValueAggregateV5, ValueAggregateRecompositionErrorV5> {
    recompose_expected_value_aggregate_level_one_v5(input, policy)
}
