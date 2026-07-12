use alloc::vec::Vec;

use zenodex_zrpf_protocol_v3::{
    merge_semantic_subtrees_v2, ProposedValueAggregateV5, ValueAggregateProposalInputV5,
};

use crate::child::{level_two_children, reject_duplicate_children};
use crate::{
    ValueAggregateLevelTwoInputV5, ValueAggregateRecompositionErrorV5,
    ValueAggregateRecompositionPolicyV5,
};

/// Recompose the exact level-two proposal implied by canonical level-one V5
/// proposal bytes and governed child identities.
///
/// Child program, profile, and manifest identity comes only from the governed
/// policy. This pure operation authenticates no receipt and grants no ledger
/// or settlement authority.
pub fn recompose_expected_value_aggregate_level_two_v5(
    input: &ValueAggregateLevelTwoInputV5,
    policy: &ValueAggregateRecompositionPolicyV5,
) -> Result<ProposedValueAggregateV5, ValueAggregateRecompositionErrorV5> {
    let children = level_two_children(input.child_proposal_bytes(), policy)?;
    reject_duplicate_children(&children)?;
    let subtrees = children
        .iter()
        .map(|child| child.subtree.clone())
        .collect::<Vec<_>>();
    let semantic_subtree = merge_semantic_subtrees_v2(&subtrees)
        .map_err(ValueAggregateRecompositionErrorV5::SemanticMerge)?;
    let descriptors = children.into_iter().map(|child| child.descriptor).collect();
    ProposedValueAggregateV5::derive(ValueAggregateProposalInputV5 {
        aggregate_level: 2,
        scope: policy.expected_scope().clone(),
        semantic_subtree,
        children: descriptors,
    })
    .map_err(Into::into)
}

/// Enter level-two composition only after the caller has verified each exact
/// level-one receipt under the corresponding governed image ID.
///
/// The name records a caller precondition. The function itself has no receipt
/// bytes, invokes no verifier, and returns only a proof-neutral proposal.
pub fn compose_value_aggregate_level_two_after_receipt_verification_v5(
    input: &ValueAggregateLevelTwoInputV5,
    policy: &ValueAggregateRecompositionPolicyV5,
) -> Result<ProposedValueAggregateV5, ValueAggregateRecompositionErrorV5> {
    recompose_expected_value_aggregate_level_two_v5(input, policy)
}
