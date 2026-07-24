use alloc::vec;
use zenodex_zrpf_protocol_v3::{encode_value_aggregate_proposal_v5, ProposedValueAggregateV5};
use zenodex_zrpf_risc0_semantic_shared::SpotSettlementAuthorizationInputV1;
use zenodex_zrpf_risc0_spot_value_aggregate_l1_policy_v6::pinned_source_opened_spot_value_leaf_identity_v6;
use zenodex_zrpf_risc0_spot_value_aggregate_l2_policy_v6::pinned_source_opened_spot_value_aggregate_l1_identity_v6;
use zenodex_zrpf_risc0_spot_value_leaf_v6_shared::{
    encode_source_opened_spot_value_leaf_statement_v6,
    recompose_source_opened_spot_value_leaf_statement_v6, SourceOpenedSpotValueLeafEnvelopeV6,
    SourceOpenedSpotValueLeafStatementV6,
};
use zenodex_zrpf_risc0_value_aggregate_shared::{
    recompose_expected_source_opened_spot_value_aggregate_level_one_v6,
    recompose_expected_value_aggregate_level_two_v5, ValueAggregateLevelOneInputV5,
    ValueAggregateLevelTwoInputV5, ValueAggregateRecompositionPolicyV5,
};

use crate::SourceOpenedSpotSettlementErrorV6;

pub fn validate_singleton_source_opened_spot_relation_v6(
    proposal: &ProposedValueAggregateV5,
    source: &SourceOpenedSpotValueLeafEnvelopeV6,
) -> Result<SourceOpenedSpotValueLeafStatementV6, SourceOpenedSpotSettlementErrorV6> {
    proposal.validate_self_consistency()?;
    if proposal.aggregate_level() != 2 || proposal.children().len() != 1 {
        return Err(SourceOpenedSpotSettlementErrorV6::InvalidSingletonRelation(
            "L2 topology",
        ));
    }
    let child = &proposal.children()[0];
    if child.child_level() != 1 {
        return Err(SourceOpenedSpotSettlementErrorV6::InvalidSingletonRelation(
            "L1 child level",
        ));
    }
    let statement = recompose_source_opened_spot_value_leaf_statement_v6(source)?;
    let statement_bytes = encode_source_opened_spot_value_leaf_statement_v6(&statement)?;
    let leaf_identity = pinned_source_opened_spot_value_leaf_identity_v6()?;
    let l1_input = ValueAggregateLevelOneInputV5::new(vec![statement_bytes])?;
    let l1_policy = ValueAggregateRecompositionPolicyV5::new(
        statement.structural_adapter_journal().scope().clone(),
        vec![leaf_identity],
    )?;
    let expected_l1 =
        recompose_expected_source_opened_spot_value_aggregate_level_one_v6(&l1_input, &l1_policy)?;
    let l1_bytes = encode_value_aggregate_proposal_v5(&expected_l1)?;
    let l1_identity = pinned_source_opened_spot_value_aggregate_l1_identity_v6()?;
    let l2_input = ValueAggregateLevelTwoInputV5::new(vec![l1_bytes])?;
    let l2_policy =
        ValueAggregateRecompositionPolicyV5::new(expected_l1.scope().clone(), vec![l1_identity])?;
    let expected_l2 = recompose_expected_value_aggregate_level_two_v5(&l2_input, &l2_policy)?;
    if proposal != &expected_l2 {
        return Err(SourceOpenedSpotSettlementErrorV6::InvalidSingletonRelation(
            "exact L1/L2 source relation",
        ));
    }
    Ok(statement)
}

/// Require settlement authorization to be the exact source-receipt-derived
/// identity committed by the V6 leaf statement.
///
/// The source profile currently authenticates accepted execution rather than
/// an end-user signature scheme. This closes caller selection of authorization
/// identifiers while preserving the separate user-signature nonclaim.
pub fn require_source_bound_spot_authorization_v6(
    statement: &SourceOpenedSpotValueLeafStatementV6,
    authorization: SpotSettlementAuthorizationInputV1,
) -> Result<(), SourceOpenedSpotSettlementErrorV6> {
    if authorization.authorization_subject_id != statement.authorization_subject_id()
        || authorization.authorization_scope_id != statement.authorization_scope_id()
        || authorization.authorization_nonce != statement.authorization_nonce()
        || authorization.authorization_grant_id != statement.authorization_grant_id()
    {
        return Err(SourceOpenedSpotSettlementErrorV6::InvalidSingletonRelation(
            "source-bound authorization",
        ));
    }
    Ok(())
}
