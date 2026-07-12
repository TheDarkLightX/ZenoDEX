use super::hash::*;
use super::validate::{bind_leaf, validate_closed_flows, validate_subtree_inputs};
use super::*;

/// Recompose one bounded subtree and close it against an exact Semantic Epoch V1 proposal.
///
/// This convenience function returns a pure proposal projection. It performs no
/// receipt verification and creates no ledger or settlement authority.
pub fn compose_spot_represented_value_v1(
    base_proposal: &ProposedSemanticEpochV1,
    leaves: &[ProposedSemanticLeafV1],
    openings: &[SpotValueLeafOpeningV1],
    policy: &SpotRepresentedValuePolicyV1,
) -> Result<SpotSemanticValueProjectionV1, SpotSemanticValueErrorV1> {
    let summary = propose_spot_value_subtree_v2(leaves, openings, policy)?;
    close_spot_represented_value_epoch_v1(base_proposal, &summary, policy)
}

/// Recompose authenticated leaf proposals plus untrusted openings into a sealed residual summary.
///
/// Asset balance closure is deliberately deferred so adjacent recursive children
/// may carry complementary debit and credit residuals.
pub fn propose_spot_value_subtree_v2(
    leaves: &[ProposedSemanticLeafV1],
    openings: &[SpotValueLeafOpeningV1],
    policy: &SpotRepresentedValuePolicyV1,
) -> Result<SpotValueSubtreeSummaryV2, SpotSemanticValueErrorV1> {
    validate_subtree_inputs(leaves, openings, policy)?;
    let mut state = CompositionStateV1::new();
    for (ordinal, (leaf, opening)) in leaves.iter().zip(openings).enumerate() {
        bind_leaf(ordinal, leaf, opening, policy, &mut state)?;
    }
    finalize_subtree(leaves, openings, policy, state)
}

/// Merge two sealed summaries by revalidating their canonical flattened witnesses.
///
/// The reference implementation demonstrates the associative summary law. It is
/// not the serialized V4 child-summary ABI.
pub fn merge_spot_value_subtrees_v2(
    left: &SpotValueSubtreeSummaryV2,
    right: &SpotValueSubtreeSummaryV2,
    policy: &SpotRepresentedValuePolicyV1,
) -> Result<SpotValueSubtreeSummaryV2, SpotSemanticValueErrorV1> {
    if left.authority_grants_root != policy.authority_grants_root()
        || right.authority_grants_root != policy.authority_grants_root()
    {
        return Err(SpotSemanticValueErrorV1::AuthorityGrantPolicyMismatch);
    }
    let mut leaves = left.leaves.clone();
    leaves.extend(right.leaves.iter().cloned());
    let mut openings = left.openings.clone();
    openings.extend(right.openings.iter().cloned());
    propose_spot_value_subtree_v2(&leaves, &openings, policy)
}

/// Require zero-origin complete-root shape, exact base recomposition, and asset closure.
///
/// The result remains a pure projection until a future governed receipt verifier
/// and atomic ledger admission layer authenticate and accept it.
pub fn close_spot_represented_value_epoch_v1(
    base_proposal: &ProposedSemanticEpochV1,
    summary: &SpotValueSubtreeSummaryV2,
    policy: &SpotRepresentedValuePolicyV1,
) -> Result<SpotSemanticValueProjectionV1, SpotSemanticValueErrorV1> {
    base_proposal
        .validate_self_consistency()
        .map_err(SpotSemanticValueErrorV1::Protocol)?;
    if summary.partition_start != 0 {
        return Err(SpotSemanticValueErrorV1::NonZeroOriginClosedEpoch);
    }
    if summary.leaves.len() > MAX_SPOT_VALUE_LEAVES_V1 {
        return Err(SpotSemanticValueErrorV1::TooManyLeaves {
            actual: summary.leaves.len(),
            maximum: MAX_SPOT_VALUE_LEAVES_V1,
        });
    }
    if base_proposal.scope().epoch_start() != base_proposal.scope().epoch_end() {
        return Err(SpotSemanticValueErrorV1::EpochRangeUnsupported);
    }
    if base_proposal.scope().public_policy_hash().as_bytes() != &policy.public_policy_hash {
        return Err(SpotSemanticValueErrorV1::PublicPolicyMismatch);
    }
    if summary.authority_grants_root != policy.authority_grants_root() {
        return Err(SpotSemanticValueErrorV1::AuthorityGrantPolicyMismatch);
    }
    let expected_scope_hash = base_proposal
        .scope()
        .canonical_hash()
        .map_err(SpotSemanticValueErrorV1::Structural)?;
    if summary.scope_hash != expected_scope_hash {
        return Err(SpotSemanticValueErrorV1::ClosedScopeMismatch);
    }
    let recomposed = ProposedSemanticEpochV1::derive(SemanticEpochProposalInputV1 {
        leaves: summary.leaves.clone(),
        proof_tree_root: base_proposal.proof_tree_root(),
        scope: base_proposal.scope().clone(),
        actual_program_id: base_proposal.actual_program_id(),
        program_manifest_root: base_proposal.program_manifest_root(),
    })
    .map_err(SpotSemanticValueErrorV1::Protocol)?;
    if &recomposed != base_proposal {
        return Err(SpotSemanticValueErrorV1::BaseProposalMismatch);
    }
    validate_closed_flows(&summary.asset_flows)?;
    finalize_projection(base_proposal, policy, summary)
}

fn finalize_subtree(
    leaves: &[ProposedSemanticLeafV1],
    openings: &[SpotValueLeafOpeningV1],
    policy: &SpotRepresentedValuePolicyV1,
    mut state: CompositionStateV1,
) -> Result<SpotValueSubtreeSummaryV2, SpotSemanticValueErrorV1> {
    let asset_flows = canonical_flows(core::mem::take(&mut state.flows));
    sort_authority_uses(&mut state.authority_uses);
    let derived = derive_subtree_fields(leaves, policy, &state, &asset_flows)?;
    Ok(SpotValueSubtreeSummaryV2 {
        leaves: leaves.to_vec(),
        openings: openings.to_vec(),
        partition_start: derived.partition_start,
        partition_end_exclusive: derived.partition_end_exclusive,
        scope_hash: derived.scope_hash,
        lane_id_hash: derived.lane_id_hash,
        raw_subtree_pre_state_root: derived.raw_pre,
        raw_subtree_post_state_root: derived.raw_post,
        leaf_count: derived.leaf_count,
        represented_row_count: derived.row_count,
        semantic_leaf_records_root: derived.semantic_leaf_records_root,
        ordered_transaction_roots_root: derived.ordered_transaction_roots_root,
        state_chain_root: derived.state_chain_root,
        authority_grants_root: policy.authority_grants_root,
        asset_flows_root: derived.asset_flows_root,
        authority_uses_root: derived.authority_uses_root,
        asset_flows,
        authority_uses: state.authority_uses,
        subtree_root: derived.subtree_root,
    })
}

#[derive(Clone, Copy)]
struct DerivedSubtreeFieldsV2 {
    partition_start: u64,
    partition_end_exclusive: u64,
    scope_hash: CommitmentV3,
    lane_id_hash: CommitmentV3,
    raw_pre: [u8; 32],
    raw_post: [u8; 32],
    leaf_count: u64,
    row_count: u64,
    semantic_leaf_records_root: CommitmentV3,
    ordered_transaction_roots_root: CommitmentV3,
    state_chain_root: CommitmentV3,
    asset_flows_root: CommitmentV3,
    authority_uses_root: CommitmentV3,
    subtree_root: CommitmentV3,
}

fn derive_subtree_fields(
    leaves: &[ProposedSemanticLeafV1],
    policy: &SpotRepresentedValuePolicyV1,
    state: &CompositionStateV1,
    asset_flows: &[SpotCanonicalAssetFlowV1],
) -> Result<DerivedSubtreeFieldsV2, SpotSemanticValueErrorV1> {
    let partition_start = leaves[0].partition().start();
    let partition_end_exclusive = leaves[leaves.len() - 1].partition().end_exclusive();
    let scope_hash = leaves[0]
        .scope()
        .canonical_hash()
        .map_err(SpotSemanticValueErrorV1::Structural)?;
    let lane_id_hash = hash_lane_id(
        state
            .lane_id
            .as_deref()
            .ok_or(SpotSemanticValueErrorV1::EmptyLeaves)?,
    )?;
    let raw_pre = state.state_records[0].raw_pre_state_root;
    let raw_post = state.state_records[state.state_records.len() - 1].raw_post_state_root;
    let leaf_count = u64::try_from(state.state_records.len())
        .map_err(|_| SpotSemanticValueErrorV1::ArithmeticOverflow("leaf_count"))?;
    let row_count = u64::try_from(state.row_count)
        .map_err(|_| SpotSemanticValueErrorV1::ArithmeticOverflow("represented_row_count"))?;
    let semantic_leaf_records_root = semantic_leaf_records_root(leaves)?;
    let ordered_transaction_roots_root = ordered_transaction_roots_root(&state.state_records)?;
    let state_chain_root = state_chain_root(&state.state_records)?;
    let asset_flows_root = asset_flows_root(asset_flows)?;
    let authority_uses_root = authority_uses_root(&state.authority_uses)?;
    let subtree_root = value_subtree_root(ValueSubtreeRootInputV2 {
        partition_start,
        partition_end_exclusive,
        scope_hash,
        lane_id_hash,
        raw_pre,
        raw_post,
        leaf_count,
        row_count,
        semantic_leaf_records_root,
        ordered_transaction_roots_root,
        state_chain_root,
        authority_grants_root: policy.authority_grants_root,
        asset_flows_root,
        authority_uses_root,
    })?;
    Ok(DerivedSubtreeFieldsV2 {
        partition_start,
        partition_end_exclusive,
        scope_hash,
        lane_id_hash,
        raw_pre,
        raw_post,
        leaf_count,
        row_count,
        semantic_leaf_records_root,
        ordered_transaction_roots_root,
        state_chain_root,
        asset_flows_root,
        authority_uses_root,
        subtree_root,
    })
}

fn sort_authority_uses(uses: &mut [SpotMintAuthorityUseV1]) {
    uses.sort_by(|left, right| {
        left.asset_id
            .cmp(&right.asset_id)
            .then_with(|| left.leaf_ordinal.cmp(&right.leaf_ordinal))
            .then_with(|| left.source_claim_id.cmp(&right.source_claim_id))
    });
}

fn finalize_projection(
    base_proposal: &ProposedSemanticEpochV1,
    policy: &SpotRepresentedValuePolicyV1,
    summary: &SpotValueSubtreeSummaryV2,
) -> Result<SpotSemanticValueProjectionV1, SpotSemanticValueErrorV1> {
    if summary.represented_row_count == 0 {
        return Err(SpotSemanticValueErrorV1::EmptyRepresentedRows);
    }
    let scope_hash = base_proposal
        .scope()
        .canonical_hash()
        .map_err(SpotSemanticValueErrorV1::Structural)?;
    let commitments = SpotSemanticValueCommitmentsV1 {
        base_semantic_epoch_root: base_proposal.semantic_epoch_root(),
        value_profile_id: spot_represented_value_profile_id_v1()?,
        accounting_domain_id: spot_accounting_domain_id_v1()?,
        atoms_unit_id: spot_atoms_unit_id_v1()?,
        state_root_scheme_id: spot_state_root_scheme_id_v1()?,
        semantic_leaf_records_root: summary.semantic_leaf_records_root,
        ordered_transaction_roots_root: summary.ordered_transaction_roots_root,
        state_chain_root: summary.state_chain_root,
        authority_grants_root: summary.authority_grants_root,
        asset_flows_root: summary.asset_flows_root,
        authority_uses_root: summary.authority_uses_root,
        value_subtree_root: summary.subtree_root,
    };
    let semantic_value_root = semantic_value_root(
        base_proposal,
        summary.lane_id_hash,
        summary.raw_subtree_pre_state_root,
        summary.raw_subtree_post_state_root,
        summary.leaf_count,
        summary.represented_row_count,
        &commitments,
    )?;
    let proposal_hash = semantic_value_proposal_hash(
        base_proposal,
        semantic_value_root,
        policy.authority_grants_root,
    )?;
    Ok(SpotSemanticValueProjectionV1 {
        scope_hash,
        lane_id_hash: summary.lane_id_hash,
        raw_epoch_pre_state_root: summary.raw_subtree_pre_state_root,
        raw_epoch_post_state_root: summary.raw_subtree_post_state_root,
        leaf_count: summary.leaf_count,
        represented_row_count: summary.represented_row_count,
        asset_flows: summary.asset_flows.clone(),
        authority_uses: summary.authority_uses.clone(),
        commitments,
        semantic_value_root,
        proposal_hash,
    })
}

fn canonical_flows(flows: BTreeMap<[u8; 32], FlowAccumulatorV1>) -> Vec<SpotCanonicalAssetFlowV1> {
    flows
        .into_iter()
        .map(|(asset_id, flow)| SpotCanonicalAssetFlowV1 {
            asset_id,
            outflow_atoms: flow.outflow_atoms,
            inflow_atoms: flow.inflow_atoms,
            issued_atoms: flow.issued_atoms,
            destroyed_atoms: flow.destroyed_atoms,
        })
        .collect()
}
