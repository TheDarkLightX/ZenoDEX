use alloc::vec;

use zenodex_zrpf_protocol_v3::{
    CommitmentV3, ProposedValueAggregateV5, SparseMerkleBatchEntryInputV1,
    SparseMerkleBatchEntryV1, SparseMerkleBatchTransitionInputV1,
    SparseMerkleCellTransitionWitnessV1, ValidatedSparseMerkleBatchTransitionV1,
    SPARSE_MERKLE_BATCH_VERSION_V1,
};

use super::{
    derive_action_projection_for_state, derive_settlement_plan_for_state,
    require_ordinary_spot_profile, SpotSettlementAuthorizationInputV1,
    SpotSettlementProjectionErrorV1, SpotSettlementProjectionV1,
};

/// Ordinary Spot projection whose ledger roots are derived from one exact
/// sparse-Merkle cell transition.
///
/// The private state typestate binds the plan's sole cell write, its economic
/// action, raw pre/post values, and the complete 256-sibling path. Receipt and
/// durable ledger authority remain separate boundaries.
///
/// ```compile_fail
/// use zenodex_zrpf_risc0_semantic_shared::SpotSettlementStateProjectionV2;
/// let projection = unimplemented!();
/// let state_transition = unimplemented!();
/// let _ = SpotSettlementStateProjectionV2 { projection, state_transition };
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpotSettlementStateProjectionV2 {
    projection: SpotSettlementProjectionV1,
    state_transition: ValidatedSparseMerkleBatchTransitionV1,
}

impl SpotSettlementStateProjectionV2 {
    pub const fn projection(&self) -> &SpotSettlementProjectionV1 {
        &self.projection
    }

    pub const fn state_transition(&self) -> &ValidatedSparseMerkleBatchTransitionV1 {
        &self.state_transition
    }
}

pub fn derive_spot_settlement_state_projection_v2(
    proposal: &ProposedValueAggregateV5,
    authorization: SpotSettlementAuthorizationInputV1,
    witness: SparseMerkleCellTransitionWitnessV1,
) -> Result<SpotSettlementStateProjectionV2, SpotSettlementProjectionErrorV1> {
    let projection = propose_spot_settlement_state_projection_v2(
        proposal,
        authorization,
        witness.claimed_pre_root(),
        witness.claimed_post_root(),
    )?;
    let settlement_plan = projection.settlement_plan();
    let cell_write = settlement_plan
        .ledger_cell_writes()
        .first()
        .ok_or(SpotSettlementProjectionErrorV1::MissingCanonicalCellWrite)?
        .clone();
    if settlement_plan.ledger_cell_writes().len() != 1 {
        return Err(SpotSettlementProjectionErrorV1::UnexpectedCellWriteCount {
            actual: settlement_plan.ledger_cell_writes().len(),
        });
    }
    let entry = SparseMerkleBatchEntryV1::new(SparseMerkleBatchEntryInputV1 {
        cell_write,
        witness,
    })?;
    let state_transition =
        ValidatedSparseMerkleBatchTransitionV1::new(SparseMerkleBatchTransitionInputV1 {
            batch_version: SPARSE_MERKLE_BATCH_VERSION_V1,
            batch_pre_root: entry.witness().claimed_pre_root(),
            batch_post_root: entry.witness().claimed_post_root(),
            entries: vec![entry],
        })?;
    Ok(SpotSettlementStateProjectionV2 {
        projection,
        state_transition,
    })
}

/// Propose the exact Spot action and plan for caller-supplied ledger roots.
///
/// This builder exists so a witness producer can learn the derived action ID
/// and cell write before constructing the sparse-Merkle witness. It validates
/// no state path and grants no receipt or ledger authority.
pub fn propose_spot_settlement_state_projection_v2(
    proposal: &ProposedValueAggregateV5,
    authorization: SpotSettlementAuthorizationInputV1,
    ledger_pre_state_root: CommitmentV3,
    ledger_post_state_root: CommitmentV3,
) -> Result<SpotSettlementProjectionV1, SpotSettlementProjectionErrorV1> {
    proposal.validate_self_consistency()?;
    require_ordinary_spot_profile(proposal)?;
    let action =
        derive_action_projection_for_state(proposal, authorization, ledger_pre_state_root)?;
    let settlement_plan =
        derive_settlement_plan_for_state(proposal, &action, ledger_post_state_root)?;
    Ok(SpotSettlementProjectionV1 {
        action_semantics_hash: action.action_semantics_hash,
        effect_commitment: action.effect_commitment,
        cell_key: action.cell_key,
        source_semantic_journal_hash: action.source_semantic_journal_hash,
        action_batch: action.action_batch,
        settlement_plan,
    })
}
