use alloc::vec;

use zenodex_zrpf_protocol_v3::{
    CommitmentV3, EconomicActionIdV1, LedgerCellWriteV2, ProposedValueAggregateV5,
    SettlementEffectPlanV2, SparseMerkleBatchEntryInputV1, SparseMerkleBatchEntryV1,
    SparseMerkleBatchTransitionInputV1, SparseMerkleCellTransitionWitnessV1,
    ValidatedSparseMerkleBatchTransitionV1, ValueHashV2, SPARSE_MERKLE_BATCH_VERSION_V1,
};

use super::{
    derive_action_projection_for_state, derive_settlement_plan_for_state,
    require_ordinary_spot_profile, SpotSettlementAuthorizationInputV1,
    SpotSettlementProjectionErrorV1, SpotSettlementProjectionV1,
};

/// Proof-neutral Spot witness material proposed for caller-supplied ledger roots.
///
/// This type exposes only the exact cell-write fields needed to construct a
/// sparse-Merkle witness. It carries no validated path, receipt, or ledger
/// authority and cannot substitute for [`SpotSettlementStateProjectionV2`].
///
/// ```compile_fail
/// use zenodex_zrpf_risc0_semantic_shared::{
///     ProposedSpotSettlementStateProjectionV2, SpotSettlementStateProjectionV2,
/// };
/// fn require_validated(_: &SpotSettlementStateProjectionV2) {}
/// fn bypass(proposed: &ProposedSpotSettlementStateProjectionV2) {
///     require_validated(proposed);
/// }
/// ```
#[derive(Debug, PartialEq, Eq)]
pub struct ProposedSpotSettlementStateProjectionV2 {
    settlement_projection: SpotSettlementProjectionV1,
    canonical_cell_write: LedgerCellWriteV2,
}

impl ProposedSpotSettlementStateProjectionV2 {
    pub const fn economic_action_id(&self) -> EconomicActionIdV1 {
        self.canonical_cell_write.economic_action_id()
    }

    pub const fn cell_key(&self) -> CommitmentV3 {
        self.canonical_cell_write.cell_key()
    }

    pub const fn pre_value_hash(&self) -> ValueHashV2 {
        self.canonical_cell_write.pre_value_hash()
    }

    pub const fn post_value_hash(&self) -> ValueHashV2 {
        self.canonical_cell_write.post_value_hash()
    }

    fn into_validated_components(self) -> (SpotSettlementProjectionV1, LedgerCellWriteV2) {
        (self.settlement_projection, self.canonical_cell_write)
    }
}

/// Ordinary Spot projection whose ledger roots are derived from one exact
/// sparse-Merkle cell transition.
///
/// The private state typestate binds the plan's sole cell write, its economic
/// action, raw pre/post values, and the complete 256-sibling path. Receipt and
/// durable ledger authority remain separate boundaries.
///
/// ```compile_fail
/// use zenodex_zrpf_risc0_semantic_shared::SpotSettlementStateProjectionV2;
/// let settlement_projection = unimplemented!();
/// let state_transition = unimplemented!();
/// let _ = SpotSettlementStateProjectionV2 {
///     settlement_projection,
///     state_transition,
/// };
/// ```
///
/// ```compile_fail
/// use zenodex_zrpf_risc0_semantic_shared::{
///     SpotSettlementProjectionV1, SpotSettlementStateProjectionV2,
/// };
/// fn detach(
///     validated: &SpotSettlementStateProjectionV2,
/// ) -> &SpotSettlementProjectionV1 {
///     validated.projection()
/// }
/// ```
///
/// ```compile_fail
/// use zenodex_zrpf_risc0_semantic_shared::SpotSettlementStateProjectionV2;
/// fn duplicate(
///     validated: SpotSettlementStateProjectionV2,
/// ) -> SpotSettlementStateProjectionV2 {
///     validated.clone()
/// }
/// ```
#[derive(Debug, PartialEq, Eq)]
pub struct SpotSettlementStateProjectionV2 {
    settlement_projection: SpotSettlementProjectionV1,
    state_transition: ValidatedSparseMerkleBatchTransitionV1,
}

impl SpotSettlementStateProjectionV2 {
    pub const fn settlement_plan(&self) -> &SettlementEffectPlanV2 {
        self.settlement_projection.settlement_plan()
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
    let proposed = propose_spot_settlement_state_projection_v2(
        proposal,
        authorization,
        witness.claimed_pre_root(),
        witness.claimed_post_root(),
    )?;
    let (settlement_projection, cell_write) = proposed.into_validated_components();
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
        settlement_projection,
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
) -> Result<ProposedSpotSettlementStateProjectionV2, SpotSettlementProjectionErrorV1> {
    proposal.validate_self_consistency()?;
    require_ordinary_spot_profile(proposal)?;
    let action =
        derive_action_projection_for_state(proposal, authorization, ledger_pre_state_root)?;
    let settlement_plan =
        derive_settlement_plan_for_state(proposal, &action, ledger_post_state_root)?;
    let canonical_cell_write = match settlement_plan.ledger_cell_writes() {
        [cell_write] => cell_write.clone(),
        [] => return Err(SpotSettlementProjectionErrorV1::MissingCanonicalCellWrite),
        cell_writes => {
            return Err(SpotSettlementProjectionErrorV1::UnexpectedCellWriteCount {
                actual: cell_writes.len(),
            });
        }
    };
    let settlement_projection = SpotSettlementProjectionV1 {
        action_semantics_hash: action.action_semantics_hash,
        effect_commitment: action.effect_commitment,
        cell_key: action.cell_key,
        source_semantic_journal_hash: action.source_semantic_journal_hash,
        action_batch: action.action_batch,
        settlement_plan,
    };
    Ok(ProposedSpotSettlementStateProjectionV2 {
        settlement_projection,
        canonical_cell_write,
    })
}
