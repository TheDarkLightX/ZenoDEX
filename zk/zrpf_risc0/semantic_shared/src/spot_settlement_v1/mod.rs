use alloc::vec;
use alloc::vec::Vec;

use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    encode_value_aggregate_proposal_v5, AssetEffectInputV2, AssetEffectKindV2, AssetEffectV2,
    AuthorizationGrantIdV1, AuthorizationScopeIdV1, AuthorizationSubjectIdV1,
    AuthorizedEconomicActionV1, CommitmentV3, EconomicActionBatchV1, EconomicActionRecordInputV1,
    EconomicActionRecordV1, EconomicActionTypeIdV1, LedgerCellWriteInputV2, LedgerCellWriteV2,
    ProposedValueAggregateV5, SettlementEffectPlanInputV2, SettlementEffectPlanV2, ValueHashV2,
};

mod error;
pub use error::SpotSettlementProjectionErrorV1;
mod state_v2;
pub use state_v2::{
    derive_spot_settlement_state_projection_v2, propose_spot_settlement_state_projection_v2,
    SpotSettlementStateProjectionV2,
};

use crate::{
    spot_accounting_domain_id_v1, spot_atoms_unit_id_v1, spot_represented_value_profile_id_v1,
    spot_state_root_scheme_id_v1,
};

const ACTION_TYPE_DOMAIN_V1: &[u8] = b"zenodex.zrpf.spot_epoch_action_type.v1";
const ACTION_SEMANTICS_DOMAIN_V1: &[u8] = b"zenodex.zrpf.spot_epoch_action_semantics.v1";
const EFFECT_COMMITMENT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.spot_epoch_effect_projection.v1";
const CELL_KEY_DOMAIN_V1: &[u8] = b"zenodex.zrpf.spot_epoch_cell_key.v1";
const SOURCE_JOURNAL_DOMAIN_V1: &[u8] = b"zenodex.zrpf.spot_value_aggregate_journal.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SpotSettlementAuthorizationInputV1 {
    pub authorization_subject_id: AuthorizationSubjectIdV1,
    pub authorization_scope_id: AuthorizationScopeIdV1,
    pub authorization_nonce: u64,
    pub authorization_grant_id: AuthorizationGrantIdV1,
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// Deterministic ordinary-Spot projection from one V5 value proposal.
///
/// This projection is proof-neutral. A settlement guest must first verify the
/// exact V5 receipt and then require exact equality with the plan derived here.
/// The initial profile rejects issuance, destruction, messages, carries, and
/// rewards so one aggregate value transition has one canonical row shape.
pub struct SpotSettlementProjectionV1 {
    action_semantics_hash: CommitmentV3,
    effect_commitment: CommitmentV3,
    cell_key: CommitmentV3,
    source_semantic_journal_hash: CommitmentV3,
    action_batch: EconomicActionBatchV1,
    settlement_plan: SettlementEffectPlanV2,
}

impl SpotSettlementProjectionV1 {
    pub const fn action_semantics_hash(&self) -> CommitmentV3 {
        self.action_semantics_hash
    }

    pub const fn effect_commitment(&self) -> CommitmentV3 {
        self.effect_commitment
    }

    pub const fn cell_key(&self) -> CommitmentV3 {
        self.cell_key
    }

    pub const fn source_semantic_journal_hash(&self) -> CommitmentV3 {
        self.source_semantic_journal_hash
    }

    pub const fn action_batch(&self) -> &EconomicActionBatchV1 {
        &self.action_batch
    }

    pub const fn settlement_plan(&self) -> &SettlementEffectPlanV2 {
        &self.settlement_plan
    }
}

pub fn derive_spot_settlement_projection_v1(
    proposal: &ProposedValueAggregateV5,
    authorization: SpotSettlementAuthorizationInputV1,
) -> Result<SpotSettlementProjectionV1, SpotSettlementProjectionErrorV1> {
    proposal.validate_self_consistency()?;
    require_ordinary_spot_profile(proposal)?;
    let action = derive_action_projection_for_state(
        proposal,
        authorization,
        proposal.semantic_subtree().raw_subtree_pre_state_root(),
    )?;
    let settlement_plan = derive_settlement_plan_for_state(
        proposal,
        &action,
        proposal.semantic_subtree().raw_subtree_post_state_root(),
    )?;
    Ok(SpotSettlementProjectionV1 {
        action_semantics_hash: action.action_semantics_hash,
        effect_commitment: action.effect_commitment,
        cell_key: action.cell_key,
        source_semantic_journal_hash: action.source_semantic_journal_hash,
        action_batch: action.action_batch,
        settlement_plan,
    })
}

struct SpotActionProjectionV1 {
    action_semantics_hash: CommitmentV3,
    effect_commitment: CommitmentV3,
    cell_key: CommitmentV3,
    source_semantic_journal_hash: CommitmentV3,
    action_batch: EconomicActionBatchV1,
}

fn derive_action_projection_for_state(
    proposal: &ProposedValueAggregateV5,
    authorization: SpotSettlementAuthorizationInputV1,
    ledger_pre_state_root: CommitmentV3,
) -> Result<SpotActionProjectionV1, SpotSettlementProjectionErrorV1> {
    let subtree = proposal.semantic_subtree();
    let epoch = proposal.scope().epoch_start();
    let cell_key = spot_epoch_cell_key_v1(proposal)?;
    let action_semantics_hash = spot_action_semantics_hash_v1(proposal)?;
    let effect_commitment = spot_effect_commitment_v1(proposal, cell_key)?;
    let source_semantic_journal_hash = spot_value_aggregate_journal_hash_v1(proposal)?;
    let consumed_object_ids = subtree
        .leaf_records()
        .iter()
        .map(|record| record.transaction_root())
        .collect();
    let record = EconomicActionRecordV1::new(EconomicActionRecordInputV1 {
        application_id: proposal.scope().application_id(),
        chain_or_domain_id: proposal.scope().chain_or_domain_id(),
        action_type_id: spot_epoch_action_type_id_v1()?,
        authorization_subject_id: authorization.authorization_subject_id,
        authorization_scope_id: authorization.authorization_scope_id,
        authorization_nonce: authorization.authorization_nonce,
        valid_from_epoch: epoch,
        valid_through_epoch: epoch,
        pre_state_root: ledger_pre_state_root,
        action_semantics_hash,
        effect_commitment,
        consumed_object_ids,
    })?;
    let authorized = AuthorizedEconomicActionV1::new(record, authorization.authorization_grant_id)?;
    let action_batch = EconomicActionBatchV1::new(epoch, ledger_pre_state_root, vec![authorized])?;
    Ok(SpotActionProjectionV1 {
        action_semantics_hash,
        effect_commitment,
        cell_key,
        source_semantic_journal_hash,
        action_batch,
    })
}

fn derive_settlement_plan_for_state(
    proposal: &ProposedValueAggregateV5,
    action: &SpotActionProjectionV1,
    ledger_post_state_root: CommitmentV3,
) -> Result<SettlementEffectPlanV2, SpotSettlementProjectionErrorV1> {
    let subtree = proposal.semantic_subtree();
    let action_batch = &action.action_batch;
    let action_id = action_batch.actions()[0].action_id()?;
    let cell_write = LedgerCellWriteV2::new(LedgerCellWriteInputV2 {
        economic_action_id: action_id,
        cell_key: action.cell_key,
        pre_value_hash: ValueHashV2::new(subtree.raw_subtree_pre_state_root().into_bytes()),
        post_value_hash: ValueHashV2::new(subtree.raw_subtree_post_state_root().into_bytes()),
    })?;
    let asset_effects = subtree
        .asset_flows()
        .iter()
        .map(|flow| {
            Ok(AssetEffectV2::new(AssetEffectInputV2 {
                kind: AssetEffectKindV2::OrdinaryTransfer,
                economic_action_id: action_id,
                asset_id: CommitmentV3::new(flow.asset_id())?,
                debit_atoms: flow.outflow_atoms(),
                credit_atoms: flow.inflow_atoms(),
                authorized_mint_atoms: 0,
                authorized_burn_atoms: 0,
                authority_scope_id: None,
                action_authorization_binding: None,
            })?)
        })
        .collect::<Result<Vec<_>, SpotSettlementProjectionErrorV1>>()?;
    let settlement_plan = SettlementEffectPlanV2::new(SettlementEffectPlanInputV2 {
        source_semantic_journal_hash: action.source_semantic_journal_hash,
        public_policy_hash: proposal.scope().public_policy_hash(),
        post_state_root: ledger_post_state_root,
        economic_action_batch: action.action_batch.clone(),
        ledger_cell_writes: vec![cell_write],
        asset_effects,
        message_effects: vec![],
        carry_effects: vec![],
        reward_effects: vec![],
    })?;
    Ok(settlement_plan)
}

pub fn spot_value_aggregate_journal_hash_v1(
    proposal: &ProposedValueAggregateV5,
) -> Result<CommitmentV3, SpotSettlementProjectionErrorV1> {
    let bytes = encode_value_aggregate_proposal_v5(proposal)?;
    let mut hasher = domain_hasher(SOURCE_JOURNAL_DOMAIN_V1)?;
    let length = u32::try_from(bytes.len())
        .map_err(|_| SpotSettlementProjectionErrorV1::ArithmeticOverflow("journal_length"))?;
    hasher.update(length.to_be_bytes());
    hasher.update(bytes);
    commitment(hasher.finalize().into())
}

fn require_ordinary_spot_profile(
    proposal: &ProposedValueAggregateV5,
) -> Result<(), SpotSettlementProjectionErrorV1> {
    let subtree = proposal.semantic_subtree();
    for (field, actual, expected) in [
        (
            "value_profile_id",
            subtree.value_profile_id(),
            spot_represented_value_profile_id_v1()?,
        ),
        (
            "accounting_domain_id",
            subtree.accounting_domain_id(),
            spot_accounting_domain_id_v1()?,
        ),
        (
            "atoms_unit_id",
            subtree.atoms_unit_id(),
            spot_atoms_unit_id_v1()?,
        ),
        (
            "state_root_scheme_id",
            subtree.state_root_scheme_id(),
            spot_state_root_scheme_id_v1()?,
        ),
    ] {
        if actual != expected {
            return Err(SpotSettlementProjectionErrorV1::ProfileMismatch(field));
        }
    }
    if subtree.asset_flows().is_empty() {
        return Err(SpotSettlementProjectionErrorV1::EmptyEconomicFlow);
    }
    if !subtree.authority_uses().is_empty() {
        return Err(SpotSettlementProjectionErrorV1::SupplyChangingFlow);
    }
    for flow in subtree.asset_flows() {
        if flow.issued_atoms() != 0 || flow.destroyed_atoms() != 0 {
            return Err(SpotSettlementProjectionErrorV1::SupplyChangingFlow);
        }
        if flow.outflow_atoms() == 0 || flow.outflow_atoms() != flow.inflow_atoms() {
            return Err(SpotSettlementProjectionErrorV1::NonCanonicalOrdinaryFlow);
        }
    }
    Ok(())
}

fn spot_epoch_action_type_id_v1() -> Result<EconomicActionTypeIdV1, SpotSettlementProjectionErrorV1>
{
    let hasher = domain_hasher(ACTION_TYPE_DOMAIN_V1)?;
    EconomicActionTypeIdV1::new(hasher.finalize().into())
        .map_err(SpotSettlementProjectionErrorV1::EconomicAction)
}

fn spot_epoch_cell_key_v1(
    proposal: &ProposedValueAggregateV5,
) -> Result<CommitmentV3, SpotSettlementProjectionErrorV1> {
    let mut hasher = domain_hasher(CELL_KEY_DOMAIN_V1)?;
    hasher.update(proposal.scope().application_id().as_bytes());
    hasher.update(proposal.scope().chain_or_domain_id().as_bytes());
    hasher.update(proposal.semantic_subtree().lane_id_hash().as_bytes());
    commitment(hasher.finalize().into())
}

fn spot_action_semantics_hash_v1(
    proposal: &ProposedValueAggregateV5,
) -> Result<CommitmentV3, SpotSettlementProjectionErrorV1> {
    let subtree = proposal.semantic_subtree();
    let mut hasher = domain_hasher(ACTION_SEMANTICS_DOMAIN_V1)?;
    hasher.update(proposal.proposal_commitment().as_bytes());
    hasher.update(proposal.scope().canonical_hash()?.as_bytes());
    hasher.update(subtree.canonical_hash()?.as_bytes());
    hasher.update(subtree.ordered_transaction_roots_root().as_bytes());
    hasher.update(subtree.state_chain_root().as_bytes());
    commitment(hasher.finalize().into())
}

fn spot_effect_commitment_v1(
    proposal: &ProposedValueAggregateV5,
    cell_key: CommitmentV3,
) -> Result<CommitmentV3, SpotSettlementProjectionErrorV1> {
    let subtree = proposal.semantic_subtree();
    let mut hasher = domain_hasher(EFFECT_COMMITMENT_DOMAIN_V1)?;
    hasher.update(cell_key.as_bytes());
    hasher.update(subtree.raw_subtree_pre_state_root().as_bytes());
    hasher.update(subtree.raw_subtree_post_state_root().as_bytes());
    let flow_count = u16::try_from(subtree.asset_flows().len())
        .map_err(|_| SpotSettlementProjectionErrorV1::ArithmeticOverflow("asset_flow_count"))?;
    hasher.update(flow_count.to_be_bytes());
    for flow in subtree.asset_flows() {
        hasher.update(flow.asset_id());
        hasher.update(flow.outflow_atoms().to_be_bytes());
        hasher.update(flow.inflow_atoms().to_be_bytes());
        hasher.update(flow.issued_atoms().to_be_bytes());
        hasher.update(flow.destroyed_atoms().to_be_bytes());
    }
    commitment(hasher.finalize().into())
}

fn domain_hasher(domain: &[u8]) -> Result<Sha256, SpotSettlementProjectionErrorV1> {
    let length = u16::try_from(domain.len())
        .map_err(|_| SpotSettlementProjectionErrorV1::ArithmeticOverflow("hash_domain"))?;
    let mut hasher = Sha256::new();
    hasher.update(length.to_be_bytes());
    hasher.update(domain);
    Ok(hasher)
}

fn commitment(bytes: [u8; 32]) -> Result<CommitmentV3, SpotSettlementProjectionErrorV1> {
    CommitmentV3::new(bytes).map_err(SpotSettlementProjectionErrorV1::Structural)
}
