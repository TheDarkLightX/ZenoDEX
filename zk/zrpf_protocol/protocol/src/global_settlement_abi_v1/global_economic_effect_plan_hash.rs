use alloc::vec::Vec;

use sha2::{Digest, Sha256};

use super::{
    GlobalAssetReconciliationV1, GlobalEconomicEffectPlanErrorV1, GlobalEconomicEffectRowV1,
};
use crate::CommitmentV3;

use super::global_economic_effect_plan_types::GlobalEconomicEffectContentV1;

const EFFECT_ROW_DOMAIN_V1: &[u8] = b"zenodex.global_settlement.effect_row.v1";
const EFFECT_ROWS_ROOT_DOMAIN_V1: &[u8] = b"zenodex.global_settlement.effect_rows_root.v1";
const EFFECT_SEMANTIC_ROW_DOMAIN_V1: &[u8] = b"zenodex.global_settlement.effect_semantic_row.v1";
const EFFECT_SEMANTICS_ROOT_DOMAIN_V1: &[u8] =
    b"zenodex.global_settlement.effect_semantics_root.v1";
const RECONCILIATION_DOMAIN_V1: &[u8] = b"zenodex.global_settlement.asset_reconciliation.v1";
const RECONCILIATIONS_ROOT_DOMAIN_V1: &[u8] =
    b"zenodex.global_settlement.asset_reconciliations_root.v1";
pub(super) const EFFECT_BODY_COMMITMENT_DOMAIN_V1: &[u8] =
    b"zenodex.global_settlement.effect_body.v1";
pub(super) const EFFECT_PLAN_COMMITMENT_DOMAIN_V1: &[u8] =
    b"zenodex.global_settlement.effect_plan.v1";

pub(super) fn effect_row_id_v1(
    row: &GlobalEconomicEffectRowV1,
) -> Result<CommitmentV3, GlobalEconomicEffectPlanErrorV1> {
    let mut hasher = domain_hasher(EFFECT_ROW_DOMAIN_V1)?;
    hasher.update([row.kind().code()]);
    match row.content() {
        GlobalEconomicEffectContentV1::AccountMovement {
            lane_id,
            asset_id,
            source_id,
            destination_id,
            amount_atoms,
        } => {
            lane(&mut hasher, *lane_id);
            commitments(&mut hasher, &[*asset_id, *source_id, *destination_id]);
            amount(&mut hasher, *amount_atoms);
        }
        GlobalEconomicEffectContentV1::IssueBurn {
            lane_id,
            asset_id,
            kind,
            bucket_id,
            amount_atoms,
            authority_scope_id,
            action_authorization_binding,
        } => {
            lane(&mut hasher, *lane_id);
            hasher.update([kind.code()]);
            commitments(&mut hasher, &[*asset_id, *bucket_id]);
            amount(&mut hasher, *amount_atoms);
            hasher.update(authority_scope_id.as_bytes());
            hasher.update(action_authorization_binding.as_bytes());
        }
        GlobalEconomicEffectContentV1::Custody {
            lane_id,
            asset_id,
            custody_id,
            custody_pre_atoms,
            custody_post_atoms,
            claimant_entitlements_pre_atoms,
            claimant_entitlements_post_atoms,
            unencumbered_reserves_pre_atoms,
            unencumbered_reserves_post_atoms,
        } => {
            lane(&mut hasher, *lane_id);
            commitments(&mut hasher, &[*asset_id, *custody_id]);
            amounts(
                &mut hasher,
                &[
                    *custody_pre_atoms,
                    *custody_post_atoms,
                    *claimant_entitlements_pre_atoms,
                    *claimant_entitlements_post_atoms,
                    *unencumbered_reserves_pre_atoms,
                    *unencumbered_reserves_post_atoms,
                ],
            );
        }
        GlobalEconomicEffectContentV1::Liability {
            lane_id,
            asset_id,
            liability_id,
            pre_atoms,
            post_atoms,
        } => {
            lane(&mut hasher, *lane_id);
            commitments(&mut hasher, &[*asset_id, *liability_id]);
            amounts(&mut hasher, &[*pre_atoms, *post_atoms]);
        }
        GlobalEconomicEffectContentV1::Reserve {
            lane_id,
            asset_id,
            reserve_id,
            pre_atoms,
            post_atoms,
        } => {
            lane(&mut hasher, *lane_id);
            commitments(&mut hasher, &[*asset_id, *reserve_id]);
            amounts(&mut hasher, &[*pre_atoms, *post_atoms]);
        }
        GlobalEconomicEffectContentV1::Fee {
            lane_id,
            asset_id,
            fee_id,
            charged_atoms,
            allocated_atoms,
            carried_residue_atoms,
        } => {
            lane(&mut hasher, *lane_id);
            commitments(&mut hasher, &[*asset_id, *fee_id]);
            amounts(
                &mut hasher,
                &[*charged_atoms, *allocated_atoms, *carried_residue_atoms],
            );
        }
        GlobalEconomicEffectContentV1::RewardSlash {
            lane_id,
            asset_id,
            kind,
            source_id,
            destination_id,
            amount_atoms,
            authority_scope_id,
            action_authorization_binding,
        } => {
            lane(&mut hasher, *lane_id);
            hasher.update([kind.code()]);
            commitments(&mut hasher, &[*asset_id, *source_id, *destination_id]);
            amount(&mut hasher, *amount_atoms);
            hasher.update(authority_scope_id.as_bytes());
            hasher.update(action_authorization_binding.as_bytes());
        }
        GlobalEconomicEffectContentV1::LaneWrite {
            lane_id,
            object_id,
            pre_value_hash,
            post_value_hash,
        } => {
            lane(&mut hasher, *lane_id);
            commitments(
                &mut hasher,
                &[*object_id, *pre_value_hash, *post_value_hash],
            );
        }
        GlobalEconomicEffectContentV1::OccurrenceConsumption {
            kind,
            consumption_id,
        } => {
            hasher.update([kind.code()]);
            hasher.update(consumption_id.as_bytes());
        }
        GlobalEconomicEffectContentV1::TerminalObligation {
            lane_id,
            obligation_id,
            pre_status_hash,
            post_status_hash,
        } => {
            lane(&mut hasher, *lane_id);
            commitments(
                &mut hasher,
                &[*obligation_id, *pre_status_hash, *post_status_hash],
            );
        }
        GlobalEconomicEffectContentV1::ExternalOutboxEnqueue {
            lane_id,
            outbox_id,
            destination_domain_id,
            asset_id,
            amount_atoms,
            value_effect_id,
            payload_commitment,
        } => {
            lane(&mut hasher, *lane_id);
            commitments(
                &mut hasher,
                &[*outbox_id, *asset_id, *value_effect_id, *payload_commitment],
            );
            hasher.update(destination_domain_id.as_bytes());
            amount(&mut hasher, *amount_atoms);
        }
    }
    commitment(hasher, "effect_row_id")
}

pub(super) fn reconciliation_hash_v1(
    row: GlobalAssetReconciliationV1,
) -> Result<CommitmentV3, GlobalEconomicEffectPlanErrorV1> {
    let mut hasher = domain_hasher(RECONCILIATION_DOMAIN_V1)?;
    hasher.update(row.asset_id().as_bytes());
    amounts(
        &mut hasher,
        &[
            row.owned_and_custodied_pre_atoms(),
            row.owned_and_custodied_post_atoms(),
            row.supply_pre_atoms(),
            row.supply_post_atoms(),
            row.liabilities_pre_atoms(),
            row.liabilities_post_atoms(),
            row.named_reserves_pre_atoms(),
            row.named_reserves_post_atoms(),
        ],
    );
    commitment(hasher, "asset_reconciliation")
}

pub(super) fn effect_rows_root_v1(
    rows: &[GlobalEconomicEffectRowV1],
) -> Result<CommitmentV3, GlobalEconomicEffectPlanErrorV1> {
    let values = rows
        .iter()
        .map(effect_row_id_v1)
        .collect::<Result<Vec<_>, _>>()?;
    list_root(EFFECT_ROWS_ROOT_DOMAIN_V1, &values, "effect_rows_root")
}

pub(super) fn effect_semantics_root_v1(
    rows: &[GlobalEconomicEffectRowV1],
) -> Result<CommitmentV3, GlobalEconomicEffectPlanErrorV1> {
    let mut values = rows
        .iter()
        .filter_map(effect_semantic_id_v1)
        .collect::<Result<Vec<_>, _>>()?;
    values.sort_unstable();
    list_root(
        EFFECT_SEMANTICS_ROOT_DOMAIN_V1,
        &values,
        "effect_semantics_root",
    )
}

fn effect_semantic_id_v1(
    row: &GlobalEconomicEffectRowV1,
) -> Option<Result<CommitmentV3, GlobalEconomicEffectPlanErrorV1>> {
    match row.content() {
        GlobalEconomicEffectContentV1::OccurrenceConsumption { .. } => None,
        GlobalEconomicEffectContentV1::IssueBurn { .. } => Some(issue_burn_semantic_id_v1(row)),
        GlobalEconomicEffectContentV1::RewardSlash { .. } => Some(reward_slash_semantic_id_v1(row)),
        GlobalEconomicEffectContentV1::ExternalOutboxEnqueue { .. } => {
            Some(outbox_semantic_id_v1(row))
        }
        _ => Some(effect_row_id_v1(row)),
    }
}

fn issue_burn_semantic_id_v1(
    row: &GlobalEconomicEffectRowV1,
) -> Result<CommitmentV3, GlobalEconomicEffectPlanErrorV1> {
    let GlobalEconomicEffectContentV1::IssueBurn {
        lane_id,
        asset_id,
        kind,
        bucket_id,
        amount_atoms,
        authority_scope_id,
        ..
    } = row.content()
    else {
        return Err(GlobalEconomicEffectPlanErrorV1::InvalidDerivedCommitment(
            "issue_burn_semantic_variant",
        ));
    };
    let mut hasher = domain_hasher(EFFECT_SEMANTIC_ROW_DOMAIN_V1)?;
    hasher.update([row.kind().code(), lane_id.code(), kind.code()]);
    commitments(&mut hasher, &[*asset_id, *bucket_id]);
    amount(&mut hasher, *amount_atoms);
    hasher.update(authority_scope_id.as_bytes());
    commitment(hasher, "effect_semantic_row")
}

fn reward_slash_semantic_id_v1(
    row: &GlobalEconomicEffectRowV1,
) -> Result<CommitmentV3, GlobalEconomicEffectPlanErrorV1> {
    let GlobalEconomicEffectContentV1::RewardSlash {
        lane_id,
        asset_id,
        kind,
        source_id,
        destination_id,
        amount_atoms,
        authority_scope_id,
        ..
    } = row.content()
    else {
        return Err(GlobalEconomicEffectPlanErrorV1::InvalidDerivedCommitment(
            "reward_slash_semantic_variant",
        ));
    };
    let mut hasher = domain_hasher(EFFECT_SEMANTIC_ROW_DOMAIN_V1)?;
    hasher.update([row.kind().code(), lane_id.code(), kind.code()]);
    commitments(&mut hasher, &[*asset_id, *source_id, *destination_id]);
    amount(&mut hasher, *amount_atoms);
    hasher.update(authority_scope_id.as_bytes());
    commitment(hasher, "effect_semantic_row")
}

fn outbox_semantic_id_v1(
    row: &GlobalEconomicEffectRowV1,
) -> Result<CommitmentV3, GlobalEconomicEffectPlanErrorV1> {
    let GlobalEconomicEffectContentV1::ExternalOutboxEnqueue {
        lane_id,
        outbox_id,
        destination_domain_id,
        asset_id,
        amount_atoms,
        payload_commitment,
        ..
    } = row.content()
    else {
        return Err(GlobalEconomicEffectPlanErrorV1::InvalidDerivedCommitment(
            "outbox_semantic_variant",
        ));
    };
    let mut hasher = domain_hasher(EFFECT_SEMANTIC_ROW_DOMAIN_V1)?;
    hasher.update([row.kind().code(), lane_id.code()]);
    commitments(&mut hasher, &[*outbox_id, *asset_id, *payload_commitment]);
    hasher.update(destination_domain_id.as_bytes());
    amount(&mut hasher, *amount_atoms);
    commitment(hasher, "effect_semantic_row")
}

pub(super) fn reconciliations_root_v1(
    rows: &[GlobalAssetReconciliationV1],
) -> Result<CommitmentV3, GlobalEconomicEffectPlanErrorV1> {
    let values = rows
        .iter()
        .copied()
        .map(reconciliation_hash_v1)
        .collect::<Result<Vec<_>, _>>()?;
    list_root(
        RECONCILIATIONS_ROOT_DOMAIN_V1,
        &values,
        "reconciliations_root",
    )
}

pub(super) fn domain_hasher(domain: &[u8]) -> Result<Sha256, GlobalEconomicEffectPlanErrorV1> {
    let length = u16::try_from(domain.len())
        .map_err(|_| GlobalEconomicEffectPlanErrorV1::ArithmeticOverflow("hash_domain_length"))?;
    let mut hasher = Sha256::new();
    hasher.update(length.to_be_bytes());
    hasher.update(domain);
    Ok(hasher)
}

pub(super) fn commitment(
    hasher: Sha256,
    field: &'static str,
) -> Result<CommitmentV3, GlobalEconomicEffectPlanErrorV1> {
    CommitmentV3::new(hasher.finalize().into())
        .map_err(|_| GlobalEconomicEffectPlanErrorV1::InvalidDerivedCommitment(field))
}

fn list_root(
    domain: &[u8],
    values: &[CommitmentV3],
    field: &'static str,
) -> Result<CommitmentV3, GlobalEconomicEffectPlanErrorV1> {
    let mut hasher = domain_hasher(domain)?;
    let count = u32::try_from(values.len())
        .map_err(|_| GlobalEconomicEffectPlanErrorV1::ArithmeticOverflow(field))?;
    hasher.update(count.to_be_bytes());
    commitments(&mut hasher, values);
    commitment(hasher, field)
}

fn lane(hasher: &mut Sha256, lane_id: super::EconomicLaneIdV1) {
    hasher.update([lane_id.code()]);
}
fn amount(hasher: &mut Sha256, value: u128) {
    hasher.update(value.to_be_bytes());
}
fn amounts(hasher: &mut Sha256, values: &[u128]) {
    for value in values {
        amount(hasher, *value);
    }
}
fn commitments(hasher: &mut Sha256, values: &[CommitmentV3]) {
    for value in values {
        hasher.update(value.as_bytes());
    }
}
