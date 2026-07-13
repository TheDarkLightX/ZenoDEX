use alloc::vec::Vec;

use sha2::{Digest, Sha256};

use super::{
    AssetEffectV2, CarryEffectV2, LedgerCellWriteV2, MessageEffectV2, RewardEffectV2,
    SettlementEffectErrorV2,
};
use crate::{CommitmentV3, EconomicActionIdV1};

const CELL_WRITE_DOMAIN_V2: &[u8] = b"zenodex.zrpf.ledger_cell_write.v2";
const ASSET_EFFECT_DOMAIN_V2: &[u8] = b"zenodex.zrpf.asset_effect.v2";
const MESSAGE_EFFECT_DOMAIN_V2: &[u8] = b"zenodex.zrpf.message_effect.v2";
const CARRY_EFFECT_DOMAIN_V2: &[u8] = b"zenodex.zrpf.carry_effect.v2";
const REWARD_EFFECT_DOMAIN_V2: &[u8] = b"zenodex.zrpf.reward_effect.v2";
const CELL_WRITES_ROOT_DOMAIN_V2: &[u8] = b"zenodex.zrpf.ledger_cell_writes_root.v2";
const ASSET_EFFECTS_ROOT_DOMAIN_V2: &[u8] = b"zenodex.zrpf.asset_effects_root.v2";
const MESSAGE_EFFECTS_ROOT_DOMAIN_V2: &[u8] = b"zenodex.zrpf.message_effects_root.v2";
const CARRY_EFFECTS_ROOT_DOMAIN_V2: &[u8] = b"zenodex.zrpf.carry_effects_root.v2";
const REWARD_EFFECTS_ROOT_DOMAIN_V2: &[u8] = b"zenodex.zrpf.reward_effects_root.v2";
pub(super) const PLAN_COMMITMENT_DOMAIN_V2: &[u8] = b"zenodex.zrpf.settlement_effect_plan.v2";

pub(super) fn cell_write_hash_v2(
    row: &LedgerCellWriteV2,
) -> Result<CommitmentV3, SettlementEffectErrorV2> {
    let mut hasher = domain_hasher(CELL_WRITE_DOMAIN_V2)?;
    write_action(&mut hasher, row.economic_action_id());
    hasher.update(row.cell_key().as_bytes());
    hasher.update(row.pre_value_hash().as_bytes());
    hasher.update(row.post_value_hash().as_bytes());
    commitment(hasher, "cell_write")
}

pub(super) fn asset_effect_id_v2(
    row: &AssetEffectV2,
) -> Result<CommitmentV3, SettlementEffectErrorV2> {
    let mut hasher = domain_hasher(ASSET_EFFECT_DOMAIN_V2)?;
    hasher.update([row.kind().code()]);
    write_action(&mut hasher, row.economic_action_id());
    hasher.update(row.asset_id().as_bytes());
    for amount in [
        row.debit_atoms(),
        row.credit_atoms(),
        row.authorized_mint_atoms(),
        row.authorized_burn_atoms(),
    ] {
        hasher.update(amount.to_be_bytes());
    }
    match (row.authority_scope_id(), row.action_authorization_binding()) {
        (Some(scope), Some(binding)) => {
            hasher.update([1]);
            hasher.update(scope.as_bytes());
            hasher.update(binding.as_bytes());
        }
        (None, None) => hasher.update([0]),
        _ => return Err(SettlementEffectErrorV2::AuthorizationMismatch),
    }
    commitment(hasher, "asset_effect_id")
}

pub(super) fn message_effect_id_v2(
    row: &MessageEffectV2,
) -> Result<CommitmentV3, SettlementEffectErrorV2> {
    let mut hasher = domain_hasher(MESSAGE_EFFECT_DOMAIN_V2)?;
    write_action(&mut hasher, row.economic_action_id());
    hasher.update(row.asset_effect_id().as_bytes());
    hasher.update(row.source_domain_id().as_bytes());
    hasher.update(row.destination_domain_id().as_bytes());
    hasher.update(row.asset_id().as_bytes());
    hasher.update(row.amount_atoms().to_be_bytes());
    hasher.update([row.kind().code()]);
    commitment(hasher, "message_effect_id")
}

pub(super) fn carry_effect_id_v2(
    row: &CarryEffectV2,
) -> Result<CommitmentV3, SettlementEffectErrorV2> {
    let mut hasher = domain_hasher(CARRY_EFFECT_DOMAIN_V2)?;
    write_action(&mut hasher, row.economic_action_id());
    hasher.update(row.message_id().as_bytes());
    hasher.update(row.asset_id().as_bytes());
    hasher.update(row.amount_atoms().to_be_bytes());
    hasher.update([row.kind().code()]);
    commitment(hasher, "carry_effect_id")
}

pub(super) fn reward_effect_id_v2(
    row: &RewardEffectV2,
) -> Result<CommitmentV3, SettlementEffectErrorV2> {
    let mut hasher = domain_hasher(REWARD_EFFECT_DOMAIN_V2)?;
    write_action(&mut hasher, row.economic_action_id());
    hasher.update(row.asset_effect_id().as_bytes());
    hasher.update(row.recipient_cell_key().as_bytes());
    hasher.update(row.asset_id().as_bytes());
    hasher.update(row.amount_atoms().to_be_bytes());
    hasher.update(row.authority_scope_id().as_bytes());
    hasher.update(row.action_authorization_binding().as_bytes());
    commitment(hasher, "reward_effect_id")
}

pub(super) fn cell_writes_root_v2(
    rows: &[LedgerCellWriteV2],
) -> Result<CommitmentV3, SettlementEffectErrorV2> {
    let values = rows
        .iter()
        .map(cell_write_hash_v2)
        .collect::<Result<Vec<_>, _>>()?;
    list_root(CELL_WRITES_ROOT_DOMAIN_V2, &values, "cell_writes_root")
}

pub(super) fn asset_effects_root_v2(
    rows: &[AssetEffectV2],
) -> Result<CommitmentV3, SettlementEffectErrorV2> {
    let values = rows
        .iter()
        .map(asset_effect_id_v2)
        .collect::<Result<Vec<_>, _>>()?;
    list_root(ASSET_EFFECTS_ROOT_DOMAIN_V2, &values, "asset_effects_root")
}

pub(super) fn message_effects_root_v2(
    rows: &[MessageEffectV2],
) -> Result<CommitmentV3, SettlementEffectErrorV2> {
    let values = rows
        .iter()
        .map(message_effect_id_v2)
        .collect::<Result<Vec<_>, _>>()?;
    list_root(
        MESSAGE_EFFECTS_ROOT_DOMAIN_V2,
        &values,
        "message_effects_root",
    )
}

pub(super) fn carry_effects_root_v2(
    rows: &[CarryEffectV2],
) -> Result<CommitmentV3, SettlementEffectErrorV2> {
    let values = rows
        .iter()
        .map(carry_effect_id_v2)
        .collect::<Result<Vec<_>, _>>()?;
    list_root(CARRY_EFFECTS_ROOT_DOMAIN_V2, &values, "carry_effects_root")
}

pub(super) fn reward_effects_root_v2(
    rows: &[RewardEffectV2],
) -> Result<CommitmentV3, SettlementEffectErrorV2> {
    let values = rows
        .iter()
        .map(reward_effect_id_v2)
        .collect::<Result<Vec<_>, _>>()?;
    list_root(
        REWARD_EFFECTS_ROOT_DOMAIN_V2,
        &values,
        "reward_effects_root",
    )
}

fn list_root(
    domain: &[u8],
    values: &[CommitmentV3],
    field: &'static str,
) -> Result<CommitmentV3, SettlementEffectErrorV2> {
    let mut hasher = domain_hasher(domain)?;
    let count = u32::try_from(values.len())
        .map_err(|_| SettlementEffectErrorV2::ArithmeticOverflow(field))?;
    hasher.update(count.to_be_bytes());
    for value in values {
        hasher.update(value.as_bytes());
    }
    commitment(hasher, field)
}

pub(super) fn domain_hasher(domain: &[u8]) -> Result<Sha256, SettlementEffectErrorV2> {
    let length = u16::try_from(domain.len())
        .map_err(|_| SettlementEffectErrorV2::ArithmeticOverflow("hash_domain"))?;
    let mut hasher = Sha256::new();
    hasher.update(length.to_be_bytes());
    hasher.update(domain);
    Ok(hasher)
}

pub(super) fn commitment(
    hasher: Sha256,
    field: &'static str,
) -> Result<CommitmentV3, SettlementEffectErrorV2> {
    CommitmentV3::new(hasher.finalize().into())
        .map_err(|_| SettlementEffectErrorV2::InvalidDerivedCommitment(field))
}

fn write_action(hasher: &mut Sha256, action_id: EconomicActionIdV1) {
    hasher.update(action_id.as_bytes());
}
