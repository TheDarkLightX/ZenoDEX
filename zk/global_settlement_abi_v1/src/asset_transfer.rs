use std::collections::BTreeMap;

use serde::Serialize;

use crate::asset_transfer_types::*;
use crate::canonical::{
    hash_global_v1, AbiErrorV1, AbiResultV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1,
    MAX_ASSET_BALANCE_ROWS_V1, ZERO_ROOT_V1,
};
use crate::effects::{
    AssetConservationRowV1, EconomicEffectKindV1, EconomicEffectRowV1, FeeConservationRowV1,
    GlobalEconomicEffectPlanV1, LaneWriteV1,
};
use crate::proof::LaneModuleTransitionJournalV1;
use crate::release::LaneIdV1;
use crate::state::EconomicAmountV1;

fn empty_effects() -> GlobalEconomicEffectPlanV1 {
    GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: Vec::new(),
        asset_conservation: Vec::new(),
        fee_conservation: Vec::new(),
        lane_writes: Vec::new(),
        occurrence_consumptions: Vec::new(),
        external_outbox_enqueue: Vec::new(),
    }
}

fn reject(
    code: AssetTransferRejectCodeV1,
    pre_state: &AssetTransferStateV1,
) -> AbiResultV1<AssetTransferResultV1> {
    let root = pre_state.state_root()?;
    Ok(AssetTransferResultV1::Rejected(Box::new(
        AssetTransferRejectedV1 {
            code,
            pre_state_root: root.clone(),
            post_state_root: root,
            effects: empty_effects(),
        },
    )))
}

fn apply_delta(current: u128, delta: i128) -> Result<u128, AssetTransferRejectCodeV1> {
    if delta < 0 {
        current
            .checked_sub(delta.unsigned_abs())
            .ok_or(AssetTransferRejectCodeV1::INSUFFICIENT_BALANCE)
    } else {
        current
            .checked_add(delta.unsigned_abs())
            .ok_or(AssetTransferRejectCodeV1::BALANCE_OVERFLOW)
    }
}

fn checked_negative_sum(left: u128, right: u128) -> Result<i128, AssetTransferRejectCodeV1> {
    let magnitude = left
        .checked_add(right)
        .ok_or(AssetTransferRejectCodeV1::EFFECT_DELTA_OVERFLOW)?;
    const I128_MIN_MAGNITUDE: u128 = 1_u128 << 127;
    if magnitude == I128_MIN_MAGNITUDE {
        return Ok(i128::MIN);
    }
    i128::try_from(magnitude)
        .ok()
        .and_then(i128::checked_neg)
        .ok_or(AssetTransferRejectCodeV1::EFFECT_DELTA_OVERFLOW)
}

fn post_balances(
    state: &AssetTransferStateV1,
    asset: &str,
    deltas: &BTreeMap<String, i128>,
) -> Result<Vec<EconomicAmountV1>, AssetTransferRejectCodeV1> {
    let mut values = state
        .balances
        .iter()
        .map(|row| ((row.asset.clone(), row.owner.clone()), row.amount_atoms))
        .collect::<BTreeMap<_, _>>();

    // Reject by semantic failure class before applying any delta. Iterating the
    // BTreeMap directly used to make the public reject code depend on the
    // lexical spelling of principals whenever an underfunded sender and an
    // overflowing credit were both present. Debit insufficiency has fixed
    // priority over credit overflow, independent of canonical map order.
    for (owner, delta) in deltas.iter().filter(|(_, delta)| **delta < 0) {
        let key = (asset.to_owned(), owner.clone());
        apply_delta(values.get(&key).copied().unwrap_or(0), *delta)?;
    }
    for (owner, delta) in deltas.iter().filter(|(_, delta)| **delta >= 0) {
        let key = (asset.to_owned(), owner.clone());
        apply_delta(values.get(&key).copied().unwrap_or(0), *delta)?;
    }

    for (owner, delta) in deltas {
        let key = (asset.to_owned(), owner.clone());
        let post = apply_delta(values.get(&key).copied().unwrap_or(0), *delta)?;
        if post == 0 {
            values.remove(&key);
        } else {
            values.insert(key, post);
        }
    }
    if values.len() > MAX_ASSET_BALANCE_ROWS_V1 {
        return Err(AssetTransferRejectCodeV1::POST_STATE_RESOURCE_BOUND_EXCEEDED);
    }
    Ok(values
        .into_iter()
        .map(|((row_asset, owner), amount_atoms)| EconomicAmountV1 {
            owner,
            asset: row_asset,
            custody_domain: ACCOUNT_CUSTODY_DOMAIN_V1.to_owned(),
            amount_atoms,
        })
        .collect())
}

fn account_total(state: &AssetTransferStateV1, asset: &str) -> AbiResultV1<u128> {
    state
        .balances
        .iter()
        .filter(|row| row.asset == asset)
        .try_fold(0_u128, |total, row| {
            total
                .checked_add(row.amount_atoms)
                .ok_or(AbiErrorV1::Conservation(
                    "asset transfer account total overflow",
                ))
        })
}

#[derive(Serialize)]
struct AssetTransferReceiptBodyV1<'a> {
    context: &'a AssetTransferContextV1,
    command: &'a AssetTransferCommandV1,
    pre_state_root: &'a RootV1,
    post_state_root: &'a RootV1,
    effect_plan_root: &'a RootV1,
    private_port_root: &'a RootV1,
    terminal_obligations_root: &'a RootV1,
}

struct PreparedTransferV1<'a> {
    context: &'a AssetTransferContextV1,
    pre_state: &'a AssetTransferStateV1,
    command: &'a AssetTransferCommandV1,
    policy: &'a AssetTransferPolicyV1,
    fee: i128,
    deltas: BTreeMap<String, i128>,
}

fn transfer_policy<'a>(
    context: &AssetTransferContextV1,
    pre_state: &'a AssetTransferStateV1,
    command: &AssetTransferCommandV1,
) -> Result<&'a AssetTransferPolicyV1, AssetTransferRejectCodeV1> {
    if context.module_release_id != pre_state.module_release_id {
        return Err(AssetTransferRejectCodeV1::RELEASE_MISMATCH);
    }
    if command.command_kind != ASSET_TRANSFER_COMMAND_KIND_V1 {
        return Err(AssetTransferRejectCodeV1::UNKNOWN_COMMAND);
    }
    let policy = pre_state
        .policies
        .iter()
        .find(|policy| policy.asset == command.asset)
        .ok_or(AssetTransferRejectCodeV1::UNKNOWN_ASSET)?;
    if !policy.enabled {
        return Err(AssetTransferRejectCodeV1::DISABLED_ASSET);
    }
    if command.sender != context.subject_id {
        return Err(AssetTransferRejectCodeV1::UNAUTHORIZED_SUBJECT);
    }
    if command.sender == command.recipient {
        return Err(AssetTransferRejectCodeV1::SELF_TRANSFER);
    }
    if command.amount_atoms == 0 {
        return Err(AssetTransferRejectCodeV1::ZERO_AMOUNT);
    }
    if policy.transfer_fee_atoms > command.max_fee_atoms {
        return Err(AssetTransferRejectCodeV1::FEE_LIMIT_EXCEEDED);
    }
    Ok(policy)
}

fn prepare_transfer<'a>(
    context: &'a AssetTransferContextV1,
    pre_state: &'a AssetTransferStateV1,
    command: &'a AssetTransferCommandV1,
) -> Result<PreparedTransferV1<'a>, AssetTransferRejectCodeV1> {
    let policy = transfer_policy(context, pre_state, command)?;
    let amount = i128::try_from(command.amount_atoms)
        .map_err(|_| AssetTransferRejectCodeV1::EFFECT_DELTA_OVERFLOW)?;
    let fee = i128::try_from(policy.transfer_fee_atoms)
        .map_err(|_| AssetTransferRejectCodeV1::EFFECT_DELTA_OVERFLOW)?;
    let mut deltas = BTreeMap::new();
    if policy.fee_owner == command.sender {
        let sender_delta = amount
            .checked_neg()
            .ok_or(AssetTransferRejectCodeV1::EFFECT_DELTA_OVERFLOW)?;
        deltas.insert(command.sender.clone(), sender_delta);
        deltas.insert(command.recipient.clone(), amount);
    } else if policy.fee_owner == command.recipient {
        let recipient_delta = amount
            .checked_add(fee)
            .ok_or(AssetTransferRejectCodeV1::EFFECT_DELTA_OVERFLOW)?;
        let sender_delta = recipient_delta
            .checked_neg()
            .ok_or(AssetTransferRejectCodeV1::EFFECT_DELTA_OVERFLOW)?;
        deltas.insert(command.sender.clone(), sender_delta);
        deltas.insert(command.recipient.clone(), recipient_delta);
    } else {
        let sender_delta = checked_negative_sum(command.amount_atoms, policy.transfer_fee_atoms)?;
        deltas.insert(command.sender.clone(), sender_delta);
        deltas.insert(command.recipient.clone(), amount);
        deltas.insert(policy.fee_owner.clone(), fee);
    }
    Ok(PreparedTransferV1 {
        context,
        pre_state,
        command,
        policy,
        fee,
        deltas,
    })
}

fn effect_rows(prepared: &PreparedTransferV1<'_>) -> Vec<EconomicEffectRowV1> {
    let command = prepared.command;
    let mut rows = prepared
        .deltas
        .iter()
        .filter(|(_, delta)| **delta != 0)
        .map(|(owner, delta_atoms)| EconomicEffectRowV1 {
            kind: EconomicEffectKindV1::ACCOUNT_MOVEMENT,
            principal: owner.clone(),
            asset: command.asset.clone(),
            custody_domain: ACCOUNT_CUSTODY_DOMAIN_V1.to_owned(),
            delta_atoms: *delta_atoms,
        })
        .collect::<Vec<_>>();
    if prepared.fee != 0 {
        rows.push(EconomicEffectRowV1 {
            kind: EconomicEffectKindV1::FEE_ALLOCATION,
            principal: prepared.policy.fee_owner.clone(),
            asset: command.asset.clone(),
            custody_domain: ACCOUNT_CUSTODY_DOMAIN_V1.to_owned(),
            delta_atoms: prepared.fee,
        });
    }
    rows
}

fn effect_plan(
    post_state: &AssetTransferStateV1,
    prepared: &PreparedTransferV1<'_>,
) -> AbiResultV1<GlobalEconomicEffectPlanV1> {
    let context = prepared.context;
    let pre_state = prepared.pre_state;
    let command = prepared.command;
    let fee_conservation = (prepared.fee != 0)
        .then(|| FeeConservationRowV1 {
            asset: command.asset.clone(),
            fee_charged_atoms: prepared.policy.transfer_fee_atoms,
            current_allocations_atoms: prepared.policy.transfer_fee_atoms,
            carried_residue_atoms: 0,
        })
        .into_iter()
        .collect();
    Ok(GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: effect_rows(prepared),
        asset_conservation: vec![AssetConservationRowV1 {
            asset: command.asset.clone(),
            owned_and_custodied_pre_atoms: account_total(pre_state, &command.asset)?,
            owned_and_custodied_post_atoms: account_total(post_state, &command.asset)?,
            supply_pre_atoms: pre_state.supply_atoms(&command.asset)?,
            supply_post_atoms: post_state.supply_atoms(&command.asset)?,
            authorized_issue_atoms: 0,
            authorized_burn_atoms: 0,
        }],
        fee_conservation,
        lane_writes: vec![LaneWriteV1 {
            lane_id: LaneIdV1::ASSET_TRANSFER,
            pre_root: pre_state.state_root()?,
            post_root: post_state.state_root()?,
        }],
        occurrence_consumptions: vec![context.command_occurrence_id.clone()],
        external_outbox_enqueue: Vec::new(),
    })
}

fn accept_transfer(
    prepared: &PreparedTransferV1<'_>,
    balances: Vec<EconomicAmountV1>,
) -> AbiResultV1<AssetTransferResultV1> {
    let context = prepared.context;
    let pre_state = prepared.pre_state;
    let command = prepared.command;
    let post_state = AssetTransferStateV1 {
        schema: ASSET_TRANSFER_MODULE_SCHEMA_V1.to_owned(),
        module_release_id: pre_state.module_release_id.clone(),
        policies: pre_state.policies.clone(),
        balances,
        supplies: pre_state.supplies.clone(),
    };
    let pre_root = pre_state.state_root()?;
    let post_root = post_state.state_root()?;
    let effects = effect_plan(&post_state, prepared)?;
    let effect_root = effects.effect_plan_root()?;
    let private_port_root = RootV1::parse(ZERO_ROOT_V1, "empty private port root", true)?;
    let terminal_obligations_root =
        RootV1::parse(ZERO_ROOT_V1, "empty terminal obligations root", true)?;
    let receipt_root = hash_global_v1(
        "asset-transfer-receipt-v1",
        &AssetTransferReceiptBodyV1 {
            context,
            command,
            pre_state_root: &pre_root,
            post_state_root: &post_root,
            effect_plan_root: &effect_root,
            private_port_root: &private_port_root,
            terminal_obligations_root: &terminal_obligations_root,
        },
    )?;
    let module_journal = LaneModuleTransitionJournalV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: context.chain_id.clone(),
        deployment_root: context.deployment_root.clone(),
        profile_root: context.profile_root.clone(),
        writer_epoch: context.writer_epoch,
        lane_id: LaneIdV1::ASSET_TRANSFER,
        module_release_id: context.module_release_id.clone(),
        command_occurrence_id: context.command_occurrence_id.clone(),
        pre_lane_root: pre_root,
        post_lane_root: post_root,
        effect_plan_root: effect_root,
        private_port_root,
        receipt_root,
        terminal_obligations_root,
    };
    let accepted = AssetTransferAcceptedV1 {
        post_state,
        effects,
        module_journal,
    };
    accepted.validate()?;
    Ok(AssetTransferResultV1::Accepted(Box::new(accepted)))
}

pub fn transition_asset_transfer_v1(
    context: &AssetTransferContextV1,
    pre_state: &AssetTransferStateV1,
    command: &AssetTransferCommandV1,
) -> AbiResultV1<AssetTransferResultV1> {
    context.validate()?;
    pre_state.validate()?;
    command.validate()?;
    let prepared = match prepare_transfer(context, pre_state, command) {
        Ok(value) => value,
        Err(code) => return reject(code, pre_state),
    };
    let balances = match post_balances(pre_state, &command.asset, &prepared.deltas) {
        Ok(value) => value,
        Err(code) => return reject(code, pre_state),
    };
    accept_transfer(&prepared, balances)
}
