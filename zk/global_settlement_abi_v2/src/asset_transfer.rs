use std::collections::BTreeMap;

use serde::Serialize;

use crate::asset_transfer_types::*;
use crate::canonical::{hash_global_v2, AbiErrorV2, AbiResultV2, RootV2, GLOBAL_SETTLEMENT_ABI_V2};
use crate::effects::{
    AssetConservationRowV2, EconomicEffectKindV2, EconomicEffectRowV2, FeeConservationRowV2,
    GlobalEconomicEffectPlanV2, LaneIdV2, LaneWriteV2,
};
use crate::proof::LaneModuleTransitionJournalV2;
use crate::state::EconomicAmountV2;

fn reject(
    code: AssetTransferRejectCodeV2,
    pre_state: &AssetTransferStateV2,
) -> AbiResultV2<AssetTransferResultV2> {
    let root = pre_state.state_root()?;
    let rejected = AssetTransferRejectedV2 {
        code,
        pre_state_root: root.clone(),
        post_state_root: root,
        effects: GlobalEconomicEffectPlanV2::empty(),
    };
    rejected.validate()?;
    Ok(AssetTransferResultV2::Rejected(Box::new(rejected)))
}

fn apply_delta(current: u128, delta: i128) -> Result<u128, AssetTransferRejectCodeV2> {
    if delta < 0 {
        current
            .checked_sub(delta.unsigned_abs())
            .ok_or(AssetTransferRejectCodeV2::INSUFFICIENT_BALANCE)
    } else {
        current
            .checked_add(delta.unsigned_abs())
            .ok_or(AssetTransferRejectCodeV2::BALANCE_OVERFLOW)
    }
}

fn positive_delta(value: u128) -> Result<i128, AssetTransferRejectCodeV2> {
    i128::try_from(value).map_err(|_| AssetTransferRejectCodeV2::EFFECT_DELTA_OVERFLOW)
}

fn negative_delta(value: u128) -> Result<i128, AssetTransferRejectCodeV2> {
    const I128_MIN_MAGNITUDE: u128 = 1_u128 << 127;
    if value == I128_MIN_MAGNITUDE {
        return Ok(i128::MIN);
    }
    positive_delta(value)?
        .checked_neg()
        .ok_or(AssetTransferRejectCodeV2::EFFECT_DELTA_OVERFLOW)
}

fn sum_atoms(left: u128, right: u128) -> Result<u128, AssetTransferRejectCodeV2> {
    left.checked_add(right)
        .ok_or(AssetTransferRejectCodeV2::EFFECT_DELTA_OVERFLOW)
}

fn transfer_deltas(
    command: &AssetTransferCommandV2,
    policy: &AssetTransferPolicyV2,
) -> Result<(BTreeMap<String, i128>, i128), AssetTransferRejectCodeV2> {
    let fee = positive_delta(policy.transfer_fee_atoms)?;
    let amount = positive_delta(command.amount_atoms)?;
    let mut deltas = BTreeMap::new();
    if policy.fee_owner == command.sender {
        deltas.insert(
            command.sender.clone(),
            negative_delta(command.amount_atoms)?,
        );
        deltas.insert(command.recipient.clone(), amount);
    } else if policy.fee_owner == command.recipient {
        let total = sum_atoms(command.amount_atoms, policy.transfer_fee_atoms)?;
        let positive_total = positive_delta(total)?;
        deltas.insert(command.sender.clone(), negative_delta(total)?);
        deltas.insert(command.recipient.clone(), positive_total);
    } else {
        let total = sum_atoms(command.amount_atoms, policy.transfer_fee_atoms)?;
        deltas.insert(command.sender.clone(), negative_delta(total)?);
        deltas.insert(command.recipient.clone(), amount);
        deltas.insert(policy.fee_owner.clone(), fee);
    }
    Ok((deltas, fee))
}

fn post_balances(
    state: &AssetTransferStateV2,
    asset: &str,
    deltas: &BTreeMap<String, i128>,
) -> Result<Vec<EconomicAmountV2>, AssetTransferRejectCodeV2> {
    let mut values = state
        .balances
        .iter()
        .map(|row| ((row.asset.clone(), row.owner.clone()), row.amount_atoms))
        .collect::<BTreeMap<_, _>>();
    for (owner, delta) in deltas {
        let key = (asset.to_owned(), owner.clone());
        let post = apply_delta(values.get(&key).copied().unwrap_or(0), *delta)?;
        if post == 0 {
            values.remove(&key);
        } else {
            values.insert(key, post);
        }
    }
    Ok(values
        .into_iter()
        .map(|((row_asset, owner), amount_atoms)| EconomicAmountV2 {
            owner,
            asset: row_asset,
            custody_domain: ACCOUNT_CUSTODY_DOMAIN_V2.to_owned(),
            amount_atoms,
        })
        .collect())
}

fn account_total(state: &AssetTransferStateV2, asset: &str) -> AbiResultV2<u128> {
    state
        .balances
        .iter()
        .filter(|row| row.asset == asset)
        .try_fold(0_u128, |total, row| {
            total
                .checked_add(row.amount_atoms)
                .ok_or(AbiErrorV2::Conservation(
                    "asset transfer account total overflow",
                ))
        })
}

fn transfer_policy<'a>(
    context: &AssetTransferContextV2,
    pre_state: &'a AssetTransferStateV2,
    command: &AssetTransferCommandV2,
    command_body_hash: &RootV2,
) -> Result<&'a AssetTransferPolicyV2, AssetTransferRejectCodeV2> {
    let occurrence = context
        .occurrence
        .as_ref()
        .ok_or(AssetTransferRejectCodeV2::MISSING_OCCURRENCE)?;
    if occurrence.pre_state_root != context.global_pre_state_root
        || !occurrence.consumed_object_ids.is_empty()
    {
        return Err(AssetTransferRejectCodeV2::OCCURRENCE_BINDING_MISMATCH);
    }
    if context.module_release_id != pre_state.module_release_id {
        return Err(AssetTransferRejectCodeV2::RELEASE_MISMATCH);
    }
    if command.command_kind != ASSET_TRANSFER_COMMAND_KIND_V2 {
        return Err(AssetTransferRejectCodeV2::UNKNOWN_COMMAND);
    }
    if occurrence.command_kind != command.command_kind
        || occurrence.command_body_hash != *command_body_hash
    {
        return Err(AssetTransferRejectCodeV2::OCCURRENCE_COMMAND_MISMATCH);
    }
    let policy = pre_state
        .policies
        .iter()
        .find(|policy| policy.asset == command.asset)
        .ok_or(AssetTransferRejectCodeV2::UNKNOWN_ASSET)?;
    if !policy.enabled {
        return Err(AssetTransferRejectCodeV2::DISABLED_ASSET);
    }
    let (Some(policy_origin), Some(command_origin)) =
        (&policy.asset_origin_root, &command.asset_origin_root)
    else {
        return Err(AssetTransferRejectCodeV2::UNREGISTERED_ASSET);
    };
    if command_origin != policy_origin {
        return Err(AssetTransferRejectCodeV2::ASSET_ORIGIN_MISMATCH);
    }
    if policy.asset_class == AssetClassV2::TauNativeCoin {
        return Err(AssetTransferRejectCodeV2::NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED);
    }
    if command.sender != occurrence.subject_id {
        return Err(AssetTransferRejectCodeV2::UNAUTHORIZED_SUBJECT);
    }
    if command.sender == command.recipient {
        return Err(AssetTransferRejectCodeV2::SELF_TRANSFER);
    }
    if command.amount_atoms == 0 {
        return Err(AssetTransferRejectCodeV2::ZERO_AMOUNT);
    }
    if policy.transfer_fee_atoms > command.max_fee_atoms {
        return Err(AssetTransferRejectCodeV2::FEE_LIMIT_EXCEEDED);
    }
    Ok(policy)
}

struct PreparedTransferV2<'a> {
    context: &'a AssetTransferContextV2,
    pre_state: &'a AssetTransferStateV2,
    command: &'a AssetTransferCommandV2,
    policy: &'a AssetTransferPolicyV2,
    deltas: BTreeMap<String, i128>,
    fee_delta: i128,
}

fn prepare_transfer<'a>(
    context: &'a AssetTransferContextV2,
    pre_state: &'a AssetTransferStateV2,
    command: &'a AssetTransferCommandV2,
) -> AbiResultV2<Result<PreparedTransferV2<'a>, AssetTransferRejectCodeV2>> {
    let command_body_hash = command.command_body_hash()?;
    let policy = match transfer_policy(context, pre_state, command, &command_body_hash) {
        Ok(policy) => policy,
        Err(code) => return Ok(Err(code)),
    };
    let (deltas, fee_delta) = match transfer_deltas(command, policy) {
        Ok(values) => values,
        Err(code) => return Ok(Err(code)),
    };
    Ok(Ok(PreparedTransferV2 {
        context,
        pre_state,
        command,
        policy,
        deltas,
        fee_delta,
    }))
}

fn effect_rows(prepared: &PreparedTransferV2<'_>) -> Vec<EconomicEffectRowV2> {
    let mut rows = prepared
        .deltas
        .iter()
        .filter(|(_, delta)| **delta != 0)
        .map(|(owner, delta_atoms)| EconomicEffectRowV2 {
            kind: EconomicEffectKindV2::ACCOUNT_MOVEMENT,
            principal: owner.clone(),
            asset: prepared.command.asset.clone(),
            custody_domain: ACCOUNT_CUSTODY_DOMAIN_V2.to_owned(),
            delta_atoms: *delta_atoms,
        })
        .collect::<Vec<_>>();
    if prepared.policy.transfer_fee_atoms != 0 {
        rows.push(EconomicEffectRowV2 {
            kind: EconomicEffectKindV2::FEE_ALLOCATION,
            principal: prepared.policy.fee_owner.clone(),
            asset: prepared.command.asset.clone(),
            custody_domain: ACCOUNT_CUSTODY_DOMAIN_V2.to_owned(),
            delta_atoms: prepared.fee_delta,
        });
    }
    rows.sort_by(|left, right| left.key().cmp(&right.key()));
    rows
}

fn effect_plan(
    post_state: &AssetTransferStateV2,
    prepared: &PreparedTransferV2<'_>,
) -> AbiResultV2<GlobalEconomicEffectPlanV2> {
    let occurrence = prepared
        .context
        .occurrence
        .as_ref()
        .ok_or(AbiErrorV2::InvalidBinding("prepared transfer occurrence"))?;
    let fee_conservation = (prepared.policy.transfer_fee_atoms != 0)
        .then(|| FeeConservationRowV2 {
            asset: prepared.command.asset.clone(),
            fee_charged_atoms: prepared.policy.transfer_fee_atoms,
            current_allocations_atoms: prepared.policy.transfer_fee_atoms,
            carried_residue_atoms: 0,
        })
        .into_iter()
        .collect();
    let effects = GlobalEconomicEffectPlanV2 {
        schema: GLOBAL_SETTLEMENT_ABI_V2.to_owned(),
        rows: effect_rows(prepared),
        asset_conservation: vec![AssetConservationRowV2 {
            asset: prepared.command.asset.clone(),
            owned_and_custodied_pre_atoms: account_total(
                prepared.pre_state,
                &prepared.command.asset,
            )?,
            owned_and_custodied_post_atoms: account_total(post_state, &prepared.command.asset)?,
            supply_pre_atoms: prepared.pre_state.supply_atoms(&prepared.command.asset)?,
            supply_post_atoms: post_state.supply_atoms(&prepared.command.asset)?,
            authorized_issue_atoms: 0,
            authorized_burn_atoms: 0,
        }],
        fee_conservation,
        lane_writes: vec![LaneWriteV2 {
            lane_id: LaneIdV2::ASSET_TRANSFER,
            pre_root: prepared.pre_state.state_root()?,
            post_root: post_state.state_root()?,
        }],
        occurrence_consumptions: vec![occurrence.occurrence_id()?],
        external_outbox_enqueue: Vec::new(),
    };
    effects.validate()?;
    Ok(effects)
}

#[derive(Serialize)]
struct AssetTransferReceiptBodyV2<'a> {
    context: &'a AssetTransferContextV2,
    command: &'a AssetTransferCommandV2,
    pre_state_root: &'a RootV2,
    post_state_root: &'a RootV2,
    effect_plan_root: &'a RootV2,
    private_port_root: &'a RootV2,
    terminal_obligations_root: &'a RootV2,
    oracle_occurrence_plan_root: &'a RootV2,
}

fn build_module_journal(
    prepared: &PreparedTransferV2<'_>,
    pre_root: RootV2,
    post_root: RootV2,
    effect_plan_root: RootV2,
) -> AbiResultV2<LaneModuleTransitionJournalV2> {
    let occurrence = prepared
        .context
        .occurrence
        .as_ref()
        .ok_or(AbiErrorV2::InvalidBinding("prepared transfer occurrence"))?;
    let private_port_root = RootV2::zero();
    let terminal_obligations_root = RootV2::zero();
    let oracle_occurrence_plan_root = RootV2::zero();
    let receipt_root = hash_global_v2(
        "asset-transfer-receipt-v2",
        &AssetTransferReceiptBodyV2 {
            context: prepared.context,
            command: prepared.command,
            pre_state_root: &pre_root,
            post_state_root: &post_root,
            effect_plan_root: &effect_plan_root,
            private_port_root: &private_port_root,
            terminal_obligations_root: &terminal_obligations_root,
            oracle_occurrence_plan_root: &oracle_occurrence_plan_root,
        },
    )?;
    Ok(LaneModuleTransitionJournalV2 {
        schema: GLOBAL_SETTLEMENT_ABI_V2.to_owned(),
        chain_id: occurrence.chain_id.clone(),
        deployment_root: occurrence.deployment_root.clone(),
        profile_root: occurrence.profile_root.clone(),
        writer_epoch: prepared.context.writer_epoch,
        lane_id: LaneIdV2::ASSET_TRANSFER,
        module_release_id: prepared.context.module_release_id.clone(),
        command_occurrence_id: occurrence.occurrence_id()?,
        pre_lane_root: pre_root,
        post_lane_root: post_root,
        effect_plan_root,
        private_port_root,
        receipt_root,
        terminal_obligations_root,
        oracle_occurrence_plan_root,
    })
}

fn accept_transfer(
    prepared: &PreparedTransferV2<'_>,
    balances: Vec<EconomicAmountV2>,
) -> AbiResultV2<AssetTransferResultV2> {
    let post_state = AssetTransferStateV2 {
        schema: ASSET_TRANSFER_MODULE_SCHEMA_V2.to_owned(),
        module_release_id: prepared.pre_state.module_release_id.clone(),
        policies: prepared.pre_state.policies.clone(),
        balances,
        supplies: prepared.pre_state.supplies.clone(),
    };
    let pre_root = prepared.pre_state.state_root()?;
    let post_root = post_state.state_root()?;
    let effects = effect_plan(&post_state, prepared)?;
    let effect_plan_root = effects.effect_plan_root()?;
    let module_journal = build_module_journal(prepared, pre_root, post_root, effect_plan_root)?;
    let accepted = AssetTransferAcceptedV2 {
        post_state,
        effects,
        module_journal,
        production_authority: ASSET_LANE_PRODUCTION_AUTHORITY_V2.to_owned(),
    };
    accepted.validate()?;
    Ok(AssetTransferResultV2::Accepted(Box::new(accepted)))
}

pub fn transition_asset_transfer_v2(
    context: &AssetTransferContextV2,
    pre_state: &AssetTransferStateV2,
    command: &AssetTransferCommandV2,
) -> AbiResultV2<AssetTransferResultV2> {
    context.validate()?;
    pre_state.validate()?;
    command.validate()?;
    let prepared = match prepare_transfer(context, pre_state, command)? {
        Ok(prepared) => prepared,
        Err(code) => return reject(code, pre_state),
    };
    let balances = match post_balances(pre_state, &command.asset, &prepared.deltas) {
        Ok(balances) => balances,
        Err(code) => return reject(code, pre_state),
    };
    accept_transfer(&prepared, balances)
}
