use std::collections::BTreeMap;

use serde::Serialize;

use crate::asset_transfer_types::ACCOUNT_CUSTODY_DOMAIN_V1;
use crate::canonical::{
    hash_global_v1, AbiErrorV1, AbiResultV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1, ZERO_ROOT_V1,
};
use crate::effects::{
    AssetConservationRowV1, EconomicEffectKindV1, EconomicEffectRowV1, GlobalEconomicEffectPlanV1,
    LaneWriteV1,
};
use crate::managed_asset_lifecycle_types::*;
use crate::proof::LaneModuleTransitionJournalV1;
use crate::release::LaneIdV1;
use crate::state::{AssetSupplyV1, EconomicAmountV1};

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
    code: ManagedAssetLifecycleRejectCodeV1,
    pre_state: &ManagedAssetLifecycleStateV1,
) -> AbiResultV1<ManagedAssetLifecycleResultV1> {
    let root = pre_state.state_root()?;
    Ok(ManagedAssetLifecycleResultV1::Rejected(Box::new(
        ManagedAssetLifecycleRejectedV1 {
            code,
            pre_state_root: root.clone(),
            post_state_root: root,
            effects: empty_effects(),
        },
    )))
}

struct PreparedLifecycleV1<'a> {
    context: &'a ManagedAssetLifecycleContextV1,
    pre_state: &'a ManagedAssetLifecycleStateV1,
    command: &'a ManagedAssetLifecycleCommandV1,
    is_issue: bool,
    signed_amount: i128,
}

fn expected_grant<'a>(
    context: &ManagedAssetLifecycleContextV1,
    command: &ManagedAssetLifecycleCommandV1,
    policy: &'a ManagedAssetLifecyclePolicyV1,
    is_issue: bool,
) -> Result<&'a RootV1, ManagedAssetLifecycleRejectCodeV1> {
    if is_issue {
        let root = policy
            .issue_policy_root
            .as_ref()
            .ok_or(ManagedAssetLifecycleRejectCodeV1::ISSUE_DISABLED)?;
        if policy.issue_authority_subject.as_deref() != Some(context.subject_id.as_str()) {
            return Err(ManagedAssetLifecycleRejectCodeV1::UNAUTHORIZED_SUBJECT);
        }
        return Ok(root);
    }
    let root = policy
        .burn_policy_root
        .as_ref()
        .ok_or(ManagedAssetLifecycleRejectCodeV1::BURN_DISABLED)?;
    if context.subject_id != command.account_owner {
        return Err(ManagedAssetLifecycleRejectCodeV1::UNAUTHORIZED_SUBJECT);
    }
    Ok(root)
}

fn authorize<'a>(
    context: &'a ManagedAssetLifecycleContextV1,
    pre_state: &'a ManagedAssetLifecycleStateV1,
    command: &'a ManagedAssetLifecycleCommandV1,
) -> Result<PreparedLifecycleV1<'a>, ManagedAssetLifecycleRejectCodeV1> {
    if context.module_release_id != pre_state.module_release_id {
        return Err(ManagedAssetLifecycleRejectCodeV1::RELEASE_MISMATCH);
    }
    if command.command_kind != MANAGED_ASSET_ISSUE_COMMAND_KIND_V1
        && command.command_kind != MANAGED_ASSET_BURN_COMMAND_KIND_V1
    {
        return Err(ManagedAssetLifecycleRejectCodeV1::UNKNOWN_COMMAND);
    }
    let policy = pre_state
        .policies
        .iter()
        .find(|policy| policy.asset == command.asset)
        .ok_or(ManagedAssetLifecycleRejectCodeV1::UNKNOWN_ASSET)?;
    if !policy.enabled {
        return Err(ManagedAssetLifecycleRejectCodeV1::DISABLED_ASSET);
    }
    if policy.asset_class != ManagedAssetClassV1::REGISTERED_ORDINARY_TOKEN {
        return Err(ManagedAssetLifecycleRejectCodeV1::GENERIC_AUTHORITY_FORBIDDEN);
    }

    let is_issue = command.command_kind == MANAGED_ASSET_ISSUE_COMMAND_KIND_V1;
    let expected_grant = expected_grant(context, command, policy, is_issue)?;
    if &context.grant_root != expected_grant {
        return Err(ManagedAssetLifecycleRejectCodeV1::AUTHORITY_PROFILE_MISMATCH);
    }
    if command.amount_atoms == 0 {
        return Err(ManagedAssetLifecycleRejectCodeV1::ZERO_AMOUNT);
    }
    let amount = i128::try_from(command.amount_atoms)
        .map_err(|_| ManagedAssetLifecycleRejectCodeV1::EFFECT_DELTA_OVERFLOW)?;
    let signed_amount = if is_issue { amount } else { -amount };
    Ok(PreparedLifecycleV1 {
        context,
        pre_state,
        command,
        is_issue,
        signed_amount,
    })
}

fn post_supplies(
    prepared: &PreparedLifecycleV1<'_>,
) -> Result<Vec<AssetSupplyV1>, ManagedAssetLifecycleRejectCodeV1> {
    let command = prepared.command;
    let pre_supply = prepared
        .pre_state
        .supplies
        .iter()
        .find(|row| row.asset == command.asset)
        .map(|row| row.amount_atoms)
        .ok_or(ManagedAssetLifecycleRejectCodeV1::UNKNOWN_ASSET)?;
    let post_supply = if prepared.is_issue {
        pre_supply
            .checked_add(command.amount_atoms)
            .ok_or(ManagedAssetLifecycleRejectCodeV1::SUPPLY_OVERFLOW)?
    } else {
        pre_supply
            .checked_sub(command.amount_atoms)
            .ok_or(ManagedAssetLifecycleRejectCodeV1::INSUFFICIENT_BALANCE)?
    };
    Ok(prepared
        .pre_state
        .supplies
        .iter()
        .map(|row| AssetSupplyV1 {
            asset: row.asset.clone(),
            amount_atoms: if row.asset == command.asset {
                post_supply
            } else {
                row.amount_atoms
            },
        })
        .collect())
}

fn apply_delta(current: u128, delta: i128) -> Result<u128, ManagedAssetLifecycleRejectCodeV1> {
    if delta < 0 {
        current
            .checked_sub(delta.unsigned_abs())
            .ok_or(ManagedAssetLifecycleRejectCodeV1::INSUFFICIENT_BALANCE)
    } else {
        current
            .checked_add(delta.unsigned_abs())
            .ok_or(ManagedAssetLifecycleRejectCodeV1::BALANCE_OVERFLOW)
    }
}

fn post_balances(
    prepared: &PreparedLifecycleV1<'_>,
) -> Result<Vec<EconomicAmountV1>, ManagedAssetLifecycleRejectCodeV1> {
    let command = prepared.command;
    let mut values = prepared
        .pre_state
        .balances
        .iter()
        .map(|row| ((row.asset.clone(), row.owner.clone()), row.amount_atoms))
        .collect::<BTreeMap<_, _>>();
    let key = (command.asset.clone(), command.account_owner.clone());
    let post = apply_delta(
        values.get(&key).copied().unwrap_or(0),
        prepared.signed_amount,
    )?;
    if post == 0 {
        values.remove(&key);
    } else {
        values.insert(key, post);
    }
    Ok(values
        .into_iter()
        .map(|((asset, owner), amount_atoms)| EconomicAmountV1 {
            owner,
            asset,
            custody_domain: ACCOUNT_CUSTODY_DOMAIN_V1.to_owned(),
            amount_atoms,
        })
        .collect())
}

fn account_total(state: &ManagedAssetLifecycleStateV1, asset: &str) -> AbiResultV1<u128> {
    state
        .balances
        .iter()
        .filter(|row| row.asset == asset)
        .try_fold(0_u128, |total, row| {
            total
                .checked_add(row.amount_atoms)
                .ok_or(AbiErrorV1::Conservation(
                    "managed asset account total overflow",
                ))
        })
}

fn effect_plan(
    prepared: &PreparedLifecycleV1<'_>,
    post_state: &ManagedAssetLifecycleStateV1,
) -> AbiResultV1<GlobalEconomicEffectPlanV1> {
    let context = prepared.context;
    let pre_state = prepared.pre_state;
    let command = prepared.command;
    let supply_kind = if prepared.is_issue {
        EconomicEffectKindV1::ISSUE
    } else {
        EconomicEffectKindV1::BURN
    };
    let (issue_atoms, burn_atoms) = if prepared.is_issue {
        (command.amount_atoms, 0)
    } else {
        (0, command.amount_atoms)
    };
    Ok(GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: vec![
            EconomicEffectRowV1 {
                kind: EconomicEffectKindV1::ACCOUNT_MOVEMENT,
                principal: command.account_owner.clone(),
                asset: command.asset.clone(),
                custody_domain: ACCOUNT_CUSTODY_DOMAIN_V1.to_owned(),
                delta_atoms: prepared.signed_amount,
            },
            EconomicEffectRowV1 {
                kind: supply_kind,
                principal: command.account_owner.clone(),
                asset: command.asset.clone(),
                custody_domain: ACCOUNT_CUSTODY_DOMAIN_V1.to_owned(),
                delta_atoms: prepared.signed_amount,
            },
        ],
        asset_conservation: vec![AssetConservationRowV1 {
            asset: command.asset.clone(),
            owned_and_custodied_pre_atoms: account_total(pre_state, &command.asset)?,
            owned_and_custodied_post_atoms: account_total(post_state, &command.asset)?,
            supply_pre_atoms: pre_state.supply_atoms(&command.asset)?,
            supply_post_atoms: post_state.supply_atoms(&command.asset)?,
            authorized_issue_atoms: issue_atoms,
            authorized_burn_atoms: burn_atoms,
        }],
        fee_conservation: Vec::new(),
        lane_writes: vec![LaneWriteV1 {
            lane_id: LaneIdV1::ASSET_TRANSFER,
            pre_root: pre_state.state_root()?,
            post_root: post_state.state_root()?,
        }],
        occurrence_consumptions: vec![context.command_occurrence_id.clone()],
        external_outbox_enqueue: Vec::new(),
    })
}

#[derive(Serialize)]
struct ManagedAssetLifecycleReceiptBodyV1<'a> {
    context: &'a ManagedAssetLifecycleContextV1,
    command: &'a ManagedAssetLifecycleCommandV1,
    pre_state_root: &'a RootV1,
    post_state_root: &'a RootV1,
    effect_plan_root: &'a RootV1,
    private_port_root: &'a RootV1,
    terminal_obligations_root: &'a RootV1,
}

fn accept(
    prepared: &PreparedLifecycleV1<'_>,
    balances: Vec<EconomicAmountV1>,
    supplies: Vec<AssetSupplyV1>,
) -> AbiResultV1<ManagedAssetLifecycleResultV1> {
    let context = prepared.context;
    let pre_state = prepared.pre_state;
    let command = prepared.command;
    let post_state = ManagedAssetLifecycleStateV1 {
        schema: MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1.to_owned(),
        module_release_id: pre_state.module_release_id.clone(),
        policies: pre_state.policies.clone(),
        balances,
        supplies,
    };
    let pre_root = pre_state.state_root()?;
    let post_root = post_state.state_root()?;
    let effects = effect_plan(prepared, &post_state)?;
    let effect_root = effects.effect_plan_root()?;
    let private_port_root = RootV1::parse(ZERO_ROOT_V1, "empty private port root", true)?;
    let terminal_obligations_root =
        RootV1::parse(ZERO_ROOT_V1, "empty terminal obligations root", true)?;
    let receipt_root = hash_global_v1(
        "managed-asset-lifecycle-receipt-v1",
        &ManagedAssetLifecycleReceiptBodyV1 {
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
    let accepted = ManagedAssetLifecycleAcceptedV1 {
        post_state,
        effects,
        module_journal,
    };
    accepted.validate()?;
    Ok(ManagedAssetLifecycleResultV1::Accepted(Box::new(accepted)))
}

pub fn transition_managed_asset_lifecycle_v1(
    context: &ManagedAssetLifecycleContextV1,
    pre_state: &ManagedAssetLifecycleStateV1,
    command: &ManagedAssetLifecycleCommandV1,
) -> AbiResultV1<ManagedAssetLifecycleResultV1> {
    context.validate()?;
    pre_state.validate()?;
    command.validate()?;
    let prepared = match authorize(context, pre_state, command) {
        Ok(value) => value,
        Err(code) => return reject(code, pre_state),
    };
    let supplies = match post_supplies(&prepared) {
        Ok(value) => value,
        Err(code) => return reject(code, pre_state),
    };
    let balances = match post_balances(&prepared) {
        Ok(value) => value,
        Err(code) => return reject(code, pre_state),
    };
    accept(&prepared, balances, supplies)
}
