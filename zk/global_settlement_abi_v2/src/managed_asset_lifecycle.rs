//! Pure Rust mirror of the Python managed issue/self-burn V2 SHADOW leaf.
//!
//! The transition derives a candidate with deterministic effects and roots. It
//! performs no registry authentication, route mounting, proof verification,
//! external custody action, settlement, publication, or production admission.

use std::collections::BTreeMap;

use serde::Serialize;

use crate::asset_transfer_types::{AssetClassV2, ACCOUNT_CUSTODY_DOMAIN_V2};
use crate::canonical::{hash_global_v2, AbiErrorV2, AbiResultV2, RootV2, GLOBAL_SETTLEMENT_ABI_V2};
use crate::effects::{
    AssetConservationRowV2, EconomicEffectKindV2, EconomicEffectRowV2, GlobalEconomicEffectPlanV2,
    LaneIdV2, LaneWriteV2,
};
use crate::managed_asset_lifecycle_types::*;
use crate::proof::LaneModuleTransitionJournalV2;
use crate::state::{AssetSupplyV2, EconomicAmountV2};

fn reject(
    code: ManagedAssetLifecycleRejectCodeV2,
    pre_state: &ManagedAssetLifecycleStateV2,
) -> AbiResultV2<ManagedAssetLifecycleResultV2> {
    let root = pre_state.state_root()?;
    let rejected = ManagedAssetLifecycleRejectedV2 {
        code,
        pre_state_root: root.clone(),
        post_state_root: root,
        effects: GlobalEconomicEffectPlanV2::empty(),
    };
    rejected.validate()?;
    Ok(ManagedAssetLifecycleResultV2::Rejected(Box::new(rejected)))
}

struct PreparedLifecycleV2<'a> {
    context: &'a ManagedAssetLifecycleContextV2,
    pre_state: &'a ManagedAssetLifecycleStateV2,
    command: &'a ManagedAssetLifecycleCommandV2,
    is_issue: bool,
    signed_amount: i128,
}

fn expected_authorization_root<'a>(
    context: &ManagedAssetLifecycleContextV2,
    command: &ManagedAssetLifecycleCommandV2,
    policy: &'a ManagedAssetLifecyclePolicyV2,
    is_issue: bool,
) -> Result<&'a RootV2, ManagedAssetLifecycleRejectCodeV2> {
    let occurrence = context
        .occurrence
        .as_ref()
        .ok_or(ManagedAssetLifecycleRejectCodeV2::MISSING_OCCURRENCE)?;
    if is_issue {
        let root = policy
            .issue_authorization_root
            .as_ref()
            .ok_or(ManagedAssetLifecycleRejectCodeV2::ISSUE_DISABLED)?;
        if policy.issue_authority_subject.as_deref() != Some(occurrence.subject_id.as_str()) {
            return Err(ManagedAssetLifecycleRejectCodeV2::UNAUTHORIZED_SUBJECT);
        }
        return Ok(root);
    }
    let root = policy
        .burn_authorization_root
        .as_ref()
        .ok_or(ManagedAssetLifecycleRejectCodeV2::BURN_DISABLED)?;
    if occurrence.subject_id != command.account_owner {
        return Err(ManagedAssetLifecycleRejectCodeV2::UNAUTHORIZED_SUBJECT);
    }
    Ok(root)
}

fn signed_amount(
    amount_atoms: u128,
    is_issue: bool,
) -> Result<i128, ManagedAssetLifecycleRejectCodeV2> {
    if is_issue {
        return i128::try_from(amount_atoms)
            .map_err(|_| ManagedAssetLifecycleRejectCodeV2::EFFECT_DELTA_OVERFLOW);
    }
    const I128_MIN_MAGNITUDE: u128 = 1_u128 << 127;
    if amount_atoms == I128_MIN_MAGNITUDE {
        return Ok(i128::MIN);
    }
    i128::try_from(amount_atoms)
        .ok()
        .and_then(i128::checked_neg)
        .ok_or(ManagedAssetLifecycleRejectCodeV2::EFFECT_DELTA_OVERFLOW)
}

fn authorize<'a>(
    context: &'a ManagedAssetLifecycleContextV2,
    pre_state: &'a ManagedAssetLifecycleStateV2,
    command: &'a ManagedAssetLifecycleCommandV2,
    command_body_hash: &RootV2,
) -> Result<PreparedLifecycleV2<'a>, ManagedAssetLifecycleRejectCodeV2> {
    let occurrence = context
        .occurrence
        .as_ref()
        .ok_or(ManagedAssetLifecycleRejectCodeV2::MISSING_OCCURRENCE)?;
    if occurrence.pre_state_root != context.global_pre_state_root
        || !occurrence.consumed_object_ids.is_empty()
    {
        return Err(ManagedAssetLifecycleRejectCodeV2::OCCURRENCE_BINDING_MISMATCH);
    }
    if context.module_release_id != pre_state.module_release_id {
        return Err(ManagedAssetLifecycleRejectCodeV2::RELEASE_MISMATCH);
    }
    if command.command_kind != MANAGED_ASSET_ISSUE_COMMAND_KIND_V2
        && command.command_kind != MANAGED_ASSET_BURN_COMMAND_KIND_V2
    {
        return Err(ManagedAssetLifecycleRejectCodeV2::UNKNOWN_COMMAND);
    }
    if occurrence.command_kind != command.command_kind
        || occurrence.command_body_hash != *command_body_hash
    {
        return Err(ManagedAssetLifecycleRejectCodeV2::OCCURRENCE_COMMAND_MISMATCH);
    }
    let policy = pre_state
        .policies
        .iter()
        .find(|policy| policy.asset == command.asset)
        .ok_or(ManagedAssetLifecycleRejectCodeV2::UNKNOWN_ASSET)?;
    if !policy.enabled {
        return Err(ManagedAssetLifecycleRejectCodeV2::DISABLED_ASSET);
    }
    if command.asset_class != policy.asset_class {
        return Err(ManagedAssetLifecycleRejectCodeV2::ASSET_CLASS_MISMATCH);
    }
    // Both exact input constructors already require eight decimals. Retain the
    // branch and closed code so a future widening fails closed at this binding.
    if command.atom_decimals != policy.atom_decimals {
        return Err(ManagedAssetLifecycleRejectCodeV2::ASSET_DECIMALS_MISMATCH);
    }
    let (Some(policy_origin), Some(command_origin)) =
        (&policy.asset_origin_root, &command.asset_origin_root)
    else {
        return Err(ManagedAssetLifecycleRejectCodeV2::UNREGISTERED_ASSET);
    };
    if command_origin != policy_origin {
        return Err(ManagedAssetLifecycleRejectCodeV2::ASSET_ORIGIN_MISMATCH);
    }
    if policy.asset_class != AssetClassV2::RegisteredOrdinaryToken {
        return Err(ManagedAssetLifecycleRejectCodeV2::GENERIC_AUTHORITY_FORBIDDEN);
    }

    let is_issue = command.command_kind == MANAGED_ASSET_ISSUE_COMMAND_KIND_V2;
    let expected = expected_authorization_root(context, command, policy, is_issue)?;
    if occurrence.grant_root != *expected || command.authorization_root.as_ref() != Some(expected) {
        return Err(ManagedAssetLifecycleRejectCodeV2::AUTHORIZATION_ROOT_MISMATCH);
    }
    if command.amount_atoms == 0 {
        return Err(ManagedAssetLifecycleRejectCodeV2::ZERO_AMOUNT);
    }
    let signed_amount = signed_amount(command.amount_atoms, is_issue)?;
    Ok(PreparedLifecycleV2 {
        context,
        pre_state,
        command,
        is_issue,
        signed_amount,
    })
}

fn post_supplies(
    prepared: &PreparedLifecycleV2<'_>,
) -> Result<Vec<AssetSupplyV2>, ManagedAssetLifecycleRejectCodeV2> {
    let command = prepared.command;
    let current = prepared
        .pre_state
        .supplies
        .iter()
        .find(|row| row.asset == command.asset)
        .map(|row| row.amount_atoms)
        .ok_or(ManagedAssetLifecycleRejectCodeV2::UNKNOWN_ASSET)?;
    let post = if prepared.is_issue {
        current
            .checked_add(command.amount_atoms)
            .ok_or(ManagedAssetLifecycleRejectCodeV2::SUPPLY_OVERFLOW)?
    } else {
        current
            .checked_sub(command.amount_atoms)
            .ok_or(ManagedAssetLifecycleRejectCodeV2::INSUFFICIENT_BALANCE)?
    };
    Ok(prepared
        .pre_state
        .supplies
        .iter()
        .map(|row| AssetSupplyV2 {
            asset: row.asset.clone(),
            amount_atoms: if row.asset == command.asset {
                post
            } else {
                row.amount_atoms
            },
        })
        .collect())
}

fn apply_delta(current: u128, delta: i128) -> Result<u128, ManagedAssetLifecycleRejectCodeV2> {
    if delta < 0 {
        current
            .checked_sub(delta.unsigned_abs())
            .ok_or(ManagedAssetLifecycleRejectCodeV2::INSUFFICIENT_BALANCE)
    } else {
        current
            .checked_add(delta.unsigned_abs())
            .ok_or(ManagedAssetLifecycleRejectCodeV2::BALANCE_OVERFLOW)
    }
}

fn post_balances(
    prepared: &PreparedLifecycleV2<'_>,
) -> Result<Vec<EconomicAmountV2>, ManagedAssetLifecycleRejectCodeV2> {
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
        .map(|((asset, owner), amount_atoms)| EconomicAmountV2 {
            owner,
            asset,
            custody_domain: ACCOUNT_CUSTODY_DOMAIN_V2.to_owned(),
            amount_atoms,
        })
        .collect())
}

fn account_total(state: &ManagedAssetLifecycleStateV2, asset: &str) -> AbiResultV2<u128> {
    state
        .balances
        .iter()
        .filter(|row| row.asset == asset)
        .try_fold(0_u128, |total, row| {
            total
                .checked_add(row.amount_atoms)
                .ok_or(AbiErrorV2::Conservation(
                    "managed asset account total overflow",
                ))
        })
}

fn effect_plan(
    prepared: &PreparedLifecycleV2<'_>,
    post_state: &ManagedAssetLifecycleStateV2,
) -> AbiResultV2<GlobalEconomicEffectPlanV2> {
    let occurrence = prepared
        .context
        .occurrence
        .as_ref()
        .ok_or(AbiErrorV2::InvalidBinding(
            "prepared managed asset occurrence",
        ))?;
    let supply_kind = if prepared.is_issue {
        EconomicEffectKindV2::ISSUE
    } else {
        EconomicEffectKindV2::BURN
    };
    let (issue_atoms, burn_atoms) = if prepared.is_issue {
        (prepared.command.amount_atoms, 0)
    } else {
        (0, prepared.command.amount_atoms)
    };
    let mut rows = vec![
        EconomicEffectRowV2 {
            kind: EconomicEffectKindV2::ACCOUNT_MOVEMENT,
            principal: prepared.command.account_owner.clone(),
            asset: prepared.command.asset.clone(),
            custody_domain: ACCOUNT_CUSTODY_DOMAIN_V2.to_owned(),
            delta_atoms: prepared.signed_amount,
        },
        EconomicEffectRowV2 {
            kind: supply_kind,
            principal: prepared.command.account_owner.clone(),
            asset: prepared.command.asset.clone(),
            custody_domain: ACCOUNT_CUSTODY_DOMAIN_V2.to_owned(),
            delta_atoms: prepared.signed_amount,
        },
    ];
    rows.sort_by(|left, right| left.key().cmp(&right.key()));
    let effects = GlobalEconomicEffectPlanV2 {
        schema: GLOBAL_SETTLEMENT_ABI_V2.to_owned(),
        rows,
        asset_conservation: vec![AssetConservationRowV2 {
            asset: prepared.command.asset.clone(),
            owned_and_custodied_pre_atoms: account_total(
                prepared.pre_state,
                &prepared.command.asset,
            )?,
            owned_and_custodied_post_atoms: account_total(post_state, &prepared.command.asset)?,
            supply_pre_atoms: prepared.pre_state.supply_atoms(&prepared.command.asset)?,
            supply_post_atoms: post_state.supply_atoms(&prepared.command.asset)?,
            authorized_issue_atoms: issue_atoms,
            authorized_burn_atoms: burn_atoms,
        }],
        fee_conservation: Vec::new(),
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
struct ManagedAssetLifecycleReceiptBodyV2<'a> {
    context: &'a ManagedAssetLifecycleContextV2,
    command: &'a ManagedAssetLifecycleCommandV2,
    pre_state_root: &'a RootV2,
    post_state_root: &'a RootV2,
    effect_plan_root: &'a RootV2,
    private_port_root: &'a RootV2,
    terminal_obligations_root: &'a RootV2,
    oracle_occurrence_plan_root: &'a RootV2,
}

fn build_module_journal(
    prepared: &PreparedLifecycleV2<'_>,
    pre_root: RootV2,
    post_root: RootV2,
    effect_plan_root: RootV2,
) -> AbiResultV2<LaneModuleTransitionJournalV2> {
    let occurrence = prepared
        .context
        .occurrence
        .as_ref()
        .ok_or(AbiErrorV2::InvalidBinding(
            "prepared managed asset occurrence",
        ))?;
    let private_port_root = RootV2::zero();
    let terminal_obligations_root = RootV2::zero();
    let oracle_occurrence_plan_root = RootV2::zero();
    let receipt_root = hash_global_v2(
        "managed-asset-lifecycle-receipt-v2",
        &ManagedAssetLifecycleReceiptBodyV2 {
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

fn accept(
    prepared: &PreparedLifecycleV2<'_>,
    balances: Vec<EconomicAmountV2>,
    supplies: Vec<AssetSupplyV2>,
) -> AbiResultV2<ManagedAssetLifecycleResultV2> {
    let post_state = ManagedAssetLifecycleStateV2 {
        schema: MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V2.to_owned(),
        module_release_id: prepared.pre_state.module_release_id.clone(),
        policies: prepared.pre_state.policies.clone(),
        balances,
        supplies,
    };
    let pre_root = prepared.pre_state.state_root()?;
    let post_root = post_state.state_root()?;
    let effects = effect_plan(prepared, &post_state)?;
    let effect_plan_root = effects.effect_plan_root()?;
    let module_journal = build_module_journal(prepared, pre_root, post_root, effect_plan_root)?;
    let accepted = ManagedAssetLifecycleAcceptedV2 {
        post_state,
        effects,
        module_journal,
    };
    accepted.validate()?;
    Ok(ManagedAssetLifecycleResultV2::Accepted(Box::new(accepted)))
}

pub fn transition_managed_asset_lifecycle_v2(
    context: &ManagedAssetLifecycleContextV2,
    pre_state: &ManagedAssetLifecycleStateV2,
    command: &ManagedAssetLifecycleCommandV2,
) -> AbiResultV2<ManagedAssetLifecycleResultV2> {
    context.validate()?;
    pre_state.validate()?;
    command.validate()?;
    let command_body_hash = command.command_body_hash()?;
    let prepared = match authorize(context, pre_state, command, &command_body_hash) {
        Ok(prepared) => prepared,
        Err(code) => return reject(code, pre_state),
    };
    let supplies = match post_supplies(&prepared) {
        Ok(supplies) => supplies,
        Err(code) => return reject(code, pre_state),
    };
    let balances = match post_balances(&prepared) {
        Ok(balances) => balances,
        Err(code) => return reject(code, pre_state),
    };
    accept(&prepared, balances, supplies)
}
