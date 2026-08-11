use std::collections::{BTreeMap, BTreeSet};

use crate::asset_lane_projection::{
    empty_asset_lane_effects_v1, AssetLaneCompositionAcceptedV1, AssetLaneCompositionRejectedV1,
    AssetLaneCompositionResultV1, AssetLaneCoordinatorContextV1, AssetLaneCoordinatorRejectCodeV1,
    AssetLanePrivatePortV1, AssetLaneStateProjectionV1,
};
use crate::asset_transfer_types::ACCOUNT_CUSTODY_DOMAIN_V1;
use crate::canonical::{AbiResultV1, GLOBAL_SETTLEMENT_ABI_V1};
use crate::effects::{EconomicEffectKindV1, GlobalEconomicEffectPlanV1, LaneWriteV1};
use crate::proof::{LaneCompositionJournalV1, LaneModuleTransitionJournalV1};
use crate::release::LaneIdV1;

type HoldingKeyV1 = (String, String, String);

fn reject(
    code: AssetLaneCoordinatorRejectCodeV1,
    pre_state: &AssetLaneStateProjectionV1,
) -> AbiResultV1<AssetLaneCompositionResultV1> {
    let root = pre_state.state_root()?;
    let rejected = AssetLaneCompositionRejectedV1 {
        code,
        pre_lane_root: root.clone(),
        post_lane_root: root,
        effects: empty_asset_lane_effects_v1(),
    };
    rejected.validate()?;
    Ok(AssetLaneCompositionResultV1::Rejected(Box::new(rejected)))
}

fn holdings(state: &AssetLaneStateProjectionV1) -> BTreeMap<HoldingKeyV1, u128> {
    state
        .balances
        .iter()
        .chain(&state.custody)
        .map(|row| {
            (
                (
                    row.asset.clone(),
                    row.owner.clone(),
                    row.custody_domain.clone(),
                ),
                row.amount_atoms,
            )
        })
        .collect()
}

fn changed_assets(
    pre_state: &AssetLaneStateProjectionV1,
    post_state: &AssetLaneStateProjectionV1,
) -> BTreeSet<String> {
    let pre_holdings = holdings(pre_state);
    let post_holdings = holdings(post_state);
    let mut changed = pre_holdings
        .keys()
        .chain(post_holdings.keys())
        .filter(|key| pre_holdings.get(*key).unwrap_or(&0) != post_holdings.get(*key).unwrap_or(&0))
        .map(|key| key.0.clone())
        .collect::<BTreeSet<_>>();
    let pre_supply = pre_state
        .supplies
        .iter()
        .map(|row| (row.asset.clone(), row.amount_atoms))
        .collect::<BTreeMap<_, _>>();
    let post_supply = post_state
        .supplies
        .iter()
        .map(|row| (row.asset.clone(), row.amount_atoms))
        .collect::<BTreeMap<_, _>>();
    for asset in pre_supply.keys().chain(post_supply.keys()) {
        if pre_supply.get(asset).unwrap_or(&0) != post_supply.get(asset).unwrap_or(&0) {
            changed.insert(asset.clone());
        }
    }
    changed
}

fn expected_movement_deltas(
    pre_state: &AssetLaneStateProjectionV1,
    post_state: &AssetLaneStateProjectionV1,
) -> Option<BTreeMap<HoldingKeyV1, i128>> {
    let pre = holdings(pre_state);
    let post = holdings(post_state);
    let mut deltas = BTreeMap::new();
    for key in pre.keys().chain(post.keys()) {
        let pre_atoms = i128::try_from(*pre.get(key).unwrap_or(&0)).ok()?;
        let post_atoms = i128::try_from(*post.get(key).unwrap_or(&0)).ok()?;
        let delta = post_atoms.checked_sub(pre_atoms)?;
        if delta != 0 {
            deltas.insert(key.clone(), delta);
        }
    }
    Some(deltas)
}

fn effect_movement_deltas(
    effects: &GlobalEconomicEffectPlanV1,
) -> Option<BTreeMap<HoldingKeyV1, i128>> {
    let mut deltas = BTreeMap::new();
    for row in &effects.rows {
        if row.kind != EconomicEffectKindV1::ACCOUNT_MOVEMENT
            && row.kind != EconomicEffectKindV1::CUSTODY
        {
            continue;
        }
        if (row.kind == EconomicEffectKindV1::ACCOUNT_MOVEMENT
            && row.custody_domain != ACCOUNT_CUSTODY_DOMAIN_V1)
            || (row.kind == EconomicEffectKindV1::CUSTODY
                && row.custody_domain == ACCOUNT_CUSTODY_DOMAIN_V1)
        {
            return None;
        }
        let key = (
            row.asset.clone(),
            row.principal.clone(),
            row.custody_domain.clone(),
        );
        let delta = deltas
            .get(&key)
            .copied()
            .unwrap_or(0_i128)
            .checked_add(row.delta_atoms)?;
        if delta == 0 {
            deltas.remove(&key);
        } else {
            deltas.insert(key, delta);
        }
    }
    Some(deltas)
}

fn conservation_reject(
    pre_state: &AssetLaneStateProjectionV1,
    post_state: &AssetLaneStateProjectionV1,
    effects: &GlobalEconomicEffectPlanV1,
) -> AbiResultV1<Option<AssetLaneCoordinatorRejectCodeV1>> {
    let expected_assets = changed_assets(pre_state, post_state);
    let actual_assets = effects
        .asset_conservation
        .iter()
        .map(|row| row.asset.clone())
        .collect::<BTreeSet<_>>();
    if expected_assets != actual_assets {
        return Ok(Some(
            AssetLaneCoordinatorRejectCodeV1::CONSERVATION_COVERAGE_MISMATCH,
        ));
    }
    for row in &effects.asset_conservation {
        if row.owned_and_custodied_pre_atoms != pre_state.owned_and_custodied_atoms(&row.asset)?
            || row.owned_and_custodied_post_atoms
                != post_state.owned_and_custodied_atoms(&row.asset)?
            || row.supply_pre_atoms != pre_state.supply_atoms(&row.asset)?
            || row.supply_post_atoms != post_state.supply_atoms(&row.asset)?
        {
            return Ok(Some(
                AssetLaneCoordinatorRejectCodeV1::CONSERVATION_STATE_MISMATCH,
            ));
        }
    }
    if expected_movement_deltas(pre_state, post_state) != effect_movement_deltas(effects) {
        return Ok(Some(
            AssetLaneCoordinatorRejectCodeV1::STATE_EFFECT_MISMATCH,
        ));
    }
    Ok(None)
}

fn context_binding_reject(
    context: &AssetLaneCoordinatorContextV1,
    module_journal: &LaneModuleTransitionJournalV1,
) -> Option<AssetLaneCoordinatorRejectCodeV1> {
    if module_journal.chain_id != context.chain_id {
        return Some(AssetLaneCoordinatorRejectCodeV1::CHAIN_MISMATCH);
    }
    if module_journal.deployment_root != context.deployment_root {
        return Some(AssetLaneCoordinatorRejectCodeV1::DEPLOYMENT_MISMATCH);
    }
    if module_journal.profile_root != context.profile_root {
        return Some(AssetLaneCoordinatorRejectCodeV1::PROFILE_MISMATCH);
    }
    if module_journal.writer_epoch != context.writer_epoch {
        return Some(AssetLaneCoordinatorRejectCodeV1::WRITER_EPOCH_MISMATCH);
    }
    (module_journal.lane_id != LaneIdV1::ASSET_TRANSFER)
        .then_some(AssetLaneCoordinatorRejectCodeV1::WRONG_LANE)
}

fn release_port_binding_reject(
    context: &AssetLaneCoordinatorContextV1,
    module_journal: &LaneModuleTransitionJournalV1,
    private_port: &AssetLanePrivatePortV1,
) -> AbiResultV1<Option<AssetLaneCoordinatorRejectCodeV1>> {
    let compatibility = context
        .compatible_modules
        .iter()
        .find(|item| item.module_release_id == module_journal.module_release_id);
    let Some(compatibility) = compatibility else {
        return Ok(Some(
            AssetLaneCoordinatorRejectCodeV1::MODULE_NOT_REGISTERED,
        ));
    };
    if private_port.producer_module_schema != compatibility.module_schema {
        return Ok(Some(
            AssetLaneCoordinatorRejectCodeV1::MODULE_SCHEMA_MISMATCH,
        ));
    }
    if private_port.module_release_id != module_journal.module_release_id {
        return Ok(Some(
            AssetLaneCoordinatorRejectCodeV1::MODULE_RELEASE_MISMATCH,
        ));
    }
    if module_journal.command_occurrence_id != context.command_occurrence_id
        || private_port.command_occurrence_id != context.command_occurrence_id
    {
        return Ok(Some(AssetLaneCoordinatorRejectCodeV1::OCCURRENCE_MISMATCH));
    }
    if module_journal.private_port_root.is_zero() {
        return Ok(Some(AssetLaneCoordinatorRejectCodeV1::PRIVATE_PORT_UNBOUND));
    }
    Ok(
        (module_journal.private_port_root != private_port.port_root()?)
            .then_some(AssetLaneCoordinatorRejectCodeV1::PRIVATE_PORT_ROOT_MISMATCH),
    )
}

fn effect_port_binding_reject(
    context: &AssetLaneCoordinatorContextV1,
    module_journal: &LaneModuleTransitionJournalV1,
    private_port: &AssetLanePrivatePortV1,
    module_effects: &GlobalEconomicEffectPlanV1,
) -> AbiResultV1<Option<AssetLaneCoordinatorRejectCodeV1>> {
    let effect_root = module_effects.effect_plan_root()?;
    if module_journal.effect_plan_root != effect_root
        || private_port.module_effect_plan_root != effect_root
    {
        return Ok(Some(AssetLaneCoordinatorRejectCodeV1::EFFECT_PLAN_MISMATCH));
    }
    if module_journal.terminal_obligations_root != private_port.terminal_obligations_root {
        return Ok(Some(
            AssetLaneCoordinatorRejectCodeV1::TERMINAL_OBLIGATION_MISMATCH,
        ));
    }
    Ok([&private_port.pre_state, &private_port.post_state]
        .iter()
        .any(|state| {
            state.asset_policy_registry_root != context.asset_policy_registry_root
                || state.fee_policy_registry_root != context.fee_policy_registry_root
        })
        .then_some(AssetLaneCoordinatorRejectCodeV1::POLICY_ROOT_MISMATCH))
}

fn effect_shape_reject(
    context: &AssetLaneCoordinatorContextV1,
    module_journal: &LaneModuleTransitionJournalV1,
    module_effects: &GlobalEconomicEffectPlanV1,
) -> Option<AssetLaneCoordinatorRejectCodeV1> {
    if module_effects.occurrence_consumptions != vec![context.command_occurrence_id.clone()] {
        return Some(AssetLaneCoordinatorRejectCodeV1::OCCURRENCE_EFFECT_MISMATCH);
    }
    let expected_module_write = vec![LaneWriteV1 {
        lane_id: LaneIdV1::ASSET_TRANSFER,
        pre_root: module_journal.pre_lane_root.clone(),
        post_root: module_journal.post_lane_root.clone(),
    }];
    if module_effects.lane_writes != expected_module_write {
        return Some(AssetLaneCoordinatorRejectCodeV1::LANE_WRITE_SHAPE_MISMATCH);
    }
    if !module_effects.external_outbox_enqueue.is_empty() {
        return Some(AssetLaneCoordinatorRejectCodeV1::EXTERNAL_OUTBOX_FORBIDDEN);
    }
    let allowed_kinds = [
        EconomicEffectKindV1::ACCOUNT_MOVEMENT,
        EconomicEffectKindV1::ISSUE,
        EconomicEffectKindV1::BURN,
        EconomicEffectKindV1::CUSTODY,
        EconomicEffectKindV1::FEE_ALLOCATION,
    ];
    module_effects
        .rows
        .iter()
        .any(|row| !allowed_kinds.contains(&row.kind))
        .then_some(AssetLaneCoordinatorRejectCodeV1::EFFECT_KIND_FORBIDDEN)
}

fn normalize_effects(
    private_port: &AssetLanePrivatePortV1,
    module_effects: &GlobalEconomicEffectPlanV1,
) -> AbiResultV1<GlobalEconomicEffectPlanV1> {
    let normalized = GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: module_effects.rows.clone(),
        asset_conservation: module_effects.asset_conservation.clone(),
        fee_conservation: module_effects.fee_conservation.clone(),
        lane_writes: vec![LaneWriteV1 {
            lane_id: LaneIdV1::ASSET_TRANSFER,
            pre_root: private_port.pre_state.state_root()?,
            post_root: private_port.post_state.state_root()?,
        }],
        occurrence_consumptions: module_effects.occurrence_consumptions.clone(),
        external_outbox_enqueue: Vec::new(),
    };
    normalized.validate()?;
    Ok(normalized)
}

fn composition_journal(
    context: &AssetLaneCoordinatorContextV1,
    module_journal: &LaneModuleTransitionJournalV1,
    private_port: &AssetLanePrivatePortV1,
    normalized_effects: &GlobalEconomicEffectPlanV1,
) -> AbiResultV1<LaneCompositionJournalV1> {
    let journal = LaneCompositionJournalV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: context.chain_id.clone(),
        deployment_root: context.deployment_root.clone(),
        profile_root: context.profile_root.clone(),
        writer_epoch: context.writer_epoch,
        lane_id: LaneIdV1::ASSET_TRANSFER,
        coordinator_release_id: context.coordinator_release_id.clone(),
        command_occurrence_id: context.command_occurrence_id.clone(),
        ordered_module_journal_roots: vec![module_journal.journal_root()?],
        pre_lane_root: private_port.pre_state.state_root()?,
        post_lane_root: private_port.post_state.state_root()?,
        effect_plan_root: normalized_effects.effect_plan_root()?,
        terminal_obligations_root: private_port.terminal_obligations_root.clone(),
    };
    journal.validate()?;
    Ok(journal)
}

pub fn compose_asset_lane_single_v1(
    context: &AssetLaneCoordinatorContextV1,
    module_journal: &LaneModuleTransitionJournalV1,
    private_port: &AssetLanePrivatePortV1,
    module_effects: &GlobalEconomicEffectPlanV1,
) -> AbiResultV1<AssetLaneCompositionResultV1> {
    context.validate()?;
    module_journal.validate()?;
    private_port.validate()?;
    module_effects.validate()?;
    let pre_state = &private_port.pre_state;

    if let Some(code) = context_binding_reject(context, module_journal) {
        return reject(code, pre_state);
    }
    if let Some(code) = release_port_binding_reject(context, module_journal, private_port)? {
        return reject(code, pre_state);
    }
    if let Some(code) =
        effect_port_binding_reject(context, module_journal, private_port, module_effects)?
    {
        return reject(code, pre_state);
    }
    if let Some(code) = effect_shape_reject(context, module_journal, module_effects) {
        return reject(code, pre_state);
    }
    if let Some(code) = conservation_reject(pre_state, &private_port.post_state, module_effects)? {
        return reject(code, pre_state);
    }

    let normalized_effects = normalize_effects(private_port, module_effects)?;
    let lane_journal =
        composition_journal(context, module_journal, private_port, &normalized_effects)?;
    let accepted = AssetLaneCompositionAcceptedV1 {
        post_state: private_port.post_state.clone(),
        effects: normalized_effects,
        lane_journal,
    };
    accepted.validate()?;
    Ok(AssetLaneCompositionResultV1::Accepted(Box::new(accepted)))
}
