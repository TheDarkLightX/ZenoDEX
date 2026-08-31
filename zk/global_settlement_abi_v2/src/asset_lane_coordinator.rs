//! Alternative composition kernel for one V2 asset-lane leaf command.
//!
//! One transfer or managed-lifecycle command is dispatched internally. The
//! coordinator then rechecks the leaf candidate and rebinds it to one aggregate
//! ASSET_TRANSFER lane write. This SHADOW mirror performs no runtime mount,
//! RISC0 verification, settlement, release, migration, UI action, or production
//! admission.

use std::collections::BTreeSet;

use serde::Serialize;

use crate::asset_lane_coordinator_types::*;
use crate::asset_lane_state::{AssetLaneContextV2, AssetLaneStateV2, ASSET_LANE_STATE_SCHEMA_V2};
use crate::asset_transfer::transition_asset_transfer_v2;
use crate::asset_transfer_types::{AssetTransferAcceptedV2, AssetTransferResultV2};
use crate::canonical::{hash_global_v2, AbiResultV2, RootV2, GLOBAL_SETTLEMENT_ABI_V2};
use crate::effects::{GlobalEconomicEffectPlanV2, LaneIdV2, LaneWriteV2};
use crate::managed_asset_lifecycle::transition_managed_asset_lifecycle_v2;
use crate::managed_asset_lifecycle_types::{
    ManagedAssetLifecycleAcceptedV2, ManagedAssetLifecycleResultV2,
};
use crate::proof::LaneModuleTransitionJournalV2;

enum LeafAcceptedV2 {
    Transfer(Box<AssetTransferAcceptedV2>),
    ManagedLifecycle(Box<ManagedAssetLifecycleAcceptedV2>),
}

impl LeafAcceptedV2 {
    fn validate(&self) -> AbiResultV2<()> {
        match self {
            Self::Transfer(candidate) => candidate.validate(),
            Self::ManagedLifecycle(candidate) => candidate.validate(),
        }
    }

    fn effects(&self) -> &GlobalEconomicEffectPlanV2 {
        match self {
            Self::Transfer(candidate) => &candidate.effects,
            Self::ManagedLifecycle(candidate) => &candidate.effects,
        }
    }

    fn journal(&self) -> &LaneModuleTransitionJournalV2 {
        match self {
            Self::Transfer(candidate) => &candidate.module_journal,
            Self::ManagedLifecycle(candidate) => &candidate.module_journal,
        }
    }
}

fn reject(
    state: &AssetLaneStateV2,
    route: AssetLaneRouteV2,
    code: AssetLaneRejectCodeV2,
) -> AbiResultV2<AssetLaneResultV2> {
    let rejected = AssetLaneRejectedV2::new(route, code, state.state_root()?)?;
    Ok(AssetLaneResultV2::Rejected(Box::new(rejected)))
}

fn expected_leaf_pre_root(
    state: &AssetLaneStateV2,
    candidate: &LeafAcceptedV2,
) -> AbiResultV2<RootV2> {
    match candidate {
        LeafAcceptedV2::Transfer(_) => state.transfer_leaf_state().state_root(),
        LeafAcceptedV2::ManagedLifecycle(_) => state.managed_leaf_state().state_root(),
    }
}

fn candidate_binding_holds(
    context: &AssetLaneContextV2,
    state: &AssetLaneStateV2,
    candidate: &LeafAcceptedV2,
) -> bool {
    if candidate.validate().is_err() {
        return false;
    }
    let Some(occurrence) = &context.occurrence else {
        return false;
    };
    let Ok(occurrence_id) = occurrence.occurrence_id() else {
        return false;
    };
    let Ok(expected_pre) = expected_leaf_pre_root(state, candidate) else {
        return false;
    };
    let journal = candidate.journal();
    let effects = candidate.effects();
    journal.chain_id == occurrence.chain_id
        && journal.deployment_root == occurrence.deployment_root
        && journal.profile_root == occurrence.profile_root
        && journal.writer_epoch == context.writer_epoch
        && journal.module_release_id == state.module_release_id
        && journal.command_occurrence_id == occurrence_id
        && journal.pre_lane_root == expected_pre
        && effects.occurrence_consumptions == vec![occurrence_id]
        && effects.external_outbox_enqueue.is_empty()
        && journal.private_port_root.is_zero()
        && journal.terminal_obligations_root.is_zero()
        && journal.oracle_occurrence_plan_root.is_zero()
}

fn aggregate_post_state(
    pre_state: &AssetLaneStateV2,
    candidate: &LeafAcceptedV2,
) -> AssetLaneStateV2 {
    let (mut balances, mut supplies) = match candidate {
        LeafAcceptedV2::Transfer(candidate) => (
            candidate.post_state.balances.clone(),
            candidate.post_state.supplies.clone(),
        ),
        LeafAcceptedV2::ManagedLifecycle(candidate) => {
            let managed_assets = pre_state
                .managed_policies
                .iter()
                .map(|policy| policy.asset.as_str())
                .collect::<BTreeSet<_>>();
            let mut balances = pre_state
                .balances
                .iter()
                .filter(|row| !managed_assets.contains(row.asset.as_str()))
                .cloned()
                .collect::<Vec<_>>();
            balances.extend(candidate.post_state.balances.iter().cloned());
            let mut supplies = pre_state
                .supplies
                .iter()
                .filter(|row| !managed_assets.contains(row.asset.as_str()))
                .cloned()
                .collect::<Vec<_>>();
            supplies.extend(candidate.post_state.supplies.iter().cloned());
            (balances, supplies)
        }
    };
    balances.sort_by(|left, right| left.key().cmp(&right.key()));
    supplies.sort_by(|left, right| left.asset.cmp(&right.asset));
    AssetLaneStateV2 {
        schema: ASSET_LANE_STATE_SCHEMA_V2.to_owned(),
        module_release_id: pre_state.module_release_id.clone(),
        origin_registry: pre_state.origin_registry.clone(),
        transfer_policies: pre_state.transfer_policies.clone(),
        managed_policies: pre_state.managed_policies.clone(),
        balances,
        supplies,
    }
}

fn projection_holds(
    route: AssetLaneRouteV2,
    post_state: &AssetLaneStateV2,
    candidate: &LeafAcceptedV2,
) -> bool {
    let projected_root = match route {
        AssetLaneRouteV2::TRANSFER => post_state.transfer_leaf_state().state_root(),
        AssetLaneRouteV2::MANAGED_LIFECYCLE => post_state.managed_leaf_state().state_root(),
        AssetLaneRouteV2::COORDINATOR => return false,
    };
    let candidate_root = match candidate {
        LeafAcceptedV2::Transfer(candidate) => candidate.post_state.state_root(),
        LeafAcceptedV2::ManagedLifecycle(candidate) => candidate.post_state.state_root(),
    };
    let (Ok(projected_root), Ok(candidate_root)) = (projected_root, candidate_root) else {
        return false;
    };
    if projected_root != candidate_root {
        return false;
    }
    let conservation = &candidate.effects().asset_conservation;
    if conservation.len() != 1 {
        return false;
    }
    let row = &conservation[0];
    let Ok(supply_atoms) = post_state.supply_atoms(&row.asset) else {
        return false;
    };
    row.owned_and_custodied_post_atoms == supply_atoms && row.supply_post_atoms == supply_atoms
}

#[derive(Serialize)]
struct AssetLaneCoordinatorReceiptBodyV2<'a> {
    route: AssetLaneRouteV2,
    source_leaf_journal_root: &'a RootV2,
    source_leaf_receipt_root: &'a RootV2,
    pre_lane_root: &'a RootV2,
    post_lane_root: &'a RootV2,
    effect_plan_root: &'a RootV2,
    private_port_root: &'a RootV2,
    terminal_obligations_root: &'a RootV2,
    oracle_occurrence_plan_root: &'a RootV2,
}

fn rebound_effects(
    pre_root: &RootV2,
    post_root: &RootV2,
    candidate: &LeafAcceptedV2,
) -> AbiResultV2<GlobalEconomicEffectPlanV2> {
    let source_effects = candidate.effects();
    let effects = GlobalEconomicEffectPlanV2 {
        schema: GLOBAL_SETTLEMENT_ABI_V2.to_owned(),
        rows: source_effects.rows.clone(),
        asset_conservation: source_effects.asset_conservation.clone(),
        fee_conservation: source_effects.fee_conservation.clone(),
        lane_writes: vec![LaneWriteV2 {
            lane_id: LaneIdV2::ASSET_TRANSFER,
            pre_root: pre_root.clone(),
            post_root: post_root.clone(),
        }],
        occurrence_consumptions: source_effects.occurrence_consumptions.clone(),
        external_outbox_enqueue: Vec::new(),
    };
    effects.validate()?;
    Ok(effects)
}

fn coordinator_receipt_root(body: &AssetLaneCoordinatorReceiptBodyV2<'_>) -> AbiResultV2<RootV2> {
    hash_global_v2("asset-lane-coordinator-receipt-v2", body)
}

struct CoordinatorJournalRootsV2 {
    pre_lane_root: RootV2,
    post_lane_root: RootV2,
    effect_plan_root: RootV2,
    receipt_root: RootV2,
}

fn coordinator_journal(
    source: &LaneModuleTransitionJournalV2,
    roots: CoordinatorJournalRootsV2,
) -> LaneModuleTransitionJournalV2 {
    LaneModuleTransitionJournalV2 {
        schema: GLOBAL_SETTLEMENT_ABI_V2.to_owned(),
        chain_id: source.chain_id.clone(),
        deployment_root: source.deployment_root.clone(),
        profile_root: source.profile_root.clone(),
        writer_epoch: source.writer_epoch,
        lane_id: LaneIdV2::ASSET_TRANSFER,
        module_release_id: source.module_release_id.clone(),
        command_occurrence_id: source.command_occurrence_id.clone(),
        pre_lane_root: roots.pre_lane_root,
        post_lane_root: roots.post_lane_root,
        effect_plan_root: roots.effect_plan_root,
        private_port_root: RootV2::zero(),
        receipt_root: roots.receipt_root,
        terminal_obligations_root: RootV2::zero(),
        oracle_occurrence_plan_root: RootV2::zero(),
    }
}

fn rebind_candidate(
    route: AssetLaneRouteV2,
    pre_state: &AssetLaneStateV2,
    post_state: AssetLaneStateV2,
    candidate: &LeafAcceptedV2,
) -> AbiResultV2<AssetLaneAcceptedV2> {
    let source_journal = candidate.journal();
    let source_leaf_journal_root = source_journal.journal_root()?;
    let pre_root = pre_state.state_root()?;
    let post_root = post_state.state_root()?;
    let effects = rebound_effects(&pre_root, &post_root, candidate)?;
    let effect_plan_root = effects.effect_plan_root()?;
    let zero_root = RootV2::zero();
    let receipt_root = coordinator_receipt_root(&AssetLaneCoordinatorReceiptBodyV2 {
        route,
        source_leaf_journal_root: &source_leaf_journal_root,
        source_leaf_receipt_root: &source_journal.receipt_root,
        pre_lane_root: &pre_root,
        post_lane_root: &post_root,
        effect_plan_root: &effect_plan_root,
        private_port_root: &zero_root,
        terminal_obligations_root: &zero_root,
        oracle_occurrence_plan_root: &zero_root,
    })?;
    let journal = coordinator_journal(
        source_journal,
        CoordinatorJournalRootsV2 {
            pre_lane_root: pre_root,
            post_lane_root: post_root,
            effect_plan_root,
            receipt_root,
        },
    );
    AssetLaneAcceptedV2::new(
        route,
        source_leaf_journal_root,
        post_state,
        effects,
        journal,
    )
}

fn compose_candidate(
    context: &AssetLaneContextV2,
    pre_state: &AssetLaneStateV2,
    route: AssetLaneRouteV2,
    candidate: LeafAcceptedV2,
) -> AbiResultV2<AssetLaneResultV2> {
    if !candidate_binding_holds(context, pre_state, &candidate) {
        return reject(
            pre_state,
            route,
            AssetLaneRejectCodeV2::Coordinator(
                AssetLaneCoordinatorRejectCodeV2::CANDIDATE_BINDING_MISMATCH,
            ),
        );
    }
    let post_state = aggregate_post_state(pre_state, &candidate);
    if !projection_holds(route, &post_state, &candidate) {
        return reject(
            pre_state,
            route,
            AssetLaneRejectCodeV2::Coordinator(
                AssetLaneCoordinatorRejectCodeV2::PROJECTION_MISMATCH,
            ),
        );
    }
    Ok(AssetLaneResultV2::Accepted(Box::new(rebind_candidate(
        route, pre_state, post_state, &candidate,
    )?)))
}

pub fn transition_asset_lane_v2(
    context: &AssetLaneContextV2,
    pre_state: &AssetLaneStateV2,
    command: &AssetLaneCommandV2,
) -> AbiResultV2<AssetLaneResultV2> {
    context.validate()?;
    pre_state.validate()?;
    command.validate()?;
    let route = command.route();
    if !pre_state.policy_origin_bindings_hold() {
        return reject(
            pre_state,
            AssetLaneRouteV2::COORDINATOR,
            AssetLaneRejectCodeV2::Coordinator(
                AssetLaneCoordinatorRejectCodeV2::REGISTRY_BINDING_MISMATCH,
            ),
        );
    }
    let candidate = match command {
        AssetLaneCommandV2::Transfer(command) => {
            match transition_asset_transfer_v2(
                &context.transfer_context(),
                &pre_state.transfer_leaf_state(),
                command,
            )? {
                AssetTransferResultV2::Accepted(candidate) => LeafAcceptedV2::Transfer(candidate),
                AssetTransferResultV2::Rejected(rejected) => {
                    return reject(
                        pre_state,
                        route,
                        AssetLaneRejectCodeV2::Transfer(rejected.code),
                    )
                }
            }
        }
        AssetLaneCommandV2::ManagedLifecycle(command) => {
            match transition_managed_asset_lifecycle_v2(
                &context.managed_context(),
                &pre_state.managed_leaf_state(),
                command,
            )? {
                ManagedAssetLifecycleResultV2::Accepted(candidate) => {
                    LeafAcceptedV2::ManagedLifecycle(candidate)
                }
                ManagedAssetLifecycleResultV2::Rejected(rejected) => {
                    return reject(
                        pre_state,
                        route,
                        AssetLaneRejectCodeV2::ManagedLifecycle(rejected.code),
                    )
                }
            }
        }
    };
    compose_candidate(context, pre_state, route, candidate)
}

#[cfg(test)]
#[path = "asset_lane_coordinator_tests.rs"]
mod tests;
