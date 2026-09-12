//! Custody-complete coordinator for the V2 ASSET_TRANSFER lane successor.
//!
//! Unchanged transfer and managed-lifecycle leaves propose account-state
//! transitions. This coordinator rechecks their source bindings, reconstructs
//! the custody-complete state, and independently replaces account-only
//! conservation totals with complete physical totals. Returned values remain
//! SHADOW evidence and grant no RISC0, settlement, release, or publication
//! authority.

use std::collections::BTreeSet;

use serde::Serialize;

use crate::asset_lane_coordinator_types::{
    AssetLaneCommandV2, AssetLaneCoordinatorRejectCodeV2, AssetLaneRejectCodeV2,
    AssetLaneRejectedV2, AssetLaneRouteV2,
};
use crate::asset_lane_custody_state::{
    AssetLaneCustodyStateV2, ASSET_LANE_CUSTODY_STATE_SCHEMA_V2,
};
use crate::asset_lane_state::{AssetLaneContextV2, ASSET_LANE_PROFILE_AUTHENTICATION_V2};
use crate::asset_transfer::transition_asset_transfer_v2;
use crate::asset_transfer_types::{
    AssetTransferAcceptedV2, AssetTransferResultV2, AssetTransferStateV2,
    ASSET_LANE_PRODUCTION_AUTHORITY_V2,
};
use crate::canonical::{hash_global_v2, AbiErrorV2, AbiResultV2, RootV2, GLOBAL_SETTLEMENT_ABI_V2};
use crate::effects::{AssetConservationRowV2, GlobalEconomicEffectPlanV2, LaneIdV2, LaneWriteV2};
use crate::managed_asset_lifecycle::transition_managed_asset_lifecycle_v2;
use crate::managed_asset_lifecycle_types::{
    ManagedAssetLifecycleAcceptedV2, ManagedAssetLifecycleResultV2,
};
use crate::proof::LaneModuleTransitionJournalV2;

const ASSET_LANE_CUSTODY_COORDINATOR_RECEIPT_DOMAIN_V2: &str =
    "asset-lane-custody-coordinator-receipt-v2";

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssetLaneCustodyAcceptedV2 {
    route: AssetLaneRouteV2,
    source_leaf_journal_root: RootV2,
    source_leaf_receipt_root: RootV2,
    post_state: AssetLaneCustodyStateV2,
    effects: GlobalEconomicEffectPlanV2,
    module_journal: LaneModuleTransitionJournalV2,
}

impl AssetLaneCustodyAcceptedV2 {
    fn new(
        route: AssetLaneRouteV2,
        source_leaf_journal_root: RootV2,
        source_leaf_receipt_root: RootV2,
        post_state: AssetLaneCustodyStateV2,
        effects: GlobalEconomicEffectPlanV2,
        module_journal: LaneModuleTransitionJournalV2,
    ) -> AbiResultV2<Self> {
        let accepted = Self {
            route,
            source_leaf_journal_root,
            source_leaf_receipt_root,
            post_state,
            effects,
            module_journal,
        };
        accepted.validate()?;
        Ok(accepted)
    }

    pub fn validate(&self) -> AbiResultV2<()> {
        if self.route == AssetLaneRouteV2::COORDINATOR {
            return Err(AbiErrorV2::InvalidBinding(
                "asset lane custody accepted route",
            ));
        }
        self.source_leaf_journal_root
            .validate("asset lane custody source leaf journal", false)?;
        self.source_leaf_receipt_root
            .validate("asset lane custody source leaf receipt", false)?;
        self.post_state.validate()?;
        self.effects.validate()?;
        self.module_journal.validate()?;

        let post_root = self.post_state.state_root()?;
        let effect_root = self.effects.effect_plan_root()?;
        let expected_write = LaneWriteV2 {
            lane_id: LaneIdV2::ASSET_TRANSFER,
            pre_root: self.module_journal.pre_lane_root.clone(),
            post_root: post_root.clone(),
        };
        if self.module_journal.lane_id != LaneIdV2::ASSET_TRANSFER
            || self.module_journal.post_lane_root != post_root
            || self.module_journal.module_release_id != *self.post_state.module_release_id()
            || self.effects.lane_writes != vec![expected_write]
            || self.module_journal.effect_plan_root != effect_root
            || self.effects.occurrence_consumptions
                != vec![self.module_journal.command_occurrence_id.clone()]
            || !self.effects.external_outbox_enqueue.is_empty()
            || !self.module_journal.private_port_root.is_zero()
            || !self.module_journal.terminal_obligations_root.is_zero()
            || !self.module_journal.oracle_occurrence_plan_root.is_zero()
            || !self.post_state.policy_origin_bindings_hold()
        {
            return Err(AbiErrorV2::InvalidBinding(
                "asset lane custody accepted bindings",
            ));
        }

        let zero_root = RootV2::zero();
        let expected_receipt =
            custody_coordinator_receipt_root(&AssetLaneCustodyCoordinatorReceiptBodyV2 {
                route: self.route,
                source_leaf_journal_root: &self.source_leaf_journal_root,
                source_leaf_receipt_root: &self.source_leaf_receipt_root,
                pre_lane_root: &self.module_journal.pre_lane_root,
                post_lane_root: &self.module_journal.post_lane_root,
                effect_plan_root: &self.module_journal.effect_plan_root,
                private_port_root: &zero_root,
                terminal_obligations_root: &zero_root,
                oracle_occurrence_plan_root: &zero_root,
            })?;
        if self.module_journal.receipt_root != expected_receipt {
            return Err(AbiErrorV2::InvalidBinding(
                "asset lane custody receipt binding",
            ));
        }
        Ok(())
    }

    pub const fn route(&self) -> AssetLaneRouteV2 {
        self.route
    }

    pub fn source_leaf_journal_root(&self) -> &RootV2 {
        &self.source_leaf_journal_root
    }

    pub fn source_leaf_receipt_root(&self) -> &RootV2 {
        &self.source_leaf_receipt_root
    }

    pub fn post_state(&self) -> &AssetLaneCustodyStateV2 {
        &self.post_state
    }

    pub fn effects(&self) -> &GlobalEconomicEffectPlanV2 {
        &self.effects
    }

    pub fn module_journal(&self) -> &LaneModuleTransitionJournalV2 {
        &self.module_journal
    }

    pub fn receipt_root(&self) -> &RootV2 {
        &self.module_journal.receipt_root
    }

    pub const fn production_authority(&self) -> &'static str {
        ASSET_LANE_PRODUCTION_AUTHORITY_V2
    }

    pub const fn profile_authentication(&self) -> &'static str {
        ASSET_LANE_PROFILE_AUTHENTICATION_V2
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
#[must_use]
pub enum AssetLaneCustodyResultV2 {
    Accepted(Box<AssetLaneCustodyAcceptedV2>),
    Rejected(Box<AssetLaneRejectedV2>),
}

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
    state: &AssetLaneCustodyStateV2,
    route: AssetLaneRouteV2,
    code: AssetLaneRejectCodeV2,
) -> AbiResultV2<AssetLaneCustodyResultV2> {
    let rejected = AssetLaneRejectedV2::new(route, code, state.state_root()?)?;
    Ok(AssetLaneCustodyResultV2::Rejected(Box::new(rejected)))
}

fn expected_leaf_pre_root(
    state: &AssetLaneCustodyStateV2,
    candidate: &LeafAcceptedV2,
) -> AbiResultV2<RootV2> {
    match candidate {
        LeafAcceptedV2::Transfer(_) => state.transfer_leaf_state().state_root(),
        LeafAcceptedV2::ManagedLifecycle(_) => state.managed_leaf_state().state_root(),
    }
}

fn candidate_binding_holds(
    context: &AssetLaneContextV2,
    state: &AssetLaneCustodyStateV2,
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
    context.module_release_id == *state.module_release_id()
        && journal.chain_id == occurrence.chain_id
        && journal.deployment_root == occurrence.deployment_root
        && journal.profile_root == occurrence.profile_root
        && journal.writer_epoch == context.writer_epoch
        && journal.module_release_id == *state.module_release_id()
        && journal.command_occurrence_id == occurrence_id
        && journal.pre_lane_root == expected_pre
        && effects.occurrence_consumptions == vec![occurrence_id]
        && effects.external_outbox_enqueue.is_empty()
        && journal.private_port_root.is_zero()
        && journal.terminal_obligations_root.is_zero()
        && journal.oracle_occurrence_plan_root.is_zero()
}

fn aggregate_post_state(
    pre_state: &AssetLaneCustodyStateV2,
    candidate: &LeafAcceptedV2,
) -> AbiResultV2<AssetLaneCustodyStateV2> {
    let transfer_state = match candidate {
        LeafAcceptedV2::Transfer(candidate) => candidate.post_state.clone(),
        LeafAcceptedV2::ManagedLifecycle(candidate) => {
            merge_managed_post_state(pre_state, &candidate.post_state)
        }
    };
    let post_state = AssetLaneCustodyStateV2 {
        schema: ASSET_LANE_CUSTODY_STATE_SCHEMA_V2.to_owned(),
        transfer_state,
        origin_registry: pre_state.origin_registry.clone(),
        managed_policies: pre_state.managed_policies.clone(),
        custody: pre_state.custody.clone(),
    };
    post_state.validate()?;
    Ok(post_state)
}

fn merge_managed_post_state(
    pre_state: &AssetLaneCustodyStateV2,
    managed_post: &crate::managed_asset_lifecycle_types::ManagedAssetLifecycleStateV2,
) -> AssetTransferStateV2 {
    let managed_assets = pre_state
        .managed_policies
        .iter()
        .map(|policy| policy.asset.as_str())
        .collect::<BTreeSet<_>>();
    let mut balances = pre_state
        .transfer_state
        .balances
        .iter()
        .filter(|row| !managed_assets.contains(row.asset.as_str()))
        .cloned()
        .collect::<Vec<_>>();
    balances.extend(managed_post.balances.iter().cloned());
    balances.sort_by(|left, right| left.key().cmp(&right.key()));

    let mut supplies = pre_state
        .transfer_state
        .supplies
        .iter()
        .filter(|row| !managed_assets.contains(row.asset.as_str()))
        .cloned()
        .collect::<Vec<_>>();
    supplies.extend(managed_post.supplies.iter().cloned());
    supplies.sort_by(|left, right| left.asset.cmp(&right.asset));
    AssetTransferStateV2 {
        schema: pre_state.transfer_state.schema.clone(),
        module_release_id: pre_state.transfer_state.module_release_id.clone(),
        policies: pre_state.transfer_state.policies.clone(),
        balances,
        supplies,
    }
}

fn leaf_post_account_total_atoms(candidate: &LeafAcceptedV2, asset: &str) -> Option<u128> {
    let balances = match candidate {
        LeafAcceptedV2::Transfer(candidate) => &candidate.post_state.balances,
        LeafAcceptedV2::ManagedLifecycle(candidate) => &candidate.post_state.balances,
    };
    balances
        .iter()
        .filter(|row| row.asset == asset)
        .try_fold(0_u128, |total, row| total.checked_add(row.amount_atoms))
}

fn leaf_post_supply_atoms(candidate: &LeafAcceptedV2, asset: &str) -> AbiResultV2<u128> {
    match candidate {
        LeafAcceptedV2::Transfer(candidate) => candidate.post_state.supply_atoms(asset),
        LeafAcceptedV2::ManagedLifecycle(candidate) => candidate.post_state.supply_atoms(asset),
    }
}

fn leaf_conservation_holds(
    pre_state: &AssetLaneCustodyStateV2,
    command: &AssetLaneCommandV2,
    candidate: &LeafAcceptedV2,
) -> bool {
    if candidate.effects().asset_conservation.len() != 1 {
        return false;
    }
    let row = &candidate.effects().asset_conservation[0];
    let command_asset = match command {
        AssetLaneCommandV2::Transfer(command) => command.asset.as_str(),
        AssetLaneCommandV2::ManagedLifecycle(command) => command.asset.as_str(),
    };
    if row.asset != command_asset {
        return false;
    }
    let values = (
        pre_state.account_total_atoms(&row.asset),
        leaf_post_account_total_atoms(candidate, &row.asset),
        pre_state.supply_atoms(&row.asset),
        leaf_post_supply_atoms(candidate, &row.asset),
    );
    let (Ok(account_pre), Some(account_post), Ok(supply_pre), Ok(supply_post)) = values else {
        return false;
    };
    row.owned_and_custodied_pre_atoms == account_pre
        && row.owned_and_custodied_post_atoms == account_post
        && row.supply_pre_atoms == supply_pre
        && row.supply_post_atoms == supply_post
}

fn projection_holds(
    route: AssetLaneRouteV2,
    pre_state: &AssetLaneCustodyStateV2,
    post_state: &AssetLaneCustodyStateV2,
    candidate: &LeafAcceptedV2,
) -> bool {
    if pre_state.custody != post_state.custody
        || pre_state.origin_registry != post_state.origin_registry
        || pre_state.managed_policies != post_state.managed_policies
        || pre_state.transfer_state.policies != post_state.transfer_state.policies
    {
        return false;
    }
    let leaf_projection_matches = match (route, candidate) {
        (AssetLaneRouteV2::TRANSFER, LeafAcceptedV2::Transfer(candidate)) => {
            post_state.transfer_leaf_state() == candidate.post_state
        }
        (AssetLaneRouteV2::MANAGED_LIFECYCLE, LeafAcceptedV2::ManagedLifecycle(candidate)) => {
            post_state.managed_leaf_state() == candidate.post_state
        }
        _ => false,
    };
    if !leaf_projection_matches || candidate.effects().asset_conservation.len() != 1 {
        return false;
    }
    let row = &candidate.effects().asset_conservation[0];
    let values = (
        pre_state.physical_total_atoms(&row.asset),
        post_state.physical_total_atoms(&row.asset),
    );
    let (Ok(physical_pre), Ok(physical_post)) = values else {
        return false;
    };
    physical_pre == row.supply_pre_atoms && physical_post == row.supply_post_atoms
}

fn completed_effects(
    pre_state: &AssetLaneCustodyStateV2,
    post_state: &AssetLaneCustodyStateV2,
    candidate: &LeafAcceptedV2,
) -> AbiResultV2<GlobalEconomicEffectPlanV2> {
    let source = candidate.effects();
    let mut conservation = Vec::with_capacity(source.asset_conservation.len());
    for row in &source.asset_conservation {
        conservation.push(AssetConservationRowV2 {
            asset: row.asset.clone(),
            owned_and_custodied_pre_atoms: pre_state.physical_total_atoms(&row.asset)?,
            owned_and_custodied_post_atoms: post_state.physical_total_atoms(&row.asset)?,
            supply_pre_atoms: row.supply_pre_atoms,
            supply_post_atoms: row.supply_post_atoms,
            authorized_issue_atoms: row.authorized_issue_atoms,
            authorized_burn_atoms: row.authorized_burn_atoms,
        });
    }
    let effects = GlobalEconomicEffectPlanV2 {
        schema: source.schema.clone(),
        rows: source.rows.clone(),
        asset_conservation: conservation,
        fee_conservation: source.fee_conservation.clone(),
        lane_writes: vec![LaneWriteV2 {
            lane_id: LaneIdV2::ASSET_TRANSFER,
            pre_root: pre_state.state_root()?,
            post_root: post_state.state_root()?,
        }],
        occurrence_consumptions: source.occurrence_consumptions.clone(),
        external_outbox_enqueue: Vec::new(),
    };
    effects.validate()?;
    Ok(effects)
}

#[derive(Serialize)]
struct AssetLaneCustodyCoordinatorReceiptBodyV2<'a> {
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

fn custody_coordinator_receipt_root(
    body: &AssetLaneCustodyCoordinatorReceiptBodyV2<'_>,
) -> AbiResultV2<RootV2> {
    hash_global_v2(ASSET_LANE_CUSTODY_COORDINATOR_RECEIPT_DOMAIN_V2, body)
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
    pre_state: &AssetLaneCustodyStateV2,
    post_state: AssetLaneCustodyStateV2,
    candidate: &LeafAcceptedV2,
) -> AbiResultV2<AssetLaneCustodyAcceptedV2> {
    let source_journal = candidate.journal();
    let source_leaf_journal_root = source_journal.journal_root()?;
    let source_leaf_receipt_root = source_journal.receipt_root.clone();
    let pre_root = pre_state.state_root()?;
    let post_root = post_state.state_root()?;
    let effects = completed_effects(pre_state, &post_state, candidate)?;
    let effect_plan_root = effects.effect_plan_root()?;
    let zero_root = RootV2::zero();
    let receipt_root =
        custody_coordinator_receipt_root(&AssetLaneCustodyCoordinatorReceiptBodyV2 {
            route,
            source_leaf_journal_root: &source_leaf_journal_root,
            source_leaf_receipt_root: &source_leaf_receipt_root,
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
    AssetLaneCustodyAcceptedV2::new(
        route,
        source_leaf_journal_root,
        source_leaf_receipt_root,
        post_state,
        effects,
        journal,
    )
}

fn compose_candidate(
    context: &AssetLaneContextV2,
    pre_state: &AssetLaneCustodyStateV2,
    command: &AssetLaneCommandV2,
    candidate: LeafAcceptedV2,
) -> AbiResultV2<AssetLaneCustodyResultV2> {
    let route = command.route();
    if !candidate_binding_holds(context, pre_state, &candidate) {
        return reject(
            pre_state,
            AssetLaneRouteV2::COORDINATOR,
            AssetLaneRejectCodeV2::Coordinator(
                AssetLaneCoordinatorRejectCodeV2::CANDIDATE_BINDING_MISMATCH,
            ),
        );
    }
    if !leaf_conservation_holds(pre_state, command, &candidate) {
        return reject(
            pre_state,
            AssetLaneRouteV2::COORDINATOR,
            AssetLaneRejectCodeV2::Coordinator(
                AssetLaneCoordinatorRejectCodeV2::PROJECTION_MISMATCH,
            ),
        );
    }
    let post_state = match aggregate_post_state(pre_state, &candidate) {
        Ok(post_state) => post_state,
        Err(AbiErrorV2::StateResourceLimit(_)) => {
            return reject(
                pre_state,
                AssetLaneRouteV2::COORDINATOR,
                AssetLaneRejectCodeV2::Coordinator(
                    AssetLaneCoordinatorRejectCodeV2::STATE_RESOURCE_LIMIT,
                ),
            )
        }
        Err(error) => return Err(error),
    };
    if !projection_holds(route, pre_state, &post_state, &candidate) {
        return reject(
            pre_state,
            AssetLaneRouteV2::COORDINATOR,
            AssetLaneRejectCodeV2::Coordinator(
                AssetLaneCoordinatorRejectCodeV2::PROJECTION_MISMATCH,
            ),
        );
    }
    Ok(AssetLaneCustodyResultV2::Accepted(Box::new(
        rebind_candidate(route, pre_state, post_state, &candidate)?,
    )))
}

pub fn transition_asset_lane_custody_v2(
    context: &AssetLaneContextV2,
    pre_state: &AssetLaneCustodyStateV2,
    command: &AssetLaneCommandV2,
) -> AbiResultV2<AssetLaneCustodyResultV2> {
    context.validate()?;
    pre_state.validate()?;
    command.validate()?;
    if !pre_state.policy_origin_bindings_hold() {
        return reject(
            pre_state,
            AssetLaneRouteV2::COORDINATOR,
            AssetLaneRejectCodeV2::Coordinator(
                AssetLaneCoordinatorRejectCodeV2::REGISTRY_BINDING_MISMATCH,
            ),
        );
    }
    let route = command.route();
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
    compose_candidate(context, pre_state, command, candidate)
}

#[cfg(test)]
mod tests {
    use serde_json::Value;

    use super::*;
    use crate::asset_lane_state::AssetLaneStateV2;
    use crate::asset_origin_registry::asset_transfer_policy_root_v2;
    use crate::asset_origin_registry_types::AssetOriginKindV2;
    use crate::asset_transfer_types::{
        AssetClassV2, AssetTransferCommandV2, ACCOUNT_CUSTODY_DOMAIN_V2,
    };
    use crate::canonical::{decode_canonical_v2, ValidateCanonicalV2};
    use crate::effects::ExternalOutboxEnqueueV2;
    use crate::managed_asset_lifecycle_types::ManagedAssetLifecycleCommandV2;
    use crate::state::{AssetSupplyV2, EconomicAmountV2};

    const GOLDEN: &str = include_str!(
        "../../../tests/data/global_settlement_abi_v2_asset_lane_coordinator_golden.json"
    );

    fn vector_bytes(case_name: &str, vector_name: &str) -> Vec<u8> {
        let fixture: Value = serde_json::from_str(GOLDEN).expect("fixture must parse");
        serde_json::to_vec(&fixture["accepted"][case_name]["vectors"][vector_name]["canonical"])
            .expect("vector must serialize")
    }

    fn typed_vector<T>(case_name: &str, vector_name: &str) -> T
    where
        T: serde::de::DeserializeOwned + Serialize + ValidateCanonicalV2,
    {
        decode_canonical_v2(&vector_bytes(case_name, vector_name)).expect("vector must decode")
    }

    fn custody_state(case_name: &str) -> AssetLaneCustodyStateV2 {
        let aggregate: AssetLaneStateV2 = typed_vector(case_name, "pre_state");
        let mut transfer_state = aggregate.transfer_leaf_state();
        transfer_state.balances = vec![EconomicAmountV2 {
            owner: "alice".to_owned(),
            asset: "USD".to_owned(),
            custody_domain: ACCOUNT_CUSTODY_DOMAIN_V2.to_owned(),
            amount_atoms: 80,
        }];
        transfer_state.supplies[0].amount_atoms = 100;
        AssetLaneCustodyStateV2 {
            schema: ASSET_LANE_CUSTODY_STATE_SCHEMA_V2.to_owned(),
            transfer_state,
            origin_registry: aggregate.origin_registry,
            managed_policies: aggregate.managed_policies,
            custody: vec![EconomicAmountV2 {
                owner: "vault".to_owned(),
                asset: "USD".to_owned(),
                custody_domain: "vault:primary".to_owned(),
                amount_atoms: 20,
            }],
        }
    }

    fn transfer_subject() -> (
        AssetLaneContextV2,
        AssetLaneCustodyStateV2,
        AssetTransferCommandV2,
    ) {
        let mut context: AssetLaneContextV2 = typed_vector("transfer", "context");
        let mut command: AssetTransferCommandV2 = typed_vector("transfer", "command");
        command.amount_atoms = 10;
        context
            .occurrence
            .as_mut()
            .expect("transfer occurrence")
            .command_body_hash = command.command_body_hash().expect("command body hash");
        (context, custody_state("transfer"), command)
    }

    fn transfer_candidate(
        context: &AssetLaneContextV2,
        state: &AssetLaneCustodyStateV2,
        command: &AssetTransferCommandV2,
    ) -> Box<AssetTransferAcceptedV2> {
        let result = transition_asset_transfer_v2(
            &context.transfer_context(),
            &state.transfer_leaf_state(),
            command,
        )
        .expect("transfer leaf executes");
        let AssetTransferResultV2::Accepted(accepted) = result else {
            panic!("transfer fixture must accept")
        };
        accepted
    }

    fn forged_transfer_candidate(
        context: &AssetLaneContextV2,
        state: &AssetLaneCustodyStateV2,
        command: &AssetTransferCommandV2,
        supply_fields: bool,
    ) -> LeafAcceptedV2 {
        let mut accepted = transfer_candidate(context, state, command);
        let row = &mut accepted.effects.asset_conservation[0];
        if supply_fields {
            row.supply_pre_atoms += 1;
            row.supply_post_atoms += 1;
        } else {
            row.owned_and_custodied_pre_atoms += 1;
            row.owned_and_custodied_post_atoms += 1;
        }
        accepted.module_journal.effect_plan_root = accepted
            .effects
            .effect_plan_root()
            .expect("forged effect root");
        accepted
            .validate()
            .expect("leaf-local validation does not own aggregate projection");
        LeafAcceptedV2::Transfer(accepted)
    }

    fn assert_coordinator_noop(
        result: AssetLaneCustodyResultV2,
        state: &AssetLaneCustodyStateV2,
        code: AssetLaneCoordinatorRejectCodeV2,
    ) {
        let rejected = match result {
            AssetLaneCustodyResultV2::Rejected(rejected) => rejected,
            AssetLaneCustodyResultV2::Accepted(accepted) => panic!(
                "faulty leaf unexpectedly accepted with {} external outbox entries",
                accepted.effects().external_outbox_enqueue.len()
            ),
        };
        assert_eq!(rejected.route(), AssetLaneRouteV2::COORDINATOR);
        assert_eq!(rejected.code(), AssetLaneRejectCodeV2::Coordinator(code));
        assert_eq!(rejected.pre_state_root(), rejected.post_state_root());
        assert_eq!(
            rejected.pre_state_root(),
            &state.state_root().expect("state root")
        );
        let effects = rejected.effects();
        assert!(effects.rows.is_empty());
        assert!(effects.asset_conservation.is_empty());
        assert!(effects.fee_conservation.is_empty());
        assert!(effects.lane_writes.is_empty());
        assert!(effects.occurrence_consumptions.is_empty());
        assert!(effects.external_outbox_enqueue.is_empty());
    }

    fn assert_projection_noop(result: AssetLaneCustodyResultV2, state: &AssetLaneCustodyStateV2) {
        assert_coordinator_noop(
            result,
            state,
            AssetLaneCoordinatorRejectCodeV2::PROJECTION_MISMATCH,
        );
    }

    #[test]
    fn forged_leaf_account_and_supply_scalars_are_projection_noops() {
        for supply_fields in [false, true] {
            let (context, state, command) = transfer_subject();
            let candidate = forged_transfer_candidate(&context, &state, &command, supply_fields);
            let result = compose_candidate(
                &context,
                &state,
                &AssetLaneCommandV2::Transfer(command),
                candidate,
            )
            .expect("coordinator evaluates forged totals");
            assert_projection_noop(result, &state);
        }
    }

    #[test]
    fn wrong_asset_conservation_is_a_projection_noop() {
        let (context, mut state, command) = transfer_subject();
        let mut eur_policy = state.transfer_state.policies[0].clone();
        eur_policy.asset = "EUR".to_owned();
        eur_policy.transfer_fee_atoms = 0;
        eur_policy.asset_origin_root = Some(root(100));
        let eur_policy_root =
            asset_transfer_policy_root_v2(&eur_policy).expect("EUR transfer policy root");
        state.transfer_state.policies.push(eur_policy);
        state
            .transfer_state
            .policies
            .sort_by(|left, right| left.asset.cmp(&right.asset));

        let mut eur_record = state.origin_registry.assets[0].clone();
        eur_record.asset = "EUR".to_owned();
        eur_record.origin_kind = AssetOriginKindV2::TAU_ORIGINATED;
        eur_record.origin_root = root(100);
        eur_record.transfer_policy_root = eur_policy_root;
        eur_record.issue_policy_root = RootV2::zero();
        state.origin_registry.assets.push(eur_record);
        state
            .origin_registry
            .assets
            .sort_by(|left, right| left.asset.cmp(&right.asset));
        state.transfer_state.balances.push(EconomicAmountV2 {
            owner: "carol".to_owned(),
            asset: "EUR".to_owned(),
            custody_domain: ACCOUNT_CUSTODY_DOMAIN_V2.to_owned(),
            amount_atoms: 7,
        });
        state
            .transfer_state
            .balances
            .sort_by(|left, right| left.key().cmp(&right.key()));
        state.transfer_state.supplies.push(AssetSupplyV2 {
            asset: "EUR".to_owned(),
            amount_atoms: 7,
        });
        state
            .transfer_state
            .supplies
            .sort_by(|left, right| left.asset.cmp(&right.asset));
        state.validate().expect("two-asset pre-state is valid");

        let mut accepted = transfer_candidate(&context, &state, &command);
        assert_eq!(command.asset, "USD");
        assert!(!accepted.effects.rows.is_empty());
        assert!(accepted
            .effects
            .rows
            .iter()
            .all(|effect| effect.asset == command.asset));
        let row = &mut accepted.effects.asset_conservation[0];
        assert_eq!(row.asset, command.asset);
        row.asset = "EUR".to_owned();
        row.owned_and_custodied_pre_atoms = 7;
        row.owned_and_custodied_post_atoms = 7;
        row.supply_pre_atoms = 7;
        row.supply_post_atoms = 7;
        row.authorized_issue_atoms = 0;
        row.authorized_burn_atoms = 0;
        accepted.module_journal.effect_plan_root = accepted
            .effects
            .effect_plan_root()
            .expect("forged effect root");
        accepted
            .validate()
            .expect("leaf-local validation does not bind conservation to the command");

        let result = compose_candidate(
            &context,
            &state,
            &AssetLaneCommandV2::Transfer(command),
            LeafAcceptedV2::Transfer(accepted),
        )
        .expect("coordinator evaluates relabelled conservation");
        assert_projection_noop(result, &state);
    }

    #[test]
    fn forged_leaf_context_binding_is_a_candidate_binding_noop() {
        let (context, state, command) = transfer_subject();
        let mut accepted = transfer_candidate(&context, &state, &command);
        accepted.module_journal.chain_id = "forged-chain".to_owned();
        accepted
            .validate()
            .expect("leaf-local validation does not own the aggregate context");
        let result = compose_candidate(
            &context,
            &state,
            &AssetLaneCommandV2::Transfer(command),
            LeafAcceptedV2::Transfer(accepted),
        )
        .expect("coordinator evaluates forged context");
        let AssetLaneCustodyResultV2::Rejected(rejected) = result else {
            panic!("forged leaf context unexpectedly accepted")
        };
        assert_eq!(rejected.route(), AssetLaneRouteV2::COORDINATOR);
        assert_eq!(
            rejected.code(),
            AssetLaneRejectCodeV2::Coordinator(
                AssetLaneCoordinatorRejectCodeV2::CANDIDATE_BINDING_MISMATCH
            )
        );
        assert_eq!(rejected.pre_state_root(), rejected.post_state_root());
        assert!(rejected.effects().is_empty());
    }

    #[test]
    fn accepted_receipt_recomputes_source_leaf_receipt_provenance() {
        let (context, state, command) = transfer_subject();
        let result = transition_asset_lane_custody_v2(
            &context,
            &state,
            &AssetLaneCommandV2::Transfer(command),
        )
        .expect("custody coordinator executes");
        let AssetLaneCustodyResultV2::Accepted(mut accepted) = result else {
            panic!("custody fixture must accept")
        };
        accepted.source_leaf_receipt_root = root(201);
        assert_eq!(
            accepted.validate(),
            Err(AbiErrorV2::InvalidBinding(
                "asset lane custody receipt binding"
            ))
        );
    }

    fn root(value: u64) -> RootV2 {
        RootV2::parse(
            format!("0x{value:064x}"),
            "custody resource test root",
            false,
        )
        .expect("test root is canonical")
    }

    fn unmanaged_subject(
        eur_rows: usize,
    ) -> (
        AssetLaneContextV2,
        AssetLaneCustodyStateV2,
        ManagedAssetLifecycleCommandV2,
    ) {
        let context: AssetLaneContextV2 = typed_vector("managed_issue", "context");
        let command: ManagedAssetLifecycleCommandV2 = typed_vector("managed_issue", "command");
        let aggregate: AssetLaneStateV2 = typed_vector("managed_issue", "pre_state");
        let mut transfer = aggregate.transfer_leaf_state();

        let mut eur_policy = transfer.policies[0].clone();
        eur_policy.asset = "EUR".to_owned();
        eur_policy.transfer_fee_atoms = 0;
        eur_policy.asset_origin_root = Some(root(100));
        let eur_policy_root =
            asset_transfer_policy_root_v2(&eur_policy).expect("EUR transfer policy root");
        transfer.policies.push(eur_policy);
        transfer
            .policies
            .sort_by(|left, right| left.asset.cmp(&right.asset));

        let mut registry = aggregate.origin_registry;
        let mut eur_record = registry.assets[0].clone();
        eur_record.asset = "EUR".to_owned();
        eur_record.origin_kind = AssetOriginKindV2::TAU_ORIGINATED;
        eur_record.origin_root = root(100);
        eur_record.transfer_policy_root = eur_policy_root;
        eur_record.issue_policy_root = RootV2::zero();
        eur_record.asset_class = AssetClassV2::RegisteredOrdinaryToken;
        registry.assets.push(eur_record);
        registry
            .assets
            .sort_by(|left, right| left.asset.cmp(&right.asset));

        transfer.balances = (0..eur_rows)
            .map(|index| EconomicAmountV2 {
                owner: format!("holder{index:04}"),
                asset: "EUR".to_owned(),
                custody_domain: ACCOUNT_CUSTODY_DOMAIN_V2.to_owned(),
                amount_atoms: 1,
            })
            .collect();
        transfer.supplies = vec![
            AssetSupplyV2 {
                asset: "EUR".to_owned(),
                amount_atoms: eur_rows as u128,
            },
            AssetSupplyV2 {
                asset: "USD".to_owned(),
                amount_atoms: 0,
            },
        ];
        let state = AssetLaneCustodyStateV2 {
            schema: ASSET_LANE_CUSTODY_STATE_SCHEMA_V2.to_owned(),
            transfer_state: transfer,
            origin_registry: registry,
            managed_policies: aggregate.managed_policies,
            custody: Vec::new(),
        };
        state.validate().expect("row-ceiling pre-state is valid");
        (context, state, command)
    }

    #[test]
    fn managed_recomposition_preserves_unmanaged_rows_and_supply_keys() {
        let (context, state, command) = unmanaged_subject(1);
        let result = transition_asset_lane_custody_v2(
            &context,
            &state,
            &AssetLaneCommandV2::ManagedLifecycle(command),
        )
        .expect("managed custody coordinator executes");
        let AssetLaneCustodyResultV2::Accepted(accepted) = result else {
            panic!("managed custody fixture must accept")
        };
        let eur_balances = accepted
            .post_state()
            .transfer_state
            .balances
            .iter()
            .filter(|row| row.asset == "EUR")
            .cloned()
            .collect::<Vec<_>>();
        let pre_eur_balances = state
            .transfer_state
            .balances
            .iter()
            .filter(|row| row.asset == "EUR")
            .cloned()
            .collect::<Vec<_>>();
        assert_eq!(eur_balances, pre_eur_balances);
        assert_eq!(
            accepted.post_state().transfer_state.supply_atoms("EUR"),
            state.transfer_state.supply_atoms("EUR")
        );
        assert_eq!(accepted.post_state().transfer_state.supplies.len(), 2);
    }

    #[test]
    fn forged_projection_precedes_simultaneous_aggregate_resource_failure() {
        let (context, state, command) =
            unmanaged_subject(crate::resource_limits::MAX_BALANCE_ROWS_PER_ASSET_STATE_V2);
        let result = transition_managed_asset_lifecycle_v2(
            &context.managed_context(),
            &state.managed_leaf_state(),
            &command,
        )
        .expect("managed leaf executes below its local row ceiling");
        let ManagedAssetLifecycleResultV2::Accepted(mut accepted) = result else {
            panic!("managed fixture must accept")
        };
        let row = &mut accepted.effects.asset_conservation[0];
        row.owned_and_custodied_pre_atoms += 1;
        row.owned_and_custodied_post_atoms += 1;
        accepted.module_journal.effect_plan_root = accepted
            .effects
            .effect_plan_root()
            .expect("forged effect root");
        accepted
            .validate()
            .expect("leaf-local validation does not own aggregate projection");

        let result = compose_candidate(
            &context,
            &state,
            &AssetLaneCommandV2::ManagedLifecycle(command),
            LeafAcceptedV2::ManagedLifecycle(accepted),
        )
        .expect("coordinator evaluates simultaneous failures");
        assert_projection_noop(result, &state);
    }

    #[test]
    fn extra_conservation_row_precedes_aggregate_resource_failure() {
        let (context, state, command) =
            unmanaged_subject(crate::resource_limits::MAX_BALANCE_ROWS_PER_ASSET_STATE_V2);
        let result = transition_managed_asset_lifecycle_v2(
            &context.managed_context(),
            &state.managed_leaf_state(),
            &command,
        )
        .expect("managed leaf executes below its local row ceiling");
        let ManagedAssetLifecycleResultV2::Accepted(mut accepted) = result else {
            panic!("managed fixture must accept")
        };
        accepted
            .effects
            .asset_conservation
            .push(AssetConservationRowV2 {
                asset: "ZZZ".to_owned(),
                owned_and_custodied_pre_atoms: 0,
                owned_and_custodied_post_atoms: 0,
                supply_pre_atoms: 0,
                supply_post_atoms: 0,
                authorized_issue_atoms: 0,
                authorized_burn_atoms: 0,
            });
        accepted.module_journal.effect_plan_root = accepted
            .effects
            .effect_plan_root()
            .expect("expanded effect root");
        accepted
            .validate()
            .expect("leaf-local validation permits an extra conservation row");

        let result = compose_candidate(
            &context,
            &state,
            &AssetLaneCommandV2::ManagedLifecycle(command),
            LeafAcceptedV2::ManagedLifecycle(accepted),
        )
        .expect("coordinator evaluates expanded conservation");
        assert_projection_noop(result, &state);
    }

    #[test]
    fn leaf_external_outbox_is_a_candidate_binding_noop() {
        let (context, state, command) = transfer_subject();
        let control = transition_asset_lane_custody_v2(
            &context,
            &state,
            &AssetLaneCommandV2::Transfer(command.clone()),
        )
        .expect("custody coordinator executes control");
        assert!(matches!(control, AssetLaneCustodyResultV2::Accepted(_)));

        let mut accepted = transfer_candidate(&context, &state, &command);
        accepted
            .effects
            .external_outbox_enqueue
            .push(ExternalOutboxEnqueueV2 {
                effect_id: root(301),
                destination_id: "external:bridge".to_owned(),
                payload_hash: root(302),
                adapter_profile_root: root(303),
            });
        accepted.module_journal.effect_plan_root = accepted
            .effects
            .effect_plan_root()
            .expect("outbox effect root");
        accepted
            .validate()
            .expect("leaf-local validation permits an external outbox entry");

        let result = compose_candidate(
            &context,
            &state,
            &AssetLaneCommandV2::Transfer(command),
            LeafAcceptedV2::Transfer(accepted),
        )
        .expect("coordinator evaluates leaf outbox");
        assert_coordinator_noop(
            result,
            &state,
            AssetLaneCoordinatorRejectCodeV2::CANDIDATE_BINDING_MISMATCH,
        );
    }

    #[test]
    fn source_binding_precedes_projection_and_aggregate_resource_failure() {
        let (context, state, command) =
            unmanaged_subject(crate::resource_limits::MAX_BALANCE_ROWS_PER_ASSET_STATE_V2);
        let control = transition_asset_lane_custody_v2(
            &context,
            &state,
            &AssetLaneCommandV2::ManagedLifecycle(command.clone()),
        )
        .expect("custody coordinator evaluates the resource control");
        assert_coordinator_noop(
            control,
            &state,
            AssetLaneCoordinatorRejectCodeV2::STATE_RESOURCE_LIMIT,
        );

        let result = transition_managed_asset_lifecycle_v2(
            &context.managed_context(),
            &state.managed_leaf_state(),
            &command,
        )
        .expect("managed leaf executes below its local row ceiling");
        let ManagedAssetLifecycleResultV2::Accepted(mut accepted) = result else {
            panic!("managed fixture must accept")
        };
        let row = &mut accepted.effects.asset_conservation[0];
        row.owned_and_custodied_pre_atoms += 1;
        row.owned_and_custodied_post_atoms += 1;
        accepted.module_journal.chain_id = "foreign-chain".to_owned();
        accepted.module_journal.effect_plan_root = accepted
            .effects
            .effect_plan_root()
            .expect("faulty effect root");
        accepted
            .validate()
            .expect("leaf-local validation permits aggregate faults");

        let result = compose_candidate(
            &context,
            &state,
            &AssetLaneCommandV2::ManagedLifecycle(command),
            LeafAcceptedV2::ManagedLifecycle(accepted),
        )
        .expect("coordinator evaluates simultaneous faults");
        assert_coordinator_noop(
            result,
            &state,
            AssetLaneCoordinatorRejectCodeV2::CANDIDATE_BINDING_MISMATCH,
        );
    }

    #[test]
    fn aggregate_resource_failure_precedes_late_exact_projection() {
        let (context, state, command) =
            unmanaged_subject(crate::resource_limits::MAX_BALANCE_ROWS_PER_ASSET_STATE_V2);
        let control = transition_asset_lane_custody_v2(
            &context,
            &state,
            &AssetLaneCommandV2::ManagedLifecycle(command.clone()),
        )
        .expect("custody coordinator evaluates the resource control");
        assert_coordinator_noop(
            control,
            &state,
            AssetLaneCoordinatorRejectCodeV2::STATE_RESOURCE_LIMIT,
        );

        let result = transition_managed_asset_lifecycle_v2(
            &context.managed_context(),
            &state.managed_leaf_state(),
            &command,
        )
        .expect("managed leaf executes below its local row ceiling");
        let ManagedAssetLifecycleResultV2::Accepted(mut accepted) = result else {
            panic!("managed fixture must accept")
        };
        accepted.post_state.policies[0].enabled = false;
        assert_ne!(
            accepted.post_state.policies,
            state.managed_leaf_state().policies
        );
        let changed_post_root = accepted
            .post_state
            .state_root()
            .expect("changed managed post root");
        accepted.effects.lane_writes[0].post_root = changed_post_root.clone();
        accepted.module_journal.post_lane_root = changed_post_root;
        accepted.module_journal.effect_plan_root = accepted
            .effects
            .effect_plan_root()
            .expect("changed effect root");
        accepted
            .validate()
            .expect("leaf-local validation permits policy drift");

        let result = compose_candidate(
            &context,
            &state,
            &AssetLaneCommandV2::ManagedLifecycle(command),
            LeafAcceptedV2::ManagedLifecycle(accepted),
        )
        .expect("coordinator evaluates resource and late projection faults");
        assert_coordinator_noop(
            result,
            &state,
            AssetLaneCoordinatorRejectCodeV2::STATE_RESOURCE_LIMIT,
        );
    }
}
