use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use crate::canonical::{hash_global_v1, AbiErrorV1, AbiResultV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1};
use crate::effects::{
    AssetConservationRowV1, EconomicEffectKindV1, EconomicEffectRowV1, GlobalEconomicEffectPlanV1,
    LaneWriteV1,
};
use crate::proof::EconomicCommandOccurrenceV1;
use crate::release::{
    EconomicPolicyRegistryV1, EconomicProfileSnapshotV1, LaneCoordinatorRegistryV1,
    LaneCoordinatorReleaseV1, LaneIdV1, LaneModuleReleaseV1, LaneRegistryV1, ProfileStatusV1,
    ReleaseStatusV1, RouteRegistryV1, RouteReleaseV1,
};
use crate::zdex_buyback_price_safety::{
    ZDEXBuybackPriceSafetyPolicyV1, ZDEX_BUYBACK_PRICE_SAFETY_POLICY_KIND_V1,
};
use crate::zdex_fee_allocation_receipt_verification::VerifiedZDEXFeeAllocationV1;
use crate::zdex_fee_allocation_types::{ZDEXFeeAllocationOccurrenceV1, FEE_BUYBACK_PRINCIPAL_V1};
use crate::zdex_purchase_burn_receipt_verification::{
    VerifiedZDEXAMMPurchaseV2, VerifiedZDEXBurnV1, ZDEXVerifiedLaneExpectationV1,
};
use crate::zdex_purchase_burn_types::{
    zdex_amm_purchase_port_schema_root_v1, zdex_burn_port_schema_root_v1,
    zdex_occurrence_burn_port_v1, zdex_pool_reserve_principal_v1, ZDEXAMMPurchaseJournalV2,
    ZDEXBurnJournalV1, ZDEXBuybackExecutionPolicyV1, AMM_PURCHASE_OUTPUT_ROLE_V1,
    PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1, ZDEX_BURN_INPUT_ROLE_V1,
    ZDEX_BUYBACK_EXECUTION_POLICY_KIND_V1,
};
use crate::zdex_tokenomics_lane_types::zdex_tokenomics_complete_lane_obligation_root_v1;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(non_camel_case_types)]
pub enum ZDEXPurchaseBurnRouteRejectCodeV1 {
    GOVERNED_PROFILE_MISMATCH,
    ROUTE_BINDING_MISMATCH,
    OCCURRENCE_MISMATCH,
    PROFILE_OR_EPOCH_MISMATCH,
    PURCHASE_WITNESS_MISMATCH,
    BURN_WITNESS_MISMATCH,
    ASSET_MISMATCH,
    PURCHASE_OCCURRENCE_MISMATCH,
    AMOUNT_MISMATCH,
    BURN_BUCKET_MISMATCH,
    BUYBACK_BUDGET_MISMATCH,
    BUYBACK_EXECUTION_POLICY_MISMATCH,
    PRICE_SAFETY_AUTHORITY_MISMATCH,
    CONSERVATION_HISTORY_DISCONNECTED,
}

pub struct ZDEXPurchaseBurnRouteProfileRegistriesV1<'a> {
    pub profile: &'a EconomicProfileSnapshotV1,
    pub lanes: &'a LaneRegistryV1,
    pub coordinators: &'a LaneCoordinatorRegistryV1,
    pub routes: &'a RouteRegistryV1,
    pub policies: &'a EconomicPolicyRegistryV1,
    pub buyback_execution_policy: &'a ZDEXBuybackExecutionPolicyV1,
    pub price_safety_policy: &'a ZDEXBuybackPriceSafetyPolicyV1,
}

pub struct GovernedZDEXPurchaseBurnRouteV1<'a> {
    profile: &'a EconomicProfileSnapshotV1,
    route_release: &'a RouteReleaseV1,
    purchase_module_release: &'a LaneModuleReleaseV1,
    burn_module_release: &'a LaneModuleReleaseV1,
    purchase_coordinator_release: &'a LaneCoordinatorReleaseV1,
    burn_coordinator_release: &'a LaneCoordinatorReleaseV1,
    buyback_execution_policy: &'a ZDEXBuybackExecutionPolicyV1,
    price_safety_policy: &'a ZDEXBuybackPriceSafetyPolicyV1,
}

fn registered_buyback_route_v1(routes: &RouteRegistryV1) -> AbiResultV1<&RouteReleaseV1> {
    routes
        .routes
        .iter()
        .find(|route| route.command_kind == PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1)
        .ok_or(AbiErrorV1::InvalidBinding(
            "ZDEX purchase-burn governed route absent",
        ))
}

fn require_governed_route_shapes_v1(
    governed: &GovernedZDEXPurchaseBurnRouteV1<'_>,
) -> AbiResultV1<()> {
    let route = governed.route_release;
    let purchase = governed.purchase_module_release;
    let burn = governed.burn_module_release;
    let purchase_coordinator = governed.purchase_coordinator_release;
    let burn_coordinator = governed.burn_coordinator_release;
    route.validate()?;
    purchase.validate()?;
    burn.validate()?;
    purchase_coordinator.validate()?;
    burn_coordinator.validate()?;
    if route.status != ReleaseStatusV1::SHADOW
        || route.accepts_new_objects
        || route.command_kind != PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1
        || route.ordered_lanes != [LaneIdV1::SPOT_LIQUIDITY, LaneIdV1::ZDEX_TOKENOMICS]
        || route.module_release_ids != [purchase.release_id.clone(), burn.release_id.clone()]
        || route.dependency_roles
            != [
                AMM_PURCHASE_OUTPUT_ROLE_V1.to_owned(),
                ZDEX_BURN_INPUT_ROLE_V1.to_owned(),
            ]
        || route.port_schema_roots
            != [
                zdex_amm_purchase_port_schema_root_v1()?,
                zdex_burn_port_schema_root_v1()?,
            ]
    {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX purchase-burn governed route shape",
        ));
    }
    for (release, lane_id) in [
        (purchase, LaneIdV1::SPOT_LIQUIDITY),
        (burn, LaneIdV1::ZDEX_TOKENOMICS),
    ] {
        if release.status != ReleaseStatusV1::SHADOW
            || release.accepts_new_objects
            || release.lane_id != lane_id
            || !release
                .command_variants
                .iter()
                .any(|command| command == PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1)
        {
            return Err(AbiErrorV1::InvalidBinding(
                "ZDEX purchase-burn governed module release shape",
            ));
        }
    }
    for (coordinator, lane_id) in [
        (purchase_coordinator, LaneIdV1::SPOT_LIQUIDITY),
        (burn_coordinator, LaneIdV1::ZDEX_TOKENOMICS),
    ] {
        if coordinator.status != ReleaseStatusV1::SHADOW
            || coordinator.accepts_new_objects
            || coordinator.lane_id != lane_id
        {
            return Err(AbiErrorV1::InvalidBinding(
                "ZDEX purchase-burn governed coordinator shape",
            ));
        }
    }
    Ok(())
}

pub fn bind_zdex_purchase_burn_shadow_profile_v1<'a>(
    expected_profile_id: &RootV1,
    expected_authority_epoch: u64,
    registries: ZDEXPurchaseBurnRouteProfileRegistriesV1<'a>,
) -> AbiResultV1<GovernedZDEXPurchaseBurnRouteV1<'a>> {
    let ZDEXPurchaseBurnRouteProfileRegistriesV1 {
        profile,
        lanes,
        coordinators,
        routes,
        policies,
        buyback_execution_policy,
        price_safety_policy,
    } = registries;
    profile.validate()?;
    if &profile.profile_id != expected_profile_id {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX purchase-burn expected profile",
        ));
    }
    if profile.authority_epoch != expected_authority_epoch {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX purchase-burn expected authority epoch",
        ));
    }
    if profile.status != ProfileStatusV1::SHADOW {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX purchase-burn profile status",
        ));
    }
    profile.validate_registries(lanes, coordinators, routes)?;
    buyback_execution_policy.validate()?;
    price_safety_policy.validate()?;
    if policies.registry_root()? != profile.policy_registry_root {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX buyback economic policy registry",
        ));
    }
    let execution_binding = policies.require_binding(
        ZDEX_BUYBACK_EXECUTION_POLICY_KIND_V1,
        PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
    )?;
    if execution_binding.policy_root != buyback_execution_policy.policy_root()? {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX buyback execution policy binding",
        ));
    }
    let price_binding = policies.require_binding(
        ZDEX_BUYBACK_PRICE_SAFETY_POLICY_KIND_V1,
        PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
    )?;
    let price_policy_root = price_safety_policy.policy_root()?;
    if price_binding.policy_root != price_policy_root
        || registered_buyback_route_v1(routes)?.oracle_policy_root != price_policy_root
    {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX buyback price-safety policy binding",
        ));
    }
    let governed = GovernedZDEXPurchaseBurnRouteV1 {
        profile,
        route_release: registered_buyback_route_v1(routes)?,
        purchase_module_release: lanes.release_for(LaneIdV1::SPOT_LIQUIDITY).ok_or(
            AbiErrorV1::InvalidBinding("ZDEX purchase-burn purchase release absent"),
        )?,
        burn_module_release: lanes.release_for(LaneIdV1::ZDEX_TOKENOMICS).ok_or(
            AbiErrorV1::InvalidBinding("ZDEX purchase-burn burn release absent"),
        )?,
        purchase_coordinator_release: coordinators.release_for(LaneIdV1::SPOT_LIQUIDITY).ok_or(
            AbiErrorV1::InvalidBinding("ZDEX purchase-burn purchase coordinator absent"),
        )?,
        burn_coordinator_release: coordinators.release_for(LaneIdV1::ZDEX_TOKENOMICS).ok_or(
            AbiErrorV1::InvalidBinding("ZDEX purchase-burn burn coordinator absent"),
        )?,
        buyback_execution_policy,
        price_safety_policy,
    };
    require_governed_route_shapes_v1(&governed)?;
    Ok(governed)
}

pub struct ZDEXPurchaseBurnRouteCandidateV1<'a> {
    pub governed_profile: GovernedZDEXPurchaseBurnRouteV1<'a>,
    pub route_release: &'a RouteReleaseV1,
    pub occurrence: &'a EconomicCommandOccurrenceV1,
    pub buyback_budget_occurrence: &'a ZDEXFeeAllocationOccurrenceV1,
    pub verified_buyback_budget: &'a VerifiedZDEXFeeAllocationV1,
    pub purchase_journal: &'a ZDEXAMMPurchaseJournalV2,
    pub purchase_effects: &'a GlobalEconomicEffectPlanV1,
    pub verified_purchase: &'a VerifiedZDEXAMMPurchaseV2,
    pub burn_journal: &'a ZDEXBurnJournalV1,
    pub burn_effects: &'a GlobalEconomicEffectPlanV1,
    pub verified_burn: &'a VerifiedZDEXBurnV1,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXPurchaseBurnRouteAcceptedV1 {
    pub route_release_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub profile_root: RootV1,
    pub writer_epoch: u64,
    pub ordered_lane_journal_roots: Vec<RootV1>,
    pub ordered_verified_binding_roots: Vec<RootV1>,
    pub verified_budget_binding_root: RootV1,
    pub buyback_execution_policy_root: RootV1,
    pub price_safety_policy_root: RootV1,
    pub price_authority_root: RootV1,
    pub effects: GlobalEconomicEffectPlanV1,
    pub terminal_obligations_root: RootV1,
}

pub const ZDEX_PURCHASE_BURN_ROUTE_COMPOSITION_SCHEMA_V3: &str =
    "zenodex/zdex-purchase-burn-route-composition/v3";

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXPurchaseBurnRouteCompositionJournalV3 {
    pub schema: String,
    pub route_release_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub profile_root: RootV1,
    pub writer_epoch: u64,
    pub ordered_lane_journal_roots: Vec<RootV1>,
    pub ordered_verified_binding_roots: Vec<RootV1>,
    pub verified_budget_binding_root: RootV1,
    pub buyback_execution_policy_root: RootV1,
    pub price_safety_policy_root: RootV1,
    pub price_authority_root: RootV1,
    pub effect_plan_root: RootV1,
    pub terminal_obligations_root: RootV1,
}

impl ZDEXPurchaseBurnRouteCompositionJournalV3 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != ZDEX_PURCHASE_BURN_ROUTE_COMPOSITION_SCHEMA_V3 {
            return Err(AbiErrorV1::InvalidBinding(
                "ZDEX route composition V3 schema",
            ));
        }
        for root in [
            &self.route_release_id,
            &self.command_occurrence_id,
            &self.profile_root,
            &self.verified_budget_binding_root,
            &self.buyback_execution_policy_root,
            &self.price_safety_policy_root,
            &self.price_authority_root,
            &self.effect_plan_root,
        ] {
            root.validate("ZDEX route composition V3 root", false)?;
        }
        self.terminal_obligations_root
            .validate("ZDEX route terminal obligations", true)?;
        if self.ordered_lane_journal_roots.len() != 2
            || self.ordered_verified_binding_roots.len() != 2
        {
            return Err(AbiErrorV1::InvalidBinding(
                "ZDEX route composition V3 ordered cardinality",
            ));
        }
        for root in self
            .ordered_lane_journal_roots
            .iter()
            .chain(&self.ordered_verified_binding_roots)
        {
            root.validate("ZDEX route composition V3 ordered root", false)?;
        }
        Ok(())
    }

    pub fn journal_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("zdex-purchase-burn-route-composition-v3", self)
    }
}

impl ZDEXPurchaseBurnRouteAcceptedV1 {
    pub fn composition_journal_v3(&self) -> AbiResultV1<ZDEXPurchaseBurnRouteCompositionJournalV3> {
        self.effects.validate()?;
        let journal = ZDEXPurchaseBurnRouteCompositionJournalV3 {
            schema: ZDEX_PURCHASE_BURN_ROUTE_COMPOSITION_SCHEMA_V3.to_owned(),
            route_release_id: self.route_release_id.clone(),
            command_occurrence_id: self.command_occurrence_id.clone(),
            profile_root: self.profile_root.clone(),
            writer_epoch: self.writer_epoch,
            ordered_lane_journal_roots: self.ordered_lane_journal_roots.clone(),
            ordered_verified_binding_roots: self.ordered_verified_binding_roots.clone(),
            verified_budget_binding_root: self.verified_budget_binding_root.clone(),
            buyback_execution_policy_root: self.buyback_execution_policy_root.clone(),
            price_safety_policy_root: self.price_safety_policy_root.clone(),
            price_authority_root: self.price_authority_root.clone(),
            effect_plan_root: self.effects.effect_plan_root()?,
            terminal_obligations_root: self.terminal_obligations_root.clone(),
        };
        journal.validate()?;
        Ok(journal)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXPurchaseBurnRouteRejectedV1 {
    pub code: ZDEXPurchaseBurnRouteRejectCodeV1,
    pub effects: GlobalEconomicEffectPlanV1,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ZDEXPurchaseBurnRouteResultV1 {
    Accepted(Box<ZDEXPurchaseBurnRouteAcceptedV1>),
    Rejected(ZDEXPurchaseBurnRouteRejectedV1),
}

fn empty_effect_plan_v1() -> GlobalEconomicEffectPlanV1 {
    GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: vec![],
        asset_conservation: vec![],
        fee_conservation: vec![],
        lane_writes: vec![],
        occurrence_consumptions: vec![],
        external_outbox_enqueue: vec![],
    }
}

fn reject_v1(code: ZDEXPurchaseBurnRouteRejectCodeV1) -> ZDEXPurchaseBurnRouteResultV1 {
    ZDEXPurchaseBurnRouteResultV1::Rejected(ZDEXPurchaseBurnRouteRejectedV1 {
        code,
        effects: empty_effect_plan_v1(),
    })
}

fn effect_kind_label_v1(kind: EconomicEffectKindV1) -> &'static str {
    match kind {
        EconomicEffectKindV1::ACCOUNT_MOVEMENT => "ACCOUNT_MOVEMENT",
        EconomicEffectKindV1::ISSUE => "ISSUE",
        EconomicEffectKindV1::BURN => "BURN",
        EconomicEffectKindV1::CUSTODY => "CUSTODY",
        EconomicEffectKindV1::LIABILITY => "LIABILITY",
        EconomicEffectKindV1::RESERVE => "RESERVE",
        EconomicEffectKindV1::FEE_ALLOCATION => "FEE_ALLOCATION",
        EconomicEffectKindV1::REWARD => "REWARD",
        EconomicEffectKindV1::SLASH => "SLASH",
    }
}

fn compose_rows_v1(
    purchase: &GlobalEconomicEffectPlanV1,
    burn: &GlobalEconomicEffectPlanV1,
) -> AbiResultV1<Vec<EconomicEffectRowV1>> {
    type EffectKey = (String, String, String, String);
    let mut totals = BTreeMap::<EffectKey, (EconomicEffectRowV1, i128)>::new();
    for row in purchase.rows.iter().chain(&burn.rows) {
        let key = (
            effect_kind_label_v1(row.kind).to_owned(),
            row.asset.clone(),
            row.principal.clone(),
            row.custody_domain.clone(),
        );
        let prior = totals.get(&key).map(|(_, value)| *value).unwrap_or(0);
        let total = prior
            .checked_add(row.delta_atoms)
            .ok_or(AbiErrorV1::Conservation("ZDEX route effect overflow"))?;
        totals.insert(key, (row.clone(), total));
    }
    Ok(totals
        .into_values()
        .filter_map(|(mut row, total)| {
            if total == 0 {
                None
            } else {
                row.delta_atoms = total;
                Some(row)
            }
        })
        .collect())
}

fn compose_effects_v1(
    candidate: &ZDEXPurchaseBurnRouteCandidateV1<'_>,
    occurrence_id: &RootV1,
) -> AbiResultV1<GlobalEconomicEffectPlanV1> {
    let purchase = candidate.purchase_journal;
    let burn = candidate.burn_journal;
    let mut conservation = vec![
        AssetConservationRowV1 {
            asset: purchase.quote_asset_id.to_string(),
            owned_and_custodied_pre_atoms: purchase.quote_owned_atoms,
            owned_and_custodied_post_atoms: purchase.quote_owned_atoms,
            supply_pre_atoms: purchase.quote_supply_atoms,
            supply_post_atoms: purchase.quote_supply_atoms,
            authorized_issue_atoms: 0,
            authorized_burn_atoms: 0,
        },
        AssetConservationRowV1 {
            asset: purchase.zdex_asset_id.to_string(),
            owned_and_custodied_pre_atoms: purchase.zdex_owned_atoms,
            owned_and_custodied_post_atoms: burn.zdex_owned_post_atoms,
            supply_pre_atoms: purchase.zdex_supply_atoms,
            supply_post_atoms: burn.zdex_supply_post_atoms,
            authorized_issue_atoms: 0,
            authorized_burn_atoms: burn.burned_zdex_atoms,
        },
    ];
    conservation.sort_by(|left, right| left.asset.cmp(&right.asset));
    let plan = GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: compose_rows_v1(candidate.purchase_effects, candidate.burn_effects)?,
        asset_conservation: conservation,
        fee_conservation: vec![],
        lane_writes: vec![LaneWriteV1 {
            lane_id: LaneIdV1::SPOT_LIQUIDITY,
            pre_root: purchase.pre_spot_lane_root.clone(),
            post_root: purchase.post_spot_lane_root.clone(),
        }],
        occurrence_consumptions: vec![occurrence_id.clone()],
        external_outbox_enqueue: vec![],
    };
    plan.validate()?;
    Ok(plan)
}

fn basic_binding_reject_code_v1(
    candidate: &ZDEXPurchaseBurnRouteCandidateV1<'_>,
    occurrence_id: &RootV1,
) -> Option<ZDEXPurchaseBurnRouteRejectCodeV1> {
    let route_id = &candidate.route_release.route_release_id;
    let purchase = candidate.purchase_journal;
    let burn = candidate.burn_journal;
    let budget = candidate.buyback_budget_occurrence;
    if route_id != &candidate.occurrence.route_release_id
        || route_id != &purchase.route_release_id
        || route_id != &burn.route_release_id
    {
        return Some(ZDEXPurchaseBurnRouteRejectCodeV1::ROUTE_BINDING_MISMATCH);
    }
    if &purchase.command_occurrence_id != occurrence_id
        || &burn.command_occurrence_id != occurrence_id
    {
        return Some(ZDEXPurchaseBurnRouteRejectCodeV1::OCCURRENCE_MISMATCH);
    }
    if purchase.profile_root != candidate.occurrence.profile_root
        || burn.profile_root != candidate.occurrence.profile_root
        || purchase.writer_epoch != burn.writer_epoch
        || purchase.chain_id != candidate.occurrence.chain_id
        || burn.chain_id != candidate.occurrence.chain_id
        || purchase.deployment_root != candidate.occurrence.deployment_root
        || burn.deployment_root != candidate.occurrence.deployment_root
    {
        return Some(ZDEXPurchaseBurnRouteRejectCodeV1::PROFILE_OR_EPOCH_MISMATCH);
    }
    if budget.chain_id != candidate.occurrence.chain_id
        || budget.deployment_root != candidate.occurrence.deployment_root
        || budget.profile_root != candidate.occurrence.profile_root
        || budget.writer_epoch != purchase.writer_epoch
        || budget.authorized_buyback_route_release_id != *route_id
        || budget.tokenomics_module_release_id != burn.tokenomics_module_release_id
        || budget.command_occurrence_id == *occurrence_id
        || purchase.quote_source_bucket_id != FEE_BUYBACK_PRINCIPAL_V1
    {
        return Some(ZDEXPurchaseBurnRouteRejectCodeV1::BUYBACK_BUDGET_MISMATCH);
    }
    None
}

fn governed_profile_reject_code_v1(
    candidate: &ZDEXPurchaseBurnRouteCandidateV1<'_>,
) -> Option<ZDEXPurchaseBurnRouteRejectCodeV1> {
    let governed = &candidate.governed_profile;
    if candidate.route_release != governed.route_release
        || candidate.occurrence.profile_root != governed.profile.profile_id
        || candidate.occurrence.route_release_id != governed.route_release.route_release_id
        || candidate.occurrence.command_kind != governed.route_release.command_kind
        || candidate.purchase_journal.writer_epoch != governed.profile.authority_epoch
        || candidate.purchase_journal.spot_module_release_id
            != governed.purchase_module_release.release_id
        || candidate.burn_journal.tokenomics_module_release_id
            != governed.burn_module_release.release_id
    {
        return Some(ZDEXPurchaseBurnRouteRejectCodeV1::GOVERNED_PROFILE_MISMATCH);
    }
    None
}

fn witness_reject_code_v1(
    candidate: &ZDEXPurchaseBurnRouteCandidateV1<'_>,
    occurrence_id: &RootV1,
) -> AbiResultV1<Option<ZDEXPurchaseBurnRouteRejectCodeV1>> {
    let route_id = &candidate.route_release.route_release_id;
    let governed = &candidate.governed_profile;
    let purchase = candidate.purchase_journal;
    let purchase_root = purchase.journal_root()?;
    let purchase_effect_plan_root = candidate.purchase_effects.effect_plan_root()?;
    if candidate.verified_purchase.module_release_id()
        != &governed.purchase_module_release.release_id
        || candidate.verified_purchase.expected_image_id()
            != &governed.purchase_module_release.guest_image_id
        || !candidate.verified_purchase.matches_route_input(
            purchase,
            ZDEXVerifiedLaneExpectationV1 {
                route_release_id: route_id,
                occurrence_id,
                profile_root: &candidate.occurrence.profile_root,
                writer_epoch: purchase.writer_epoch,
                journal_root: &purchase_root,
                effect_plan_root: &purchase_effect_plan_root,
            },
        )?
    {
        return Ok(Some(
            ZDEXPurchaseBurnRouteRejectCodeV1::PURCHASE_WITNESS_MISMATCH,
        ));
    }
    let burn = candidate.burn_journal;
    let burn_root = burn.journal_root()?;
    let burn_effect_plan_root = candidate.burn_effects.effect_plan_root()?;
    if candidate.verified_burn.module_release_id() != &governed.burn_module_release.release_id
        || candidate.verified_burn.expected_image_id()
            != &governed.burn_module_release.guest_image_id
        || !candidate.verified_burn.matches_route_input(
            burn,
            ZDEXVerifiedLaneExpectationV1 {
                route_release_id: route_id,
                occurrence_id,
                profile_root: &candidate.occurrence.profile_root,
                writer_epoch: burn.writer_epoch,
                journal_root: &burn_root,
                effect_plan_root: &burn_effect_plan_root,
            },
        )?
    {
        return Ok(Some(
            ZDEXPurchaseBurnRouteRejectCodeV1::BURN_WITNESS_MISMATCH,
        ));
    }
    if candidate.verified_buyback_budget.module_release_id()
        != &governed.burn_module_release.release_id
        || candidate.verified_buyback_budget.expected_image_id()
            != &governed.burn_module_release.guest_image_id
        || !candidate
            .verified_buyback_budget
            .matches_route_input(route_id, candidate.buyback_budget_occurrence)?
        || candidate.verified_buyback_budget.fee_ingress_atoms()
            != candidate.buyback_budget_occurrence.fee_charged_atoms
    {
        return Ok(Some(
            ZDEXPurchaseBurnRouteRejectCodeV1::BUYBACK_BUDGET_MISMATCH,
        ));
    }
    Ok(None)
}

fn economic_reject_code_v1(
    candidate: &ZDEXPurchaseBurnRouteCandidateV1<'_>,
) -> AbiResultV1<Option<ZDEXPurchaseBurnRouteRejectCodeV1>> {
    let purchase = candidate.purchase_journal;
    let burn = candidate.burn_journal;
    let budget = candidate.buyback_budget_occurrence;
    let execution_policy = candidate.governed_profile.buyback_execution_policy;
    let price_policy = candidate.governed_profile.price_safety_policy;
    let budget_root = budget.occurrence_root()?;
    let expected_consumed = vec![budget_root.to_string()];
    if budget_root == candidate.occurrence.occurrence_id()?
        || candidate.occurrence.consumed_object_ids != expected_consumed
    {
        return Ok(Some(
            ZDEXPurchaseBurnRouteRejectCodeV1::BUYBACK_BUDGET_MISMATCH,
        ));
    }
    let expected_quote_pool_bucket = zdex_pool_reserve_principal_v1(
        &execution_policy.pool_id,
        &execution_policy.quote_asset_id,
    )?;
    let expected_zdex_pool_bucket =
        zdex_pool_reserve_principal_v1(&execution_policy.pool_id, &execution_policy.zdex_asset_id)?;
    let expected_burn_bucket = zdex_occurrence_burn_port_v1(
        &candidate.occurrence.profile_root,
        &candidate.route_release.route_release_id,
        &candidate.occurrence.occurrence_id()?,
    )?;
    if purchase.buyback_execution_policy_root != execution_policy.policy_root()?
        || purchase.quote_asset_id != execution_policy.quote_asset_id
        || purchase.zdex_asset_id != execution_policy.zdex_asset_id
        || purchase.quote_pool_bucket_id != expected_quote_pool_bucket
        || purchase.zdex_pool_bucket_id != expected_zdex_pool_bucket
        || purchase.burn_bucket_id != expected_burn_bucket
    {
        return Ok(Some(
            ZDEXPurchaseBurnRouteRejectCodeV1::BUYBACK_EXECUTION_POLICY_MISMATCH,
        ));
    }
    let price_policy_root = price_policy.policy_root()?;
    if purchase.price_safety_policy_root != price_policy_root
        || candidate.verified_purchase.price_safety_policy_root() != Some(&price_policy_root)
        || candidate.verified_purchase.price_authority_root().is_none()
    {
        return Ok(Some(
            ZDEXPurchaseBurnRouteRejectCodeV1::PRICE_SAFETY_AUTHORITY_MISMATCH,
        ));
    }
    if purchase.zdex_asset_id != burn.zdex_asset_id {
        return Ok(Some(ZDEXPurchaseBurnRouteRejectCodeV1::ASSET_MISMATCH));
    }
    if burn.purchase_occurrence_root != purchase.journal_root()? {
        return Ok(Some(
            ZDEXPurchaseBurnRouteRejectCodeV1::PURCHASE_OCCURRENCE_MISMATCH,
        ));
    }
    if purchase.purchased_zdex_atoms != burn.burned_zdex_atoms {
        return Ok(Some(ZDEXPurchaseBurnRouteRejectCodeV1::AMOUNT_MISMATCH));
    }
    if purchase.burn_bucket_id != burn.burn_bucket_id
        || purchase.burn_bucket_post_atoms != burn.burn_bucket_pre_atoms
    {
        return Ok(Some(
            ZDEXPurchaseBurnRouteRejectCodeV1::BURN_BUCKET_MISMATCH,
        ));
    }
    if purchase.buyback_budget_occurrence_root != budget_root
        || burn.buyback_budget_occurrence_root != budget_root
        || purchase.quote_asset_id != budget.fee_asset_id
        || purchase.quote_amount_in_atoms != burn.authorized_quote_input_atoms
        || purchase.quote_amount_in_atoms != budget.buyback_quote_atoms()
    {
        return Ok(Some(
            ZDEXPurchaseBurnRouteRejectCodeV1::BUYBACK_BUDGET_MISMATCH,
        ));
    }
    if purchase.zdex_owned_atoms != burn.zdex_owned_pre_atoms
        || purchase.zdex_supply_atoms != burn.zdex_supply_pre_atoms
        || purchase.quote_owned_atoms != purchase.quote_supply_atoms
        || purchase.zdex_owned_atoms != purchase.zdex_supply_atoms
    {
        return Ok(Some(
            ZDEXPurchaseBurnRouteRejectCodeV1::CONSERVATION_HISTORY_DISCONNECTED,
        ));
    }
    Ok(None)
}

pub fn compose_zdex_purchase_burn_route_v1(
    candidate: ZDEXPurchaseBurnRouteCandidateV1<'_>,
) -> AbiResultV1<ZDEXPurchaseBurnRouteResultV1> {
    candidate.route_release.validate()?;
    candidate.occurrence.validate()?;
    candidate.buyback_budget_occurrence.validate()?;
    candidate.purchase_journal.validate()?;
    candidate.burn_journal.validate()?;
    candidate.purchase_effects.validate()?;
    candidate.burn_effects.validate()?;
    let occurrence_id = candidate.occurrence.occurrence_id()?;
    if let Some(code) = governed_profile_reject_code_v1(&candidate) {
        return Ok(reject_v1(code));
    }
    if let Some(code) = basic_binding_reject_code_v1(&candidate, &occurrence_id) {
        return Ok(reject_v1(code));
    }
    if let Some(code) = witness_reject_code_v1(&candidate, &occurrence_id)? {
        return Ok(reject_v1(code));
    }
    if let Some(code) = economic_reject_code_v1(&candidate)? {
        return Ok(reject_v1(code));
    }

    let route_id = &candidate.route_release.route_release_id;
    let purchase = candidate.purchase_journal;
    let burn = candidate.burn_journal;
    let purchase_root = purchase.journal_root()?;
    let burn_root = burn.journal_root()?;
    Ok(ZDEXPurchaseBurnRouteResultV1::Accepted(Box::new(
        ZDEXPurchaseBurnRouteAcceptedV1 {
            route_release_id: route_id.clone(),
            command_occurrence_id: occurrence_id.clone(),
            profile_root: candidate.occurrence.profile_root.clone(),
            writer_epoch: purchase.writer_epoch,
            ordered_lane_journal_roots: vec![purchase_root, burn_root],
            ordered_verified_binding_roots: vec![
                candidate.verified_purchase.binding_root()?,
                candidate.verified_burn.binding_root()?,
            ],
            verified_budget_binding_root: candidate.verified_buyback_budget.binding_root()?,
            buyback_execution_policy_root: candidate
                .governed_profile
                .buyback_execution_policy
                .policy_root()?,
            price_safety_policy_root: candidate
                .governed_profile
                .price_safety_policy
                .policy_root()?,
            price_authority_root: candidate
                .verified_purchase
                .price_authority_root()
                .ok_or(AbiErrorV1::InvalidBinding(
                    "ZDEX buyback price authority absent",
                ))?
                .clone(),
            effects: compose_effects_v1(&candidate, &occurrence_id)?,
            terminal_obligations_root: zdex_tokenomics_complete_lane_obligation_root_v1()?,
        },
    )))
}
