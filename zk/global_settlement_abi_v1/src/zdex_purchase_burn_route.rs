use std::collections::BTreeMap;

use serde::Serialize;

use crate::canonical::{hash_global_v1, AbiErrorV1, AbiResultV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1};
use crate::effects::{
    AssetConservationRowV1, EconomicEffectKindV1, EconomicEffectRowV1, GlobalEconomicEffectPlanV1,
    LaneWriteV1,
};
use crate::proof::EconomicCommandOccurrenceV1;
use crate::release::{LaneIdV1, RouteReleaseV1};
use crate::zdex_fee_allocation_receipt_verification::VerifiedZDEXFeeAllocationV1;
use crate::zdex_fee_allocation_types::{ZDEXFeeAllocationOccurrenceV1, FEE_BUYBACK_PRINCIPAL_V1};
use crate::zdex_purchase_burn_receipt_verification::{
    VerifiedZDEXAMMPurchaseV1, VerifiedZDEXBurnV1, ZDEXVerifiedLaneExpectationV1,
};
use crate::zdex_purchase_burn_types::{ZDEXAMMPurchaseJournalV1, ZDEXBurnJournalV1};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(non_camel_case_types)]
pub enum ZDEXPurchaseBurnRouteRejectCodeV1 {
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
    CONSERVATION_HISTORY_DISCONNECTED,
}

pub struct ZDEXPurchaseBurnRouteCandidateV1<'a> {
    pub route_release: &'a RouteReleaseV1,
    pub occurrence: &'a EconomicCommandOccurrenceV1,
    pub buyback_budget_occurrence: &'a ZDEXFeeAllocationOccurrenceV1,
    pub verified_buyback_budget: &'a VerifiedZDEXFeeAllocationV1,
    pub purchase_journal: &'a ZDEXAMMPurchaseJournalV1,
    pub purchase_effects: &'a GlobalEconomicEffectPlanV1,
    pub verified_purchase: &'a VerifiedZDEXAMMPurchaseV1,
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
    pub effects: GlobalEconomicEffectPlanV1,
    pub terminal_obligations_root: RootV1,
}

impl ZDEXPurchaseBurnRouteAcceptedV1 {
    pub fn composition_root(&self) -> AbiResultV1<RootV1> {
        self.effects.validate()?;
        self.terminal_obligations_root
            .validate("ZDEX route terminal obligations", true)?;
        #[derive(Serialize)]
        struct Composition<'a> {
            schema: &'static str,
            route_release_id: &'a RootV1,
            command_occurrence_id: &'a RootV1,
            profile_root: &'a RootV1,
            writer_epoch: u64,
            ordered_lane_journal_roots: &'a [RootV1],
            ordered_verified_binding_roots: &'a [RootV1],
            verified_budget_binding_root: &'a RootV1,
            effect_plan_root: RootV1,
            terminal_obligations_root: &'a RootV1,
        }
        hash_global_v1(
            "zdex-purchase-burn-route-composition-v1",
            &Composition {
                schema: GLOBAL_SETTLEMENT_ABI_V1,
                route_release_id: &self.route_release_id,
                command_occurrence_id: &self.command_occurrence_id,
                profile_root: &self.profile_root,
                writer_epoch: self.writer_epoch,
                ordered_lane_journal_roots: &self.ordered_lane_journal_roots,
                ordered_verified_binding_roots: &self.ordered_verified_binding_roots,
                verified_budget_binding_root: &self.verified_budget_binding_root,
                effect_plan_root: self.effects.effect_plan_root()?,
                terminal_obligations_root: &self.terminal_obligations_root,
            },
        )
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXPurchaseBurnRouteRejectedV1 {
    pub code: ZDEXPurchaseBurnRouteRejectCodeV1,
    pub effects: GlobalEconomicEffectPlanV1,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ZDEXPurchaseBurnRouteResultV1 {
    Accepted(ZDEXPurchaseBurnRouteAcceptedV1),
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

fn tokenomics_coordinator_obligation_root_v1() -> AbiResultV1<RootV1> {
    #[derive(Serialize)]
    struct Requirement {
        schema: &'static str,
        lane_id: LaneIdV1,
        requirement: &'static str,
    }
    hash_global_v1(
        "zdex-tokenomics-coordinator-obligation-v1",
        &Requirement {
            schema: GLOBAL_SETTLEMENT_ABI_V1,
            lane_id: LaneIdV1::ZDEX_TOKENOMICS,
            requirement: "VERIFIED_COMPLETE_LANE_ROOT",
        },
    )
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

fn witness_reject_code_v1(
    candidate: &ZDEXPurchaseBurnRouteCandidateV1<'_>,
    occurrence_id: &RootV1,
) -> AbiResultV1<Option<ZDEXPurchaseBurnRouteRejectCodeV1>> {
    let route_id = &candidate.route_release.route_release_id;
    let purchase = candidate.purchase_journal;
    let purchase_root = purchase.journal_root()?;
    let purchase_effect_plan_root = candidate.purchase_effects.effect_plan_root()?;
    if !candidate.verified_purchase.matches_route_input(
        purchase,
        ZDEXVerifiedLaneExpectationV1 {
            route_release_id: route_id,
            occurrence_id,
            profile_root: &candidate.occurrence.profile_root,
            writer_epoch: purchase.writer_epoch,
            journal_root: &purchase_root,
            effect_plan_root: &purchase_effect_plan_root,
        },
    )? {
        return Ok(Some(
            ZDEXPurchaseBurnRouteRejectCodeV1::PURCHASE_WITNESS_MISMATCH,
        ));
    }
    let burn = candidate.burn_journal;
    let burn_root = burn.journal_root()?;
    let burn_effect_plan_root = candidate.burn_effects.effect_plan_root()?;
    if !candidate.verified_burn.matches_route_input(
        burn,
        ZDEXVerifiedLaneExpectationV1 {
            route_release_id: route_id,
            occurrence_id,
            profile_root: &candidate.occurrence.profile_root,
            writer_epoch: burn.writer_epoch,
            journal_root: &burn_root,
            effect_plan_root: &burn_effect_plan_root,
        },
    )? {
        return Ok(Some(
            ZDEXPurchaseBurnRouteRejectCodeV1::BURN_WITNESS_MISMATCH,
        ));
    }
    if !candidate
        .verified_buyback_budget
        .matches_route_input(route_id, candidate.buyback_budget_occurrence)?
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
    let budget_root = budget.occurrence_root()?;
    if purchase.buyback_budget_occurrence_root != budget_root
        || burn.buyback_budget_occurrence_root != budget_root
        || purchase.quote_asset_id != budget.fee_asset_id
        || purchase.quote_amount_in_atoms != burn.authorized_quote_input_atoms
        || purchase.quote_amount_in_atoms != budget.buyback_quote_atoms()
        || budget_root == candidate.occurrence.occurrence_id()?
        || candidate.occurrence.consumed_object_ids != vec![budget_root.to_string()]
    {
        return Ok(Some(
            ZDEXPurchaseBurnRouteRejectCodeV1::BUYBACK_BUDGET_MISMATCH,
        ));
    }
    if purchase.zdex_owned_atoms != burn.zdex_owned_pre_atoms
        || purchase.zdex_supply_atoms != burn.zdex_supply_pre_atoms
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
    Ok(ZDEXPurchaseBurnRouteResultV1::Accepted(
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
            effects: compose_effects_v1(&candidate, &occurrence_id)?,
            terminal_obligations_root: tokenomics_coordinator_obligation_root_v1()?,
        },
    ))
}
