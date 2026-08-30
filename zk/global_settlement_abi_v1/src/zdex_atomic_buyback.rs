//! Same-occurrence fee allocation, governed Spot purchase, and exact ZDEX burn.
//!
//! The transition binds complete global and tokenomics prestates to opaque
//! verifier outputs, derives the only accepted accounting poststate, and emits
//! one canonical effect plan. Its accepted result retains a nonzero lane-
//! coordination obligation. This module grants no route, epoch, settlement, or
//! publication authority.

use std::collections::BTreeMap;

use serde::Serialize;

use crate::canonical::{hash_global_v1, AbiErrorV1, AbiResultV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1};
use crate::effects::{
    AssetConservationRowV1, EconomicEffectKindV1, EconomicEffectRowV1, GlobalEconomicEffectPlanV1,
    LaneWriteV1,
};
use crate::proof::{EconomicCommandOccurrenceV1, ReceiptKindV1};
use crate::release::{LaneIdV1, ReleaseStatusV1, RouteReleaseV1};
use crate::state::GlobalEconomicStateV1;
use crate::zdex_atomic_buyback_state::ZDEXAtomicBuybackTokenomicsStateV1;
use crate::zdex_buyback_price_authority::VerifiedZDEXBuybackPriceAuthorityV1;
use crate::zdex_buyback_spend::ZDEXBuybackSpendAcceptedV1;
use crate::zdex_fee_allocation_types::{ZDEXFeeDestinationV1, FEE_BUYBACK_PRINCIPAL_V1};
use crate::zdex_hyperdeflation::transition_zdex_purchase_and_burn_v1;
use crate::zdex_hyperdeflation_results::ZDEXPurchaseAndBurnResultV1;
use crate::zdex_hyperdeflation_route_refinement::{
    refine_zdex_burn_leaf_v1, ZDEXBurnLeafProjectionV1,
};
use crate::zdex_hyperdeflation_types::{
    ZDEXAmountBucketV1, ZDEXBurnRouteContextV1, ZDEXHyperdeflationPolicyV1,
    ZDEXPurchaseAndBurnCommandV1, ZDEXSupplyStateV1,
};
use crate::zdex_purchase_burn_effects::{burn_effects_v1, purchase_effects_v1};
use crate::zdex_purchase_burn_receipt_verification::{
    GovernedVerifiedZDEXAMMPurchaseV2, GovernedVerifiedZDEXBurnV1, ZDEXVerifiedLaneExpectationV1,
};
use crate::zdex_purchase_burn_route::GovernedZDEXAtomicBuybackProfileV1;
use crate::zdex_purchase_burn_types::{
    ZDEXAMMPurchaseJournalV2, AMM_POOL_CUSTODY_DOMAIN_V1, PROTOCOL_BUYBACK_CUSTODY_DOMAIN_V1,
    PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
};

pub const ZDEX_ATOMIC_BUYBACK_PENDING_SCHEMA_V1: &str = "zenodex/zdex-atomic-buyback-pending/v1";
pub const ZDEX_ATOMIC_BUYBACK_ACCEPTED_SCHEMA_V1: &str = "zenodex/zdex-atomic-buyback-accepted/v1";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(non_camel_case_types)]
pub enum ZDEXAtomicBuybackRejectCodeV1 {
    ROUTE_MISMATCH,
    GLOBAL_STATE_MISMATCH,
    SPEND_MISMATCH,
    PURCHASE_MISMATCH,
    PURCHASE_WITNESS_MISMATCH,
    TOKENOMICS_STATE_MISMATCH,
    BURN_REJECTED,
    BURN_WITNESS_MISMATCH,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXAtomicBuybackCandidateV1 {
    pub governed_profile: GovernedZDEXAtomicBuybackProfileV1,
    pub global_pre_state: GlobalEconomicStateV1,
    pub tokenomics_pre_state: ZDEXAtomicBuybackTokenomicsStateV1,
    pub occurrence: EconomicCommandOccurrenceV1,
    pub route: RouteReleaseV1,
    pub price_authority: VerifiedZDEXBuybackPriceAuthorityV1,
    pub verified_spend: ZDEXBuybackSpendAcceptedV1,
    pub purchase_journal: ZDEXAMMPurchaseJournalV2,
    pub purchase_effects: GlobalEconomicEffectPlanV1,
    pub verified_purchase: GovernedVerifiedZDEXAMMPurchaseV2,
    pub hyperdeflation_policy: ZDEXHyperdeflationPolicyV1,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXAtomicBuybackRejectedV1 {
    code: ZDEXAtomicBuybackRejectCodeV1,
    pre_state: ZDEXAtomicBuybackTokenomicsStateV1,
    post_state: ZDEXAtomicBuybackTokenomicsStateV1,
    effects: GlobalEconomicEffectPlanV1,
}

impl ZDEXAtomicBuybackRejectedV1 {
    pub fn code(&self) -> ZDEXAtomicBuybackRejectCodeV1 {
        self.code
    }

    pub fn pre_state(&self) -> &ZDEXAtomicBuybackTokenomicsStateV1 {
        &self.pre_state
    }

    pub fn post_state(&self) -> &ZDEXAtomicBuybackTokenomicsStateV1 {
        &self.post_state
    }

    pub fn effects(&self) -> &GlobalEconomicEffectPlanV1 {
        &self.effects
    }

    fn validate(&self) -> AbiResultV1<()> {
        self.pre_state.validate()?;
        self.post_state.validate()?;
        self.effects.validate()?;
        if self.pre_state != self.post_state || !self.effects.is_empty() {
            return Err(AbiErrorV1::InvalidBinding(
                "atomic buyback reject is exact no-op",
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXAtomicBuybackPendingV1 {
    candidate: ZDEXAtomicBuybackCandidateV1,
    pre_state: ZDEXAtomicBuybackTokenomicsStateV1,
    post_state: ZDEXAtomicBuybackTokenomicsStateV1,
    effects: GlobalEconomicEffectPlanV1,
    burn: ZDEXBurnLeafProjectionV1,
    burn_receipt_obligation_root: RootV1,
}

impl ZDEXAtomicBuybackPendingV1 {
    pub fn pre_state(&self) -> &ZDEXAtomicBuybackTokenomicsStateV1 {
        &self.pre_state
    }

    pub fn post_state(&self) -> &ZDEXAtomicBuybackTokenomicsStateV1 {
        &self.post_state
    }

    pub fn effects(&self) -> &GlobalEconomicEffectPlanV1 {
        &self.effects
    }

    pub fn burn(&self) -> &ZDEXBurnLeafProjectionV1 {
        &self.burn
    }

    pub fn burn_receipt_obligation_root(&self) -> &RootV1 {
        &self.burn_receipt_obligation_root
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXAtomicBuybackAcceptedV1 {
    pre_state: ZDEXAtomicBuybackTokenomicsStateV1,
    post_state: ZDEXAtomicBuybackTokenomicsStateV1,
    effects: GlobalEconomicEffectPlanV1,
    burn: ZDEXBurnLeafProjectionV1,
    terminal_obligations_root: RootV1,
}

impl ZDEXAtomicBuybackAcceptedV1 {
    pub fn pre_state(&self) -> &ZDEXAtomicBuybackTokenomicsStateV1 {
        &self.pre_state
    }

    pub fn post_state(&self) -> &ZDEXAtomicBuybackTokenomicsStateV1 {
        &self.post_state
    }

    pub fn effects(&self) -> &GlobalEconomicEffectPlanV1 {
        &self.effects
    }

    pub fn burn(&self) -> &ZDEXBurnLeafProjectionV1 {
        &self.burn
    }

    pub fn terminal_obligations_root(&self) -> &RootV1 {
        &self.terminal_obligations_root
    }

    fn validate(&self) -> AbiResultV1<()> {
        self.pre_state.validate()?;
        self.post_state.validate()?;
        self.effects.validate()?;
        self.burn.validate()?;
        if self.burn.accepted().post_state() != &self.post_state.tokenomics.supply_state
            || self.terminal_obligations_root
                != zdex_atomic_buyback_lane_coordination_obligation_root_v1(
                    &self.post_state,
                    &self.effects,
                    &self.burn,
                )?
        {
            return Err(AbiErrorV1::InvalidBinding(
                "atomic buyback accepted projection",
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ZDEXAtomicBuybackPrepareResultV1 {
    Pending(Box<ZDEXAtomicBuybackPendingV1>),
    Rejected(Box<ZDEXAtomicBuybackRejectedV1>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ZDEXAtomicBuybackFinalizeResultV1 {
    Accepted(Box<ZDEXAtomicBuybackAcceptedV1>),
    Rejected(Box<ZDEXAtomicBuybackRejectedV1>),
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

fn reject_v1(
    code: ZDEXAtomicBuybackRejectCodeV1,
    state: &ZDEXAtomicBuybackTokenomicsStateV1,
) -> AbiResultV1<ZDEXAtomicBuybackRejectedV1> {
    let rejected = ZDEXAtomicBuybackRejectedV1 {
        code,
        pre_state: state.clone(),
        post_state: state.clone(),
        effects: empty_effect_plan_v1(),
    };
    rejected.validate()?;
    Ok(rejected)
}

pub fn zdex_atomic_buyback_lane_coordination_obligation_root_v1(
    post_state: &ZDEXAtomicBuybackTokenomicsStateV1,
    effects: &GlobalEconomicEffectPlanV1,
    burn: &ZDEXBurnLeafProjectionV1,
) -> AbiResultV1<RootV1> {
    #[derive(Serialize)]
    struct Obligation<'a> {
        schema: &'static str,
        command_occurrence_id: &'a RootV1,
        burn_journal_root: RootV1,
        effect_plan_root: RootV1,
        post_tokenomics_state_root: RootV1,
        lane_writes: &'a [LaneWriteV1],
        requirement: &'static str,
    }

    post_state.validate()?;
    effects.validate()?;
    burn.validate()?;
    hash_global_v1(
        "zdex-atomic-buyback-lane-coordination-obligation-v1",
        &Obligation {
            schema: ZDEX_ATOMIC_BUYBACK_ACCEPTED_SCHEMA_V1,
            command_occurrence_id: &burn.journal().command_occurrence_id,
            burn_journal_root: burn.journal().journal_root()?,
            effect_plan_root: effects.effect_plan_root()?,
            post_tokenomics_state_root: post_state.state_root()?,
            lane_writes: &effects.lane_writes,
            requirement: "VERIFIED_COMPLETE_LANE_ROOTS_AND_GLOBAL_REFINEMENT",
        },
    )
}

fn burn_receipt_obligation_root_v1(burn: &ZDEXBurnLeafProjectionV1) -> AbiResultV1<RootV1> {
    #[derive(Serialize)]
    struct Obligation<'a> {
        schema: &'static str,
        command_occurrence_id: &'a RootV1,
        burn_journal_root: RootV1,
        burn_effect_plan_root: RootV1,
        requirement: &'static str,
    }

    burn.validate()?;
    hash_global_v1(
        "zdex-atomic-buyback-burn-receipt-obligation-v1",
        &Obligation {
            schema: ZDEX_ATOMIC_BUYBACK_PENDING_SCHEMA_V1,
            command_occurrence_id: &burn.journal().command_occurrence_id,
            burn_journal_root: burn.journal().journal_root()?,
            burn_effect_plan_root: burn.effects().effect_plan_root()?,
            requirement: "VERIFIED_TOKENOMICS_BURN_RECEIPT",
        },
    )
}

fn route_shape_matches_v1(candidate: &ZDEXAtomicBuybackCandidateV1) -> AbiResultV1<bool> {
    candidate.route.validate()?;
    candidate.occurrence.validate()?;
    candidate.hyperdeflation_policy.validate()?;
    let occurrence_id = candidate.occurrence.occurrence_id()?;
    let execution_policy_root = candidate.price_authority.execution_policy_root();
    let price_policy_root = candidate.price_authority.price_policy_root();
    Ok(candidate.governed_profile.matches_candidate_v1(
        &candidate.route,
        &candidate.occurrence,
        candidate.global_pre_state.writer_epoch,
        execution_policy_root,
        price_policy_root,
    ) && candidate.route.status == ReleaseStatusV1::SHADOW
        && !candidate.route.accepts_new_objects
        && candidate.route.command_kind == PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1
        && candidate.route.ordered_lanes == [LaneIdV1::SPOT_LIQUIDITY, LaneIdV1::ZDEX_TOKENOMICS]
        && candidate.route.module_release_ids.len() == 2
        && candidate.route.route_release_id == candidate.occurrence.route_release_id
        && candidate.route.command_kind == candidate.occurrence.command_kind
        && candidate.route.issue_burn_policy_root
            == candidate.hyperdeflation_policy.policy_root()?
        && candidate.occurrence.consumed_object_ids.is_empty()
        && candidate.purchase_journal.command_occurrence_id == occurrence_id)
}

fn global_state_matches_v1(candidate: &ZDEXAtomicBuybackCandidateV1) -> AbiResultV1<bool> {
    let state = &candidate.global_pre_state;
    state.validate()?;
    candidate.tokenomics_pre_state.validate()?;
    let state_root = state.state_root()?;
    let tokenomics_root = candidate.tokenomics_pre_state.state_root()?;
    let spot = state
        .lane_roots
        .iter()
        .find(|lane| lane.lane_id == LaneIdV1::SPOT_LIQUIDITY);
    let tokenomics = state
        .lane_roots
        .iter()
        .find(|lane| lane.lane_id == LaneIdV1::ZDEX_TOKENOMICS);
    let (Some(spot), Some(tokenomics)) = (spot, tokenomics) else {
        return Ok(false);
    };
    Ok(state_root == candidate.occurrence.pre_state_root
        && state_root == *candidate.price_authority.pre_state_root()
        && state.chain_id == candidate.occurrence.chain_id
        && state.deployment_root == candidate.occurrence.deployment_root
        && state.profile_root == candidate.occurrence.profile_root
        && state.writer_epoch == candidate.purchase_journal.writer_epoch
        && state.height.checked_add(1) == Some(candidate.occurrence.height)
        && !spot.enabled
        && !tokenomics.enabled
        && spot.module_release_id == candidate.route.module_release_ids[0]
        && tokenomics.module_release_id == candidate.route.module_release_ids[1]
        && spot.state_root == candidate.purchase_journal.pre_spot_lane_root
        && tokenomics.state_root == tokenomics_root)
}

fn global_asset_total_v1(
    state: &GlobalEconomicStateV1,
    asset: &RootV1,
) -> AbiResultV1<(u128, u128)> {
    let mut owned = 0_u128;
    for rows in [&state.balances, &state.custody, &state.reserves] {
        for row in rows.iter().filter(|row| row.asset == asset.as_str()) {
            owned = owned
                .checked_add(row.amount_atoms)
                .ok_or(AbiErrorV1::Conservation(
                    "atomic buyback global owned total",
                ))?;
        }
    }
    let supply = state
        .supplies
        .iter()
        .find(|row| row.asset == asset.as_str())
        .map(|row| row.amount_atoms)
        .ok_or(AbiErrorV1::InvalidBinding(
            "atomic buyback global asset supply",
        ))?;
    Ok((owned, supply))
}

fn spend_matches_v1(candidate: &ZDEXAtomicBuybackCandidateV1) -> AbiResultV1<bool> {
    let spend = &candidate.verified_spend;
    spend.validate()?;
    let purchase = &candidate.purchase_journal;
    let price_authority_root = candidate.price_authority.authority_root()?;
    let fee_pre = candidate
        .tokenomics_pre_state
        .fee_state_for(&purchase.quote_asset_id)?;
    let cadence_pre = candidate
        .tokenomics_pre_state
        .cadence_state_for(&purchase.quote_asset_id)?;
    Ok(spend.fee_allocation().pre_state == *fee_pre
        && spend.cadence_pre_state() == cadence_pre
        && spend.context().profile_root == candidate.occurrence.profile_root
        && spend.context().route_release_id == candidate.route.route_release_id
        && spend.context().command_occurrence_id == candidate.occurrence.occurrence_id()?
        && spend.context().current_height == candidate.occurrence.height
        && spend.context().safety_limit_binding_root == price_authority_root
        && spend.context().route_safe_quote_limit_atoms == purchase.route_safe_quote_limit_atoms
        && spend.intent().quote_asset_id == purchase.quote_asset_id
        && spend.intent().quote_spend_atoms == purchase.quote_amount_in_atoms
        && spend.fee_context().chain_id == candidate.occurrence.chain_id
        && spend.fee_context().deployment_root == candidate.occurrence.deployment_root
        && spend.fee_context().writer_epoch == candidate.global_pre_state.writer_epoch
        && spend.fee_context().tokenomics_module_release_id
            == candidate.route.module_release_ids[1])
}

fn buyback_balance_v1(
    state: &crate::zdex_fee_allocation_types::ZDEXFeeStateV1,
) -> AbiResultV1<u128> {
    let buyback = state
        .destination_balances
        .first()
        .ok_or(AbiErrorV1::InvalidBinding(
            "atomic buyback destination balance",
        ))?;
    if buyback.destination != ZDEXFeeDestinationV1::BUYBACK {
        return Err(AbiErrorV1::InvalidBinding(
            "atomic buyback destination order",
        ));
    }
    Ok(buyback.allocation_atoms)
}

fn purchase_matches_v1(candidate: &ZDEXAtomicBuybackCandidateV1) -> AbiResultV1<bool> {
    let purchase = &candidate.purchase_journal;
    purchase.validate()?;
    candidate.purchase_effects.validate()?;
    let spend = &candidate.verified_spend;
    let occurrence_id = candidate.occurrence.occurrence_id()?;
    let available = buyback_balance_v1(&spend.fee_allocation().post_state)?;
    let fee_post = buyback_balance_v1(spend.fee_post_state())?;
    let (quote_owned, quote_supply) =
        global_asset_total_v1(&candidate.global_pre_state, &purchase.quote_asset_id)?;
    let (zdex_owned, zdex_supply) =
        global_asset_total_v1(&candidate.global_pre_state, &purchase.zdex_asset_id)?;
    let fee_pre = &spend.fee_allocation().pre_state;
    Ok(candidate
        .governed_profile
        .matches_purchase_identity_v1(purchase, &candidate.occurrence)?
        && purchase.chain_id == candidate.occurrence.chain_id
        && purchase.deployment_root == candidate.occurrence.deployment_root
        && purchase.profile_root == candidate.occurrence.profile_root
        && purchase.route_release_id == candidate.route.route_release_id
        && purchase.command_occurrence_id == occurrence_id
        && purchase.spot_module_release_id == candidate.route.module_release_ids[0]
        && purchase.buyback_budget_occurrence_root == spend.intent().intent_root()?
        && purchase.buyback_execution_policy_root
            == *candidate.price_authority.execution_policy_root()
        && purchase.price_safety_policy_root == *candidate.price_authority.price_policy_root()
        && purchase.oracle_occurrence_root == *candidate.price_authority.price_occurrence_root()
        && purchase.quote_source_bucket_id == FEE_BUYBACK_PRINCIPAL_V1
        && purchase.quote_source_pre_atoms == available
        && purchase.quote_source_post_atoms == fee_post
        && purchase.quote_owned_atoms == quote_owned
        && purchase.quote_supply_atoms == quote_supply
        && fee_pre.owned_and_custodied_atoms == quote_owned
        && fee_pre.supply_atoms == quote_supply
        && purchase.zdex_owned_atoms == zdex_owned
        && purchase.zdex_supply_atoms == zdex_supply
        && candidate.purchase_effects == purchase_effects_v1(purchase)?)
}

fn purchase_witness_matches_v1(candidate: &ZDEXAtomicBuybackCandidateV1) -> AbiResultV1<bool> {
    let journal_root = candidate.purchase_journal.journal_root()?;
    let effect_plan_root = candidate.purchase_effects.effect_plan_root()?;
    let occurrence_id = candidate.occurrence.occurrence_id()?;
    let price_authority_root = candidate.price_authority.authority_root()?;
    let verified = candidate.verified_purchase.leaf();
    let expectation = ZDEXVerifiedLaneExpectationV1 {
        route_release_id: &candidate.route.route_release_id,
        occurrence_id: &occurrence_id,
        profile_root: &candidate.occurrence.profile_root,
        writer_epoch: candidate.global_pre_state.writer_epoch,
        journal_root: &journal_root,
        effect_plan_root: &effect_plan_root,
    };
    Ok(
        verified.module_release_id() == &candidate.route.module_release_ids[0]
            && verified.expected_image_id() == candidate.governed_profile.purchase_guest_image_id()
            && verified.price_authority_root() == Some(&price_authority_root)
            && verified.price_safety_policy_root()
                == Some(candidate.price_authority.price_policy_root())
            && verified.receipt_kind() == ReceiptKindV1::SUCCINCT
            && verified.matches_route_input(&candidate.purchase_journal, expectation)?
            && candidate.verified_purchase.authority_head_root()
                == candidate.governed_profile.authority_head_root()
            && candidate.verified_purchase.authority_generation()
                == candidate.governed_profile.authority_generation()
            && candidate.verified_purchase.verifier_binding_root()
                == candidate.governed_profile.verifier_binding_root()
            && candidate.verified_purchase.policy_registry_root()
                == candidate.governed_profile.policy_registry_root(),
    )
}

fn intermediate_supply_v1(
    state: &ZDEXSupplyStateV1,
    purchase: &ZDEXAMMPurchaseJournalV2,
) -> AbiResultV1<Option<ZDEXSupplyStateV1>> {
    state.validate()?;
    if state.live_supply_atoms != purchase.zdex_supply_atoms
        || state.bucket_atoms(&purchase.zdex_pool_bucket_id)? != Some(purchase.zdex_pool_pre_atoms)
        || state.bucket_atoms(&purchase.burn_bucket_id)?.is_some()
    {
        return Ok(None);
    }
    let mut buckets: Vec<_> = state
        .buckets
        .iter()
        .filter(|bucket| bucket.bucket_id != purchase.zdex_pool_bucket_id)
        .cloned()
        .collect();
    if purchase.zdex_pool_post_atoms > 0 {
        buckets.push(ZDEXAmountBucketV1 {
            bucket_id: purchase.zdex_pool_bucket_id.clone(),
            amount_atoms: purchase.zdex_pool_post_atoms,
        });
    }
    buckets.push(ZDEXAmountBucketV1 {
        bucket_id: purchase.burn_bucket_id.clone(),
        amount_atoms: purchase.purchased_zdex_atoms,
    });
    buckets.sort_by(|left, right| left.bucket_id.cmp(&right.bucket_id));
    let intermediate = ZDEXSupplyStateV1 {
        buckets,
        ..state.clone()
    };
    intermediate.validate()?;
    Ok(Some(intermediate))
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

fn aggregate_rows_v1(
    rows: impl IntoIterator<Item = EconomicEffectRowV1>,
) -> AbiResultV1<Vec<EconomicEffectRowV1>> {
    type Key = (String, String, String, String);
    let mut totals = BTreeMap::<Key, (EconomicEffectKindV1, i128)>::new();
    for row in rows {
        let key = (
            effect_kind_label_v1(row.kind).to_owned(),
            row.asset.clone(),
            row.principal.clone(),
            row.custody_domain.clone(),
        );
        let prior = totals.get(&key).map(|(_, value)| *value).unwrap_or(0);
        let total = prior
            .checked_add(row.delta_atoms)
            .ok_or(AbiErrorV1::InvalidBounds("atomic buyback aggregate effect"))?;
        totals.insert(key, (row.kind, total));
    }
    Ok(totals
        .into_iter()
        .filter_map(
            |((_, asset, principal, custody_domain), (kind, delta_atoms))| {
                (delta_atoms != 0).then_some(EconomicEffectRowV1 {
                    kind,
                    principal,
                    asset,
                    custody_domain,
                    delta_atoms,
                })
            },
        )
        .collect())
}

fn fee_funded_purchase_rows_v1(
    candidate: &ZDEXAtomicBuybackCandidateV1,
) -> AbiResultV1<Vec<EconomicEffectRowV1>> {
    let allocation = candidate.verified_spend.fee_allocation();
    let purchase = &candidate.purchase_journal;
    let buyback_allocated = allocation.occurrence.buyback_quote_atoms();
    let existing_buyback = buyback_balance_v1(&allocation.pre_state)?;
    let spend_from_existing = purchase.quote_amount_in_atoms.min(existing_buyback);
    let spend_from_new = purchase
        .quote_amount_in_atoms
        .checked_sub(spend_from_existing)
        .ok_or(AbiErrorV1::Conservation("atomic buyback new fee spend"))?;
    let retained_new =
        buyback_allocated
            .checked_sub(spend_from_new)
            .ok_or(AbiErrorV1::Conservation(
                "atomic buyback available fee allocation",
            ))?;
    let mut rows = Vec::new();
    for row in &allocation.effects.rows {
        if row.kind != EconomicEffectKindV1::FEE_ALLOCATION {
            rows.push(row.clone());
        } else if row.principal != FEE_BUYBACK_PRINCIPAL_V1 {
            rows.push(row.clone());
            rows.push(EconomicEffectRowV1 {
                kind: EconomicEffectKindV1::CUSTODY,
                principal: row.principal.clone(),
                asset: row.asset.clone(),
                custody_domain: row.custody_domain.clone(),
                delta_atoms: row.delta_atoms,
            });
        } else {
            for (principal, custody_domain, amount) in [
                (
                    FEE_BUYBACK_PRINCIPAL_V1.to_owned(),
                    PROTOCOL_BUYBACK_CUSTODY_DOMAIN_V1.to_owned(),
                    retained_new,
                ),
                (
                    purchase.quote_pool_bucket_id.clone(),
                    AMM_POOL_CUSTODY_DOMAIN_V1.to_owned(),
                    spend_from_new,
                ),
            ] {
                if amount == 0 {
                    continue;
                }
                let delta_atoms = i128::try_from(amount)
                    .map_err(|_| AbiErrorV1::InvalidBounds("atomic buyback fee effect width"))?;
                rows.push(EconomicEffectRowV1 {
                    kind: EconomicEffectKindV1::FEE_ALLOCATION,
                    principal: principal.clone(),
                    asset: row.asset.clone(),
                    custody_domain: custody_domain.clone(),
                    delta_atoms,
                });
                rows.push(EconomicEffectRowV1 {
                    kind: EconomicEffectKindV1::CUSTODY,
                    principal,
                    asset: row.asset.clone(),
                    custody_domain,
                    delta_atoms,
                });
            }
        }
    }
    for row in &candidate.purchase_effects.rows {
        if row.kind == EconomicEffectKindV1::CUSTODY
            && row.principal == purchase.quote_source_bucket_id
            && row.custody_domain == PROTOCOL_BUYBACK_CUSTODY_DOMAIN_V1
        {
            if spend_from_existing > 0 {
                rows.push(EconomicEffectRowV1 {
                    delta_atoms: -i128::try_from(spend_from_existing).map_err(|_| {
                        AbiErrorV1::InvalidBounds("atomic buyback existing reserve effect width")
                    })?,
                    ..row.clone()
                });
            }
        } else if row.kind == EconomicEffectKindV1::CUSTODY
            && row.principal == purchase.quote_pool_bucket_id
            && row.custody_domain == AMM_POOL_CUSTODY_DOMAIN_V1
        {
            if spend_from_existing > 0 {
                rows.push(EconomicEffectRowV1 {
                    delta_atoms: i128::try_from(spend_from_existing).map_err(|_| {
                        AbiErrorV1::InvalidBounds("atomic buyback existing pool effect width")
                    })?,
                    ..row.clone()
                });
            }
        } else {
            rows.push(row.clone());
        }
    }
    Ok(rows)
}

fn compose_effects_v1(
    candidate: &ZDEXAtomicBuybackCandidateV1,
    post_state: &ZDEXAtomicBuybackTokenomicsStateV1,
    burn: &ZDEXBurnLeafProjectionV1,
) -> AbiResultV1<GlobalEconomicEffectPlanV1> {
    let purchase = &candidate.purchase_journal;
    let mut rows = fee_funded_purchase_rows_v1(candidate)?;
    rows.extend(burn.effects().rows.iter().cloned());
    let mut conservation = vec![
        AssetConservationRowV1 {
            asset: purchase.quote_asset_id.as_str().to_owned(),
            owned_and_custodied_pre_atoms: purchase.quote_owned_atoms,
            owned_and_custodied_post_atoms: purchase.quote_owned_atoms,
            supply_pre_atoms: purchase.quote_supply_atoms,
            supply_post_atoms: purchase.quote_supply_atoms,
            authorized_issue_atoms: 0,
            authorized_burn_atoms: 0,
        },
        AssetConservationRowV1 {
            asset: purchase.zdex_asset_id.as_str().to_owned(),
            owned_and_custodied_pre_atoms: candidate
                .tokenomics_pre_state
                .tokenomics
                .supply_state
                .live_supply_atoms,
            owned_and_custodied_post_atoms: post_state.tokenomics.supply_state.live_supply_atoms,
            supply_pre_atoms: candidate
                .tokenomics_pre_state
                .tokenomics
                .supply_state
                .live_supply_atoms,
            supply_post_atoms: post_state.tokenomics.supply_state.live_supply_atoms,
            authorized_issue_atoms: 0,
            authorized_burn_atoms: purchase.purchased_zdex_atoms,
        },
    ];
    conservation.sort_by(|left, right| left.asset.cmp(&right.asset));
    let effects = GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: aggregate_rows_v1(rows)?,
        asset_conservation: conservation,
        fee_conservation: candidate
            .verified_spend
            .fee_allocation()
            .effects
            .fee_conservation
            .clone(),
        lane_writes: vec![
            LaneWriteV1 {
                lane_id: LaneIdV1::SPOT_LIQUIDITY,
                pre_root: purchase.pre_spot_lane_root.clone(),
                post_root: purchase.post_spot_lane_root.clone(),
            },
            LaneWriteV1 {
                lane_id: LaneIdV1::ZDEX_TOKENOMICS,
                pre_root: candidate.tokenomics_pre_state.state_root()?,
                post_root: post_state.state_root()?,
            },
        ],
        occurrence_consumptions: vec![candidate.occurrence.occurrence_id()?],
        external_outbox_enqueue: vec![],
    };
    effects.validate()?;
    Ok(effects)
}

pub fn prepare_zdex_atomic_buyback_v1(
    candidate: &ZDEXAtomicBuybackCandidateV1,
) -> AbiResultV1<ZDEXAtomicBuybackPrepareResultV1> {
    candidate.purchase_journal.validate()?;
    if !route_shape_matches_v1(candidate)? {
        return Ok(ZDEXAtomicBuybackPrepareResultV1::Rejected(Box::new(
            reject_v1(
                ZDEXAtomicBuybackRejectCodeV1::ROUTE_MISMATCH,
                &candidate.tokenomics_pre_state,
            )?,
        )));
    }
    if !global_state_matches_v1(candidate)? {
        return Ok(ZDEXAtomicBuybackPrepareResultV1::Rejected(Box::new(
            reject_v1(
                ZDEXAtomicBuybackRejectCodeV1::GLOBAL_STATE_MISMATCH,
                &candidate.tokenomics_pre_state,
            )?,
        )));
    }
    if !spend_matches_v1(candidate)? {
        return Ok(ZDEXAtomicBuybackPrepareResultV1::Rejected(Box::new(
            reject_v1(
                ZDEXAtomicBuybackRejectCodeV1::SPEND_MISMATCH,
                &candidate.tokenomics_pre_state,
            )?,
        )));
    }
    if !purchase_matches_v1(candidate)? {
        return Ok(ZDEXAtomicBuybackPrepareResultV1::Rejected(Box::new(
            reject_v1(
                ZDEXAtomicBuybackRejectCodeV1::PURCHASE_MISMATCH,
                &candidate.tokenomics_pre_state,
            )?,
        )));
    }
    if !purchase_witness_matches_v1(candidate)? {
        return Ok(ZDEXAtomicBuybackPrepareResultV1::Rejected(Box::new(
            reject_v1(
                ZDEXAtomicBuybackRejectCodeV1::PURCHASE_WITNESS_MISMATCH,
                &candidate.tokenomics_pre_state,
            )?,
        )));
    }

    let Some(intermediate) = intermediate_supply_v1(
        &candidate.tokenomics_pre_state.tokenomics.supply_state,
        &candidate.purchase_journal,
    )?
    else {
        return Ok(ZDEXAtomicBuybackPrepareResultV1::Rejected(Box::new(
            reject_v1(
                ZDEXAtomicBuybackRejectCodeV1::TOKENOMICS_STATE_MISMATCH,
                &candidate.tokenomics_pre_state,
            )?,
        )));
    };
    let purchase_root = candidate.purchase_journal.journal_root()?;
    let burn_context = ZDEXBurnRouteContextV1 {
        route_release_id: candidate.route.route_release_id.clone(),
        policy_root: candidate.hyperdeflation_policy.policy_root()?,
        purchase_occurrence_root: purchase_root.clone(),
        burn_source_bucket_id: candidate.purchase_journal.burn_bucket_id.clone(),
        purchased_zdex_atoms: candidate.purchase_journal.purchased_zdex_atoms,
        source_reserve_floor_atoms: 0,
        remaining_epoch_burn_cap_atoms: intermediate.remaining_epoch_burn_cap_atoms,
        route_safe_output_cap_atoms: candidate.purchase_journal.purchased_zdex_atoms,
        burn_budget_epoch: intermediate.burn_budget_epoch,
    };
    let burn_command = ZDEXPurchaseAndBurnCommandV1 {
        expected_pre_state_root: intermediate.state_root()?,
        expected_precision_epoch: intermediate.precision_epoch,
        expected_purchase_occurrence_root: purchase_root,
        source_bucket_id: candidate.purchase_journal.burn_bucket_id.clone(),
        purchased_zdex_atoms: candidate.purchase_journal.purchased_zdex_atoms,
    };
    let burn_accepted = match transition_zdex_purchase_and_burn_v1(
        &candidate.hyperdeflation_policy,
        &intermediate,
        &burn_context,
        &burn_command,
    )? {
        ZDEXPurchaseAndBurnResultV1::Accepted(accepted) => *accepted,
        ZDEXPurchaseAndBurnResultV1::Rejected(_) => {
            return Ok(ZDEXAtomicBuybackPrepareResultV1::Rejected(Box::new(
                reject_v1(
                    ZDEXAtomicBuybackRejectCodeV1::BURN_REJECTED,
                    &candidate.tokenomics_pre_state,
                )?,
            )))
        }
    };
    let burn = refine_zdex_burn_leaf_v1(
        &burn_accepted,
        &candidate.purchase_journal,
        &candidate.route.module_release_ids[1],
    )?;
    let mut post_state = candidate.tokenomics_pre_state.with_buyback_result(
        candidate.verified_spend.fee_post_state(),
        candidate.verified_spend.cadence_post_state(),
    )?;
    post_state.tokenomics.supply_state = burn_accepted.post_state().clone();
    post_state.validate()?;
    let effects = compose_effects_v1(candidate, &post_state, &burn)?;
    let pending = ZDEXAtomicBuybackPendingV1 {
        candidate: candidate.clone(),
        pre_state: candidate.tokenomics_pre_state.clone(),
        post_state,
        effects,
        burn_receipt_obligation_root: burn_receipt_obligation_root_v1(&burn)?,
        burn,
    };
    Ok(ZDEXAtomicBuybackPrepareResultV1::Pending(Box::new(pending)))
}

pub fn finalize_zdex_atomic_buyback_v1(
    pending: &ZDEXAtomicBuybackPendingV1,
    verified_burn: &GovernedVerifiedZDEXBurnV1,
) -> AbiResultV1<ZDEXAtomicBuybackFinalizeResultV1> {
    let recomputed = prepare_zdex_atomic_buyback_v1(&pending.candidate)?;
    let ZDEXAtomicBuybackPrepareResultV1::Pending(recomputed) = recomputed else {
        return Ok(ZDEXAtomicBuybackFinalizeResultV1::Rejected(Box::new(
            reject_v1(
                ZDEXAtomicBuybackRejectCodeV1::BURN_WITNESS_MISMATCH,
                &pending.pre_state,
            )?,
        )));
    };
    if *recomputed != *pending {
        return Ok(ZDEXAtomicBuybackFinalizeResultV1::Rejected(Box::new(
            reject_v1(
                ZDEXAtomicBuybackRejectCodeV1::BURN_WITNESS_MISMATCH,
                &pending.pre_state,
            )?,
        )));
    }
    let journal_root = pending.burn.journal().journal_root()?;
    let effect_plan_root = burn_effects_v1(pending.burn.journal())?.effect_plan_root()?;
    let occurrence_id = pending.candidate.occurrence.occurrence_id()?;
    let expectation = ZDEXVerifiedLaneExpectationV1 {
        route_release_id: &pending.candidate.route.route_release_id,
        occurrence_id: &occurrence_id,
        profile_root: &pending.candidate.occurrence.profile_root,
        writer_epoch: pending.candidate.global_pre_state.writer_epoch,
        journal_root: &journal_root,
        effect_plan_root: &effect_plan_root,
    };
    let verified = verified_burn.leaf();
    let witness_matches = verified.module_release_id()
        == &pending.candidate.route.module_release_ids[1]
        && verified.expected_image_id() == pending.candidate.governed_profile.burn_guest_image_id()
        && verified.price_authority_root().is_none()
        && verified.price_safety_policy_root().is_none()
        && verified.receipt_kind() == ReceiptKindV1::SUCCINCT
        && verified.matches_route_input(pending.burn.journal(), expectation)?
        && verified_burn.authority_head_root()
            == pending.candidate.governed_profile.authority_head_root()
        && verified_burn.authority_generation()
            == pending.candidate.governed_profile.authority_generation()
        && verified_burn.verifier_binding_root()
            == pending.candidate.governed_profile.verifier_binding_root()
        && verified_burn.policy_registry_root()
            == pending.candidate.governed_profile.policy_registry_root();
    if !witness_matches {
        return Ok(ZDEXAtomicBuybackFinalizeResultV1::Rejected(Box::new(
            reject_v1(
                ZDEXAtomicBuybackRejectCodeV1::BURN_WITNESS_MISMATCH,
                &pending.pre_state,
            )?,
        )));
    }
    let terminal_obligations_root = zdex_atomic_buyback_lane_coordination_obligation_root_v1(
        &pending.post_state,
        &pending.effects,
        &pending.burn,
    )?;
    let accepted = ZDEXAtomicBuybackAcceptedV1 {
        pre_state: pending.pre_state.clone(),
        post_state: pending.post_state.clone(),
        effects: pending.effects.clone(),
        burn: pending.burn.clone(),
        terminal_obligations_root,
    };
    accepted.validate()?;
    Ok(ZDEXAtomicBuybackFinalizeResultV1::Accepted(Box::new(
        accepted,
    )))
}
