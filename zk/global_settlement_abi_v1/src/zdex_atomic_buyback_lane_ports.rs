//! Exact value-carrying ports for one same-occurrence ZDEX buy-and-burn.
//!
//! The constructor derives every field from closed purchase and burn journals
//! plus current-authority receipt witnesses. This is structural SHADOW
//! evidence and grants no lane, route, settlement, or publication authority.

use serde::{Deserialize, Serialize};

use crate::canonical::{hash_global_v1, validate_token_v1, AbiErrorV1, AbiResultV1, RootV1};
use crate::zdex_purchase_burn_receipt_verification::{
    GovernedVerifiedZDEXAMMPurchaseV2, GovernedVerifiedZDEXBurnV1,
};
use crate::zdex_purchase_burn_types::{
    zdex_occurrence_burn_port_v1, ZDEXAMMPurchaseJournalV2, ZDEXBurnJournalV1,
};

pub const ZDEX_ATOMIC_BUYBACK_LANE_PORT_CONTEXT_SCHEMA_V1: &str =
    "zenodex/zdex-atomic-buyback-lane-port-context/v1";
pub const ZDEX_ATOMIC_BUYBACK_LANE_PORTS_SCHEMA_V1: &str =
    "zenodex/zdex-atomic-buyback-lane-ports/v1";

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXAtomicBuybackLanePortContextV1 {
    pub schema: String,
    pub authority_head_root: RootV1,
    pub policy_registry_root: RootV1,
    pub verifier_binding_root: RootV1,
    pub profile_root: RootV1,
    pub route_release_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub spot_module_release_id: RootV1,
    pub tokenomics_module_release_id: RootV1,
    pub issue_burn_policy_root: RootV1,
    pub buyback_execution_policy_root: RootV1,
    pub price_safety_policy_root: RootV1,
    pub oracle_occurrence_root: RootV1,
    pub quote_asset_id: RootV1,
    pub zdex_asset_id: RootV1,
    pub quote_source_bucket_id: String,
    pub quote_pool_bucket_id: RootV1,
    pub zdex_pool_bucket_id: RootV1,
    pub burn_port_identity_root: RootV1,
    pub purchase_journal_root: RootV1,
    pub burn_journal_root: RootV1,
    pub purchase_leaf_binding_root: RootV1,
    pub burn_leaf_binding_root: RootV1,
}

impl ZDEXAtomicBuybackLanePortContextV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != ZDEX_ATOMIC_BUYBACK_LANE_PORT_CONTEXT_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidSchema);
        }
        for root in [
            &self.authority_head_root,
            &self.policy_registry_root,
            &self.verifier_binding_root,
            &self.profile_root,
            &self.route_release_id,
            &self.command_occurrence_id,
            &self.spot_module_release_id,
            &self.tokenomics_module_release_id,
            &self.issue_burn_policy_root,
            &self.buyback_execution_policy_root,
            &self.price_safety_policy_root,
            &self.oracle_occurrence_root,
            &self.quote_asset_id,
            &self.zdex_asset_id,
            &self.quote_pool_bucket_id,
            &self.zdex_pool_bucket_id,
            &self.burn_port_identity_root,
            &self.purchase_journal_root,
            &self.burn_journal_root,
            &self.purchase_leaf_binding_root,
            &self.burn_leaf_binding_root,
        ] {
            root.validate("atomic buyback lane-port context root", false)?;
        }
        validate_token_v1(
            &self.quote_source_bucket_id,
            "atomic buyback lane-port quote source",
        )?;
        if self.quote_asset_id == self.zdex_asset_id {
            return Err(AbiErrorV1::InvalidBinding(
                "atomic buyback distinct lane-port assets",
            ));
        }
        Ok(())
    }

    pub fn context_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("zdex-atomic-buyback-lane-port-context-v1", self)
    }
}

pub fn zdex_atomic_buyback_quote_flow_root_v1(
    context: &ZDEXAtomicBuybackLanePortContextV1,
    quote_amount_atoms: u128,
) -> AbiResultV1<RootV1> {
    context.validate()?;
    if quote_amount_atoms == 0 || quote_amount_atoms > i128::MAX.unsigned_abs() {
        return Err(AbiErrorV1::InvalidBounds(
            "atomic buyback quote-flow amount",
        ));
    }
    #[derive(Serialize)]
    struct QuoteFlow<'a> {
        schema: &'static str,
        context_root: RootV1,
        quote_asset_id: &'a RootV1,
        quote_source_bucket_id: &'a str,
        quote_pool_bucket_id: &'a RootV1,
        quote_amount_atoms: u128,
    }
    hash_global_v1(
        "zdex-atomic-buyback-quote-flow-v1",
        &QuoteFlow {
            schema: ZDEX_ATOMIC_BUYBACK_LANE_PORTS_SCHEMA_V1,
            context_root: context.context_root()?,
            quote_asset_id: &context.quote_asset_id,
            quote_source_bucket_id: &context.quote_source_bucket_id,
            quote_pool_bucket_id: &context.quote_pool_bucket_id,
            quote_amount_atoms,
        },
    )
}

pub fn zdex_atomic_buyback_purchased_zdex_flow_root_v1(
    context: &ZDEXAtomicBuybackLanePortContextV1,
    purchased_zdex_atoms: u128,
) -> AbiResultV1<RootV1> {
    context.validate()?;
    if purchased_zdex_atoms == 0 || purchased_zdex_atoms > i128::MAX.unsigned_abs() {
        return Err(AbiErrorV1::InvalidBounds(
            "atomic buyback purchased-ZDEX flow amount",
        ));
    }
    #[derive(Serialize)]
    struct PurchasedZDEXFlow<'a> {
        schema: &'static str,
        context_root: RootV1,
        zdex_asset_id: &'a RootV1,
        zdex_pool_bucket_id: &'a RootV1,
        burn_port_identity_root: &'a RootV1,
        purchased_zdex_atoms: u128,
    }
    hash_global_v1(
        "zdex-atomic-buyback-purchased-zdex-flow-v1",
        &PurchasedZDEXFlow {
            schema: ZDEX_ATOMIC_BUYBACK_LANE_PORTS_SCHEMA_V1,
            context_root: context.context_root()?,
            zdex_asset_id: &context.zdex_asset_id,
            zdex_pool_bucket_id: &context.zdex_pool_bucket_id,
            burn_port_identity_root: &context.burn_port_identity_root,
            purchased_zdex_atoms,
        },
    )
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXAtomicBuybackLanePortsV1 {
    pub schema: String,
    pub context: ZDEXAtomicBuybackLanePortContextV1,
    pub quote_flow_root: RootV1,
    pub purchased_zdex_flow_root: RootV1,
    pub tokenomics_quote_out_atoms: u128,
    pub spot_quote_in_atoms: u128,
    pub spot_zdex_out_atoms: u128,
    pub tokenomics_burn_in_atoms: u128,
}

impl ZDEXAtomicBuybackLanePortsV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != ZDEX_ATOMIC_BUYBACK_LANE_PORTS_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidSchema);
        }
        self.context.validate()?;
        self.quote_flow_root
            .validate("atomic buyback quote-flow root", false)?;
        self.purchased_zdex_flow_root
            .validate("atomic buyback purchased-ZDEX flow root", false)?;
        for amount in [
            self.tokenomics_quote_out_atoms,
            self.spot_quote_in_atoms,
            self.spot_zdex_out_atoms,
            self.tokenomics_burn_in_atoms,
        ] {
            if amount == 0 || amount > i128::MAX.unsigned_abs() {
                return Err(AbiErrorV1::InvalidBounds("atomic buyback lane-port amount"));
            }
        }
        if self.tokenomics_quote_out_atoms != self.spot_quote_in_atoms
            || self.spot_zdex_out_atoms != self.tokenomics_burn_in_atoms
            || self.quote_flow_root
                != zdex_atomic_buyback_quote_flow_root_v1(
                    &self.context,
                    self.tokenomics_quote_out_atoms,
                )?
            || self.purchased_zdex_flow_root
                != zdex_atomic_buyback_purchased_zdex_flow_root_v1(
                    &self.context,
                    self.spot_zdex_out_atoms,
                )?
        {
            return Err(AbiErrorV1::InvalidBinding(
                "atomic buyback exact lane-port pairing",
            ));
        }
        Ok(())
    }

    pub fn binding_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("zdex-atomic-buyback-lane-ports-v1", self)
    }
}

fn require_journal_pair_v1(
    purchase: &ZDEXAMMPurchaseJournalV2,
    burn: &ZDEXBurnJournalV1,
    expected_burn_port: &RootV1,
) -> AbiResultV1<()> {
    if burn.chain_id != purchase.chain_id
        || burn.deployment_root != purchase.deployment_root
        || burn.profile_root != purchase.profile_root
        || burn.writer_epoch != purchase.writer_epoch
        || burn.route_release_id != purchase.route_release_id
        || burn.command_occurrence_id != purchase.command_occurrence_id
        || burn.issue_burn_policy_root != purchase.issue_burn_policy_root
        || burn.buyback_budget_occurrence_root != purchase.buyback_budget_occurrence_root
        || burn.zdex_asset_id != purchase.zdex_asset_id
        || burn.purchase_occurrence_root != purchase.journal_root()?
        || burn.authorized_quote_input_atoms != purchase.quote_amount_in_atoms
        || burn.burned_zdex_atoms != purchase.purchased_zdex_atoms
        || purchase.burn_bucket_id != expected_burn_port.as_str()
        || burn.burn_bucket_id != expected_burn_port.as_str()
        || purchase.burn_bucket_post_atoms != burn.burn_bucket_pre_atoms
    {
        return Err(AbiErrorV1::InvalidBinding(
            "atomic buyback purchase and burn port binding",
        ));
    }
    Ok(())
}

fn require_receipt_pair_v1(
    purchase: &ZDEXAMMPurchaseJournalV2,
    burn: &ZDEXBurnJournalV1,
    verified_purchase: &GovernedVerifiedZDEXAMMPurchaseV2,
    verified_burn: &GovernedVerifiedZDEXBurnV1,
) -> AbiResultV1<()> {
    let purchase_leaf = verified_purchase.leaf();
    let burn_leaf = verified_burn.leaf();
    if purchase_leaf.route_release_id() != &purchase.route_release_id
        || purchase_leaf.module_release_id() != &purchase.spot_module_release_id
        || purchase_leaf.command_occurrence_id() != &purchase.command_occurrence_id
        || purchase_leaf.profile_root() != &purchase.profile_root
        || purchase_leaf.writer_epoch() != purchase.writer_epoch
        || purchase_leaf.journal_root() != &purchase.journal_root()?
        || purchase_leaf.effect_plan_root() != &purchase.effect_plan_root
        || burn_leaf.route_release_id() != &burn.route_release_id
        || burn_leaf.module_release_id() != &burn.tokenomics_module_release_id
        || burn_leaf.command_occurrence_id() != &burn.command_occurrence_id
        || burn_leaf.profile_root() != &burn.profile_root
        || burn_leaf.writer_epoch() != burn.writer_epoch
        || burn_leaf.journal_root() != &burn.journal_root()?
        || burn_leaf.effect_plan_root() != &burn.effect_plan_root
        || verified_purchase.authority_head_root() != verified_burn.authority_head_root()
        || verified_purchase.authority_generation() != verified_burn.authority_generation()
        || verified_purchase.policy_registry_root() != verified_burn.policy_registry_root()
        || verified_purchase.verifier_binding_root() != verified_burn.verifier_binding_root()
    {
        return Err(AbiErrorV1::InvalidBinding(
            "atomic buyback purchase and burn port binding",
        ));
    }
    Ok(())
}

fn build_lane_port_context_v1(
    purchase: &ZDEXAMMPurchaseJournalV2,
    burn: &ZDEXBurnJournalV1,
    verified_purchase: &GovernedVerifiedZDEXAMMPurchaseV2,
    verified_burn: &GovernedVerifiedZDEXBurnV1,
) -> AbiResultV1<ZDEXAtomicBuybackLanePortContextV1> {
    let expected_burn_port = RootV1::parse(
        zdex_occurrence_burn_port_v1(
            &purchase.profile_root,
            &purchase.route_release_id,
            &purchase.command_occurrence_id,
        )?,
        "atomic buyback burn-port identity",
        false,
    )?;
    let context = ZDEXAtomicBuybackLanePortContextV1 {
        schema: ZDEX_ATOMIC_BUYBACK_LANE_PORT_CONTEXT_SCHEMA_V1.to_owned(),
        authority_head_root: verified_purchase.authority_head_root().clone(),
        policy_registry_root: verified_purchase.policy_registry_root().clone(),
        verifier_binding_root: verified_purchase.verifier_binding_root().clone(),
        profile_root: purchase.profile_root.clone(),
        route_release_id: purchase.route_release_id.clone(),
        command_occurrence_id: purchase.command_occurrence_id.clone(),
        spot_module_release_id: purchase.spot_module_release_id.clone(),
        tokenomics_module_release_id: burn.tokenomics_module_release_id.clone(),
        issue_burn_policy_root: purchase.issue_burn_policy_root.clone(),
        buyback_execution_policy_root: purchase.buyback_execution_policy_root.clone(),
        price_safety_policy_root: purchase.price_safety_policy_root.clone(),
        oracle_occurrence_root: purchase.oracle_occurrence_root.clone(),
        quote_asset_id: purchase.quote_asset_id.clone(),
        zdex_asset_id: purchase.zdex_asset_id.clone(),
        quote_source_bucket_id: purchase.quote_source_bucket_id.clone(),
        quote_pool_bucket_id: RootV1::parse(
            &purchase.quote_pool_bucket_id,
            "atomic buyback quote-pool principal",
            false,
        )?,
        zdex_pool_bucket_id: RootV1::parse(
            &purchase.zdex_pool_bucket_id,
            "atomic buyback ZDEX-pool principal",
            false,
        )?,
        burn_port_identity_root: expected_burn_port,
        purchase_journal_root: purchase.journal_root()?,
        burn_journal_root: burn.journal_root()?,
        purchase_leaf_binding_root: verified_purchase.leaf().binding_root()?,
        burn_leaf_binding_root: verified_burn.leaf().binding_root()?,
    };
    context.validate()?;
    Ok(context)
}

pub fn derive_zdex_atomic_buyback_lane_ports_v1(
    purchase: &ZDEXAMMPurchaseJournalV2,
    burn: &ZDEXBurnJournalV1,
    verified_purchase: &GovernedVerifiedZDEXAMMPurchaseV2,
    verified_burn: &GovernedVerifiedZDEXBurnV1,
) -> AbiResultV1<ZDEXAtomicBuybackLanePortsV1> {
    purchase.validate()?;
    burn.validate()?;
    let expected_burn_port = RootV1::parse(
        zdex_occurrence_burn_port_v1(
            &purchase.profile_root,
            &purchase.route_release_id,
            &purchase.command_occurrence_id,
        )?,
        "atomic buyback burn-port identity",
        false,
    )?;
    require_journal_pair_v1(purchase, burn, &expected_burn_port)?;
    require_receipt_pair_v1(purchase, burn, verified_purchase, verified_burn)?;
    let context = build_lane_port_context_v1(purchase, burn, verified_purchase, verified_burn)?;
    let ports = ZDEXAtomicBuybackLanePortsV1 {
        schema: ZDEX_ATOMIC_BUYBACK_LANE_PORTS_SCHEMA_V1.to_owned(),
        quote_flow_root: zdex_atomic_buyback_quote_flow_root_v1(
            &context,
            purchase.quote_amount_in_atoms,
        )?,
        purchased_zdex_flow_root: zdex_atomic_buyback_purchased_zdex_flow_root_v1(
            &context,
            purchase.purchased_zdex_atoms,
        )?,
        context,
        tokenomics_quote_out_atoms: purchase.quote_amount_in_atoms,
        spot_quote_in_atoms: purchase.quote_amount_in_atoms,
        spot_zdex_out_atoms: purchase.purchased_zdex_atoms,
        tokenomics_burn_in_atoms: burn.burned_zdex_atoms,
    };
    ports.validate()?;
    Ok(ports)
}
