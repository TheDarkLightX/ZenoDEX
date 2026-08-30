//! Exact pre-state and Oracle authority for one ZDEX buyback price envelope.

use serde::Serialize;

use crate::canonical::{hash_global_v1, AbiErrorV1, AbiResultV1, RootV1};
use crate::proof::EconomicCommandOccurrenceV1;
use crate::release::RouteReleaseV1;
use crate::state::GlobalEconomicStateV1;
use crate::zdex_buyback_price_safety::{
    verify_zdex_buyback_price_safety_v1, VerifiedZDEXBuybackPriceSafetyV1,
    ZDEXBuybackOraclePriceOccurrenceV1, ZDEXBuybackPriceSafetyObservationV1,
    ZDEXBuybackPriceSafetyPolicyV1, ZDEXBuybackPriceSafetyResultV1,
    ZDEX_BUYBACK_PRICE_SAFETY_OBSERVATION_SCHEMA_V1,
};
use crate::zdex_purchase_burn_types::{
    zdex_pool_reserve_principal_v1, ZDEXBuybackExecutionPolicyV1, AMM_POOL_CUSTODY_DOMAIN_V1,
};

pub const VERIFIED_ZDEX_BUYBACK_PRICE_AUTHORITY_SCHEMA_V1: &str =
    "zenodex/verified-zdex-buyback-price-authority/v1";

pub struct ZDEXBuybackPriceAuthorityCandidateV1<'a> {
    pub pre_state: &'a GlobalEconomicStateV1,
    pub route: &'a RouteReleaseV1,
    pub occurrence: &'a EconomicCommandOccurrenceV1,
    pub execution_policy: &'a ZDEXBuybackExecutionPolicyV1,
    pub price_policy: &'a ZDEXBuybackPriceSafetyPolicyV1,
    pub price_occurrence: &'a ZDEXBuybackOraclePriceOccurrenceV1,
    pub route_safe_quote_limit_atoms: u128,
    pub minimum_output_atoms: u128,
    pub expected_quote_reserve_atoms: u128,
    pub expected_zdex_reserve_atoms: u128,
    pub quote_amount_in_atoms: u128,
    pub purchased_zdex_atoms: u128,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifiedZDEXBuybackPriceAuthorityV1 {
    pre_state_root: RootV1,
    command_occurrence_id: RootV1,
    execution_policy_root: RootV1,
    price_policy_root: RootV1,
    price_occurrence_root: RootV1,
    price_safety: VerifiedZDEXBuybackPriceSafetyV1,
}

impl VerifiedZDEXBuybackPriceAuthorityV1 {
    pub fn pre_state_root(&self) -> &RootV1 {
        &self.pre_state_root
    }

    pub fn command_occurrence_id(&self) -> &RootV1 {
        &self.command_occurrence_id
    }

    pub fn execution_policy_root(&self) -> &RootV1 {
        &self.execution_policy_root
    }

    pub fn price_policy_root(&self) -> &RootV1 {
        &self.price_policy_root
    }

    pub fn price_occurrence_root(&self) -> &RootV1 {
        &self.price_occurrence_root
    }

    pub fn price_safety_binding_root(&self) -> AbiResultV1<RootV1> {
        self.price_safety.binding_root()
    }

    pub fn authority_root(&self) -> AbiResultV1<RootV1> {
        #[derive(Serialize)]
        struct Binding<'a> {
            schema: &'static str,
            pre_state_root: &'a RootV1,
            command_occurrence_id: &'a RootV1,
            execution_policy_root: &'a RootV1,
            price_policy_root: &'a RootV1,
            price_occurrence_root: &'a RootV1,
            price_safety_binding_root: RootV1,
        }
        hash_global_v1(
            "verified-zdex-buyback-price-authority-v1",
            &Binding {
                schema: VERIFIED_ZDEX_BUYBACK_PRICE_AUTHORITY_SCHEMA_V1,
                pre_state_root: &self.pre_state_root,
                command_occurrence_id: &self.command_occurrence_id,
                execution_policy_root: &self.execution_policy_root,
                price_policy_root: &self.price_policy_root,
                price_occurrence_root: &self.price_occurrence_root,
                price_safety_binding_root: self.price_safety_binding_root()?,
            },
        )
    }
}

fn require_context_v1(
    candidate: &ZDEXBuybackPriceAuthorityCandidateV1<'_>,
    pre_state_root: &RootV1,
    execution_policy_root: &RootV1,
    price_policy_root: &RootV1,
) -> AbiResultV1<RootV1> {
    let expected_height = candidate
        .pre_state
        .height
        .checked_add(1)
        .ok_or(AbiErrorV1::InvalidBounds("ZDEX buyback command height"))?;
    let occurrence_id = candidate.occurrence.occurrence_id()?;
    if candidate.route.oracle_policy_root != *price_policy_root
        || candidate.occurrence.chain_id != candidate.pre_state.chain_id
        || candidate.occurrence.deployment_root != candidate.pre_state.deployment_root
        || candidate.occurrence.profile_root != candidate.pre_state.profile_root
        || candidate.occurrence.pre_state_root != *pre_state_root
        || candidate.occurrence.route_release_id != candidate.route.route_release_id
        || candidate.occurrence.command_kind != candidate.route.command_kind
        || candidate.occurrence.height != expected_height
        || candidate.price_occurrence.oracle_id != candidate.price_policy.oracle_id
        || candidate.price_occurrence.quote_asset_id != candidate.execution_policy.quote_asset_id
        || candidate.price_occurrence.zdex_asset_id != candidate.execution_policy.zdex_asset_id
        || candidate.execution_policy.policy_root()? != *execution_policy_root
    {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX buyback price authority context",
        ));
    }
    Ok(occurrence_id)
}

fn require_finalized_oracle_v1(
    candidate: &ZDEXBuybackPriceAuthorityCandidateV1<'_>,
    price_occurrence_root: &RootV1,
) -> AbiResultV1<()> {
    let occurrence = candidate
        .pre_state
        .oracle_occurrences
        .iter()
        .find(|row| row.oracle_id == candidate.price_policy.oracle_id)
        .ok_or(AbiErrorV1::InvalidBinding(
            "ZDEX buyback Oracle occurrence absent",
        ))?;
    if !occurrence.finalized
        || occurrence.occurrence_root != *price_occurrence_root
        || occurrence.observed_height != candidate.price_occurrence.observed_height
        || occurrence.observed_height > candidate.pre_state.height
        || candidate.occurrence.height - occurrence.observed_height
            > candidate.price_policy.maximum_oracle_age_blocks
    {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX buyback Oracle occurrence authority",
        ));
    }
    Ok(())
}

fn require_committed_reserves_v1(
    candidate: &ZDEXBuybackPriceAuthorityCandidateV1<'_>,
) -> AbiResultV1<(u128, u128)> {
    let quote_principal = zdex_pool_reserve_principal_v1(
        &candidate.execution_policy.pool_id,
        &candidate.execution_policy.quote_asset_id,
    )?;
    let zdex_principal = zdex_pool_reserve_principal_v1(
        &candidate.execution_policy.pool_id,
        &candidate.execution_policy.zdex_asset_id,
    )?;
    let amount = |principal: &str, asset: &RootV1| {
        candidate
            .pre_state
            .custody
            .iter()
            .find(|row| {
                row.owner == principal
                    && row.asset == asset.as_str()
                    && row.custody_domain == AMM_POOL_CUSTODY_DOMAIN_V1
            })
            .map(|row| row.amount_atoms)
    };
    let quote_reserve = amount(&quote_principal, &candidate.execution_policy.quote_asset_id)
        .ok_or(AbiErrorV1::InvalidBinding(
            "ZDEX buyback quote reserve absent",
        ))?;
    let zdex_reserve = amount(&zdex_principal, &candidate.execution_policy.zdex_asset_id).ok_or(
        AbiErrorV1::InvalidBinding("ZDEX buyback ZDEX reserve absent"),
    )?;
    Ok((quote_reserve, zdex_reserve))
}

pub fn verify_zdex_buyback_price_authority_v1(
    candidate: ZDEXBuybackPriceAuthorityCandidateV1<'_>,
) -> AbiResultV1<VerifiedZDEXBuybackPriceAuthorityV1> {
    candidate.pre_state.validate()?;
    candidate.route.validate()?;
    candidate.occurrence.validate()?;
    candidate.execution_policy.validate()?;
    candidate.price_policy.validate()?;
    candidate.price_occurrence.validate()?;
    let pre_state_root = candidate.pre_state.state_root()?;
    let execution_policy_root = candidate.execution_policy.policy_root()?;
    let price_policy_root = candidate.price_policy.policy_root()?;
    let price_occurrence_root = candidate.price_occurrence.occurrence_root()?;
    let occurrence_id = require_context_v1(
        &candidate,
        &pre_state_root,
        &execution_policy_root,
        &price_policy_root,
    )?;
    require_finalized_oracle_v1(&candidate, &price_occurrence_root)?;
    let (quote_reserve_atoms, zdex_reserve_atoms) = require_committed_reserves_v1(&candidate)?;
    if quote_reserve_atoms != candidate.expected_quote_reserve_atoms
        || zdex_reserve_atoms != candidate.expected_zdex_reserve_atoms
    {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX buyback committed reserve amount",
        ));
    }
    let observation = ZDEXBuybackPriceSafetyObservationV1 {
        schema: ZDEX_BUYBACK_PRICE_SAFETY_OBSERVATION_SCHEMA_V1.to_owned(),
        oracle_occurrence_root: price_occurrence_root.clone(),
        current_height: candidate.occurrence.height,
        oracle_observed_height: candidate.price_occurrence.observed_height,
        oracle_quote_numerator_atoms: candidate.price_occurrence.quote_numerator_atoms,
        oracle_zdex_denominator_atoms: candidate.price_occurrence.zdex_denominator_atoms,
        quote_reserve_atoms,
        zdex_reserve_atoms,
        quote_amount_in_atoms: candidate.quote_amount_in_atoms,
        purchased_zdex_atoms: candidate.purchased_zdex_atoms,
        claimed_route_safe_quote_limit_atoms: candidate.route_safe_quote_limit_atoms,
        claimed_minimum_output_atoms: candidate.minimum_output_atoms,
    };
    let ZDEXBuybackPriceSafetyResultV1::Accepted(price_safety) =
        verify_zdex_buyback_price_safety_v1(candidate.price_policy, &observation)?
    else {
        return Err(AbiErrorV1::InvalidBinding("ZDEX buyback price envelope"));
    };
    Ok(VerifiedZDEXBuybackPriceAuthorityV1 {
        pre_state_root,
        command_occurrence_id: occurrence_id,
        execution_policy_root,
        price_policy_root,
        price_occurrence_root,
        price_safety,
    })
}
