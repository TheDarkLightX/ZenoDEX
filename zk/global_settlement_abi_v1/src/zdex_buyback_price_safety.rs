use serde::{Deserialize, Serialize};

use crate::canonical::{hash_global_v1, validate_token_v1, AbiErrorV1, AbiResultV1, RootV1};

pub const ZDEX_BUYBACK_PRICE_SAFETY_POLICY_SCHEMA_V1: &str =
    "zenodex/zdex-buyback-price-safety-policy/v1";
pub const ZDEX_BUYBACK_PRICE_SAFETY_OBSERVATION_SCHEMA_V1: &str =
    "zenodex/zdex-buyback-price-safety-observation/v1";
pub const ZDEX_BUYBACK_PRICE_SAFETY_POLICY_KIND_V1: &str = "zdex_buyback_price_safety_v1";
pub const BASIS_POINTS_V1: u128 = 10_000;

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXBuybackPriceSafetyPolicyV1 {
    pub schema: String,
    pub oracle_id: String,
    pub maximum_oracle_age_blocks: u64,
    pub minimum_quote_reserve_atoms: u128,
    pub minimum_zdex_reserve_atoms: u128,
    pub maximum_pool_oracle_deviation_bps: u64,
    pub maximum_execution_impact_bps: u64,
    pub maximum_oracle_execution_deviation_bps: u64,
    pub maximum_quote_reserve_spend_bps: u64,
}

impl ZDEXBuybackPriceSafetyPolicyV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != ZDEX_BUYBACK_PRICE_SAFETY_POLICY_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidBinding(
                "ZDEX buyback price-safety policy schema",
            ));
        }
        validate_token_v1(&self.oracle_id, "ZDEX buyback price-safety Oracle id")?;
        if self.minimum_quote_reserve_atoms == 0 || self.minimum_zdex_reserve_atoms == 0 {
            return Err(AbiErrorV1::InvalidBounds(
                "ZDEX buyback price-safety minimum depth",
            ));
        }
        if self.maximum_pool_oracle_deviation_bps >= BASIS_POINTS_V1 as u64
            || self.maximum_execution_impact_bps >= BASIS_POINTS_V1 as u64
            || self.maximum_oracle_execution_deviation_bps >= BASIS_POINTS_V1 as u64
            || self.maximum_quote_reserve_spend_bps == 0
            || self.maximum_quote_reserve_spend_bps > BASIS_POINTS_V1 as u64
        {
            return Err(AbiErrorV1::InvalidBounds(
                "ZDEX buyback price-safety basis points",
            ));
        }
        Ok(())
    }

    pub fn policy_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("zdex-buyback-price-safety-policy-v1", self)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXBuybackPriceSafetyObservationV1 {
    pub schema: String,
    pub oracle_occurrence_root: RootV1,
    pub current_height: u64,
    pub oracle_observed_height: u64,
    pub oracle_quote_numerator_atoms: u128,
    pub oracle_zdex_denominator_atoms: u128,
    pub quote_reserve_atoms: u128,
    pub zdex_reserve_atoms: u128,
    pub quote_amount_in_atoms: u128,
    pub purchased_zdex_atoms: u128,
    pub claimed_route_safe_quote_limit_atoms: u128,
    pub claimed_minimum_output_atoms: u128,
}

impl ZDEXBuybackPriceSafetyObservationV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != ZDEX_BUYBACK_PRICE_SAFETY_OBSERVATION_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidBinding(
                "ZDEX buyback price-safety observation schema",
            ));
        }
        self.oracle_occurrence_root
            .validate("ZDEX buyback Oracle occurrence root", false)?;
        let positive = [
            self.oracle_quote_numerator_atoms,
            self.oracle_zdex_denominator_atoms,
            self.quote_reserve_atoms,
            self.zdex_reserve_atoms,
            self.quote_amount_in_atoms,
            self.purchased_zdex_atoms,
            self.claimed_route_safe_quote_limit_atoms,
            self.claimed_minimum_output_atoms,
        ];
        if positive.contains(&0)
            || self.quote_amount_in_atoms > i128::MAX.unsigned_abs()
            || self.purchased_zdex_atoms > i128::MAX.unsigned_abs()
        {
            return Err(AbiErrorV1::InvalidBounds(
                "ZDEX buyback price-safety positive atoms",
            ));
        }
        Ok(())
    }

    pub fn observation_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("zdex-buyback-price-safety-observation-v1", self)
    }
}

#[allow(non_camel_case_types)]
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum ZDEXBuybackPriceSafetyRejectCodeV1 {
    HEIGHT_REGRESSION,
    STALE_ORACLE,
    INSUFFICIENT_DEPTH,
    ARITHMETIC_OVERFLOW,
    POOL_ORACLE_DEVIATION,
    EXECUTION_IMPACT,
    ORACLE_EXECUTION_DEVIATION,
    DERIVED_LIMIT_MISMATCH,
    QUOTE_LIMIT_EXCEEDED,
    DERIVED_MINIMUM_OUTPUT_MISMATCH,
    MINIMUM_OUTPUT_NOT_MET,
    OUTPUT_EXCEEDS_RESERVE,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifiedZDEXBuybackPriceSafetyV1 {
    policy_root: RootV1,
    observation_root: RootV1,
    route_safe_quote_limit_atoms: u128,
    minimum_output_atoms: u128,
}

impl VerifiedZDEXBuybackPriceSafetyV1 {
    pub fn policy_root(&self) -> &RootV1 {
        &self.policy_root
    }

    pub fn observation_root(&self) -> &RootV1 {
        &self.observation_root
    }

    pub fn route_safe_quote_limit_atoms(&self) -> u128 {
        self.route_safe_quote_limit_atoms
    }

    pub fn minimum_output_atoms(&self) -> u128 {
        self.minimum_output_atoms
    }

    pub fn binding_root(&self) -> AbiResultV1<RootV1> {
        #[derive(Serialize)]
        struct Binding<'a> {
            policy_root: &'a RootV1,
            observation_root: &'a RootV1,
            route_safe_quote_limit_atoms: u128,
            minimum_output_atoms: u128,
        }
        hash_global_v1(
            "verified-zdex-buyback-price-safety-v1",
            &Binding {
                policy_root: &self.policy_root,
                observation_root: &self.observation_root,
                route_safe_quote_limit_atoms: self.route_safe_quote_limit_atoms,
                minimum_output_atoms: self.minimum_output_atoms,
            },
        )
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ZDEXBuybackPriceSafetyResultV1 {
    Accepted(VerifiedZDEXBuybackPriceSafetyV1),
    Rejected(ZDEXBuybackPriceSafetyRejectCodeV1),
}

fn checked_product_v1(values: &[u128]) -> Option<u128> {
    values
        .iter()
        .try_fold(1_u128, |product, value| product.checked_mul(*value))
}

fn ceil_div_v1(numerator: u128, denominator: u128) -> u128 {
    numerator / denominator + u128::from(numerator % denominator != 0)
}

pub fn verify_zdex_buyback_price_safety_v1(
    policy: &ZDEXBuybackPriceSafetyPolicyV1,
    observation: &ZDEXBuybackPriceSafetyObservationV1,
) -> AbiResultV1<ZDEXBuybackPriceSafetyResultV1> {
    policy.validate()?;
    observation.validate()?;
    use ZDEXBuybackPriceSafetyRejectCodeV1 as Reject;
    use ZDEXBuybackPriceSafetyResultV1::{Accepted, Rejected};

    if observation.current_height < observation.oracle_observed_height {
        return Ok(Rejected(Reject::HEIGHT_REGRESSION));
    }
    if observation.current_height - observation.oracle_observed_height
        > policy.maximum_oracle_age_blocks
    {
        return Ok(Rejected(Reject::STALE_ORACLE));
    }
    if observation.quote_reserve_atoms < policy.minimum_quote_reserve_atoms
        || observation.zdex_reserve_atoms < policy.minimum_zdex_reserve_atoms
    {
        return Ok(Rejected(Reject::INSUFFICIENT_DEPTH));
    }
    if observation.purchased_zdex_atoms > observation.zdex_reserve_atoms {
        return Ok(Rejected(Reject::OUTPUT_EXCEEDS_RESERVE));
    }

    let products = [
        checked_product_v1(&[
            observation.quote_reserve_atoms,
            observation.oracle_zdex_denominator_atoms,
        ]),
        checked_product_v1(&[
            observation.zdex_reserve_atoms,
            observation.oracle_quote_numerator_atoms,
        ]),
        checked_product_v1(&[
            observation.quote_reserve_atoms,
            u128::from(policy.maximum_quote_reserve_spend_bps),
        ]),
        checked_product_v1(&[
            observation.quote_amount_in_atoms,
            observation.oracle_zdex_denominator_atoms,
            BASIS_POINTS_V1,
        ]),
        checked_product_v1(&[
            observation.oracle_quote_numerator_atoms,
            BASIS_POINTS_V1 + u128::from(policy.maximum_oracle_execution_deviation_bps),
        ]),
        checked_product_v1(&[
            observation.quote_amount_in_atoms,
            observation.zdex_reserve_atoms,
            BASIS_POINTS_V1,
        ]),
        checked_product_v1(&[
            observation.purchased_zdex_atoms,
            observation.quote_reserve_atoms,
            BASIS_POINTS_V1 + u128::from(policy.maximum_execution_impact_bps),
        ]),
        checked_product_v1(&[
            observation.purchased_zdex_atoms,
            observation.oracle_quote_numerator_atoms,
            BASIS_POINTS_V1 + u128::from(policy.maximum_oracle_execution_deviation_bps),
        ]),
    ];
    let [Some(pool_price_numerator), Some(oracle_pool_numerator), Some(safe_limit_product), Some(minimum_output_numerator), Some(minimum_output_denominator), Some(execution_impact_lhs), Some(execution_impact_rhs), Some(oracle_execution_rhs)] =
        products
    else {
        return Ok(Rejected(Reject::ARITHMETIC_OVERFLOW));
    };

    let route_safe_quote_limit_atoms =
        (safe_limit_product / BASIS_POINTS_V1).min(i128::MAX.unsigned_abs());
    let minimum_output_atoms = ceil_div_v1(minimum_output_numerator, minimum_output_denominator);
    if route_safe_quote_limit_atoms == 0
        || observation.claimed_route_safe_quote_limit_atoms != route_safe_quote_limit_atoms
    {
        return Ok(Rejected(Reject::DERIVED_LIMIT_MISMATCH));
    }
    if observation.quote_amount_in_atoms > route_safe_quote_limit_atoms {
        return Ok(Rejected(Reject::QUOTE_LIMIT_EXCEEDED));
    }
    if observation.claimed_minimum_output_atoms != minimum_output_atoms {
        return Ok(Rejected(Reject::DERIVED_MINIMUM_OUTPUT_MISMATCH));
    }
    if observation.purchased_zdex_atoms < minimum_output_atoms {
        return Ok(Rejected(Reject::MINIMUM_OUTPUT_NOT_MET));
    }

    let Some(pool_deviation_lhs) = pool_price_numerator
        .abs_diff(oracle_pool_numerator)
        .checked_mul(BASIS_POINTS_V1)
    else {
        return Ok(Rejected(Reject::ARITHMETIC_OVERFLOW));
    };
    let Some(pool_deviation_rhs) =
        oracle_pool_numerator.checked_mul(u128::from(policy.maximum_pool_oracle_deviation_bps))
    else {
        return Ok(Rejected(Reject::ARITHMETIC_OVERFLOW));
    };
    if pool_deviation_lhs > pool_deviation_rhs {
        return Ok(Rejected(Reject::POOL_ORACLE_DEVIATION));
    }
    if execution_impact_lhs > execution_impact_rhs {
        return Ok(Rejected(Reject::EXECUTION_IMPACT));
    }
    if minimum_output_numerator > oracle_execution_rhs {
        return Ok(Rejected(Reject::ORACLE_EXECUTION_DEVIATION));
    }

    Ok(Accepted(VerifiedZDEXBuybackPriceSafetyV1 {
        policy_root: policy.policy_root()?,
        observation_root: observation.observation_root()?,
        route_safe_quote_limit_atoms,
        minimum_output_atoms,
    }))
}
