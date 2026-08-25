//! Typed price payload binding for finalized GlobalSettlementABI occurrences.

use serde::{Deserialize, Serialize};

use crate::canonical::{hash_global_v1, validate_token_v1, AbiErrorV1, AbiResultV1, RootV1};
use crate::global_oracle_occurrence_authority::GlobalOracleOccurrenceAuthorityV1;

pub const GLOBAL_ORACLE_PRICE_OCCURRENCE_SCHEMA_V1: &str =
    "zenodex/global-oracle-price-occurrence/v1";
pub const VERIFIED_GLOBAL_ORACLE_PRICE_SCHEMA_V1: &str = "zenodex/verified-global-oracle-price/v1";

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GlobalOraclePriceOccurrenceV1 {
    pub schema: String,
    pub oracle_id: String,
    pub market_id: String,
    pub base_asset: String,
    pub quote_asset: String,
    pub price_e8: u128,
    pub observed_height: u64,
}

impl GlobalOraclePriceOccurrenceV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != GLOBAL_ORACLE_PRICE_OCCURRENCE_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidSchema);
        }
        validate_token_v1(&self.oracle_id, "global Oracle price oracle id")?;
        validate_token_v1(&self.market_id, "global Oracle price market id")?;
        validate_token_v1(&self.base_asset, "global Oracle price base asset")?;
        validate_token_v1(&self.quote_asset, "global Oracle price quote asset")?;
        if self.base_asset == self.quote_asset {
            return Err(AbiErrorV1::InvalidBinding(
                "global Oracle price distinct assets",
            ));
        }
        if self.price_e8 == 0 {
            return Err(AbiErrorV1::InvalidBounds("global Oracle price e8"));
        }
        Ok(())
    }

    pub fn occurrence_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("global-oracle-price-occurrence-v1", self)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifiedGlobalOraclePriceV1 {
    oracle_authority_root: RootV1,
    pre_state_root: RootV1,
    route_release_id: RootV1,
    command_occurrence_id: RootV1,
    policy_root: RootV1,
    oracle_id: String,
    occurrence_root: RootV1,
    observed_height: u64,
    market_id: String,
    base_asset: String,
    quote_asset: String,
    price_e8: u128,
}

#[derive(Serialize)]
struct VerifiedGlobalOraclePriceContentV1<'a> {
    schema: &'static str,
    oracle_authority_root: &'a RootV1,
    pre_state_root: &'a RootV1,
    route_release_id: &'a RootV1,
    command_occurrence_id: &'a RootV1,
    policy_root: &'a RootV1,
    oracle_id: &'a str,
    occurrence_root: &'a RootV1,
    observed_height: u64,
    market_id: &'a str,
    base_asset: &'a str,
    quote_asset: &'a str,
    price_e8: u128,
}

impl VerifiedGlobalOraclePriceV1 {
    pub fn oracle_authority_root(&self) -> &RootV1 {
        &self.oracle_authority_root
    }

    pub fn pre_state_root(&self) -> &RootV1 {
        &self.pre_state_root
    }

    pub fn route_release_id(&self) -> &RootV1 {
        &self.route_release_id
    }

    pub fn command_occurrence_id(&self) -> &RootV1 {
        &self.command_occurrence_id
    }

    pub fn policy_root(&self) -> &RootV1 {
        &self.policy_root
    }

    pub fn oracle_id(&self) -> &str {
        &self.oracle_id
    }

    pub fn occurrence_root(&self) -> &RootV1 {
        &self.occurrence_root
    }

    pub fn observed_height(&self) -> u64 {
        self.observed_height
    }

    pub fn market_id(&self) -> &str {
        &self.market_id
    }

    pub fn base_asset(&self) -> &str {
        &self.base_asset
    }

    pub fn quote_asset(&self) -> &str {
        &self.quote_asset
    }

    pub fn price_e8(&self) -> u128 {
        self.price_e8
    }

    pub fn binding_root(&self) -> AbiResultV1<RootV1> {
        hash_global_v1(
            "verified-global-oracle-price-v1",
            &VerifiedGlobalOraclePriceContentV1 {
                schema: VERIFIED_GLOBAL_ORACLE_PRICE_SCHEMA_V1,
                oracle_authority_root: &self.oracle_authority_root,
                pre_state_root: &self.pre_state_root,
                route_release_id: &self.route_release_id,
                command_occurrence_id: &self.command_occurrence_id,
                policy_root: &self.policy_root,
                oracle_id: &self.oracle_id,
                occurrence_root: &self.occurrence_root,
                observed_height: self.observed_height,
                market_id: &self.market_id,
                base_asset: &self.base_asset,
                quote_asset: &self.quote_asset,
                price_e8: self.price_e8,
            },
        )
    }
}

pub fn verify_global_oracle_price_occurrence_v1(
    authority: &GlobalOracleOccurrenceAuthorityV1,
    payload: &GlobalOraclePriceOccurrenceV1,
) -> AbiResultV1<VerifiedGlobalOraclePriceV1> {
    payload.validate()?;
    let occurrence_root = payload.occurrence_root()?;
    if payload.oracle_id != authority.oracle_id() {
        return Err(AbiErrorV1::InvalidBinding("global Oracle price oracle id"));
    }
    if payload.observed_height != authority.observed_height() {
        return Err(AbiErrorV1::InvalidBinding(
            "global Oracle price observed height",
        ));
    }
    if &occurrence_root != authority.occurrence_root() {
        return Err(AbiErrorV1::InvalidBinding(
            "global Oracle price occurrence root",
        ));
    }
    Ok(VerifiedGlobalOraclePriceV1 {
        oracle_authority_root: authority.authority_root()?,
        pre_state_root: authority.pre_state_root().clone(),
        route_release_id: authority.route_release_id().clone(),
        command_occurrence_id: authority.command_occurrence_id().clone(),
        policy_root: authority.policy_root().clone(),
        oracle_id: payload.oracle_id.clone(),
        occurrence_root,
        observed_height: payload.observed_height,
        market_id: payload.market_id.clone(),
        base_asset: payload.base_asset.clone(),
        quote_asset: payload.quote_asset.clone(),
        price_e8: payload.price_e8,
    })
}
