//! Profile-bound identifiers for one perps market and Oracle price pair.

use serde::{Deserialize, Serialize};

use crate::canonical::{hash_global_v1, validate_token_v1, AbiErrorV1, AbiResultV1, RootV1};
use crate::proof::EconomicCommandOccurrenceV1;
use crate::release::{EconomicPolicyRegistryV1, EconomicProfileSnapshotV1};

pub const PERPS_MARKET_POLICY_SCHEMA_V1: &str = "zenodex/perps-market-policy/v1";
pub const PERPS_MARKET_POLICY_KIND_V1: &str = "perps_market_policy_v1";

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct PerpsMarketPolicyV1 {
    pub schema: String,
    pub market_id: String,
    pub base_asset: String,
    pub quote_asset: String,
    pub oracle_id: String,
}

impl PerpsMarketPolicyV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != PERPS_MARKET_POLICY_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidSchema);
        }
        validate_token_v1(&self.market_id, "perps market policy market id")?;
        validate_token_v1(&self.base_asset, "perps market policy base asset")?;
        validate_token_v1(&self.quote_asset, "perps market policy quote asset")?;
        validate_token_v1(&self.oracle_id, "perps market policy Oracle id")?;
        if self.base_asset == self.quote_asset {
            return Err(AbiErrorV1::InvalidBinding(
                "perps market policy distinct assets",
            ));
        }
        Ok(())
    }

    pub fn policy_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("perps-market-policy-v1", self)
    }
}

pub fn require_governed_perps_market_policy_v1(
    profile: &EconomicProfileSnapshotV1,
    policy_registry: &EconomicPolicyRegistryV1,
    occurrence: &EconomicCommandOccurrenceV1,
    market_policy: &PerpsMarketPolicyV1,
) -> AbiResultV1<()> {
    profile.validate()?;
    occurrence.validate()?;
    market_policy.validate()?;
    if policy_registry.registry_root()? != profile.policy_registry_root {
        return Err(AbiErrorV1::InvalidBinding(
            "perps market policy registry outside profile",
        ));
    }
    let binding =
        policy_registry.require_binding(PERPS_MARKET_POLICY_KIND_V1, &occurrence.command_kind)?;
    if binding.policy_root != market_policy.policy_root()? {
        return Err(AbiErrorV1::InvalidBinding("perps market policy root"));
    }
    Ok(())
}
