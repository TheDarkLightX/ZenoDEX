use serde::{Deserialize, Serialize};

use crate::canonical::{validate_token_v2, AbiResultV2, ValidateCanonicalV2};

#[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EconomicAmountV2 {
    pub owner: String,
    pub asset: String,
    pub custody_domain: String,
    pub amount_atoms: u128,
}

impl EconomicAmountV2 {
    pub(crate) fn validate(&self) -> AbiResultV2<()> {
        validate_token_v2(&self.owner, "economic amount owner")?;
        validate_token_v2(&self.asset, "economic amount asset")?;
        validate_token_v2(&self.custody_domain, "economic amount custody domain")
    }

    pub(crate) fn key(&self) -> (&str, &str, &str) {
        (&self.asset, &self.owner, &self.custody_domain)
    }
}

impl ValidateCanonicalV2 for EconomicAmountV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetSupplyV2 {
    pub asset: String,
    pub amount_atoms: u128,
}

impl AssetSupplyV2 {
    pub(crate) fn validate(&self) -> AbiResultV2<()> {
        validate_token_v2(&self.asset, "supply asset")
    }
}

impl ValidateCanonicalV2 for AssetSupplyV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}
