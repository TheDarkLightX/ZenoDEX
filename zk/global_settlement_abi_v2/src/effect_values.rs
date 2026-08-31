use serde::{Deserialize, Serialize};

use crate::canonical::{validate_token_v2, AbiErrorV2, AbiResultV2, RootV2};

pub const FEE_RESIDUE_PRINCIPAL_V2: &str = "protocol:fee-unallocated-reserve";
pub const FEE_RESIDUE_CONTROL_DOMAIN_V2: &str = "zenoledger:protocol-fee-residue";

#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[allow(non_camel_case_types)]
pub enum LaneIdV2 {
    ASSET_TRANSFER,
    SPOT_LIQUIDITY,
    FARM_INCENTIVES,
    ZDEX_TOKENOMICS,
    ZUSD_MONETARY,
    PERPS_MARKET,
    ORACLE_MARKET,
    SEALED_AUCTION,
    STRATEGY_ESCROW,
    PROOF_REWARDS,
    EXTERNAL_CUSTODY,
    GOVERNANCE_MIGRATION,
}

impl LaneIdV2 {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::ASSET_TRANSFER => "ASSET_TRANSFER",
            Self::SPOT_LIQUIDITY => "SPOT_LIQUIDITY",
            Self::FARM_INCENTIVES => "FARM_INCENTIVES",
            Self::ZDEX_TOKENOMICS => "ZDEX_TOKENOMICS",
            Self::ZUSD_MONETARY => "ZUSD_MONETARY",
            Self::PERPS_MARKET => "PERPS_MARKET",
            Self::ORACLE_MARKET => "ORACLE_MARKET",
            Self::SEALED_AUCTION => "SEALED_AUCTION",
            Self::STRATEGY_ESCROW => "STRATEGY_ESCROW",
            Self::PROOF_REWARDS => "PROOF_REWARDS",
            Self::EXTERNAL_CUSTODY => "EXTERNAL_CUSTODY",
            Self::GOVERNANCE_MIGRATION => "GOVERNANCE_MIGRATION",
        }
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum EconomicEffectKindV2 {
    ACCOUNT_MOVEMENT,
    ISSUE,
    BURN,
    CUSTODY,
    LIABILITY,
    RESERVE,
    FEE_ALLOCATION,
    REWARD,
    SLASH,
}

impl EconomicEffectKindV2 {
    fn as_str(self) -> &'static str {
        match self {
            Self::ACCOUNT_MOVEMENT => "ACCOUNT_MOVEMENT",
            Self::ISSUE => "ISSUE",
            Self::BURN => "BURN",
            Self::CUSTODY => "CUSTODY",
            Self::LIABILITY => "LIABILITY",
            Self::RESERVE => "RESERVE",
            Self::FEE_ALLOCATION => "FEE_ALLOCATION",
            Self::REWARD => "REWARD",
            Self::SLASH => "SLASH",
        }
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EconomicEffectRowV2 {
    pub kind: EconomicEffectKindV2,
    pub principal: String,
    pub asset: String,
    pub custody_domain: String,
    pub delta_atoms: i128,
}

impl EconomicEffectRowV2 {
    pub(crate) fn validate(&self) -> AbiResultV2<()> {
        validate_token_v2(&self.principal, "economic effect principal")?;
        validate_token_v2(&self.asset, "economic effect asset")?;
        validate_token_v2(&self.custody_domain, "economic effect custody domain")?;
        if self.delta_atoms == 0 {
            return Err(AbiErrorV2::InvalidBounds("economic effect delta"));
        }
        if self.kind == EconomicEffectKindV2::ISSUE && self.delta_atoms < 0 {
            return Err(AbiErrorV2::InvalidBinding("issue effect sign"));
        }
        if self.kind == EconomicEffectKindV2::BURN && self.delta_atoms > 0 {
            return Err(AbiErrorV2::InvalidBinding("burn effect sign"));
        }
        Ok(())
    }

    pub(crate) fn key(&self) -> (&'static str, &str, &str, &str) {
        (
            self.kind.as_str(),
            &self.asset,
            &self.principal,
            &self.custody_domain,
        )
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetConservationRowV2 {
    pub asset: String,
    pub owned_and_custodied_pre_atoms: u128,
    pub owned_and_custodied_post_atoms: u128,
    pub supply_pre_atoms: u128,
    pub supply_post_atoms: u128,
    pub authorized_issue_atoms: u128,
    pub authorized_burn_atoms: u128,
}

impl AssetConservationRowV2 {
    pub(crate) fn validate(&self) -> AbiResultV2<()> {
        validate_token_v2(&self.asset, "conservation asset")?;
        let apply_authorized_delta = |pre_atoms: u128, overflow_label: &'static str| {
            if self.authorized_issue_atoms >= self.authorized_burn_atoms {
                pre_atoms.checked_add(self.authorized_issue_atoms - self.authorized_burn_atoms)
            } else {
                pre_atoms.checked_sub(self.authorized_burn_atoms - self.authorized_issue_atoms)
            }
            .ok_or(AbiErrorV2::Conservation(overflow_label))
        };
        let expected_owned = apply_authorized_delta(
            self.owned_and_custodied_pre_atoms,
            "owned and custodied overflow",
        )?;
        let expected_supply = apply_authorized_delta(self.supply_pre_atoms, "supply overflow")?;
        if expected_owned != self.owned_and_custodied_post_atoms {
            return Err(AbiErrorV2::Conservation("owned and custodied"));
        }
        if expected_supply != self.supply_post_atoms {
            return Err(AbiErrorV2::Conservation("supply"));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct FeeConservationRowV2 {
    pub asset: String,
    pub fee_charged_atoms: u128,
    pub current_allocations_atoms: u128,
    pub carried_residue_atoms: u128,
}

impl FeeConservationRowV2 {
    pub(crate) fn validate(&self) -> AbiResultV2<()> {
        validate_token_v2(&self.asset, "fee conservation asset")?;
        let allocated = self
            .current_allocations_atoms
            .checked_add(self.carried_residue_atoms)
            .ok_or(AbiErrorV2::Conservation("fee overflow"))?;
        if self.fee_charged_atoms != allocated {
            return Err(AbiErrorV2::Conservation("fee allocation"));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct LaneWriteV2 {
    pub lane_id: LaneIdV2,
    pub pre_root: RootV2,
    pub post_root: RootV2,
}

impl LaneWriteV2 {
    pub(crate) fn validate(&self) -> AbiResultV2<()> {
        self.pre_root.validate("lane write pre root", true)?;
        self.post_root.validate("lane write post root", true)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ExternalOutboxEnqueueV2 {
    pub effect_id: RootV2,
    pub destination_id: String,
    pub payload_hash: RootV2,
    pub adapter_profile_root: RootV2,
}

impl ExternalOutboxEnqueueV2 {
    pub(crate) fn validate(&self) -> AbiResultV2<()> {
        self.effect_id
            .validate("external outbox effect id", false)?;
        validate_token_v2(&self.destination_id, "external outbox destination")?;
        if self.destination_id.starts_with("zenoledger:") {
            return Err(AbiErrorV2::InvalidBinding("same-ledger external outbox"));
        }
        self.payload_hash
            .validate("external outbox payload hash", false)?;
        self.adapter_profile_root
            .validate("external outbox adapter profile root", false)
    }
}
