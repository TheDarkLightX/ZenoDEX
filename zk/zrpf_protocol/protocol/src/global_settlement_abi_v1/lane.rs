use serde::{Deserialize, Serialize};

use super::{GlobalSettlementAbiErrorV1, ECONOMIC_LANE_COUNT_V1};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum EconomicLaneIdV1 {
    AssetTransfer,
    SpotLiquidity,
    FarmIncentives,
    ZdexTokenomics,
    ZusdMonetary,
    PerpsMarket,
    OracleMarket,
    SealedAuction,
    StrategyEscrow,
    ProofRewards,
    ExternalCustody,
    GovernanceMigration,
}

impl EconomicLaneIdV1 {
    pub const ALL: [Self; ECONOMIC_LANE_COUNT_V1] = [
        Self::AssetTransfer,
        Self::SpotLiquidity,
        Self::FarmIncentives,
        Self::ZdexTokenomics,
        Self::ZusdMonetary,
        Self::PerpsMarket,
        Self::OracleMarket,
        Self::SealedAuction,
        Self::StrategyEscrow,
        Self::ProofRewards,
        Self::ExternalCustody,
        Self::GovernanceMigration,
    ];

    pub const fn code(self) -> u8 {
        match self {
            Self::AssetTransfer => 0,
            Self::SpotLiquidity => 1,
            Self::FarmIncentives => 2,
            Self::ZdexTokenomics => 3,
            Self::ZusdMonetary => 4,
            Self::PerpsMarket => 5,
            Self::OracleMarket => 6,
            Self::SealedAuction => 7,
            Self::StrategyEscrow => 8,
            Self::ProofRewards => 9,
            Self::ExternalCustody => 10,
            Self::GovernanceMigration => 11,
        }
    }

    pub const fn as_str(self) -> &'static str {
        match self {
            Self::AssetTransfer => "ASSET_TRANSFER",
            Self::SpotLiquidity => "SPOT_LIQUIDITY",
            Self::FarmIncentives => "FARM_INCENTIVES",
            Self::ZdexTokenomics => "ZDEX_TOKENOMICS",
            Self::ZusdMonetary => "ZUSD_MONETARY",
            Self::PerpsMarket => "PERPS_MARKET",
            Self::OracleMarket => "ORACLE_MARKET",
            Self::SealedAuction => "SEALED_AUCTION",
            Self::StrategyEscrow => "STRATEGY_ESCROW",
            Self::ProofRewards => "PROOF_REWARDS",
            Self::ExternalCustody => "EXTERNAL_CUSTODY",
            Self::GovernanceMigration => "GOVERNANCE_MIGRATION",
        }
    }

    pub fn parse_exact(value: &str) -> Result<Self, GlobalSettlementAbiErrorV1> {
        match value {
            "ASSET_TRANSFER" => Ok(Self::AssetTransfer),
            "SPOT_LIQUIDITY" => Ok(Self::SpotLiquidity),
            "FARM_INCENTIVES" => Ok(Self::FarmIncentives),
            "ZDEX_TOKENOMICS" => Ok(Self::ZdexTokenomics),
            "ZUSD_MONETARY" => Ok(Self::ZusdMonetary),
            "PERPS_MARKET" => Ok(Self::PerpsMarket),
            "ORACLE_MARKET" => Ok(Self::OracleMarket),
            "SEALED_AUCTION" => Ok(Self::SealedAuction),
            "STRATEGY_ESCROW" => Ok(Self::StrategyEscrow),
            "PROOF_REWARDS" => Ok(Self::ProofRewards),
            "EXTERNAL_CUSTODY" => Ok(Self::ExternalCustody),
            "GOVERNANCE_MIGRATION" => Ok(Self::GovernanceMigration),
            _ => Err(GlobalSettlementAbiErrorV1::UnknownLaneIdentifier),
        }
    }

    pub fn from_code(code: u8) -> Result<Self, GlobalSettlementAbiErrorV1> {
        match code {
            0 => Ok(Self::AssetTransfer),
            1 => Ok(Self::SpotLiquidity),
            2 => Ok(Self::FarmIncentives),
            3 => Ok(Self::ZdexTokenomics),
            4 => Ok(Self::ZusdMonetary),
            5 => Ok(Self::PerpsMarket),
            6 => Ok(Self::OracleMarket),
            7 => Ok(Self::SealedAuction),
            8 => Ok(Self::StrategyEscrow),
            9 => Ok(Self::ProofRewards),
            10 => Ok(Self::ExternalCustody),
            11 => Ok(Self::GovernanceMigration),
            _ => Err(GlobalSettlementAbiErrorV1::UnknownLaneCode(code)),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum EconomicLaneCommandStatusV1 {
    Disabled,
    Enabled,
}

impl EconomicLaneCommandStatusV1 {
    pub const fn code(self) -> u8 {
        match self {
            Self::Disabled => 0,
            Self::Enabled => 1,
        }
    }
}
