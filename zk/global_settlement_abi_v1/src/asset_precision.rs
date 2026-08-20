use serde::{Deserialize, Serialize};

use crate::canonical::{
    hash_global_v1, validate_schema_v1, validate_token_v1, AbiErrorV1, AbiResultV1, RootV1,
};

pub const MAX_ASSET_DECIMALS_V1: u8 = 18;
pub const MAX_ASSET_PRECISION_POLICIES_V1: usize = 256;
pub const TARGET_COMMON_DECIMALS_V1: u8 = 8;
pub const CURRENT_TAU_TESTNET_DECIMALS_V1: u8 = 4;
pub const BPS_DENOMINATOR_V1: u128 = 10_000;
pub const MAX_SETTLEMENT_DELTA_ATOMS_V1: u128 = i128::MAX as u128;

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum TauAmountWidthV1 {
    Bv24,
    Bv64,
}

impl TauAmountWidthV1 {
    pub const fn bits(self) -> u8 {
        match self {
            Self::Bv24 => 24,
            Self::Bv64 => 64,
        }
    }

    pub const fn max_atoms(self) -> u128 {
        match self {
            Self::Bv24 => (1_u128 << 24) - 1,
            Self::Bv64 => (1_u128 << 64) - 1,
        }
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ScaleChangePolicyV1 {
    NewAssetOrProvedMigrationOnly,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetPrecisionPolicyV1 {
    pub asset: String,
    pub source_decimals: u8,
    pub ledger_decimals: u8,
    pub tau_amount_width: Option<TauAmountWidthV1>,
    pub max_supply_atoms: u128,
    pub max_ledger_transfer_atoms: u128,
    pub scale_change_policy: ScaleChangePolicyV1,
}

impl AssetPrecisionPolicyV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.asset, "asset precision policy asset")?;
        if self.source_decimals > MAX_ASSET_DECIMALS_V1
            || self.ledger_decimals > MAX_ASSET_DECIMALS_V1
        {
            return Err(AbiErrorV1::InvalidBounds("asset precision decimals"));
        }
        if self.max_supply_atoms == 0
            || self.max_supply_atoms > MAX_SETTLEMENT_DELTA_ATOMS_V1
            || self.max_ledger_transfer_atoms == 0
            || self.max_ledger_transfer_atoms > self.max_supply_atoms
        {
            return Err(AbiErrorV1::InvalidBounds("asset precision atom envelope"));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetPrecisionRegistryV1 {
    pub schema: String,
    pub policies: Vec<AssetPrecisionPolicyV1>,
}

impl AssetPrecisionRegistryV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        validate_schema_v1(&self.schema)?;
        if self.policies.is_empty() || self.policies.len() > MAX_ASSET_PRECISION_POLICIES_V1 {
            return Err(AbiErrorV1::InvalidBounds("asset precision policies"));
        }
        for policy in &self.policies {
            policy.validate()?;
        }
        if self
            .policies
            .windows(2)
            .any(|pair| pair[0].asset >= pair[1].asset)
        {
            return Err(AbiErrorV1::InvalidOrder("asset precision policies"));
        }
        Ok(())
    }

    pub fn registry_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("asset-precision-registry-v1", self)
    }

    pub fn policy_for(&self, asset: &str) -> Option<&AssetPrecisionPolicyV1> {
        self.policies.iter().find(|policy| policy.asset == asset)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AssetPrecisionRejectCodeV1 {
    DecimalsOutOfRange,
    AmountOutOfRange,
    InexactRescale,
    TauAmountOutOfRange,
    BasisPointsOutOfRange,
    BurnAmountZero,
    BurnExceedsSupply,
    FinalAtomRequiresRetirement,
    RetirementRequiresZeroSupply,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AssetPrecisionRejectV1 {
    pub code: AssetPrecisionRejectCodeV1,
}

pub type AssetPrecisionResultV1<T> = Result<T, AssetPrecisionRejectV1>;

const fn reject_v1(code: AssetPrecisionRejectCodeV1) -> AssetPrecisionRejectV1 {
    AssetPrecisionRejectV1 { code }
}

fn validate_decimals_v1(decimals: u8) -> AssetPrecisionResultV1<()> {
    if decimals > MAX_ASSET_DECIMALS_V1 {
        return Err(reject_v1(AssetPrecisionRejectCodeV1::DecimalsOutOfRange));
    }
    Ok(())
}

fn validate_amount_v1(amount_atoms: u128) -> AssetPrecisionResultV1<()> {
    if amount_atoms > MAX_SETTLEMENT_DELTA_ATOMS_V1 {
        return Err(reject_v1(AssetPrecisionRejectCodeV1::AmountOutOfRange));
    }
    Ok(())
}

fn scale_factor_v1(decimal_difference: u8) -> u128 {
    10_u128.pow(u32::from(decimal_difference))
}

/// Converts integer atoms between declared scales without rounding.
///
/// Zero is valid. A downscale with nonzero remainder rejects, and an upscale
/// rejects before the result can exceed the signed effect-delta domain.
pub fn exact_rescale_atoms_v1(
    amount_atoms: u128,
    source_decimals: u8,
    destination_decimals: u8,
) -> AssetPrecisionResultV1<u128> {
    validate_amount_v1(amount_atoms)?;
    validate_decimals_v1(source_decimals)?;
    validate_decimals_v1(destination_decimals)?;
    match destination_decimals.cmp(&source_decimals) {
        core::cmp::Ordering::Equal => Ok(amount_atoms),
        core::cmp::Ordering::Greater => {
            let factor = scale_factor_v1(destination_decimals - source_decimals);
            amount_atoms
                .checked_mul(factor)
                .filter(|value| *value <= MAX_SETTLEMENT_DELTA_ATOMS_V1)
                .ok_or_else(|| reject_v1(AssetPrecisionRejectCodeV1::AmountOutOfRange))
        }
        core::cmp::Ordering::Less => {
            let factor = scale_factor_v1(source_decimals - destination_decimals);
            if amount_atoms % factor != 0 {
                return Err(reject_v1(AssetPrecisionRejectCodeV1::InexactRescale));
            }
            Ok(amount_atoms / factor)
        }
    }
}

/// Admits one positive Tau transfer amount under the exact selected wire width.
pub fn admit_tau_amount_v1(
    amount_atoms: u128,
    width: TauAmountWidthV1,
) -> AssetPrecisionResultV1<u128> {
    if amount_atoms == 0 || amount_atoms > width.max_atoms() {
        return Err(reject_v1(AssetPrecisionRejectCodeV1::TauAmountOutOfRange));
    }
    Ok(amount_atoms)
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum BurnDispositionV1 {
    PreserveAsset,
    RetireAsset,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BurnAdmissionV1 {
    pub supply_after_atoms: u128,
    pub disposition: BurnDispositionV1,
}

/// Checks an exact integer burn and makes final-atom retirement explicit.
pub fn admit_burn_v1(
    supply_before_atoms: u128,
    burn_atoms: u128,
    disposition: BurnDispositionV1,
) -> AssetPrecisionResultV1<BurnAdmissionV1> {
    validate_amount_v1(supply_before_atoms)?;
    validate_amount_v1(burn_atoms)?;
    if burn_atoms == 0 {
        return Err(reject_v1(AssetPrecisionRejectCodeV1::BurnAmountZero));
    }
    let supply_after_atoms = supply_before_atoms
        .checked_sub(burn_atoms)
        .ok_or_else(|| reject_v1(AssetPrecisionRejectCodeV1::BurnExceedsSupply))?;
    match (supply_after_atoms, disposition) {
        (0, BurnDispositionV1::PreserveAsset) => Err(reject_v1(
            AssetPrecisionRejectCodeV1::FinalAtomRequiresRetirement,
        )),
        (1.., BurnDispositionV1::RetireAsset) => Err(reject_v1(
            AssetPrecisionRejectCodeV1::RetirementRequiresZeroSupply,
        )),
        _ => Ok(BurnAdmissionV1 {
            supply_after_atoms,
            disposition,
        }),
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FloorBurnQuoteV1 {
    pub burn_atoms: u128,
    pub residue_numerator: u16,
    pub residue_denominator: u16,
}

/// Computes floor(supply * burn_bps / 10_000) without a wide product.
pub fn quote_floor_bps_burn_v1(
    supply_atoms: u128,
    burn_bps: u16,
) -> AssetPrecisionResultV1<FloorBurnQuoteV1> {
    validate_amount_v1(supply_atoms)?;
    if u128::from(burn_bps) > BPS_DENOMINATOR_V1 {
        return Err(reject_v1(AssetPrecisionRejectCodeV1::BasisPointsOutOfRange));
    }
    let whole = supply_atoms / BPS_DENOMINATOR_V1;
    let remainder = supply_atoms % BPS_DENOMINATOR_V1;
    let burn_bps_u128 = u128::from(burn_bps);
    let remainder_product = remainder * burn_bps_u128;
    let burn_atoms = whole * burn_bps_u128 + remainder_product / BPS_DENOMINATOR_V1;
    Ok(FloorBurnQuoteV1 {
        burn_atoms,
        residue_numerator: (remainder_product % BPS_DENOMINATOR_V1) as u16,
        residue_denominator: BPS_DENOMINATOR_V1 as u16,
    })
}
