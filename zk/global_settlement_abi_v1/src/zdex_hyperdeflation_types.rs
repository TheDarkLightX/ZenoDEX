//! Closed canonical values for the experimental ZDEX hyperdeflation core.
//!
//! Accepted values are self-validating transition data. They are not opaque
//! receipt or settlement-authority witnesses.

use serde::{Deserialize, Serialize};

use crate::canonical::{hash_global_v1, validate_token_v1, AbiErrorV1, AbiResultV1, RootV1};

pub const MAX_DECIMAL_SCALE_STEP_V1: u64 = 38;
pub const MAX_ZDEX_PROJECTION_BUCKETS_V1: usize = 1024;

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum ZDEXBurnRejectCodeV1 {
    POLICY_MISMATCH,
    STATE_OUTSIDE_POLICY,
    STALE_STATE,
    PRECISION_EPOCH_MISMATCH,
    BURN_BUDGET_EPOCH_MISMATCH,
    PURCHASE_BINDING_MISMATCH,
    SOURCE_BUCKET_UNKNOWN,
    ZERO_PURCHASE,
    EFFECT_WIDTH_EXCEEDED,
    PRECISION_RESCALE_REQUIRED,
    SOURCE_RESERVE_FLOOR_REACHED,
    EPOCH_BURN_CAP_REACHED,
    ROUTE_OUTPUT_CAP_ZERO,
    PURCHASE_EXCEEDS_BURN_CAPACITY,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum ZDEXPrecisionRejectCodeV1 {
    POLICY_MISMATCH,
    STALE_STATE,
    PRECISION_EPOCH_MISMATCH,
    ZERO_DECIMAL_STEP,
    DECIMAL_STEP_EXCEEDS_POLICY,
    MAXIMUM_DECIMALS_EXCEEDED,
    EPOCH_COUNTER_EXHAUSTED,
    ATOM_OVERFLOW,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ZDEXHyperdeflationPolicyV1 {
    pub asset_id: RootV1,
    pub retained_numerator: u64,
    pub retained_denominator: u64,
    pub maximum_decimals: u64,
    pub maximum_decimal_step: u64,
}

impl ZDEXHyperdeflationPolicyV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.asset_id.validate("ZDEX policy asset id", false)?;
        if self.retained_numerator == 0
            || self.retained_denominator == 0
            || self.retained_numerator >= self.retained_denominator
        {
            return Err(AbiErrorV1::InvalidBounds("ZDEX retained fraction"));
        }
        if self.maximum_decimal_step == 0 || self.maximum_decimal_step > MAX_DECIMAL_SCALE_STEP_V1 {
            return Err(AbiErrorV1::InvalidBounds("ZDEX maximum decimal step"));
        }
        Ok(())
    }

    pub fn policy_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("zdex-hyperdeflation-policy-v1", self)
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub struct ZDEXAmountBucketV1 {
    pub bucket_id: String,
    pub amount_atoms: u128,
}

impl ZDEXAmountBucketV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.bucket_id, "ZDEX bucket id")?;
        if self.amount_atoms == 0 {
            return Err(AbiErrorV1::InvalidBounds("ZDEX bucket amount"));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ZDEXSupplyStateV1 {
    pub asset_id: RootV1,
    pub policy_root: RootV1,
    pub decimals: u64,
    pub precision_epoch: u64,
    pub live_supply_atoms: u128,
    pub buckets: Vec<ZDEXAmountBucketV1>,
    pub burn_budget_epoch: u64,
    pub remaining_epoch_burn_cap_atoms: u128,
}

impl ZDEXSupplyStateV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.asset_id.validate("ZDEX state asset id", false)?;
        self.policy_root.validate("ZDEX state policy root", false)?;
        if self.live_supply_atoms == 0
            || self.buckets.is_empty()
            || self.buckets.len() > MAX_ZDEX_PROJECTION_BUCKETS_V1
        {
            return Err(AbiErrorV1::InvalidBounds("ZDEX live supply projection"));
        }
        if self
            .buckets
            .windows(2)
            .any(|pair| pair[0].bucket_id >= pair[1].bucket_id)
        {
            return Err(AbiErrorV1::InvalidOrder("ZDEX state buckets"));
        }
        let mut total = 0_u128;
        for bucket in &self.buckets {
            bucket.validate()?;
            total = total
                .checked_add(bucket.amount_atoms)
                .ok_or(AbiErrorV1::Conservation("ZDEX bucket sum overflow"))?;
        }
        if total != self.live_supply_atoms {
            return Err(AbiErrorV1::Conservation("ZDEX live bucket sum"));
        }
        Ok(())
    }

    pub fn state_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("zdex-supply-state-v1", self)
    }

    pub fn bucket_atoms(&self, bucket_id: &str) -> AbiResultV1<Option<u128>> {
        validate_token_v1(bucket_id, "ZDEX bucket lookup id")?;
        Ok(self
            .buckets
            .iter()
            .find(|bucket| bucket.bucket_id == bucket_id)
            .map(|bucket| bucket.amount_atoms))
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ZDEXBurnRouteContextV1 {
    pub route_release_id: RootV1,
    pub policy_root: RootV1,
    pub purchase_occurrence_root: RootV1,
    pub burn_source_bucket_id: String,
    pub purchased_zdex_atoms: u128,
    pub source_reserve_floor_atoms: u128,
    pub remaining_epoch_burn_cap_atoms: u128,
    pub route_safe_output_cap_atoms: u128,
    pub burn_budget_epoch: u64,
}

impl ZDEXBurnRouteContextV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.route_release_id
            .validate("ZDEX burn route release id", false)?;
        self.policy_root
            .validate("ZDEX burn route policy root", false)?;
        self.purchase_occurrence_root
            .validate("ZDEX purchase occurrence root", false)?;
        validate_token_v1(&self.burn_source_bucket_id, "ZDEX route burn source bucket")?;
        if self.purchased_zdex_atoms == 0 {
            return Err(AbiErrorV1::InvalidBounds("ZDEX route purchased amount"));
        }
        Ok(())
    }

    pub fn context_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("zdex-burn-route-context-v1", self)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ZDEXPurchaseAndBurnCommandV1 {
    pub expected_pre_state_root: RootV1,
    pub expected_precision_epoch: u64,
    pub expected_purchase_occurrence_root: RootV1,
    pub source_bucket_id: String,
    pub purchased_zdex_atoms: u128,
}

impl ZDEXPurchaseAndBurnCommandV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.expected_pre_state_root
            .validate("ZDEX burn expected pre-state", false)?;
        self.expected_purchase_occurrence_root
            .validate("ZDEX burn expected purchase occurrence", false)?;
        validate_token_v1(&self.source_bucket_id, "ZDEX burn source bucket id")
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ZDEXBurnCapacityV1 {
    pub retained_supply_atoms: u128,
    pub ratio_headroom_atoms: u128,
    pub source_headroom_atoms: u128,
    pub epoch_headroom_atoms: u128,
    pub route_headroom_atoms: u128,
    pub maximum_burn_atoms: u128,
}

impl ZDEXBurnCapacityV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.retained_supply_atoms == 0 {
            return Err(AbiErrorV1::InvalidBounds("ZDEX retained supply capacity"));
        }
        let expected = self
            .ratio_headroom_atoms
            .min(self.source_headroom_atoms)
            .min(self.epoch_headroom_atoms)
            .min(self.route_headroom_atoms);
        if self.maximum_burn_atoms != expected {
            return Err(AbiErrorV1::InvalidBinding("ZDEX maximum burn headroom"));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ZDEXBurnEffectV1 {
    pub purchase_occurrence_root: RootV1,
    pub source_bucket_id: String,
    pub source_debit_atoms: u128,
    pub authorized_burn_atoms: u128,
    pub authorized_issue_atoms: u128,
}

impl ZDEXBurnEffectV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.purchase_occurrence_root
            .validate("ZDEX burn effect purchase occurrence", false)?;
        validate_token_v1(&self.source_bucket_id, "ZDEX burn effect source bucket")?;
        if self.source_debit_atoms == 0
            || self.source_debit_atoms > i128::MAX.unsigned_abs()
            || self.source_debit_atoms != self.authorized_burn_atoms
            || self.authorized_issue_atoms != 0
        {
            return Err(AbiErrorV1::InvalidBinding("ZDEX burn effect"));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ZDEXPrecisionRescaleCommandV1 {
    pub expected_pre_state_root: RootV1,
    pub expected_precision_epoch: u64,
    pub additional_decimals: u64,
}

impl ZDEXPrecisionRescaleCommandV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.expected_pre_state_root
            .validate("ZDEX rescale expected pre-state", false)
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub struct ZDEXBucketScaleV1 {
    pub bucket_id: String,
    pub before_atoms: u128,
    pub after_atoms: u128,
}

impl ZDEXBucketScaleV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.bucket_id, "ZDEX scaled bucket id")
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ZDEXPrecisionEffectV1 {
    pub scale_factor: u128,
    pub supply_before_atoms: u128,
    pub supply_after_atoms: u128,
    pub bucket_scales: Vec<ZDEXBucketScaleV1>,
    pub authorized_issue_atoms: u128,
    pub authorized_burn_atoms: u128,
    pub burn_budget_remaining_before_atoms: u128,
    pub burn_budget_remaining_after_atoms: u128,
}

impl ZDEXPrecisionEffectV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.scale_factor <= 1
            || self.bucket_scales.is_empty()
            || self.bucket_scales.len() > MAX_ZDEX_PROJECTION_BUCKETS_V1
        {
            return Err(AbiErrorV1::InvalidBounds("ZDEX precision effect"));
        }
        if self.supply_before_atoms.checked_mul(self.scale_factor) != Some(self.supply_after_atoms)
        {
            return Err(AbiErrorV1::InvalidBinding("ZDEX precision supply scale"));
        }
        if self
            .bucket_scales
            .windows(2)
            .any(|pair| pair[0].bucket_id >= pair[1].bucket_id)
        {
            return Err(AbiErrorV1::InvalidOrder("ZDEX precision bucket scales"));
        }
        let mut before_total = 0_u128;
        let mut after_total = 0_u128;
        for row in &self.bucket_scales {
            row.validate()?;
            if row.before_atoms.checked_mul(self.scale_factor) != Some(row.after_atoms) {
                return Err(AbiErrorV1::InvalidBinding("ZDEX precision bucket scale"));
            }
            before_total = before_total
                .checked_add(row.before_atoms)
                .ok_or(AbiErrorV1::Conservation("ZDEX precision before sum"))?;
            after_total = after_total
                .checked_add(row.after_atoms)
                .ok_or(AbiErrorV1::Conservation("ZDEX precision after sum"))?;
        }
        if before_total != self.supply_before_atoms
            || after_total != self.supply_after_atoms
            || self
                .burn_budget_remaining_before_atoms
                .checked_mul(self.scale_factor)
                != Some(self.burn_budget_remaining_after_atoms)
            || self.authorized_issue_atoms != 0
            || self.authorized_burn_atoms != 0
        {
            return Err(AbiErrorV1::InvalidBinding(
                "ZDEX precision effect projection",
            ));
        }
        Ok(())
    }
}
