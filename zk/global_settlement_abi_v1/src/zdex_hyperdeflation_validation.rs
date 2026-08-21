//! Cross-field validation for accepted ZDEX hyperdeflation transitions.

use crate::canonical::{AbiErrorV1, AbiResultV1};
use crate::zdex_hyperdeflation::{burned_bucket_projection_v1, compute_zdex_burn_capacity_v1};
use crate::zdex_hyperdeflation_results::{
    ZDEXPrecisionRescaleAcceptedV1, ZDEXPurchaseAndBurnAcceptedV1,
};
use crate::zdex_hyperdeflation_types::{
    ZDEXAmountBucketV1, ZDEXBucketScaleV1, MAX_DECIMAL_SCALE_STEP_V1,
};

impl ZDEXPurchaseAndBurnAcceptedV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.policy.validate()?;
        self.route_context.validate()?;
        self.pre_state.validate()?;
        self.post_state.validate()?;
        self.capacity.validate()?;
        self.effect.validate()?;
        if self.policy.asset_id != self.pre_state.asset_id
            || self.policy.policy_root()? != self.pre_state.policy_root
            || self.route_context.policy_root != self.policy.policy_root()?
        {
            return Err(AbiErrorV1::InvalidBinding("ZDEX accepted burn policy"));
        }
        if self.pre_state.decimals > self.policy.maximum_decimals {
            return Err(AbiErrorV1::InvalidBinding(
                "ZDEX accepted burn policy envelope",
            ));
        }
        if self.route_context.burn_budget_epoch != self.pre_state.burn_budget_epoch {
            return Err(AbiErrorV1::InvalidBinding(
                "ZDEX accepted burn budget epoch",
            ));
        }
        if self.effect.purchase_occurrence_root != self.route_context.purchase_occurrence_root
            || self.effect.source_bucket_id != self.route_context.burn_source_bucket_id
            || self.effect.authorized_burn_atoms != self.route_context.purchased_zdex_atoms
        {
            return Err(AbiErrorV1::InvalidBinding("ZDEX accepted burn route"));
        }
        let expected_capacity = compute_zdex_burn_capacity_v1(
            &self.policy,
            &self.pre_state,
            &self.route_context,
            &self.route_context.burn_source_bucket_id,
        )?
        .ok_or(AbiErrorV1::InvalidBinding("ZDEX accepted burn source"))?;
        if self.capacity != expected_capacity
            || self.effect.authorized_burn_atoms > self.capacity.maximum_burn_atoms
        {
            return Err(AbiErrorV1::InvalidBinding("ZDEX accepted burn capacity"));
        }
        let burn = self.effect.authorized_burn_atoms;
        if self.pre_state.asset_id != self.post_state.asset_id
            || self.pre_state.policy_root != self.post_state.policy_root
            || self.pre_state.decimals != self.post_state.decimals
            || self.pre_state.precision_epoch != self.post_state.precision_epoch
            || self.pre_state.burn_budget_epoch != self.post_state.burn_budget_epoch
            || self.pre_state.live_supply_atoms.checked_sub(burn)
                != Some(self.post_state.live_supply_atoms)
            || self
                .pre_state
                .remaining_epoch_burn_cap_atoms
                .checked_sub(burn)
                != Some(self.post_state.remaining_epoch_burn_cap_atoms)
            || self.post_state.live_supply_atoms < self.capacity.retained_supply_atoms
            || burned_bucket_projection_v1(&self.pre_state, &self.effect.source_bucket_id, burn)?
                != self.post_state.buckets
        {
            return Err(AbiErrorV1::InvalidBinding("ZDEX accepted burn post-state"));
        }
        Ok(())
    }
}

impl ZDEXPrecisionRescaleAcceptedV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.policy.validate()?;
        self.pre_state.validate()?;
        self.post_state.validate()?;
        self.effect.validate()?;
        if self.policy.asset_id != self.pre_state.asset_id
            || self.policy.policy_root()? != self.pre_state.policy_root
            || self.post_state.asset_id != self.pre_state.asset_id
            || self.post_state.policy_root != self.pre_state.policy_root
            || self.post_state.burn_budget_epoch != self.pre_state.burn_budget_epoch
            || self.pre_state.precision_epoch.checked_add(1)
                != Some(self.post_state.precision_epoch)
        {
            return Err(AbiErrorV1::InvalidBinding("ZDEX precision identity"));
        }
        let decimal_step = self
            .post_state
            .decimals
            .checked_sub(self.pre_state.decimals)
            .ok_or(AbiErrorV1::InvalidBinding("ZDEX precision decimal step"))?;
        if decimal_step == 0
            || decimal_step > MAX_DECIMAL_SCALE_STEP_V1
            || decimal_step > self.policy.maximum_decimal_step
            || self.post_state.decimals > self.policy.maximum_decimals
        {
            return Err(AbiErrorV1::InvalidBounds("ZDEX precision decimal step"));
        }
        let exponent = u32::try_from(decimal_step)
            .map_err(|_| AbiErrorV1::InvalidBounds("ZDEX precision exponent"))?;
        if 10_u128.checked_pow(exponent) != Some(self.effect.scale_factor)
            || self.effect.supply_before_atoms != self.pre_state.live_supply_atoms
            || self.effect.supply_after_atoms != self.post_state.live_supply_atoms
            || self.effect.burn_budget_remaining_before_atoms
                != self.pre_state.remaining_epoch_burn_cap_atoms
            || self.effect.burn_budget_remaining_after_atoms
                != self.post_state.remaining_epoch_burn_cap_atoms
        {
            return Err(AbiErrorV1::InvalidBinding("ZDEX precision effect"));
        }
        let expected_scales = self
            .pre_state
            .buckets
            .iter()
            .map(|bucket| {
                Ok(ZDEXBucketScaleV1 {
                    bucket_id: bucket.bucket_id.clone(),
                    before_atoms: bucket.amount_atoms,
                    after_atoms: bucket
                        .amount_atoms
                        .checked_mul(self.effect.scale_factor)
                        .ok_or(AbiErrorV1::InvalidBounds("ZDEX precision bucket"))?,
                })
            })
            .collect::<AbiResultV1<Vec<_>>>()?;
        let expected_buckets = expected_scales
            .iter()
            .map(|row| ZDEXAmountBucketV1 {
                bucket_id: row.bucket_id.clone(),
                amount_atoms: row.after_atoms,
            })
            .collect::<Vec<_>>();
        if self.effect.bucket_scales != expected_scales
            || self.post_state.buckets != expected_buckets
        {
            return Err(AbiErrorV1::InvalidBinding(
                "ZDEX precision bucket projection",
            ));
        }
        Ok(())
    }
}
