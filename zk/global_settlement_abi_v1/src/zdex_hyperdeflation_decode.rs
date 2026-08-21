//! Fail-closed decoding for bounded ZDEX hyperdeflation projections.

use core::fmt;
use core::marker::PhantomData;

use serde::de::{Error as _, SeqAccess, Visitor};
use serde::{Deserialize, Deserializer};

use crate::canonical::RootV1;
use crate::zdex_hyperdeflation_types::{
    ZDEXAmountBucketV1, ZDEXBurnRouteContextV1, ZDEXHyperdeflationPolicyV1,
    ZDEXPrecisionRescaleCommandV1, ZDEXPurchaseAndBurnCommandV1, ZDEXSupplyStateV1,
    MAX_ZDEX_PROJECTION_BUCKETS_V1,
};

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ZDEXHyperdeflationPolicyWireV1 {
    asset_id: RootV1,
    retained_numerator: u64,
    retained_denominator: u64,
    maximum_decimals: u64,
    maximum_decimal_step: u64,
}

impl<'de> Deserialize<'de> for ZDEXHyperdeflationPolicyV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = ZDEXHyperdeflationPolicyWireV1::deserialize(deserializer)?;
        let policy = Self {
            asset_id: wire.asset_id,
            retained_numerator: wire.retained_numerator,
            retained_denominator: wire.retained_denominator,
            maximum_decimals: wire.maximum_decimals,
            maximum_decimal_step: wire.maximum_decimal_step,
        };
        policy
            .validate()
            .map_err(|error| D::Error::custom(format!("invalid ZDEX policy: {error:?}")))?;
        Ok(policy)
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ZDEXAmountBucketWireV1 {
    bucket_id: String,
    amount_atoms: u128,
}

impl<'de> Deserialize<'de> for ZDEXAmountBucketV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = ZDEXAmountBucketWireV1::deserialize(deserializer)?;
        let bucket = Self {
            bucket_id: wire.bucket_id,
            amount_atoms: wire.amount_atoms,
        };
        bucket
            .validate()
            .map_err(|error| D::Error::custom(format!("invalid ZDEX amount bucket: {error:?}")))?;
        Ok(bucket)
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ZDEXSupplyStateWireV1 {
    asset_id: RootV1,
    policy_root: RootV1,
    decimals: u64,
    precision_epoch: u64,
    live_supply_atoms: u128,
    #[serde(deserialize_with = "deserialize_zdex_amount_buckets_v1")]
    buckets: Vec<ZDEXAmountBucketV1>,
    burn_budget_epoch: u64,
    remaining_epoch_burn_cap_atoms: u128,
}

impl<'de> Deserialize<'de> for ZDEXSupplyStateV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = ZDEXSupplyStateWireV1::deserialize(deserializer)?;
        let state = Self {
            asset_id: wire.asset_id,
            policy_root: wire.policy_root,
            decimals: wire.decimals,
            precision_epoch: wire.precision_epoch,
            live_supply_atoms: wire.live_supply_atoms,
            buckets: wire.buckets,
            burn_budget_epoch: wire.burn_budget_epoch,
            remaining_epoch_burn_cap_atoms: wire.remaining_epoch_burn_cap_atoms,
        };
        state
            .validate()
            .map_err(|error| D::Error::custom(format!("invalid ZDEX supply state: {error:?}")))?;
        Ok(state)
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ZDEXBurnRouteContextWireV1 {
    route_release_id: RootV1,
    policy_root: RootV1,
    purchase_occurrence_root: RootV1,
    burn_source_bucket_id: String,
    purchased_zdex_atoms: u128,
    source_reserve_floor_atoms: u128,
    remaining_epoch_burn_cap_atoms: u128,
    route_safe_output_cap_atoms: u128,
    burn_budget_epoch: u64,
}

impl<'de> Deserialize<'de> for ZDEXBurnRouteContextV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = ZDEXBurnRouteContextWireV1::deserialize(deserializer)?;
        let context = Self {
            route_release_id: wire.route_release_id,
            policy_root: wire.policy_root,
            purchase_occurrence_root: wire.purchase_occurrence_root,
            burn_source_bucket_id: wire.burn_source_bucket_id,
            purchased_zdex_atoms: wire.purchased_zdex_atoms,
            source_reserve_floor_atoms: wire.source_reserve_floor_atoms,
            remaining_epoch_burn_cap_atoms: wire.remaining_epoch_burn_cap_atoms,
            route_safe_output_cap_atoms: wire.route_safe_output_cap_atoms,
            burn_budget_epoch: wire.burn_budget_epoch,
        };
        context
            .validate()
            .map_err(|error| D::Error::custom(format!("invalid ZDEX burn context: {error:?}")))?;
        Ok(context)
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ZDEXPurchaseAndBurnCommandWireV1 {
    expected_pre_state_root: RootV1,
    expected_precision_epoch: u64,
    expected_purchase_occurrence_root: RootV1,
    source_bucket_id: String,
    purchased_zdex_atoms: u128,
}

impl<'de> Deserialize<'de> for ZDEXPurchaseAndBurnCommandV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = ZDEXPurchaseAndBurnCommandWireV1::deserialize(deserializer)?;
        let command = Self {
            expected_pre_state_root: wire.expected_pre_state_root,
            expected_precision_epoch: wire.expected_precision_epoch,
            expected_purchase_occurrence_root: wire.expected_purchase_occurrence_root,
            source_bucket_id: wire.source_bucket_id,
            purchased_zdex_atoms: wire.purchased_zdex_atoms,
        };
        command
            .validate()
            .map_err(|error| D::Error::custom(format!("invalid ZDEX burn command: {error:?}")))?;
        Ok(command)
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ZDEXPrecisionRescaleCommandWireV1 {
    expected_pre_state_root: RootV1,
    expected_precision_epoch: u64,
    additional_decimals: u64,
}

impl<'de> Deserialize<'de> for ZDEXPrecisionRescaleCommandV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = ZDEXPrecisionRescaleCommandWireV1::deserialize(deserializer)?;
        let command = Self {
            expected_pre_state_root: wire.expected_pre_state_root,
            expected_precision_epoch: wire.expected_precision_epoch,
            additional_decimals: wire.additional_decimals,
        };
        command.validate().map_err(|error| {
            D::Error::custom(format!("invalid ZDEX precision command: {error:?}"))
        })?;
        Ok(command)
    }
}

fn deserialize_zdex_amount_buckets_v1<'de, D>(
    deserializer: D,
) -> Result<Vec<ZDEXAmountBucketV1>, D::Error>
where
    D: Deserializer<'de>,
{
    deserialize_bounded_zdex_vec_v1(deserializer, "ZDEX state buckets")
}

fn deserialize_bounded_zdex_vec_v1<'de, D, T>(
    deserializer: D,
    label: &'static str,
) -> Result<Vec<T>, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de>,
{
    deserializer.deserialize_seq(BoundedZDEXVecVisitorV1 {
        label,
        marker: PhantomData,
    })
}

struct BoundedZDEXVecVisitorV1<T> {
    label: &'static str,
    marker: PhantomData<T>,
}

impl<'de, T> Visitor<'de> for BoundedZDEXVecVisitorV1<T>
where
    T: Deserialize<'de>,
{
    type Value = Vec<T>;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "{} with at most {} entries",
            self.label, MAX_ZDEX_PROJECTION_BUCKETS_V1
        )
    }

    fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        if sequence
            .size_hint()
            .is_some_and(|size| size > MAX_ZDEX_PROJECTION_BUCKETS_V1)
        {
            return Err(A::Error::custom("ZDEX projection exceeds the V1 bound"));
        }
        let mut values = Vec::with_capacity(
            sequence
                .size_hint()
                .unwrap_or(0)
                .min(MAX_ZDEX_PROJECTION_BUCKETS_V1),
        );
        while let Some(value) = sequence.next_element()? {
            if values.len() == MAX_ZDEX_PROJECTION_BUCKETS_V1 {
                return Err(A::Error::custom("ZDEX projection exceeds the V1 bound"));
            }
            values.push(value);
        }
        Ok(values)
    }
}
