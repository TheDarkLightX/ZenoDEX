//! Fresh unmounted SRGD-v1 fee-apportionment candidate kernel.
//!
//! This module implements arithmetic, sparse deficit state, and canonical
//! evidence bytes only. It has no settlement, balance, receipt, commit, shell,
//! or mounted-runtime authority.

use std::collections::BTreeMap;

use num_bigint::{BigInt, BigUint};

use crate::canonical::{canonical_json_bytes, sha256_hex, JsonValue};

pub const BPS_DENOMINATOR_V2: u32 = 10_000;
pub const MAX_FEE_AMOUNT_CANDIDATES_V2: usize = 256;
pub const MAX_FEE_APPORTIONMENT_KEYS_V2: usize = 50_000;
pub const SRGD_ALGORITHM_VERSION_V1: &str = "SUPPORT_RESPECTING_GREEDY_DEFICIT_V1";

pub const COMMITTED_FEE_APPORTIONMENT_STATE_SCHEMA_ID_V2: &str =
    "zenodex/fcis/fee-apportionment/committed-state/v2";
pub const ASSET_FEE_ALLOCATION_BATCH_SCHEMA_ID_V2: &str =
    "zenodex/fcis/fee-apportionment/asset-allocation-batch/v2";
pub const FEE_APPORTIONMENT_TRANSITION_RESULT_SCHEMA_ID_V2: &str =
    "zenodex/fcis/fee-apportionment/transition-result/v2";

const MAX_TEXT_CHARACTERS_V2: usize = 4_096;
const MAX_TEXT_UTF8_BYTES_V2: usize = 16_384;
const BPS_DENOMINATOR_I32_V2: i32 = 10_000;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FeeApportionmentTransitionCodeV2 {
    WrongExactType,
    ItemLimit,
    NoncanonicalIdentifier,
    AmountOutOfRange,
    InvalidPolicy,
    InvalidPrestate,
    AggregateOverflow,
    InternalRelationFailure,
}

impl FeeApportionmentTransitionCodeV2 {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::WrongExactType => "wrong_exact_type",
            Self::ItemLimit => "item_limit",
            Self::NoncanonicalIdentifier => "noncanonical_identifier",
            Self::AmountOutOfRange => "amount_out_of_range",
            Self::InvalidPolicy => "invalid_policy",
            Self::InvalidPrestate => "invalid_prestate",
            Self::AggregateOverflow => "aggregate_overflow",
            Self::InternalRelationFailure => "internal_relation_failure",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FeeApportionmentTransitionRejectV2 {
    code: FeeApportionmentTransitionCodeV2,
    path: Vec<String>,
}

impl FeeApportionmentTransitionRejectV2 {
    fn new(code: FeeApportionmentTransitionCodeV2, path: &[&str]) -> Self {
        Self {
            code,
            path: path.iter().map(|part| (*part).to_owned()).collect(),
        }
    }

    fn dynamic(code: FeeApportionmentTransitionCodeV2, path: Vec<String>) -> Self {
        Self { code, path }
    }

    pub fn code(&self) -> FeeApportionmentTransitionCodeV2 {
        self.code
    }

    pub fn path(&self) -> &[String] {
        &self.path
    }
}

fn u256_max() -> BigUint {
    (BigUint::from(1_u8) << 256_usize) - BigUint::from(1_u8)
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct AmountU256(BigUint);

impl AmountU256 {
    pub fn try_new(value: BigUint) -> Result<Self, FeeApportionmentTransitionRejectV2> {
        if value > u256_max() {
            return Err(FeeApportionmentTransitionRejectV2::new(
                FeeApportionmentTransitionCodeV2::AmountOutOfRange,
                &["amount"],
            ));
        }
        Ok(Self(value))
    }

    pub fn try_from_decimal(value: &str) -> Result<Self, FeeApportionmentTransitionRejectV2> {
        let parsed = BigUint::parse_bytes(value.as_bytes(), 10).ok_or_else(|| {
            FeeApportionmentTransitionRejectV2::new(
                FeeApportionmentTransitionCodeV2::WrongExactType,
                &["amount"],
            )
        })?;
        Self::try_new(parsed)
    }

    pub fn zero() -> Self {
        Self(BigUint::ZERO)
    }

    pub fn as_biguint(&self) -> &BigUint {
        &self.0
    }
}

fn text_is_canonical(value: &str) -> bool {
    !value.is_empty()
        && value.chars().count() <= MAX_TEXT_CHARACTERS_V2
        && value.len() <= MAX_TEXT_UTF8_BYTES_V2
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct FeeApportionmentKeyV2 {
    fee_distribution_domain_id: String,
    asset: String,
}

impl FeeApportionmentKeyV2 {
    pub fn try_new(
        fee_distribution_domain_id: String,
        asset: String,
    ) -> Result<Self, FeeApportionmentTransitionRejectV2> {
        if !text_is_canonical(&fee_distribution_domain_id) {
            return Err(FeeApportionmentTransitionRejectV2::new(
                FeeApportionmentTransitionCodeV2::NoncanonicalIdentifier,
                &["key", "fee_distribution_domain_id"],
            ));
        }
        if !text_is_canonical(&asset) {
            return Err(FeeApportionmentTransitionRejectV2::new(
                FeeApportionmentTransitionCodeV2::NoncanonicalIdentifier,
                &["key", "asset"],
            ));
        }
        Ok(Self {
            fee_distribution_domain_id,
            asset,
        })
    }

    pub fn fee_distribution_domain_id(&self) -> &str {
        &self.fee_distribution_domain_id
    }

    pub fn asset(&self) -> &str {
        &self.asset
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FeeAmountCandidateV2 {
    key: FeeApportionmentKeyV2,
    amount: AmountU256,
}

impl FeeAmountCandidateV2 {
    pub fn new(key: FeeApportionmentKeyV2, amount: AmountU256) -> Self {
        Self { key, amount }
    }

    pub fn key(&self) -> &FeeApportionmentKeyV2 {
        &self.key
    }

    pub fn amount(&self) -> &AmountU256 {
        &self.amount
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FeeDeficitEntryV2 {
    key: FeeApportionmentKeyV2,
    deficit_buyback: i32,
    deficit_treasury: i32,
}

impl FeeDeficitEntryV2 {
    pub fn try_new(
        key: FeeApportionmentKeyV2,
        deficit_buyback: i32,
        deficit_treasury: i32,
    ) -> Result<Self, FeeApportionmentTransitionRejectV2> {
        let entry = Self {
            key,
            deficit_buyback,
            deficit_treasury,
        };
        let deficits = entry.deficits();
        if deficits
            .iter()
            .any(|value| !(-BPS_DENOMINATOR_I32_V2 < *value && *value < BPS_DENOMINATOR_I32_V2))
            || deficits == [0, 0, 0]
        {
            return Err(FeeApportionmentTransitionRejectV2::new(
                FeeApportionmentTransitionCodeV2::InvalidPrestate,
                &["state", "entries", "deficits"],
            ));
        }
        Ok(entry)
    }

    pub fn key(&self) -> &FeeApportionmentKeyV2 {
        &self.key
    }

    pub fn deficit_buyback(&self) -> i32 {
        self.deficit_buyback
    }

    pub fn deficit_treasury(&self) -> i32 {
        self.deficit_treasury
    }

    pub fn deficits(&self) -> [i32; 3] {
        [
            self.deficit_buyback,
            self.deficit_treasury,
            -self.deficit_buyback - self.deficit_treasury,
        ]
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CommittedFeeApportionmentStateV2 {
    algorithm_version: String,
    entries: Vec<FeeDeficitEntryV2>,
}

impl CommittedFeeApportionmentStateV2 {
    pub fn empty() -> Self {
        Self {
            algorithm_version: SRGD_ALGORITHM_VERSION_V1.to_owned(),
            entries: Vec::new(),
        }
    }

    pub fn try_new(
        algorithm_version: String,
        entries: Vec<FeeDeficitEntryV2>,
    ) -> Result<Self, FeeApportionmentTransitionRejectV2> {
        if algorithm_version != SRGD_ALGORITHM_VERSION_V1 {
            return Err(FeeApportionmentTransitionRejectV2::new(
                FeeApportionmentTransitionCodeV2::InvalidPrestate,
                &["state", "algorithm_version"],
            ));
        }
        if entries.len() > MAX_FEE_APPORTIONMENT_KEYS_V2 {
            return Err(FeeApportionmentTransitionRejectV2::new(
                FeeApportionmentTransitionCodeV2::ItemLimit,
                &["state", "entries"],
            ));
        }
        for pair in entries.windows(2) {
            if pair[0].key >= pair[1].key {
                return Err(FeeApportionmentTransitionRejectV2::new(
                    FeeApportionmentTransitionCodeV2::InvalidPrestate,
                    &["state", "entries", "protocol_order"],
                ));
            }
        }
        Ok(Self {
            algorithm_version,
            entries,
        })
    }

    pub fn algorithm_version(&self) -> &str {
        &self.algorithm_version
    }

    pub fn entries(&self) -> &[FeeDeficitEntryV2] {
        &self.entries
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FeeDistributionPolicyV2 {
    weights: [u16; 3],
    destinations: [String; 3],
}

impl FeeDistributionPolicyV2 {
    pub fn try_new(
        weights: [u16; 3],
        destinations: [String; 3],
    ) -> Result<Self, FeeApportionmentTransitionRejectV2> {
        if weights
            .iter()
            .any(|weight| u32::from(*weight) > BPS_DENOMINATOR_V2)
            || weights.iter().map(|weight| u32::from(*weight)).sum::<u32>() != BPS_DENOMINATOR_V2
        {
            return Err(FeeApportionmentTransitionRejectV2::new(
                FeeApportionmentTransitionCodeV2::InvalidPolicy,
                &["policy", "weights"],
            ));
        }
        if destinations.iter().any(|value| !text_is_canonical(value)) {
            return Err(FeeApportionmentTransitionRejectV2::new(
                FeeApportionmentTransitionCodeV2::NoncanonicalIdentifier,
                &["policy", "destinations"],
            ));
        }
        Ok(Self {
            weights,
            destinations,
        })
    }

    pub fn weights(&self) -> [u16; 3] {
        self.weights
    }

    pub fn destinations(&self) -> &[String; 3] {
        &self.destinations
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssetFeeAllocationV2 {
    key: FeeApportionmentKeyV2,
    amount: AmountU256,
    destinations: [String; 3],
    fractions: [u16; 3],
    bonuses: [u8; 3],
    amounts: [AmountU256; 3],
    deficits_pre: [i32; 3],
    deficits_post: [i32; 3],
}

impl AssetFeeAllocationV2 {
    pub fn key(&self) -> &FeeApportionmentKeyV2 {
        &self.key
    }

    pub fn amount(&self) -> &AmountU256 {
        &self.amount
    }

    pub fn destinations(&self) -> &[String; 3] {
        &self.destinations
    }

    pub fn fractions(&self) -> [u16; 3] {
        self.fractions
    }

    pub fn bonuses(&self) -> [u8; 3] {
        self.bonuses
    }

    pub fn amounts(&self) -> &[AmountU256; 3] {
        &self.amounts
    }

    pub fn deficits_pre(&self) -> [i32; 3] {
        self.deficits_pre
    }

    pub fn deficits_post(&self) -> [i32; 3] {
        self.deficits_post
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FeeApportionmentTransitionOkV2 {
    state: CommittedFeeApportionmentStateV2,
    allocations: Vec<AssetFeeAllocationV2>,
}

impl FeeApportionmentTransitionOkV2 {
    pub fn state(&self) -> &CommittedFeeApportionmentStateV2 {
        &self.state
    }

    pub fn allocations(&self) -> &[AssetFeeAllocationV2] {
        &self.allocations
    }
}

fn select_bonuses(
    deficits: [i32; 3],
    fractions: [u16; 3],
    denominator: u16,
) -> Result<[u8; 3], FeeApportionmentTransitionRejectV2> {
    if denominator == 0
        || fractions.iter().any(|value| *value >= denominator)
        || fractions.iter().map(|value| u32::from(*value)).sum::<u32>() % u32::from(denominator)
            != 0
    {
        return Err(FeeApportionmentTransitionRejectV2::new(
            FeeApportionmentTransitionCodeV2::InternalRelationFailure,
            &["relation", "selector_input"],
        ));
    }
    let sum = fractions.iter().map(|value| u32::from(*value)).sum::<u32>();
    let seat_count = usize::try_from(sum / u32::from(denominator)).map_err(|_| {
        FeeApportionmentTransitionRejectV2::new(
            FeeApportionmentTransitionCodeV2::InternalRelationFailure,
            &["relation", "selector_count"],
        )
    })?;
    if seat_count > 2 {
        return Err(FeeApportionmentTransitionRejectV2::new(
            FeeApportionmentTransitionCodeV2::InternalRelationFailure,
            &["relation", "selector_count"],
        ));
    }
    let mut eligible: Vec<usize> = (0..3).filter(|index| fractions[*index] > 0).collect();
    if eligible.len() < seat_count {
        return Err(FeeApportionmentTransitionRejectV2::new(
            FeeApportionmentTransitionCodeV2::InternalRelationFailure,
            &["relation", "selector_support"],
        ));
    }
    eligible.sort_by(|left, right| {
        let left_score = deficits[*left] + i32::from(fractions[*left]);
        let right_score = deficits[*right] + i32::from(fractions[*right]);
        right_score.cmp(&left_score).then_with(|| left.cmp(right))
    });
    let mut bonuses = [0_u8; 3];
    for index in eligible.into_iter().take(seat_count) {
        bonuses[index] = 1;
    }
    Ok(bonuses)
}

fn small_biguint_to_u32(value: &BigUint) -> Option<u32> {
    let digits = value.to_u32_digits();
    match digits.as_slice() {
        [] => Some(0),
        [single] => Some(*single),
        _ => None,
    }
}

fn allocate_one(
    key: FeeApportionmentKeyV2,
    amount: BigUint,
    policy: &FeeDistributionPolicyV2,
    deficits_pre: [i32; 3],
) -> Result<AssetFeeAllocationV2, FeeApportionmentTransitionRejectV2> {
    let denominator = BigUint::from(BPS_DENOMINATOR_V2);
    let cycles = &amount / &denominator;
    let remainder_big = &amount % &denominator;
    let remainder = small_biguint_to_u32(&remainder_big).ok_or_else(|| {
        FeeApportionmentTransitionRejectV2::new(
            FeeApportionmentTransitionCodeV2::InternalRelationFailure,
            &["relation", "remainder"],
        )
    })?;
    let weights = policy.weights();
    let products = [
        remainder * u32::from(weights[0]),
        remainder * u32::from(weights[1]),
        remainder * u32::from(weights[2]),
    ];
    let lowers = [
        &cycles * BigUint::from(weights[0]) + BigUint::from(products[0] / BPS_DENOMINATOR_V2),
        &cycles * BigUint::from(weights[1]) + BigUint::from(products[1] / BPS_DENOMINATOR_V2),
        &cycles * BigUint::from(weights[2]) + BigUint::from(products[2] / BPS_DENOMINATOR_V2),
    ];
    let fractions = [
        u16::try_from(products[0] % BPS_DENOMINATOR_V2).map_err(|_| {
            FeeApportionmentTransitionRejectV2::new(
                FeeApportionmentTransitionCodeV2::InternalRelationFailure,
                &["relation", "fraction"],
            )
        })?,
        u16::try_from(products[1] % BPS_DENOMINATOR_V2).map_err(|_| {
            FeeApportionmentTransitionRejectV2::new(
                FeeApportionmentTransitionCodeV2::InternalRelationFailure,
                &["relation", "fraction"],
            )
        })?,
        u16::try_from(products[2] % BPS_DENOMINATOR_V2).map_err(|_| {
            FeeApportionmentTransitionRejectV2::new(
                FeeApportionmentTransitionCodeV2::InternalRelationFailure,
                &["relation", "fraction"],
            )
        })?,
    ];
    let bonuses = select_bonuses(
        deficits_pre,
        fractions,
        u16::try_from(BPS_DENOMINATOR_V2).map_err(|_| {
            FeeApportionmentTransitionRejectV2::new(
                FeeApportionmentTransitionCodeV2::InternalRelationFailure,
                &["relation", "denominator"],
            )
        })?,
    )?;
    let amount_values = [
        &lowers[0] + BigUint::from(bonuses[0]),
        &lowers[1] + BigUint::from(bonuses[1]),
        &lowers[2] + BigUint::from(bonuses[2]),
    ];
    let deficits_post = [
        deficits_pre[0] + i32::from(fractions[0]) - BPS_DENOMINATOR_I32_V2 * i32::from(bonuses[0]),
        deficits_pre[1] + i32::from(fractions[1]) - BPS_DENOMINATOR_I32_V2 * i32::from(bonuses[1]),
        deficits_pre[2] + i32::from(fractions[2]) - BPS_DENOMINATOR_I32_V2 * i32::from(bonuses[2]),
    ];
    let amount_sum = &amount_values[0] + &amount_values[1] + &amount_values[2];
    if amount_sum != amount
        || deficits_post.iter().sum::<i32>() != 0
        || deficits_post
            .iter()
            .any(|value| !(-BPS_DENOMINATOR_I32_V2 < *value && *value < BPS_DENOMINATOR_I32_V2))
        || bonuses
            .iter()
            .zip(fractions.iter())
            .any(|(bonus, fraction)| *bonus == 1 && *fraction == 0)
        || amount_values.iter().any(|value| value > &u256_max())
    {
        return Err(FeeApportionmentTransitionRejectV2::new(
            FeeApportionmentTransitionCodeV2::InternalRelationFailure,
            &["relation", "postconditions"],
        ));
    }
    Ok(AssetFeeAllocationV2 {
        key,
        amount: AmountU256::try_new(amount)?,
        destinations: policy.destinations.clone(),
        fractions,
        bonuses,
        amounts: [
            AmountU256::try_new(amount_values[0].clone())?,
            AmountU256::try_new(amount_values[1].clone())?,
            AmountU256::try_new(amount_values[2].clone())?,
        ],
        deficits_pre,
        deficits_post,
    })
}

pub fn apply_fee_apportionment_v2(
    contributions: &[FeeAmountCandidateV2],
    policy: &FeeDistributionPolicyV2,
    state: &CommittedFeeApportionmentStateV2,
) -> Result<FeeApportionmentTransitionOkV2, FeeApportionmentTransitionRejectV2> {
    if contributions.len() > MAX_FEE_AMOUNT_CANDIDATES_V2 {
        return Err(FeeApportionmentTransitionRejectV2::new(
            FeeApportionmentTransitionCodeV2::ItemLimit,
            &["contributions"],
        ));
    }
    let mut grouped: BTreeMap<FeeApportionmentKeyV2, BigUint> = BTreeMap::new();
    for candidate in contributions {
        let total = grouped
            .entry(candidate.key.clone())
            .or_insert_with(|| BigUint::ZERO);
        *total += candidate.amount.as_biguint();
    }
    for (key, amount) in &grouped {
        if amount > &u256_max() {
            return Err(FeeApportionmentTransitionRejectV2::dynamic(
                FeeApportionmentTransitionCodeV2::AggregateOverflow,
                vec![
                    "contributions".to_owned(),
                    "aggregate".to_owned(),
                    key.fee_distribution_domain_id.clone(),
                    key.asset.clone(),
                ],
            ));
        }
    }

    let mut state_by_key: BTreeMap<FeeApportionmentKeyV2, FeeDeficitEntryV2> = state
        .entries
        .iter()
        .cloned()
        .map(|entry| (entry.key.clone(), entry))
        .collect();
    let mut allocations = Vec::with_capacity(grouped.len());
    for (key, amount) in grouped {
        let deficits_pre = state_by_key
            .get(&key)
            .map(FeeDeficitEntryV2::deficits)
            .unwrap_or([0, 0, 0]);
        let allocation = allocate_one(key.clone(), amount, policy, deficits_pre)?;
        if allocation.deficits_post == [0, 0, 0] {
            state_by_key.remove(&key);
        } else {
            state_by_key.insert(
                key.clone(),
                FeeDeficitEntryV2::try_new(
                    key,
                    allocation.deficits_post[0],
                    allocation.deficits_post[1],
                )?,
            );
        }
        allocations.push(allocation);
    }
    let next_state = CommittedFeeApportionmentStateV2::try_new(
        SRGD_ALGORITHM_VERSION_V1.to_owned(),
        state_by_key.into_values().collect(),
    )?;
    Ok(FeeApportionmentTransitionOkV2 {
        state: next_state,
        allocations,
    })
}

fn int_json<T: Into<BigInt>>(value: T) -> JsonValue {
    JsonValue::Int(value.into())
}

fn key_json(value: &FeeApportionmentKeyV2) -> JsonValue {
    JsonValue::Object(vec![
        (
            "fee_distribution_domain_id".to_owned(),
            JsonValue::Str(value.fee_distribution_domain_id.clone()),
        ),
        ("asset".to_owned(), JsonValue::Str(value.asset.clone())),
    ])
}

fn deficit_entry_json(value: &FeeDeficitEntryV2) -> JsonValue {
    JsonValue::Object(vec![
        ("key".to_owned(), key_json(&value.key)),
        (
            "deficit_buyback".to_owned(),
            int_json(value.deficit_buyback),
        ),
        (
            "deficit_treasury".to_owned(),
            int_json(value.deficit_treasury),
        ),
    ])
}

fn state_json(value: &CommittedFeeApportionmentStateV2) -> JsonValue {
    JsonValue::Object(vec![
        (
            "algorithm_version".to_owned(),
            JsonValue::Str(value.algorithm_version.clone()),
        ),
        (
            "entries".to_owned(),
            JsonValue::Array(value.entries.iter().map(deficit_entry_json).collect()),
        ),
    ])
}

fn allocation_json(value: &AssetFeeAllocationV2) -> JsonValue {
    JsonValue::Object(vec![
        ("key".to_owned(), key_json(&value.key)),
        ("amount".to_owned(), int_json(value.amount.0.clone())),
        (
            "buyback_destination".to_owned(),
            JsonValue::Str(value.destinations[0].clone()),
        ),
        (
            "treasury_destination".to_owned(),
            JsonValue::Str(value.destinations[1].clone()),
        ),
        (
            "rewards_destination".to_owned(),
            JsonValue::Str(value.destinations[2].clone()),
        ),
        ("buyback_fraction".to_owned(), int_json(value.fractions[0])),
        ("treasury_fraction".to_owned(), int_json(value.fractions[1])),
        ("rewards_fraction".to_owned(), int_json(value.fractions[2])),
        ("buyback_bonus".to_owned(), int_json(value.bonuses[0])),
        ("treasury_bonus".to_owned(), int_json(value.bonuses[1])),
        ("rewards_bonus".to_owned(), int_json(value.bonuses[2])),
        (
            "buyback_amount".to_owned(),
            int_json(value.amounts[0].0.clone()),
        ),
        (
            "treasury_amount".to_owned(),
            int_json(value.amounts[1].0.clone()),
        ),
        (
            "rewards_amount".to_owned(),
            int_json(value.amounts[2].0.clone()),
        ),
        (
            "deficit_buyback_pre".to_owned(),
            int_json(value.deficits_pre[0]),
        ),
        (
            "deficit_treasury_pre".to_owned(),
            int_json(value.deficits_pre[1]),
        ),
        (
            "deficit_rewards_pre".to_owned(),
            int_json(value.deficits_pre[2]),
        ),
        (
            "deficit_buyback_post".to_owned(),
            int_json(value.deficits_post[0]),
        ),
        (
            "deficit_treasury_post".to_owned(),
            int_json(value.deficits_post[1]),
        ),
        (
            "deficit_rewards_post".to_owned(),
            int_json(value.deficits_post[2]),
        ),
    ])
}

fn envelope(schema: &str, value: JsonValue) -> Vec<u8> {
    canonical_json_bytes(&JsonValue::Object(vec![
        ("schema".to_owned(), JsonValue::Str(schema.to_owned())),
        ("value".to_owned(), value),
    ]))
}

pub fn encode_state_v2(value: &CommittedFeeApportionmentStateV2) -> Vec<u8> {
    envelope(
        COMMITTED_FEE_APPORTIONMENT_STATE_SCHEMA_ID_V2,
        state_json(value),
    )
}

pub fn encode_allocations_v2(value: &[AssetFeeAllocationV2]) -> Vec<u8> {
    envelope(
        ASSET_FEE_ALLOCATION_BATCH_SCHEMA_ID_V2,
        JsonValue::Array(value.iter().map(allocation_json).collect()),
    )
}

pub fn encode_result_v2(value: &FeeApportionmentTransitionOkV2) -> Vec<u8> {
    envelope(
        FEE_APPORTIONMENT_TRANSITION_RESULT_SCHEMA_ID_V2,
        JsonValue::Object(vec![
            ("state".to_owned(), state_json(&value.state)),
            (
                "allocations".to_owned(),
                JsonValue::Array(value.allocations.iter().map(allocation_json).collect()),
            ),
        ]),
    )
}

pub fn canonical_evidence_sha256(bytes: &[u8]) -> String {
    sha256_hex(bytes)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture() -> serde_json::Value {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../../tests/fixtures/fcis_fee_apportionment_v2_golden.json"
        );
        let raw = std::fs::read_to_string(path).expect("shared fixture exists");
        serde_json::from_str(&raw).expect("shared fixture parses")
    }

    fn as_u16(value: &serde_json::Value) -> u16 {
        u16::try_from(value.as_u64().expect("fixture u16")).expect("fixture u16 bound")
    }

    fn as_i32(value: &serde_json::Value) -> i32 {
        i32::try_from(value.as_i64().expect("fixture i32")).expect("fixture i32 bound")
    }

    fn amount(value: &serde_json::Value) -> AmountU256 {
        AmountU256::try_from_decimal(&value.to_string()).expect("fixture U256")
    }

    fn key(value: &serde_json::Value) -> FeeApportionmentKeyV2 {
        FeeApportionmentKeyV2::try_new(
            value["fee_distribution_domain_id"]
                .as_str()
                .expect("fixture domain")
                .to_owned(),
            value["asset"].as_str().expect("fixture asset").to_owned(),
        )
        .expect("fixture key")
    }

    fn policy(value: &serde_json::Value) -> FeeDistributionPolicyV2 {
        FeeDistributionPolicyV2::try_new(
            [
                as_u16(&value["buyback_bps"]),
                as_u16(&value["treasury_bps"]),
                as_u16(&value["rewards_bps"]),
            ],
            [
                value["buyback_destination"]
                    .as_str()
                    .expect("fixture buyback destination")
                    .to_owned(),
                value["treasury_destination"]
                    .as_str()
                    .expect("fixture treasury destination")
                    .to_owned(),
                value["rewards_destination"]
                    .as_str()
                    .expect("fixture rewards destination")
                    .to_owned(),
            ],
        )
        .expect("fixture policy")
    }

    fn state(value: &serde_json::Value) -> CommittedFeeApportionmentStateV2 {
        let entries = value["entries"]
            .as_array()
            .expect("fixture state entries")
            .iter()
            .map(|entry| {
                FeeDeficitEntryV2::try_new(
                    key(&entry["key"]),
                    as_i32(&entry["deficit_buyback"]),
                    as_i32(&entry["deficit_treasury"]),
                )
                .expect("fixture deficit entry")
            })
            .collect();
        CommittedFeeApportionmentStateV2::try_new(
            value["algorithm_version"]
                .as_str()
                .expect("fixture algorithm")
                .to_owned(),
            entries,
        )
        .expect("fixture state")
    }

    #[test]
    fn rust_matches_every_shared_python_vector() {
        let document = fixture();
        let cases = document["cases"].as_array().expect("fixture cases");
        assert_eq!(cases.len(), 12);
        for case in cases {
            let input = &case["input"];
            let contributions: Vec<FeeAmountCandidateV2> = input["contributions"]
                .as_array()
                .expect("fixture contributions")
                .iter()
                .map(|candidate| {
                    FeeAmountCandidateV2::new(key(&candidate["key"]), amount(&candidate["amount"]))
                })
                .collect();
            let got = apply_fee_apportionment_v2(
                &contributions,
                &policy(&input["policy"]),
                &state(&input["state"]),
            );
            let expected = &case["expected"];
            if expected["accept"].as_bool().expect("fixture decision") {
                let accepted = got.unwrap_or_else(|error| {
                    panic!(
                        "case {} rejected: {} {:?}",
                        case["id"],
                        error.code.as_str(),
                        error.path
                    )
                });
                let canonical = &expected["canonical"];
                let state_bytes = encode_state_v2(&accepted.state);
                let allocation_bytes = encode_allocations_v2(&accepted.allocations);
                let result_bytes = encode_result_v2(&accepted);
                assert_eq!(
                    String::from_utf8(state_bytes.clone()).expect("state UTF-8"),
                    canonical["state_utf8"].as_str().expect("expected state"),
                    "case {} state bytes",
                    case["id"]
                );
                assert_eq!(
                    String::from_utf8(allocation_bytes.clone()).expect("allocation UTF-8"),
                    canonical["allocations_utf8"]
                        .as_str()
                        .expect("expected allocations"),
                    "case {} allocation bytes",
                    case["id"]
                );
                assert_eq!(
                    String::from_utf8(result_bytes.clone()).expect("result UTF-8"),
                    canonical["result_utf8"].as_str().expect("expected result"),
                    "case {} result bytes",
                    case["id"]
                );
                assert_eq!(
                    canonical_evidence_sha256(&state_bytes),
                    canonical["state_sha256"]
                        .as_str()
                        .expect("expected state digest")
                );
                assert_eq!(
                    canonical_evidence_sha256(&allocation_bytes),
                    canonical["allocations_sha256"]
                        .as_str()
                        .expect("expected allocations digest")
                );
                assert_eq!(
                    canonical_evidence_sha256(&result_bytes),
                    canonical["result_sha256"]
                        .as_str()
                        .expect("expected result digest")
                );
            } else {
                let rejected = got.expect_err("fixture expects rejection");
                assert_eq!(
                    rejected.code.as_str(),
                    expected["code"].as_str().expect("expected reject code")
                );
                let expected_path: Vec<String> = expected["path"]
                    .as_array()
                    .expect("expected reject path")
                    .iter()
                    .map(|part| part.as_str().expect("path part").to_owned())
                    .collect();
                assert_eq!(rejected.path, expected_path);
            }
        }
    }

    fn reference_selector(deficits: [i32; 3], fractions: [u16; 3], denominator: u16) -> [u8; 3] {
        let seats =
            fractions.iter().map(|value| u32::from(*value)).sum::<u32>() / u32::from(denominator);
        let mut candidates = Vec::new();
        for bits in 0_u8..8 {
            let bonus = [bits & 1, (bits >> 1) & 1, (bits >> 2) & 1];
            if bonus.iter().map(|value| u32::from(*value)).sum::<u32>() != seats {
                continue;
            }
            if (0..3).any(|index| bonus[index] == 1 && fractions[index] == 0) {
                continue;
            }
            let valid = (0..3).all(|chosen| {
                bonus[chosen] == 0
                    || (0..3).all(|skipped| {
                        bonus[skipped] == 1
                            || fractions[skipped] == 0
                            || (
                                deficits[chosen] + i32::from(fractions[chosen]),
                                -(chosen as i32),
                            ) >= (
                                deficits[skipped] + i32::from(fractions[skipped]),
                                -(skipped as i32),
                            )
                    })
            });
            if valid {
                candidates.push(bonus);
            }
        }
        assert_eq!(candidates.len(), 1);
        candidates[0]
    }

    #[test]
    fn selector_matches_independent_eight_tuple_oracle_at_d4() {
        let mut checked = 0_usize;
        for d0 in -3..=3 {
            for d1 in -3..=3 {
                let deficits = [d0, d1, -d0 - d1];
                if !(-4 < deficits[2] && deficits[2] < 4) {
                    continue;
                }
                for f0 in 0_u16..4 {
                    for f1 in 0_u16..4 {
                        for f2 in 0_u16..4 {
                            let fractions = [f0, f1, f2];
                            if !matches!(f0 + f1 + f2, 0 | 4 | 8) {
                                continue;
                            }
                            assert_eq!(
                                select_bonuses(deficits, fractions, 4).expect("valid selector"),
                                reference_selector(deficits, fractions, 4)
                            );
                            checked += 1;
                        }
                    }
                }
            }
        }
        assert_eq!(checked, 592);
    }
}
