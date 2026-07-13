//! Network state-root shadow (v5).
//!
//! Byte-for-byte mirror of `compute_state_root` in `src/state/state_root.py`.
//! The root commits to six ordered sections: balances, pools, LP balances, LP
//! duration-risk metadata, nonces, and fee-accumulator dust, under a versioned
//! domain separator:
//!
//! ```text
//! sha256(
//!   domain_sep("state_root", v5)
//!   + b"BAL" + encode_bytes(balances_section)
//!   + b"POL" + encode_bytes(pools_section)
//!   + b"LPB" + encode_bytes(lp_section)
//!   + b"LPA" + encode_bytes(lp_duration_risk_section)
//!   + b"NNC" + encode_bytes(nonce_section)
//!   + b"FEE" + encode_bytes(fee_section)
//! )
//! ```
//!
//! Each entry's hex identifiers are decoded to fixed-width bytes
//! (`pubkey` 48, `asset`/`pool_id` 32) and entries are sorted by those *decoded
//! bytes*, not by hex string. Pool IDs are stricter: every occurrence must use
//! canonical lowercase `0x` form, and pool entries must match the ID recomputed
//! from assets, fee, and curve configuration. Duplicate decoded keys are a
//! typed rejection.
//!
//! Domain note: amounts are taken as `u128`. The Python encoder accepts up to
//! 256-bit uvarints, but every runtime state amount (balances ≤ 2^112−1,
//! reserves ≤ 3e9, nonces ≤ u32, …) is far below 2^128, so `u128` covers the
//! whole live domain. Values that do not fit `u128` are out of this shadow's
//! domain and are rejected at the CLI bridge rather than silently truncated.

use crate::canonical::{
    domain_sep_bytes, encode_bytes, encode_uvarint, hex_to_bytes_fixed, sha256_hex, CanonicalError,
};
use num_bigint::BigUint;
use std::collections::BTreeSet;

/// State-root encoding version (must equal `STATE_ROOT_VERSION` in Python).
pub const STATE_ROOT_VERSION: u32 = 5;

const PUBKEY_NBYTES: usize = 48;
const ASSET_NBYTES: usize = 32;
const POOL_NBYTES: usize = 32;
const MAX_FEE_BPS: u128 = 10_000;
const MAX_NONCE: u128 = 0xFFFF_FFFF;
const CURVE_TAG_CPMM: &str = "CPMM";
const CURVE_TAG_CUBIC_SUM_V1: &str = "CUBIC_SUM_V1";
const CURVE_TAG_SUM_BOOST_V1: &str = "SUM_BOOST_V1";
const CURVE_TAG_QUARTIC_BLEND_V1: &str = "QUARTIC_BLEND_V1";
const CURVE_TAG_QUINTIC_BLEND_V1: &str = "QUINTIC_BLEND_V1";

/// Typed rejection for state-root computation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StateRootError {
    /// A hex identifier failed `hex_to_bytes_fixed`.
    Hex(CanonicalError),
    /// Two entries decode to the same key in a section (`section` names it).
    DuplicateKey(&'static str),
    /// `fee_bps > 10000` for a pool.
    FeeBpsTooLarge,
    /// Pool status code outside `{1,2,3}`.
    UnknownPoolStatus,
    /// Nonce exceeds Python `NonceTable`'s u32 domain.
    NonceTooLarge,
    /// Sparse tables must not contain explicit zero amounts.
    ZeroAmount(&'static str),
    /// Pool assets are not in the Python authority's canonical byte order.
    NonCanonicalPoolAssets,
    /// Pool curve tag/params are unsupported or not in canonical normalized form.
    InvalidCurveConfig,
    /// A pool ID is not exact lowercase, 0x-prefixed, fixed-width hex.
    NonCanonicalPoolId,
    /// A pool ID does not bind the pool's assets, fee, and curve configuration.
    PoolIdentityMismatch,
    /// LP mint metadata exists for a non-existent or zero LP balance.
    MissingLpBalanceForMintMetadata,
    /// LP duration metadata entry would be dropped by Python's sparse filter.
    EmptyLpDurationMetadata,
}

impl StateRootError {
    pub fn code(&self) -> String {
        match self {
            StateRootError::Hex(e) => e.code().to_string(),
            StateRootError::DuplicateKey(section) => format!("duplicate_key:{section}"),
            StateRootError::FeeBpsTooLarge => "fee_bps_too_large".to_string(),
            StateRootError::UnknownPoolStatus => "unknown_pool_status".to_string(),
            StateRootError::NonceTooLarge => "nonce_too_large".to_string(),
            StateRootError::ZeroAmount(section) => format!("zero_amount:{section}"),
            StateRootError::NonCanonicalPoolAssets => "non_canonical_pool_assets".to_string(),
            StateRootError::InvalidCurveConfig => "invalid_curve_config".to_string(),
            StateRootError::NonCanonicalPoolId => "non_canonical_pool_id".to_string(),
            StateRootError::PoolIdentityMismatch => "pool_identity_mismatch".to_string(),
            StateRootError::MissingLpBalanceForMintMetadata => {
                "missing_lp_balance_for_mint_metadata".to_string()
            }
            StateRootError::EmptyLpDurationMetadata => "empty_lp_duration_metadata".to_string(),
        }
    }
}

impl From<CanonicalError> for StateRootError {
    fn from(e: CanonicalError) -> Self {
        StateRootError::Hex(e)
    }
}

/// Pool lifecycle status; the integer code is part of the state-root encoding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PoolStatus {
    Active,
    Frozen,
    Disabled,
}

impl PoolStatus {
    pub fn code(self) -> u128 {
        match self {
            PoolStatus::Active => 1,
            PoolStatus::Frozen => 2,
            PoolStatus::Disabled => 3,
        }
    }

    /// Parse the lowercase status label used by the Python `PoolStatus` enum.
    pub fn from_label(s: &str) -> Option<PoolStatus> {
        match s {
            "active" => Some(PoolStatus::Active),
            "frozen" => Some(PoolStatus::Frozen),
            "disabled" => Some(PoolStatus::Disabled),
            _ => None,
        }
    }
}

/// One `(pubkey, asset) -> amount` balance entry.
pub struct BalanceEntry {
    pub pubkey: String,
    pub asset: String,
    pub amount: u128,
}

/// One pool's full state.
pub struct PoolEntry {
    pub pool_id: String,
    pub asset0: String,
    pub asset1: String,
    pub reserve0: u128,
    pub reserve1: u128,
    pub fee_bps: u128,
    pub lp_supply: u128,
    pub status: PoolStatus,
    pub created_at: u128,
    pub curve_tag: String,
    pub curve_params: String,
}

/// One `(pubkey, pool_id) -> amount` LP balance entry.
pub struct LpEntry {
    pub pubkey: String,
    pub pool_id: String,
    pub amount: u128,
}

/// One `(pubkey, pool_id)` LP duration-risk metadata entry. Only "present"
/// entries (per the Python `get_all_duration_risk_metadata` filter — at least
/// one timestamp set or `churn_tier > 0`) should appear here.
pub struct LpDurationEntry {
    pub pubkey: String,
    pub pool_id: String,
    pub last_mint_timestamp: Option<u128>,
    pub last_remove_timestamp: Option<u128>,
    pub churn_tier: u128,
    pub last_churn_update_timestamp: Option<u128>,
}

/// One `pubkey -> last_nonce` entry.
pub struct NonceEntry {
    pub pubkey: String,
    pub last_nonce: u128,
}

/// The full state snapshot the root commits to.
#[derive(Default)]
pub struct StateInput {
    pub balances: Vec<BalanceEntry>,
    pub pools: Vec<PoolEntry>,
    pub lp_balances: Vec<LpEntry>,
    pub lp_duration_risk: Vec<LpDurationEntry>,
    pub nonces: Vec<NonceEntry>,
    pub fee_accumulator_dust: u128,
}

fn push_optional_ts(out: &mut Vec<u8>, ts: Option<u128>) {
    out.extend_from_slice(&encode_uvarint(if ts.is_some() { 1 } else { 0 }));
    if let Some(v) = ts {
        out.extend_from_slice(&encode_uvarint(v));
    }
}

fn validate_pool_fee_bps(fee_bps: u128) -> Result<u128, StateRootError> {
    if fee_bps > MAX_FEE_BPS {
        return Err(StateRootError::FeeBpsTooLarge);
    }
    Ok(fee_bps)
}

fn validate_nonce_value(last_nonce: u128) -> Result<u128, StateRootError> {
    if last_nonce > MAX_NONCE {
        return Err(StateRootError::NonceTooLarge);
    }
    Ok(last_nonce)
}

fn pool_assets_in_canonical_order(asset0: &[u8], asset1: &[u8]) -> bool {
    asset0 < asset1
}

fn decode_canonical_pool_id(pool_id: &str) -> Result<Vec<u8>, StateRootError> {
    let bytes = pool_id.as_bytes();
    if bytes.len() != 2 + 2 * POOL_NBYTES
        || !pool_id.starts_with("0x")
        || !bytes[2..]
            .iter()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(byte))
    {
        return Err(StateRootError::NonCanonicalPoolId);
    }
    Ok(hex_to_bytes_fixed(pool_id, POOL_NBYTES)?)
}

fn canonical_pool_identity(
    asset0: &[u8],
    asset1: &[u8],
    fee_bps: u128,
    curve_tag: &str,
    curve_params: &str,
) -> String {
    let mut payload = b"TauSwapPool".to_vec();
    payload.extend_from_slice(format!("0x{}", hex::encode(asset0)).as_bytes());
    payload.extend_from_slice(format!("0x{}", hex::encode(asset1)).as_bytes());
    payload.extend_from_slice(fee_bps.to_string().as_bytes());
    payload.extend_from_slice(curve_tag.as_bytes());
    payload.extend_from_slice(curve_params.as_bytes());
    sha256_hex(&payload)
}

fn duration_metadata_is_present_flags(
    has_mint: bool,
    has_remove: bool,
    churn_tier: u128,
    has_churn_update: bool,
) -> bool {
    has_mint || has_remove || churn_tier > 0 || has_churn_update
}

fn canonical_curve_config(tag: &str, params: &str) -> Result<(), StateRootError> {
    // DbC precondition: the caller supplies raw pool curve fields from an
    // untrusted state boundary. Postcondition: accepted fields are already the
    // exact Python-normalized bytes that participate in the state root.
    match tag.trim().to_uppercase().as_str() {
        CURVE_TAG_CPMM => validate_cpmm_curve(tag, params),
        CURVE_TAG_CUBIC_SUM_V1 => validate_cubic_sum_curve(tag, params),
        CURVE_TAG_SUM_BOOST_V1 => validate_sum_boost_curve(tag, params),
        CURVE_TAG_QUARTIC_BLEND_V1 => validate_blend_curve(tag, params, CURVE_TAG_QUARTIC_BLEND_V1),
        CURVE_TAG_QUINTIC_BLEND_V1 => validate_blend_curve(tag, params, CURVE_TAG_QUINTIC_BLEND_V1),
        _ => Err(StateRootError::InvalidCurveConfig),
    }
}

fn validate_cpmm_curve(tag: &str, params: &str) -> Result<(), StateRootError> {
    if tag != CURVE_TAG_CPMM || !params.is_empty() {
        return Err(StateRootError::InvalidCurveConfig);
    }
    Ok(())
}

fn validate_cubic_sum_curve(tag: &str, params: &str) -> Result<(), StateRootError> {
    if tag != CURVE_TAG_CUBIC_SUM_V1 {
        return Err(StateRootError::InvalidCurveConfig);
    }
    let values = parse_canonical_integer_object(params, &["p", "q"])?;
    require_positive(&values[0])?;
    require_positive(&values[1])
}

fn validate_sum_boost_curve(tag: &str, params: &str) -> Result<(), StateRootError> {
    if tag != CURVE_TAG_SUM_BOOST_V1 {
        return Err(StateRootError::InvalidCurveConfig);
    }
    let values = parse_canonical_integer_object(params, &["mu_den", "mu_num"])?;
    require_positive(&values[0])?;
    Ok(())
}

fn validate_blend_curve(tag: &str, params: &str, expected_tag: &str) -> Result<(), StateRootError> {
    if tag != expected_tag {
        return Err(StateRootError::InvalidCurveConfig);
    }
    let values = parse_canonical_integer_object(params, &["c_den", "c_num"])?;
    require_positive(&values[0])?;
    require_reduced_ratio(&values[1], &values[0])
}

fn parse_canonical_integer_object(
    params: &str,
    keys: &[&str; 2],
) -> Result<[BigUint; 2], StateRootError> {
    let prefix = format!("{{\"{}\":", keys[0]);
    let separator = format!(",\"{}\":", keys[1]);
    let body = params
        .strip_prefix(&prefix)
        .and_then(|rest| rest.strip_suffix('}'))
        .ok_or(StateRootError::InvalidCurveConfig)?;
    let (first, second) = body
        .split_once(&separator)
        .ok_or(StateRootError::InvalidCurveConfig)?;
    Ok([parse_canonical_u128(first)?, parse_canonical_u128(second)?])
}

fn parse_canonical_u128(value: &str) -> Result<BigUint, StateRootError> {
    if value.is_empty() || (value.len() > 1 && value.starts_with('0')) {
        return Err(StateRootError::InvalidCurveConfig);
    }
    BigUint::parse_bytes(value.as_bytes(), 10).ok_or(StateRootError::InvalidCurveConfig)
}

fn require_positive(value: &BigUint) -> Result<(), StateRootError> {
    if value == &BigUint::from(0u8) {
        return Err(StateRootError::InvalidCurveConfig);
    }
    Ok(())
}

fn require_reduced_ratio(num: &BigUint, den: &BigUint) -> Result<(), StateRootError> {
    if num == &BigUint::from(0u8) && den == &BigUint::from(1u8) {
        return Ok(());
    }
    if num == &BigUint::from(0u8) || gcd(num.clone(), den.clone()) != BigUint::from(1u8) {
        return Err(StateRootError::InvalidCurveConfig);
    }
    Ok(())
}

fn gcd(mut a: BigUint, mut b: BigUint) -> BigUint {
    while b != BigUint::from(0u8) {
        let next = a % &b;
        a = b;
        b = next;
    }
    a
}

fn duration_entry_is_present(entry: &LpDurationEntry) -> bool {
    duration_metadata_is_present_flags(
        entry.last_mint_timestamp.is_some(),
        entry.last_remove_timestamp.is_some(),
        entry.churn_tier,
        entry.last_churn_update_timestamp.is_some(),
    )
}

fn collect_lp_balance_keys(entries: &[LpEntry]) -> Result<BTreeSet<DecodedLpKey>, StateRootError> {
    let mut keys = BTreeSet::new();
    for e in entries {
        let pk = hex_to_bytes_fixed(&e.pubkey, PUBKEY_NBYTES)?;
        let pool = decode_canonical_pool_id(&e.pool_id)?;
        if e.amount == 0 {
            return Err(StateRootError::ZeroAmount("lp_balances"));
        }
        keys.insert((pk, pool));
    }
    Ok(keys)
}

fn encode_balances(entries: &[BalanceEntry]) -> Result<Vec<u8>, StateRootError> {
    let mut decoded: Vec<(Vec<u8>, Vec<u8>, u128)> = Vec::with_capacity(entries.len());
    let mut seen: BTreeSet<(Vec<u8>, Vec<u8>)> = BTreeSet::new();
    for e in entries {
        let pk = hex_to_bytes_fixed(&e.pubkey, PUBKEY_NBYTES)?;
        let asset = hex_to_bytes_fixed(&e.asset, ASSET_NBYTES)?;
        if !seen.insert((pk.clone(), asset.clone())) {
            return Err(StateRootError::DuplicateKey("balances"));
        }
        if e.amount == 0 {
            return Err(StateRootError::ZeroAmount("balances"));
        }
        decoded.push((pk, asset, e.amount));
    }
    decoded.sort_by(|a, b| (&a.0, &a.1).cmp(&(&b.0, &b.1)));
    let mut out = encode_uvarint(decoded.len() as u128);
    for (pk, asset, amount) in &decoded {
        out.extend_from_slice(pk);
        out.extend_from_slice(asset);
        out.extend_from_slice(&encode_uvarint(*amount));
    }
    Ok(out)
}

/// A decoded `(pubkey, pool_id)` LP key.
type DecodedLpKey = (Vec<u8>, Vec<u8>);

/// A pool entry with its decoded key/assets: `(pool_id_bytes, entry, asset0_bytes, asset1_bytes)`.
type DecodedPool<'a> = (Vec<u8>, &'a PoolEntry, Vec<u8>, Vec<u8>);

fn encode_pools(entries: &[PoolEntry]) -> Result<Vec<u8>, StateRootError> {
    let mut decoded: Vec<DecodedPool<'_>> = Vec::with_capacity(entries.len());
    let mut seen: BTreeSet<Vec<u8>> = BTreeSet::new();
    for e in entries {
        let pool = decode_canonical_pool_id(&e.pool_id)?;
        let asset0 = hex_to_bytes_fixed(&e.asset0, ASSET_NBYTES)?;
        let asset1 = hex_to_bytes_fixed(&e.asset1, ASSET_NBYTES)?;
        validate_pool_fee_bps(e.fee_bps)?;
        if !pool_assets_in_canonical_order(&asset0, &asset1) {
            return Err(StateRootError::NonCanonicalPoolAssets);
        }
        canonical_curve_config(&e.curve_tag, &e.curve_params)?;
        if e.pool_id
            != canonical_pool_identity(&asset0, &asset1, e.fee_bps, &e.curve_tag, &e.curve_params)
        {
            return Err(StateRootError::PoolIdentityMismatch);
        }
        if !seen.insert(pool.clone()) {
            return Err(StateRootError::DuplicateKey("pools"));
        }
        decoded.push((pool, e, asset0, asset1));
    }
    decoded.sort_by(|a, b| a.0.cmp(&b.0));
    let mut out = encode_uvarint(decoded.len() as u128);
    for (pool, e, asset0, asset1) in &decoded {
        out.extend_from_slice(pool);
        out.extend_from_slice(asset0);
        out.extend_from_slice(asset1);
        out.extend_from_slice(&encode_uvarint(e.reserve0));
        out.extend_from_slice(&encode_uvarint(e.reserve1));
        out.extend_from_slice(&encode_uvarint(e.fee_bps));
        out.extend_from_slice(&encode_uvarint(e.lp_supply));
        out.extend_from_slice(&encode_uvarint(e.status.code()));
        out.extend_from_slice(&encode_uvarint(e.created_at));
        out.extend_from_slice(&encode_bytes(e.curve_tag.as_bytes()));
        out.extend_from_slice(&encode_bytes(e.curve_params.as_bytes()));
    }
    Ok(out)
}

fn encode_lp(entries: &[LpEntry]) -> Result<Vec<u8>, StateRootError> {
    let mut decoded: Vec<(Vec<u8>, Vec<u8>, u128)> = Vec::with_capacity(entries.len());
    let mut seen: BTreeSet<(Vec<u8>, Vec<u8>)> = BTreeSet::new();
    for e in entries {
        let pk = hex_to_bytes_fixed(&e.pubkey, PUBKEY_NBYTES)?;
        let pool = decode_canonical_pool_id(&e.pool_id)?;
        if !seen.insert((pk.clone(), pool.clone())) {
            return Err(StateRootError::DuplicateKey("lp_balances"));
        }
        if e.amount == 0 {
            return Err(StateRootError::ZeroAmount("lp_balances"));
        }
        decoded.push((pk, pool, e.amount));
    }
    decoded.sort_by(|a, b| (&a.0, &a.1).cmp(&(&b.0, &b.1)));
    let mut out = encode_uvarint(decoded.len() as u128);
    for (pk, pool, amount) in &decoded {
        out.extend_from_slice(pk);
        out.extend_from_slice(pool);
        out.extend_from_slice(&encode_uvarint(*amount));
    }
    Ok(out)
}

fn encode_lp_duration(
    entries: &[LpDurationEntry],
    lp_balance_keys: &BTreeSet<DecodedLpKey>,
) -> Result<Vec<u8>, StateRootError> {
    let mut decoded: Vec<(Vec<u8>, Vec<u8>, &LpDurationEntry)> = Vec::with_capacity(entries.len());
    let mut seen: BTreeSet<(Vec<u8>, Vec<u8>)> = BTreeSet::new();
    for e in entries {
        let pk = hex_to_bytes_fixed(&e.pubkey, PUBKEY_NBYTES)?;
        let pool = decode_canonical_pool_id(&e.pool_id)?;
        if !duration_entry_is_present(e) {
            return Err(StateRootError::EmptyLpDurationMetadata);
        }
        if !seen.insert((pk.clone(), pool.clone())) {
            return Err(StateRootError::DuplicateKey("lp_duration_risk"));
        }
        if e.last_mint_timestamp.is_some() && !lp_balance_keys.contains(&(pk.clone(), pool.clone()))
        {
            return Err(StateRootError::MissingLpBalanceForMintMetadata);
        }
        decoded.push((pk, pool, e));
    }
    decoded.sort_by(|a, b| (&a.0, &a.1).cmp(&(&b.0, &b.1)));
    let mut out = encode_uvarint(decoded.len() as u128);
    for (pk, pool, e) in &decoded {
        out.extend_from_slice(pk);
        out.extend_from_slice(pool);
        // Interleaving matches Python: mint flag/value, remove flag/value,
        // churn_tier, then churn-update flag/value (churn_tier sits between the
        // first two timestamps and the third).
        push_optional_ts(&mut out, e.last_mint_timestamp);
        push_optional_ts(&mut out, e.last_remove_timestamp);
        out.extend_from_slice(&encode_uvarint(e.churn_tier));
        push_optional_ts(&mut out, e.last_churn_update_timestamp);
    }
    Ok(out)
}

fn encode_nonces(entries: &[NonceEntry]) -> Result<Vec<u8>, StateRootError> {
    let mut decoded: Vec<(Vec<u8>, u128)> = Vec::with_capacity(entries.len());
    let mut seen: BTreeSet<Vec<u8>> = BTreeSet::new();
    for e in entries {
        let pk = hex_to_bytes_fixed(&e.pubkey, PUBKEY_NBYTES)?;
        if !seen.insert(pk.clone()) {
            return Err(StateRootError::DuplicateKey("nonces"));
        }
        validate_nonce_value(e.last_nonce)?;
        decoded.push((pk, e.last_nonce));
    }
    decoded.sort_by(|a, b| a.0.cmp(&b.0));
    let mut out = encode_uvarint(decoded.len() as u128);
    for (pk, last_nonce) in &decoded {
        out.extend_from_slice(pk);
        out.extend_from_slice(&encode_uvarint(*last_nonce));
    }
    Ok(out)
}

fn encode_fee_accumulator(dust: u128) -> Vec<u8> {
    encode_uvarint(dust)
}

/// Compute the deterministic v5 state root. Returns a `0x`-prefixed SHA-256.
pub fn compute_state_root(input: &StateInput) -> Result<String, StateRootError> {
    let balances = encode_balances(&input.balances)?;
    let pools = encode_pools(&input.pools)?;
    let lp_balance_keys = collect_lp_balance_keys(&input.lp_balances)?;
    let lp = encode_lp(&input.lp_balances)?;
    let lp_duration = encode_lp_duration(&input.lp_duration_risk, &lp_balance_keys)?;
    let nonces = encode_nonces(&input.nonces)?;
    let fee = encode_fee_accumulator(input.fee_accumulator_dust);

    let mut payload = domain_sep_bytes("state_root", STATE_ROOT_VERSION);
    payload.extend_from_slice(b"BAL");
    payload.extend_from_slice(&encode_bytes(&balances));
    payload.extend_from_slice(b"POL");
    payload.extend_from_slice(&encode_bytes(&pools));
    payload.extend_from_slice(b"LPB");
    payload.extend_from_slice(&encode_bytes(&lp));
    payload.extend_from_slice(b"LPA");
    payload.extend_from_slice(&encode_bytes(&lp_duration));
    payload.extend_from_slice(b"NNC");
    payload.extend_from_slice(&encode_bytes(&nonces));
    payload.extend_from_slice(b"FEE");
    payload.extend_from_slice(&encode_bytes(&fee));
    Ok(sha256_hex(&payload))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pk(byte: u8) -> String {
        format!("0x{}", hex::encode([byte; PUBKEY_NBYTES]))
    }
    fn id32(byte: u8) -> String {
        format!("0x{}", hex::encode([byte; ASSET_NBYTES]))
    }

    fn valid_pool() -> PoolEntry {
        let asset0 = id32(2);
        let asset1 = id32(3);
        PoolEntry {
            pool_id: canonical_pool_identity(
                &[2; ASSET_NBYTES],
                &[3; ASSET_NBYTES],
                30,
                CURVE_TAG_CPMM,
                "",
            ),
            asset0,
            asset1,
            reserve0: 1,
            reserve1: 1,
            fee_bps: 30,
            lp_supply: 0,
            status: PoolStatus::Active,
            created_at: 0,
            curve_tag: "CPMM".to_string(),
            curve_params: String::new(),
        }
    }

    #[test]
    fn empty_state_is_stable() {
        let root = compute_state_root(&StateInput::default()).unwrap();
        // Recomputing the empty state is deterministic.
        assert_eq!(root, compute_state_root(&StateInput::default()).unwrap());
        assert!(root.starts_with("0x") && root.len() == 66);
    }

    #[test]
    fn balance_order_independent() {
        let a = StateInput {
            balances: vec![
                BalanceEntry {
                    pubkey: pk(1),
                    asset: id32(9),
                    amount: 100,
                },
                BalanceEntry {
                    pubkey: pk(2),
                    asset: id32(8),
                    amount: 200,
                },
            ],
            ..Default::default()
        };
        let b = StateInput {
            balances: vec![
                BalanceEntry {
                    pubkey: pk(2),
                    asset: id32(8),
                    amount: 200,
                },
                BalanceEntry {
                    pubkey: pk(1),
                    asset: id32(9),
                    amount: 100,
                },
            ],
            ..Default::default()
        };
        assert_eq!(
            compute_state_root(&a).unwrap(),
            compute_state_root(&b).unwrap()
        );
    }

    #[test]
    fn different_amount_changes_root() {
        let a = StateInput {
            balances: vec![BalanceEntry {
                pubkey: pk(1),
                asset: id32(9),
                amount: 100,
            }],
            ..Default::default()
        };
        let b = StateInput {
            balances: vec![BalanceEntry {
                pubkey: pk(1),
                asset: id32(9),
                amount: 101,
            }],
            ..Default::default()
        };
        assert_ne!(
            compute_state_root(&a).unwrap(),
            compute_state_root(&b).unwrap()
        );
    }

    #[test]
    fn fee_accumulator_dust_changes_root() {
        let a = StateInput {
            fee_accumulator_dust: 0,
            ..Default::default()
        };
        let b = StateInput {
            fee_accumulator_dust: 7,
            ..Default::default()
        };
        assert_ne!(
            compute_state_root(&a).unwrap(),
            compute_state_root(&b).unwrap()
        );
    }

    #[test]
    fn duplicate_balance_key_rejected() {
        let s = StateInput {
            balances: vec![
                BalanceEntry {
                    pubkey: pk(1),
                    asset: id32(9),
                    amount: 1,
                },
                BalanceEntry {
                    pubkey: pk(1),
                    asset: id32(9),
                    amount: 2,
                },
            ],
            ..Default::default()
        };
        assert_eq!(
            compute_state_root(&s),
            Err(StateRootError::DuplicateKey("balances"))
        );
    }

    #[test]
    fn fee_bps_too_large_rejected() {
        let s = StateInput {
            pools: vec![PoolEntry {
                pool_id: id32(1),
                asset0: id32(2),
                asset1: id32(3),
                reserve0: 1,
                reserve1: 1,
                fee_bps: 10_001,
                lp_supply: 0,
                status: PoolStatus::Active,
                created_at: 0,
                curve_tag: "CPMM".to_string(),
                curve_params: String::new(),
            }],
            ..Default::default()
        };
        assert_eq!(compute_state_root(&s), Err(StateRootError::FeeBpsTooLarge));
    }

    #[test]
    fn bad_hex_rejected() {
        let s = StateInput {
            nonces: vec![NonceEntry {
                pubkey: "0x1234".to_string(),
                last_nonce: 1,
            }],
            ..Default::default()
        };
        assert!(matches!(
            compute_state_root(&s),
            Err(StateRootError::Hex(_))
        ));
    }

    #[test]
    fn nonce_above_u32_rejected() {
        let s = StateInput {
            nonces: vec![NonceEntry {
                pubkey: pk(1),
                last_nonce: (1u128 << 32),
            }],
            ..Default::default()
        };
        assert_eq!(compute_state_root(&s), Err(StateRootError::NonceTooLarge));
    }

    #[test]
    fn zero_balance_rejected() {
        let s = StateInput {
            balances: vec![BalanceEntry {
                pubkey: pk(1),
                asset: id32(9),
                amount: 0,
            }],
            ..Default::default()
        };
        assert_eq!(
            compute_state_root(&s),
            Err(StateRootError::ZeroAmount("balances"))
        );
    }

    #[test]
    fn non_canonical_pool_assets_rejected() {
        let s = StateInput {
            pools: vec![PoolEntry {
                asset0: id32(3),
                asset1: id32(2),
                ..valid_pool()
            }],
            ..Default::default()
        };
        assert_eq!(
            compute_state_root(&s),
            Err(StateRootError::NonCanonicalPoolAssets)
        );
    }

    #[test]
    fn non_canonical_curve_config_rejected() {
        let s = StateInput {
            pools: vec![PoolEntry {
                curve_tag: "cpmm".to_string(),
                curve_params: String::new(),
                ..valid_pool()
            }],
            ..Default::default()
        };
        assert_eq!(
            compute_state_root(&s),
            Err(StateRootError::InvalidCurveConfig)
        );
    }

    #[test]
    fn non_reduced_curve_params_rejected() {
        let s = StateInput {
            pools: vec![PoolEntry {
                curve_tag: "QUARTIC_BLEND_V1".to_string(),
                curve_params: "{\"c_den\":4,\"c_num\":2}".to_string(),
                ..valid_pool()
            }],
            ..Default::default()
        };
        assert_eq!(
            compute_state_root(&s),
            Err(StateRootError::InvalidCurveConfig)
        );
    }

    #[test]
    fn mismatched_pool_identity_rejected() {
        let s = StateInput {
            pools: vec![PoolEntry {
                pool_id: id32(1),
                ..valid_pool()
            }],
            ..Default::default()
        };
        assert_eq!(
            compute_state_root(&s),
            Err(StateRootError::PoolIdentityMismatch)
        );
    }

    #[test]
    fn noncanonical_pool_id_case_rejected() {
        let pool = valid_pool();
        let s = StateInput {
            pools: vec![PoolEntry {
                pool_id: format!("0x{}", pool.pool_id[2..].to_uppercase()),
                ..pool
            }],
            ..Default::default()
        };
        assert_eq!(
            compute_state_root(&s),
            Err(StateRootError::NonCanonicalPoolId)
        );
    }

    #[test]
    fn lp_duration_present_entry_encodes() {
        // churn_tier > 0 with no timestamps is a valid "present" entry.
        let s = StateInput {
            lp_duration_risk: vec![LpDurationEntry {
                pubkey: pk(7),
                pool_id: id32(7),
                last_mint_timestamp: None,
                last_remove_timestamp: None,
                churn_tier: 2,
                last_churn_update_timestamp: None,
            }],
            ..Default::default()
        };
        let root = compute_state_root(&s).unwrap();
        assert!(root.starts_with("0x"));
    }

    #[test]
    fn lp_mint_metadata_requires_balance() {
        let s = StateInput {
            lp_duration_risk: vec![LpDurationEntry {
                pubkey: pk(7),
                pool_id: id32(7),
                last_mint_timestamp: Some(5),
                last_remove_timestamp: None,
                churn_tier: 0,
                last_churn_update_timestamp: None,
            }],
            ..Default::default()
        };
        assert_eq!(
            compute_state_root(&s),
            Err(StateRootError::MissingLpBalanceForMintMetadata)
        );
    }
}

// ---------------------------------------------------------------------------
// CBC_CORE_V0 — Kani contracts on hash-free state-root guard predicates.
//
// The complete state root includes heap-backed section encoders, BTreeSet
// duplicate detection, BigUint curve-param parsing, and SHA-256. Those remain
// vector/fuzz/differential backed. These contracts prove the scalar guards that
// decide whether a root preimage is admissible before those heavier encoders run.
// ---------------------------------------------------------------------------
#[cfg(kani)]
mod kani_contracts {
    use super::*;

    #[kani::proof]
    fn pool_fee_bps_guard_is_exact() {
        let fee_bps: u128 = kani::any();
        match validate_pool_fee_bps(fee_bps) {
            Ok(v) => {
                assert_eq!(v, fee_bps);
                assert!(fee_bps <= MAX_FEE_BPS);
            }
            Err(e) => {
                assert_eq!(e, StateRootError::FeeBpsTooLarge);
                assert!(fee_bps > MAX_FEE_BPS);
            }
        }
    }

    #[kani::proof]
    fn nonce_guard_is_exact() {
        let last_nonce: u128 = kani::any();
        match validate_nonce_value(last_nonce) {
            Ok(v) => {
                assert_eq!(v, last_nonce);
                assert!(last_nonce <= MAX_NONCE);
            }
            Err(e) => {
                assert_eq!(e, StateRootError::NonceTooLarge);
                assert!(last_nonce > MAX_NONCE);
            }
        }
    }

    #[kani::proof]
    fn duration_metadata_presence_is_exact() {
        let has_mint: bool = kani::any();
        let has_remove: bool = kani::any();
        let churn_tier: u128 = kani::any();
        let has_churn_update: bool = kani::any();
        assert_eq!(
            duration_metadata_is_present_flags(has_mint, has_remove, churn_tier, has_churn_update,),
            has_mint || has_remove || churn_tier > 0 || has_churn_update
        );
    }

    #[kani::proof]
    fn pool_asset_order_guard_matches_fixed_width_byte_order() {
        let asset0: [u8; ASSET_NBYTES] = kani::any();
        let asset1: [u8; ASSET_NBYTES] = kani::any();
        assert_eq!(
            pool_assets_in_canonical_order(&asset0, &asset1),
            asset0 < asset1
        );
    }

    #[kani::proof]
    fn pool_asset_order_guard_rejects_equal_assets() {
        let asset: [u8; ASSET_NBYTES] = kani::any();
        assert!(!pool_assets_in_canonical_order(&asset, &asset));
    }

    #[kani::proof]
    fn pool_status_codes_are_in_domain_and_distinct() {
        let active = PoolStatus::Active.code();
        let frozen = PoolStatus::Frozen.code();
        let disabled = PoolStatus::Disabled.code();
        assert_eq!(active, 1);
        assert_eq!(frozen, 2);
        assert_eq!(disabled, 3);
        assert!(active != frozen);
        assert!(active != disabled);
        assert!(frozen != disabled);
    }

    #[kani::proof]
    fn state_root_guard_covers_are_reachable() {
        let zero = [0_u8; ASSET_NBYTES];
        let mut one = [0_u8; ASSET_NBYTES];
        one[ASSET_NBYTES - 1] = 1;
        kani::cover!(pool_assets_in_canonical_order(&zero, &one));
        kani::cover!(!pool_assets_in_canonical_order(&one, &zero));
        kani::cover!(!pool_assets_in_canonical_order(&zero, &zero));
    }
}
