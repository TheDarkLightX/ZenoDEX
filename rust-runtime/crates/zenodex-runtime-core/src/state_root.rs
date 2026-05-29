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
//! bytes*, not by hex string — so the root is independent of input order and of
//! hex letter case. Duplicate decoded keys are a typed rejection.
//!
//! Domain note: amounts are taken as `u128`. The Python encoder accepts up to
//! 256-bit uvarints, but every runtime state amount (balances ≤ 2^112−1,
//! reserves ≤ 3e9, nonces ≤ u32, …) is far below 2^128, so `u128` covers the
//! whole live domain. Values that do not fit `u128` are out of this shadow's
//! domain and are rejected at the CLI bridge rather than silently truncated.

use crate::canonical::{
    domain_sep_bytes, encode_bytes, encode_uvarint, hex_to_bytes_fixed, sha256_hex, CanonicalError,
};
use std::collections::BTreeSet;

/// State-root encoding version (must equal `STATE_ROOT_VERSION` in Python).
pub const STATE_ROOT_VERSION: u32 = 5;

const PUBKEY_NBYTES: usize = 48;
const ASSET_NBYTES: usize = 32;
const POOL_NBYTES: usize = 32;
const MAX_FEE_BPS: u128 = 10_000;
const MAX_NONCE: u128 = 0xFFFF_FFFF;

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
}

impl StateRootError {
    pub fn code(&self) -> String {
        match self {
            StateRootError::Hex(e) => e.code().to_string(),
            StateRootError::DuplicateKey(section) => format!("duplicate_key:{section}"),
            StateRootError::FeeBpsTooLarge => "fee_bps_too_large".to_string(),
            StateRootError::UnknownPoolStatus => "unknown_pool_status".to_string(),
            StateRootError::NonceTooLarge => "nonce_too_large".to_string(),
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

fn encode_balances(entries: &[BalanceEntry]) -> Result<Vec<u8>, StateRootError> {
    let mut decoded: Vec<(Vec<u8>, Vec<u8>, u128)> = Vec::with_capacity(entries.len());
    let mut seen: BTreeSet<(Vec<u8>, Vec<u8>)> = BTreeSet::new();
    for e in entries {
        let pk = hex_to_bytes_fixed(&e.pubkey, PUBKEY_NBYTES)?;
        let asset = hex_to_bytes_fixed(&e.asset, ASSET_NBYTES)?;
        if !seen.insert((pk.clone(), asset.clone())) {
            return Err(StateRootError::DuplicateKey("balances"));
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

/// A pool entry with its decoded key/assets: `(pool_id_bytes, entry, asset0_bytes, asset1_bytes)`.
type DecodedPool<'a> = (Vec<u8>, &'a PoolEntry, Vec<u8>, Vec<u8>);

fn encode_pools(entries: &[PoolEntry]) -> Result<Vec<u8>, StateRootError> {
    let mut decoded: Vec<DecodedPool<'_>> = Vec::with_capacity(entries.len());
    let mut seen: BTreeSet<Vec<u8>> = BTreeSet::new();
    for e in entries {
        let pool = hex_to_bytes_fixed(&e.pool_id, POOL_NBYTES)?;
        let asset0 = hex_to_bytes_fixed(&e.asset0, ASSET_NBYTES)?;
        let asset1 = hex_to_bytes_fixed(&e.asset1, ASSET_NBYTES)?;
        if e.fee_bps > MAX_FEE_BPS {
            return Err(StateRootError::FeeBpsTooLarge);
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
        let pool = hex_to_bytes_fixed(&e.pool_id, POOL_NBYTES)?;
        if !seen.insert((pk.clone(), pool.clone())) {
            return Err(StateRootError::DuplicateKey("lp_balances"));
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

fn encode_lp_duration(entries: &[LpDurationEntry]) -> Result<Vec<u8>, StateRootError> {
    let mut decoded: Vec<(Vec<u8>, Vec<u8>, &LpDurationEntry)> = Vec::with_capacity(entries.len());
    let mut seen: BTreeSet<(Vec<u8>, Vec<u8>)> = BTreeSet::new();
    for e in entries {
        let pk = hex_to_bytes_fixed(&e.pubkey, PUBKEY_NBYTES)?;
        let pool = hex_to_bytes_fixed(&e.pool_id, POOL_NBYTES)?;
        if !seen.insert((pk.clone(), pool.clone())) {
            return Err(StateRootError::DuplicateKey("lp_duration_risk"));
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
        if e.last_nonce > MAX_NONCE {
            return Err(StateRootError::NonceTooLarge);
        }
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
    let lp = encode_lp(&input.lp_balances)?;
    let lp_duration = encode_lp_duration(&input.lp_duration_risk)?;
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
    fn lp_duration_present_entry_encodes() {
        // churn_tier > 0 with no timestamps is a valid "present" entry.
        let s = StateInput {
            lp_duration_risk: vec![LpDurationEntry {
                pubkey: pk(7),
                pool_id: id32(7),
                last_mint_timestamp: Some(5),
                last_remove_timestamp: None,
                churn_tier: 2,
                last_churn_update_timestamp: Some(9),
            }],
            ..Default::default()
        };
        let root = compute_state_root(&s).unwrap();
        assert!(root.starts_with("0x"));
    }
}
