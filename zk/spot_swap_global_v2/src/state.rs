//! Owned single-pool Spot frame: physical reserves plus exact LP share rights.
//!
//! Mirrors `src/core/spot_swap_state_v2.py`. Shares retain the existing
//! proportional burn semantics; they are not fixed atom liabilities and swaps
//! never reprice or redistribute them. Public Rust construction is untrusted:
//! every consumer validates before use, and validation checks row capacities
//! before it traverses any row. The value grants no publication authority.

use serde::{Deserialize, Deserializer, Serialize};
use zenodex_global_settlement_abi_v2::{
    canonical_bytes_v2, hash_bytes_sha256_v2, hash_global_v2, validate_schema_v2,
    validate_token_v2, AbiErrorV2, AbiResultV2, EconomicAmountV2, RootV2,
    MAX_BALANCE_ROWS_PER_ASSET_STATE_V2, MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2,
};

use crate::quote::{BPS_DENOM_V2, DEX_POOL_RESERVE_MAX_V2};

pub const SPOT_SWAP_STATE_SCHEMA_V2: &str = "zenodex/spot-swap-state/v2";
pub const SPOT_POOL_CUSTODY_DOMAIN_V2: &str = "spot_pool";
pub const CURVE_TAG_CPMM_V2: &str = "CPMM";
pub const MIN_LP_LOCK_V2: u64 = 1_000;
pub const DEX_LP_SUPPLY_MAX_V2: u64 = 3_000_000_000;
pub const MAX_SPOT_OWNER_ROWS_V2: usize = MAX_BALANCE_ROWS_PER_ASSET_STATE_V2;
pub const MAX_SPOT_STATE_CANONICAL_BYTES_V2: usize = MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2;
pub const MAX_SPOT_INTENT_NONCE_V2: u64 = 4_294_967_295;
pub const MAX_SPOT_POOL_TEXT_CHARS_V2: usize = 512;
pub const MAX_SPOT_CURVE_PARAMS_CHARS_V2: usize = 4_096;
/// `0x` plus 48 bytes of lowercase hex.
pub const SPOT_OWNER_HEX_CHARS_V2: usize = 98;
/// The existing all-zero minimum-lock owner (`support_root.LP_LOCK_PUBKEY`).
pub const LP_LOCK_PUBKEY_V2: &str =
    "0x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";

/// Whether `owner` is the all-zero minimum-lock identity (`LP_LOCK_PUBKEY_V2`).
pub const fn is_lp_lock_owner_v2(owner: &str) -> bool {
    let bytes = owner.as_bytes();
    if bytes.len() != SPOT_OWNER_HEX_CHARS_V2 || bytes[0] != b'0' || bytes[1] != b'x' {
        return false;
    }
    let mut index = 2;
    while index < bytes.len() {
        if bytes[index] != b'0' {
            return false;
        }
        index += 1;
    }
    true
}

const _: () = assert!(is_lp_lock_owner_v2(LP_LOCK_PUBKEY_V2));

fn deserialize_required_option<'de, D, T>(deserializer: D) -> Result<Option<T>, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de>,
{
    Option::<T>::deserialize(deserializer)
}

/// Canonical lowercase `0x`-prefixed 48-byte hex identity, as legacy committed
/// state stores LP owners, nonce owners and joint swap parties. Prefix and case
/// aliases reject; signed bytes are never rewritten. This establishes unique
/// identity text, not BLS point validity.
pub fn validate_spot_owner_v2(owner: &str, field: &'static str) -> AbiResultV2<()> {
    validate_token_v2(owner, field)?;
    let bytes = owner.as_bytes();
    let canonical = bytes.len() == SPOT_OWNER_HEX_CHARS_V2
        && owner.starts_with("0x")
        && bytes[2..]
            .iter()
            .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'));
    if !canonical {
        return Err(AbiErrorV2::InvalidBinding(field));
    }
    Ok(())
}

/// `canonical_pool_asset_id(asset) == asset`: symbolic ids are unchanged, while
/// `0x`-prefixed hex ids must already be lowercase with a lowercase prefix.
pub fn is_canonical_pool_asset_id_v2(asset: &str) -> bool {
    let bytes = asset.as_bytes();
    if bytes.len() < 3 {
        return true;
    }
    let prefix = &bytes[..2];
    if !prefix.eq_ignore_ascii_case(b"0x") {
        return true;
    }
    let body = &bytes[2..];
    if !body.iter().all(u8::is_ascii_hexdigit) {
        return true;
    }
    prefix == b"0x" && !body.iter().any(u8::is_ascii_uppercase)
}

/// `compute_pool_id`: `sha256("TauSwapPool" + asset0 + asset1 + str(fee_bps) + curve_tag + curve_params)`.
pub fn compute_pool_id_v2(
    asset0: &str,
    asset1: &str,
    fee_bps: u64,
    curve_tag: &str,
    curve_params: &str,
) -> String {
    let mut data = Vec::new();
    data.extend_from_slice(b"TauSwapPool");
    data.extend_from_slice(asset0.as_bytes());
    data.extend_from_slice(asset1.as_bytes());
    data.extend_from_slice(fee_bps.to_string().as_bytes());
    data.extend_from_slice(curve_tag.as_bytes());
    data.extend_from_slice(curve_params.as_bytes());
    format!("0x{}", hash_bytes_sha256_v2(&data))
}

fn require_pool_text(value: &str, field: &'static str) -> AbiResultV2<()> {
    let chars = value.chars().count();
    if chars == 0 || chars > MAX_SPOT_POOL_TEXT_CHARS_V2 {
        return Err(AbiErrorV2::InvalidBounds(field));
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum PoolStatusV2 {
    ACTIVE,
    FROZEN,
    DISABLED,
}

/// Complete immutable `PoolState` value; LP ownership stays in the Spot frame.
///
/// Amounts are stored in the state-admitted domain (`u64`, at most 3e9 for
/// reserves) and widened to `u128` by the quote arithmetic.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SpotPoolSnapshotV2 {
    pub pool_id: String,
    pub asset0: String,
    pub asset1: String,
    pub reserve0: u64,
    pub reserve1: u64,
    pub fee_bps: u64,
    pub lp_supply: u64,
    pub status: PoolStatusV2,
    pub created_at: u64,
    pub curve_tag: String,
    pub curve_params: String,
}

impl SpotPoolSnapshotV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        for (value, field) in [
            (&self.pool_id, "Spot pool id"),
            (&self.asset0, "Spot pool asset0"),
            (&self.asset1, "Spot pool asset1"),
            (&self.curve_tag, "Spot pool curve tag"),
        ] {
            require_pool_text(value, field)?;
        }
        if !is_canonical_pool_asset_id_v2(&self.asset0)
            || !is_canonical_pool_asset_id_v2(&self.asset1)
        {
            return Err(AbiErrorV2::InvalidBinding(
                "Spot pool asset must already be canonical",
            ));
        }
        if self.asset0 >= self.asset1 {
            return Err(AbiErrorV2::InvalidOrder("Spot pool assets"));
        }
        if u128::from(self.reserve0) > DEX_POOL_RESERVE_MAX_V2
            || u128::from(self.reserve1) > DEX_POOL_RESERVE_MAX_V2
        {
            return Err(AbiErrorV2::InvalidBounds("Spot pool reserve"));
        }
        if u128::from(self.fee_bps) > BPS_DENOM_V2 {
            return Err(AbiErrorV2::InvalidBounds("Spot pool fee bps"));
        }
        if self.curve_params.chars().count() > MAX_SPOT_CURVE_PARAMS_CHARS_V2 {
            return Err(AbiErrorV2::InvalidBounds("Spot pool curve params"));
        }
        Ok(())
    }

    pub fn is_active(&self) -> bool {
        self.status == PoolStatusV2::ACTIVE
    }

    /// The only curve the isolated profile prices: `CPMM` with empty params.
    pub fn is_cpmm(&self) -> bool {
        self.curve_tag == CURVE_TAG_CPMM_V2 && self.curve_params.is_empty()
    }

    pub fn canonical_pool_id(&self) -> String {
        compute_pool_id_v2(
            &self.asset0,
            &self.asset1,
            self.fee_bps,
            &self.curve_tag,
            &self.curve_params,
        )
    }

    pub fn with_reserves(&self, reserve0: u64, reserve1: u64) -> Self {
        Self {
            reserve0,
            reserve1,
            ..self.clone()
        }
    }
}

/// One LP owner row with all four existing duration/churn metadata fields.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SpotLPPositionV2 {
    pub owner: String,
    pub shares: u64,
    #[serde(deserialize_with = "deserialize_required_option")]
    pub last_mint_timestamp: Option<u64>,
    #[serde(deserialize_with = "deserialize_required_option")]
    pub last_remove_timestamp: Option<u64>,
    pub churn_tier: u64,
    #[serde(deserialize_with = "deserialize_required_option")]
    pub last_churn_update_timestamp: Option<u64>,
}

impl SpotLPPositionV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        validate_spot_owner_v2(&self.owner, "Spot LP owner")?;
        if self.shares > DEX_LP_SUPPLY_MAX_V2 {
            return Err(AbiErrorV2::InvalidBounds("Spot LP shares"));
        }
        Ok(())
    }
}

/// Last consumed inner intent nonce per sender; zero is represented by absence.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SpotIntentNonceV2 {
    pub owner: String,
    pub last_nonce: u64,
}

impl SpotIntentNonceV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        validate_spot_owner_v2(&self.owner, "Spot intent nonce owner")?;
        if self.last_nonce == 0 || self.last_nonce > MAX_SPOT_INTENT_NONCE_V2 {
            return Err(AbiErrorV2::InvalidBounds("Spot intent nonce"));
        }
        Ok(())
    }
}

/// The committed Spot frame: one pool, its complete LP table and per-sender
/// intent nonces. Canonical form equals `SpotSwapStateV2.to_canonical()`.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SpotSwapStateV2 {
    pub schema: String,
    pub module_release_id: RootV2,
    pub pool: SpotPoolSnapshotV2,
    pub lp_positions: Vec<SpotLPPositionV2>,
    pub intent_nonces: Vec<SpotIntentNonceV2>,
}

impl SpotSwapStateV2 {
    /// Row capacities are checked before any row is validated, then schema,
    /// release, pool, rows, pool ownership and the canonical byte ceiling.
    pub fn validate(&self) -> AbiResultV2<()> {
        if self.lp_positions.len() > MAX_SPOT_OWNER_ROWS_V2 {
            return Err(AbiErrorV2::StateResourceLimit("Spot LP positions"));
        }
        if self.intent_nonces.len() > MAX_SPOT_OWNER_ROWS_V2 {
            return Err(AbiErrorV2::StateResourceLimit("Spot intent nonces"));
        }
        validate_schema_v2(&self.schema, SPOT_SWAP_STATE_SCHEMA_V2, "Spot swap state")?;
        self.module_release_id
            .validate("Spot module release", false)?;
        self.pool.validate()?;
        for row in &self.lp_positions {
            row.validate()?;
        }
        if self
            .lp_positions
            .windows(2)
            .any(|pair| pair[0].owner >= pair[1].owner)
        {
            return Err(AbiErrorV2::InvalidOrder("Spot LP positions"));
        }
        for row in &self.intent_nonces {
            row.validate()?;
        }
        if self
            .intent_nonces
            .windows(2)
            .any(|pair| pair[0].owner >= pair[1].owner)
        {
            return Err(AbiErrorV2::InvalidOrder("Spot intent nonces"));
        }
        self.require_pool_ownership()?;
        if canonical_bytes_v2(self)?.len() > MAX_SPOT_STATE_CANONICAL_BYTES_V2 {
            return Err(AbiErrorV2::StateResourceLimit(
                "Spot swap state canonical encoding bytes",
            ));
        }
        Ok(())
    }

    fn require_pool_ownership(&self) -> AbiResultV2<()> {
        let pool = &self.pool;
        if pool.pool_id != pool.canonical_pool_id() {
            return Err(AbiErrorV2::InvalidBinding(
                "Spot pool identity differs from its complete parameters",
            ));
        }
        if pool.reserve0 == 0 || pool.reserve1 == 0 {
            return Err(AbiErrorV2::InvalidBounds(
                "Spot pool reserves outside the existing domain",
            ));
        }
        if pool.lp_supply < MIN_LP_LOCK_V2 || pool.lp_supply > DEX_LP_SUPPLY_MAX_V2 {
            return Err(AbiErrorV2::InvalidBounds(
                "Spot pool LP supply outside the existing domain",
            ));
        }
        let mut total: u128 = 0;
        for row in &self.lp_positions {
            total = total
                .checked_add(u128::from(row.shares))
                .ok_or(AbiErrorV2::InvalidBounds("Spot LP share total"))?;
        }
        if total != u128::from(pool.lp_supply) {
            return Err(AbiErrorV2::InvalidBinding(
                "Spot LP ownership must cover the complete supply",
            ));
        }
        let locked = self
            .lp_positions
            .iter()
            .find(|row| is_lp_lock_owner_v2(&row.owner))
            .map_or(0, |row| row.shares);
        if locked < MIN_LP_LOCK_V2 {
            return Err(AbiErrorV2::InvalidBinding(
                "Spot LP ownership must retain the minimum locked shares",
            ));
        }
        Ok(())
    }

    pub fn state_root(&self) -> AbiResultV2<RootV2> {
        self.validate()?;
        hash_global_v2("spot-swap-state-v2", self)
    }

    /// Last consumed inner nonce for `owner`, zero when absent.
    pub fn intent_nonce(&self, owner: &str) -> u64 {
        self.intent_nonces
            .iter()
            .find(|row| row.owner == owner)
            .map_or(0, |row| row.last_nonce)
    }

    /// The two physical custody rows this pool must hold under `spot_pool`,
    /// in `(asset0, asset1)` order.
    pub fn pool_holdings(&self) -> Vec<EconomicAmountV2> {
        vec![
            EconomicAmountV2 {
                owner: self.pool.pool_id.clone(),
                asset: self.pool.asset0.clone(),
                custody_domain: SPOT_POOL_CUSTODY_DOMAIN_V2.to_owned(),
                amount_atoms: u128::from(self.pool.reserve0),
            },
            EconomicAmountV2 {
                owner: self.pool.pool_id.clone(),
                asset: self.pool.asset1.clone(),
                custody_domain: SPOT_POOL_CUSTODY_DOMAIN_V2.to_owned(),
                amount_atoms: u128::from(self.pool.reserve1),
            },
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn owner(byte: &str) -> String {
        format!("0x{}", byte.repeat(48))
    }

    fn root(value: u64) -> RootV2 {
        RootV2::parse(format!("0x{value:064x}"), "test root", false).expect("root")
    }

    fn pool() -> SpotPoolSnapshotV2 {
        let mut pool = SpotPoolSnapshotV2 {
            pool_id: String::new(),
            asset0: "A".to_owned(),
            asset1: "B".to_owned(),
            reserve0: 10_000,
            reserve1: 20_000,
            fee_bps: 30,
            lp_supply: 14_142,
            status: PoolStatusV2::ACTIVE,
            created_at: 7,
            curve_tag: CURVE_TAG_CPMM_V2.to_owned(),
            curve_params: String::new(),
        };
        pool.pool_id = pool.canonical_pool_id();
        pool
    }

    fn position(owner: String, shares: u64) -> SpotLPPositionV2 {
        SpotLPPositionV2 {
            owner,
            shares,
            last_mint_timestamp: None,
            last_remove_timestamp: None,
            churn_tier: 0,
            last_churn_update_timestamp: None,
        }
    }

    fn rows() -> Vec<SpotLPPositionV2> {
        vec![
            position(LP_LOCK_PUBKEY_V2.to_owned(), MIN_LP_LOCK_V2),
            SpotLPPositionV2 {
                owner: owner("bb"),
                shares: 13_142,
                last_mint_timestamp: Some(7),
                last_remove_timestamp: None,
                churn_tier: 2,
                last_churn_update_timestamp: Some(7),
            },
            SpotLPPositionV2 {
                owner: owner("cc"),
                shares: 0,
                last_mint_timestamp: Some(2),
                last_remove_timestamp: Some(6),
                churn_tier: 1,
                last_churn_update_timestamp: Some(6),
            },
        ]
    }

    fn state(pool: SpotPoolSnapshotV2, lp_positions: Vec<SpotLPPositionV2>) -> SpotSwapStateV2 {
        SpotSwapStateV2 {
            schema: SPOT_SWAP_STATE_SCHEMA_V2.to_owned(),
            module_release_id: root(20),
            pool,
            lp_positions,
            intent_nonces: Vec::new(),
        }
    }

    #[test]
    fn genesis_donor_shares_and_dormant_metadata_are_fully_committed() {
        let base = state(pool(), rows());
        let baseline = base.state_root().expect("root");
        assert_eq!(base.intent_nonce(&owner("aa")), 0);
        for name in [
            "shares",
            "last_mint_timestamp",
            "last_remove_timestamp",
            "churn_tier",
            "last_churn_update_timestamp",
        ] {
            let mut positions = rows();
            match name {
                "shares" => {
                    positions[1].shares -= 3;
                    positions[2].shares = 3;
                }
                "last_mint_timestamp" => positions[2].last_mint_timestamp = Some(3),
                "last_remove_timestamp" => positions[2].last_remove_timestamp = Some(3),
                "churn_tier" => positions[2].churn_tier = 3,
                _ => positions[2].last_churn_update_timestamp = Some(3),
            }
            let candidate = state(pool(), positions);
            assert_ne!(candidate.state_root().expect("root"), baseline, "{name}");
        }
    }

    #[test]
    fn invalid_ownership_is_unrepresentable() {
        for defect in [
            "missing",
            "duplicate",
            "unordered",
            "sum",
            "lock",
            "identity",
            "zero-reserve",
        ] {
            let mut pool = pool();
            let mut positions = rows();
            match defect {
                "missing" => positions.truncate(1),
                "duplicate" => {
                    positions = vec![rows()[0].clone(), rows()[1].clone(), rows()[1].clone()]
                }
                "unordered" => positions.reverse(),
                "sum" => positions[1].shares += 1,
                "lock" => {
                    positions[0].shares = 999;
                    positions[1].shares += 1;
                }
                "identity" => pool.pool_id = root(99).as_str().to_owned(),
                _ => pool.reserve1 = 0,
            }
            assert!(state(pool, positions).validate().is_err(), "{defect}");
        }
        assert!(state(pool(), rows()).validate().is_ok());
    }

    #[test]
    fn nonce_rows_are_positive_exact_u32() {
        for nonce in [0, 1 << 32] {
            let row = SpotIntentNonceV2 {
                owner: owner("aa"),
                last_nonce: nonce,
            };
            assert!(row.validate().is_err(), "{nonce}");
        }
        let row = SpotIntentNonceV2 {
            owner: owner("aa"),
            last_nonce: MAX_SPOT_INTENT_NONCE_V2,
        };
        assert!(row.validate().is_ok());
    }

    #[test]
    fn capacity_is_checked_before_traversing_rows() {
        let invalid = position("not-an-owner".to_owned(), 1);
        let too_many = state(pool(), vec![invalid.clone(); MAX_SPOT_OWNER_ROWS_V2 + 1]);
        assert_eq!(
            too_many.validate(),
            Err(AbiErrorV2::StateResourceLimit("Spot LP positions"))
        );
        let mut nonce_heavy = state(pool(), rows());
        nonce_heavy.intent_nonces = vec![
            SpotIntentNonceV2 {
                owner: "not-an-owner".to_owned(),
                last_nonce: 0,
            };
            MAX_SPOT_OWNER_ROWS_V2 + 1
        ];
        assert_eq!(
            nonce_heavy.validate(),
            Err(AbiErrorV2::StateResourceLimit("Spot intent nonces"))
        );
        let one_invalid = state(pool(), vec![invalid]);
        assert!(matches!(
            one_invalid.validate(),
            Err(AbiErrorV2::InvalidBinding(_))
        ));
    }

    #[test]
    fn owner_aliases_cannot_create_distinct_lp_or_nonce_identities() {
        let canonical = owner("aa");
        for alias in [
            canonical[2..].to_owned(),
            canonical.to_ascii_uppercase(),
            "alice".to_owned(),
            format!(" {canonical}"),
        ] {
            assert!(validate_spot_owner_v2(&alias, "alias").is_err(), "{alias}");
            assert!(position(alias.clone(), 1).validate().is_err());
            assert!(SpotIntentNonceV2 {
                owner: alias,
                last_nonce: 1
            }
            .validate()
            .is_err());
        }
        assert!(validate_spot_owner_v2(&canonical, "canonical").is_ok());
        assert!(validate_spot_owner_v2(LP_LOCK_PUBKEY_V2, "lock").is_ok());
        assert!(is_lp_lock_owner_v2(LP_LOCK_PUBKEY_V2));
        assert!(!is_lp_lock_owner_v2(&canonical));
        assert!(!is_lp_lock_owner_v2(&LP_LOCK_PUBKEY_V2[..97]));
    }

    #[test]
    fn pool_asset_canonical_form_matches_the_python_normalizer() {
        assert!(is_canonical_pool_asset_id_v2("A"));
        assert!(is_canonical_pool_asset_id_v2("0x"));
        assert!(is_canonical_pool_asset_id_v2("0xzz"));
        assert!(is_canonical_pool_asset_id_v2("0xabc123"));
        assert!(!is_canonical_pool_asset_id_v2("0xABC"));
        assert!(!is_canonical_pool_asset_id_v2("0Xabc"));
        let mut aliased = pool();
        aliased.asset0 = "0XAB".to_owned();
        aliased.asset1 = "0xcd".to_owned();
        assert!(aliased.validate().is_err());
    }

    #[test]
    fn canonical_pool_id_follows_the_legacy_preimage() {
        let pool = pool();
        let expected = format!("0x{}", hash_bytes_sha256_v2(b"TauSwapPoolAB30CPMM"));
        assert_eq!(pool.pool_id, expected);
        assert_ne!(
            compute_pool_id_v2("A", "B", 30, "CPMM", ""),
            compute_pool_id_v2("A", "B", 31, "CPMM", "")
        );
    }
}
