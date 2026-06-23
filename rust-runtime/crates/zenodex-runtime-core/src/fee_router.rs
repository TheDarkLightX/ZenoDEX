//! Protocol fee router: 4-way split (`buyburn` / `stakers` / `reserve` /
//! `hosts`) with dust carry.
//!
//! This is the Rust shadow of the authoritative Python reference
//! (`src/core/fee_router.py`). It is the first Rust-owned runtime surface.
//!
//! Conservation invariant (identical to the ESSO `fee_split_dust_carry`
//! kernel, generalized from 3 to 4 buckets):
//!
//! ```text
//! amount + dust_in == buyburn + stakers + reserve + hosts + dust_out
//! ```
//!
//! The MVP split tables ([`canonical_split_table`]) are:
//!
//! | domain     | buyburn | stakers | reserve | hosts |
//! |------------|---------|---------|---------|-------|
//! | dex/perps  | 6000    | 0       | 2000    | 2000  |
//! | borrow     | 0       | 6000    | 2000    | 2000  |
//! | redemption | 0       | 6000    | 4000    | 0     |

use std::collections::BTreeSet;

use crate::arith::{checked_add, checked_mul};
use crate::canonical::{domain_sep_bytes, encode_bytes, encode_uvarint, sha256_hex};
use crate::error::{DomainConstraint, RejectedReason};

/// Basis-point denominator.
pub const BPS_DENOM: u128 = 10_000;

/// Upper bound on a single fee amount and on each accumulator component.
///
/// Bounding every value below `2**112` guarantees `(amount + dust) * bps`
/// stays below `2**128`, so the `u128` arithmetic never overflows for in-range
/// inputs and matches the Python reference's rejection boundary.
pub const MAX_FEE_AMOUNT: u128 = (1u128 << 112) - 1;

const RECEIPT_LABEL: &str = "fee_receipt";
const ACCUMULATOR_LABEL: &str = "fee_accumulator";
const RECEIPT_VERSION: u32 = 1;
const ACCUMULATOR_VERSION: u32 = 2;

const BUYBURN_FLOOR_BPS: i64 = 5_000;
const STAKERS_FLOOR_BPS: i64 = 5_000;
const REDEMPTION_RESERVE_FLOOR_BPS: i64 = 2_000;

/// A protocol-fee domain.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Domain {
    Dex,
    Perps,
    Borrow,
    Redemption,
}

impl Domain {
    /// Parse a canonical lowercase domain label.
    pub fn from_label(label: &str) -> Option<Domain> {
        match label {
            "dex" => Some(Domain::Dex),
            "perps" => Some(Domain::Perps),
            "borrow" => Some(Domain::Borrow),
            "redemption" => Some(Domain::Redemption),
            _ => None,
        }
    }

    /// Canonical lowercase label.
    pub fn label(self) -> &'static str {
        match self {
            Domain::Dex => "dex",
            Domain::Perps => "perps",
            Domain::Borrow => "borrow",
            Domain::Redemption => "redemption",
        }
    }
}

/// A 4-way basis-point split. Plain data; policy is validated in [`route_fee`].
///
/// `bps` are `i64` so out-of-range (negative or `> 10000`) values are
/// representable and rejected with [`RejectedReason::SplitComponentOutOfRange`],
/// matching the Python reference where bps are unbounded `int`s.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FeeSplitTable {
    pub buyburn_bps: i64,
    pub stakers_bps: i64,
    pub reserve_bps: i64,
    pub hosts_bps: i64,
}

impl FeeSplitTable {
    fn components(&self) -> [i64; 4] {
        [
            self.buyburn_bps,
            self.stakers_bps,
            self.reserve_bps,
            self.hosts_bps,
        ]
    }
}

/// The canonical MVP split table for a domain.
pub fn canonical_split_table(domain: Domain) -> FeeSplitTable {
    match domain {
        Domain::Dex | Domain::Perps => FeeSplitTable {
            buyburn_bps: 6_000,
            stakers_bps: 0,
            reserve_bps: 2_000,
            hosts_bps: 2_000,
        },
        Domain::Borrow => FeeSplitTable {
            buyburn_bps: 0,
            stakers_bps: 6_000,
            reserve_bps: 2_000,
            hosts_bps: 2_000,
        },
        Domain::Redemption => FeeSplitTable {
            buyburn_bps: 0,
            stakers_bps: 6_000,
            reserve_bps: 4_000,
            hosts_bps: 0,
        },
    }
}

/// Receipt for a single routed fee. `amount` is the raw input fee; `dust` is the
/// remainder carried out for this `(source, asset)` stream.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FeeReceipt {
    pub source: String,
    pub asset: String,
    pub amount: u128,
    pub buyburn: u128,
    pub stakers: u128,
    pub reserve: u128,
    pub hosts: u128,
    pub dust: u128,
}

impl FeeReceipt {
    /// Canonical receipt hash (`0x`-prefixed SHA-256). Mirrors
    /// `FeeReceipt.receipt_hash` in the Python reference.
    pub fn receipt_hash(&self) -> String {
        let mut buf = domain_sep_bytes(RECEIPT_LABEL, RECEIPT_VERSION);
        buf.extend_from_slice(b"SRC");
        buf.extend(encode_bytes(self.source.as_bytes()));
        buf.extend_from_slice(b"AST");
        buf.extend(encode_bytes(self.asset.as_bytes()));
        buf.extend_from_slice(b"AMT");
        buf.extend(encode_uvarint(self.amount));
        buf.extend_from_slice(b"BBN");
        buf.extend(encode_uvarint(self.buyburn));
        buf.extend_from_slice(b"STK");
        buf.extend(encode_uvarint(self.stakers));
        buf.extend_from_slice(b"RSV");
        buf.extend(encode_uvarint(self.reserve));
        buf.extend_from_slice(b"HST");
        buf.extend(encode_uvarint(self.hosts));
        buf.extend_from_slice(b"DST");
        buf.extend(encode_uvarint(self.dust));
        sha256_hex(&buf)
    }
}

/// Canonical amount for one asset in one accumulator bucket.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssetAmount {
    pub asset: String,
    pub amount: u128,
}

/// Rounding dust carried for exactly one source/asset fee stream.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DustEntry {
    pub source: String,
    pub asset: String,
    pub amount: u128,
    pub buyburn_remainder: u128,
    pub stakers_remainder: u128,
    pub reserve_remainder: u128,
    pub hosts_remainder: u128,
}

fn canonical_asset_amounts(mut entries: Vec<AssetAmount>) -> Vec<AssetAmount> {
    entries.retain(|entry| entry.amount != 0);
    entries.sort_by(|a, b| a.asset.cmp(&b.asset));
    entries
}

fn canonical_dust_entries(mut entries: Vec<DustEntry>) -> Vec<DustEntry> {
    entries.retain(|entry| entry.amount != 0);
    entries.sort_by(|a, b| {
        (a.source.as_str(), a.asset.as_str()).cmp(&(b.source.as_str(), b.asset.as_str()))
    });
    entries
}

fn asset_amount(entries: &[AssetAmount], asset: &str) -> u128 {
    entries
        .iter()
        .find(|entry| entry.asset == asset)
        .map(|entry| entry.amount)
        .unwrap_or(0)
}

fn dust_entry<'a>(entries: &'a [DustEntry], source: &str, asset: &str) -> Option<&'a DustEntry> {
    entries
        .iter()
        .find(|entry| entry.source == source && entry.asset == asset)
}

fn dust_amount(entries: &[DustEntry], source: &str, asset: &str) -> u128 {
    dust_entry(entries, source, asset)
        .map(|entry| entry.amount)
        .unwrap_or(0)
}

fn legacy_remainders(amount: u128, split: &FeeSplitTable) -> (u128, u128, u128, u128) {
    (
        amount * split.buyburn_bps as u128,
        amount * split.stakers_bps as u128,
        amount * split.reserve_bps as u128,
        amount * split.hosts_bps as u128,
    )
}

fn entry_remainders(entry: Option<&DustEntry>, split: &FeeSplitTable) -> (u128, u128, u128, u128) {
    let Some(entry) = entry else {
        return (0, 0, 0, 0);
    };
    let remainders = (
        entry.buyburn_remainder,
        entry.stakers_remainder,
        entry.reserve_remainder,
        entry.hosts_remainder,
    );
    if remainders == (0, 0, 0, 0) && entry.amount != 0 {
        return legacy_remainders(entry.amount, split);
    }
    remainders
}

fn dust_from_remainders(remainders: (u128, u128, u128, u128)) -> Result<u128, RejectedReason> {
    let total = checked_add(
        checked_add(remainders.0, remainders.1)?,
        checked_add(remainders.2, remainders.3)?,
    )?;
    if total % BPS_DENOM != 0 {
        return Err(RejectedReason::ArithmeticOverflow);
    }
    Ok(total / BPS_DENOM)
}

fn receipt_conserves(
    amount: u128,
    dust_in: u128,
    receipt: &FeeReceipt,
) -> Result<bool, RejectedReason> {
    let lhs = checked_add(amount, dust_in)?;
    let bucket_sum = checked_add(
        checked_add(receipt.buyburn, receipt.stakers)?,
        checked_add(receipt.reserve, receipt.hosts)?,
    )?;
    let rhs = checked_add(bucket_sum, receipt.dust)?;
    Ok(receipt.amount == amount && lhs == rhs)
}

fn set_asset_amount(entries: &[AssetAmount], asset: &str, amount: u128) -> Vec<AssetAmount> {
    let mut out: Vec<AssetAmount> = entries
        .iter()
        .filter(|entry| entry.asset != asset)
        .cloned()
        .collect();
    if amount != 0 {
        out.push(AssetAmount {
            asset: asset.to_string(),
            amount,
        });
    }
    canonical_asset_amounts(out)
}

fn set_dust_amount(
    entries: &[DustEntry],
    source: &str,
    asset: &str,
    amount: u128,
    remainders: (u128, u128, u128, u128),
) -> Vec<DustEntry> {
    let mut out: Vec<DustEntry> = entries
        .iter()
        .filter(|entry| !(entry.source == source && entry.asset == asset))
        .cloned()
        .collect();
    if amount != 0 {
        let (buyburn_remainder, stakers_remainder, reserve_remainder, hosts_remainder) = remainders;
        out.push(DustEntry {
            source: source.to_string(),
            asset: asset.to_string(),
            amount,
            buyburn_remainder,
            stakers_remainder,
            reserve_remainder,
            hosts_remainder,
        });
    }
    canonical_dust_entries(out)
}

fn encode_asset_amounts(entries: &[AssetAmount]) -> Vec<u8> {
    let canonical = canonical_asset_amounts(entries.to_vec());
    let mut buf = encode_uvarint(canonical.len() as u128);
    for entry in canonical {
        buf.extend_from_slice(b"AST");
        buf.extend(encode_bytes(entry.asset.as_bytes()));
        buf.extend_from_slice(b"AMT");
        buf.extend(encode_uvarint(entry.amount));
    }
    buf
}

fn encode_dust_entries(entries: &[DustEntry]) -> Vec<u8> {
    let canonical = canonical_dust_entries(entries.to_vec());
    let mut buf = encode_uvarint(canonical.len() as u128);
    for entry in canonical {
        buf.extend_from_slice(b"SRC");
        buf.extend(encode_bytes(entry.source.as_bytes()));
        buf.extend_from_slice(b"AST");
        buf.extend(encode_bytes(entry.asset.as_bytes()));
        buf.extend_from_slice(b"AMT");
        buf.extend(encode_uvarint(entry.amount));
        buf.extend_from_slice(b"BBR");
        buf.extend(encode_uvarint(entry.buyburn_remainder));
        buf.extend_from_slice(b"STR");
        buf.extend(encode_uvarint(entry.stakers_remainder));
        buf.extend_from_slice(b"RSR");
        buf.extend(encode_uvarint(entry.reserve_remainder));
        buf.extend_from_slice(b"HSR");
        buf.extend(encode_uvarint(entry.hosts_remainder));
    }
    buf
}

/// Carried fee-router state. Dust is keyed by `(source, asset)` so one token or
/// policy stream cannot consume another stream's rounding remainder. Cumulative
/// buckets are keyed by asset because different token units are not addable.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct FeeAccumulator {
    dust_by_stream: Vec<DustEntry>,
    cum_buyburn: Vec<AssetAmount>,
    cum_stakers: Vec<AssetAmount>,
    cum_reserve: Vec<AssetAmount>,
    cum_hosts: Vec<AssetAmount>,
}

impl FeeAccumulator {
    /// Build an accumulator from explicit sparse entries.
    ///
    /// Live authority calls use this to evaluate one route from the current
    /// Python accumulator. Duplicate decoded keys, zero entries, and values
    /// above the live MAX domain reject.
    pub fn from_parts(
        dust_by_stream: Vec<DustEntry>,
        cum_buyburn: Vec<AssetAmount>,
        cum_stakers: Vec<AssetAmount>,
        cum_reserve: Vec<AssetAmount>,
        cum_hosts: Vec<AssetAmount>,
    ) -> Result<FeeAccumulator, &'static str> {
        validate_dust_entries(&dust_by_stream)?;
        validate_asset_entries(&cum_buyburn)?;
        validate_asset_entries(&cum_stakers)?;
        validate_asset_entries(&cum_reserve)?;
        validate_asset_entries(&cum_hosts)?;
        Ok(FeeAccumulator {
            dust_by_stream: canonical_dust_entries(dust_by_stream),
            cum_buyburn: canonical_asset_amounts(cum_buyburn),
            cum_stakers: canonical_asset_amounts(cum_stakers),
            cum_reserve: canonical_asset_amounts(cum_reserve),
            cum_hosts: canonical_asset_amounts(cum_hosts),
        })
    }

    pub fn dust_entries(&self) -> impl Iterator<Item = (&str, &str, u128)> {
        self.dust_by_stream
            .iter()
            .map(|e| (e.source.as_str(), e.asset.as_str(), e.amount))
    }

    pub fn dust_entries_full(&self) -> impl Iterator<Item = &DustEntry> {
        self.dust_by_stream.iter()
    }

    pub fn buyburn_entries(&self) -> impl Iterator<Item = (&str, u128)> {
        self.cum_buyburn
            .iter()
            .map(|e| (e.asset.as_str(), e.amount))
    }

    pub fn stakers_entries(&self) -> impl Iterator<Item = (&str, u128)> {
        self.cum_stakers
            .iter()
            .map(|e| (e.asset.as_str(), e.amount))
    }

    pub fn reserve_entries(&self) -> impl Iterator<Item = (&str, u128)> {
        self.cum_reserve
            .iter()
            .map(|e| (e.asset.as_str(), e.amount))
    }

    pub fn hosts_entries(&self) -> impl Iterator<Item = (&str, u128)> {
        self.cum_hosts.iter().map(|e| (e.asset.as_str(), e.amount))
    }

    pub fn dust_for(&self, source: &str, asset: &str) -> u128 {
        dust_amount(&self.dust_by_stream, source, asset)
    }

    pub fn buyburn_for(&self, asset: &str) -> u128 {
        asset_amount(&self.cum_buyburn, asset)
    }

    pub fn stakers_for(&self, asset: &str) -> u128 {
        asset_amount(&self.cum_stakers, asset)
    }

    pub fn reserve_for(&self, asset: &str) -> u128 {
        asset_amount(&self.cum_reserve, asset)
    }

    pub fn hosts_for(&self, asset: &str) -> u128 {
        asset_amount(&self.cum_hosts, asset)
    }

    /// Canonical state root (`0x`-prefixed SHA-256). Mirrors
    /// `FeeAccumulator.state_root` in the Python reference.
    pub fn state_root(&self) -> String {
        let mut buf = domain_sep_bytes(ACCUMULATOR_LABEL, ACCUMULATOR_VERSION);
        buf.extend_from_slice(b"DST");
        buf.extend(encode_dust_entries(&self.dust_by_stream));
        buf.extend_from_slice(b"CBB");
        buf.extend(encode_asset_amounts(&self.cum_buyburn));
        buf.extend_from_slice(b"CST");
        buf.extend(encode_asset_amounts(&self.cum_stakers));
        buf.extend_from_slice(b"CRS");
        buf.extend(encode_asset_amounts(&self.cum_reserve));
        buf.extend_from_slice(b"CHS");
        buf.extend(encode_asset_amounts(&self.cum_hosts));
        sha256_hex(&buf)
    }
}

fn validate_asset_entries(entries: &[AssetAmount]) -> Result<(), &'static str> {
    let mut seen = BTreeSet::new();
    for entry in entries {
        if entry.amount == 0 || entry.amount > MAX_FEE_AMOUNT {
            return Err("invalid_accumulator_amount");
        }
        if !seen.insert(entry.asset.as_str()) {
            return Err("duplicate_asset_entry");
        }
    }
    Ok(())
}

fn validate_dust_entries(entries: &[DustEntry]) -> Result<(), &'static str> {
    let mut seen = BTreeSet::new();
    for entry in entries {
        if Domain::from_label(&entry.source).is_none() {
            return Err("unknown_domain");
        }
        if entry.amount == 0 || entry.amount > MAX_FEE_AMOUNT {
            return Err("invalid_accumulator_amount");
        }
        validate_dust_remainders(entry)?;
        if !seen.insert((entry.source.as_str(), entry.asset.as_str())) {
            return Err("duplicate_dust_entry");
        }
    }
    Ok(())
}

fn validate_dust_remainders(entry: &DustEntry) -> Result<(), &'static str> {
    let remainders = [
        entry.buyburn_remainder,
        entry.stakers_remainder,
        entry.reserve_remainder,
        entry.hosts_remainder,
    ];
    if remainders == [0, 0, 0, 0] {
        return Ok(());
    }
    if remainders.iter().any(|remainder| *remainder >= BPS_DENOM) {
        return Err("invalid_dust_remainder");
    }
    let sum: u128 = remainders.iter().sum();
    if sum != entry.amount * BPS_DENOM {
        return Err("invalid_dust_remainder");
    }
    Ok(())
}

/// Successful transition: a receipt plus the next accumulator.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Accepted {
    pub receipt: FeeReceipt,
    pub accumulator: FeeAccumulator,
}

fn check_domain_constraints(domain: Domain, t: &FeeSplitTable) -> Result<(), RejectedReason> {
    use RejectedReason::DomainConstraintViolated as Viol;
    match domain {
        Domain::Dex | Domain::Perps => {
            if t.buyburn_bps < BUYBURN_FLOOR_BPS {
                return Err(Viol(DomainConstraint::BuyburnBelowFloor));
            }
        }
        Domain::Borrow => {
            if t.stakers_bps < STAKERS_FLOOR_BPS {
                return Err(Viol(DomainConstraint::StakersBelowFloor));
            }
        }
        Domain::Redemption => {
            if t.buyburn_bps != 0 {
                return Err(Viol(DomainConstraint::RedemptionBuyburnMustBeZero));
            }
            if t.hosts_bps != 0 {
                return Err(Viol(DomainConstraint::RedemptionHostsMustBeZero));
            }
            if t.reserve_bps < REDEMPTION_RESERVE_FLOOR_BPS {
                return Err(Viol(DomainConstraint::RedemptionReserveBelowFloor));
            }
        }
    }
    Ok(())
}

fn check_split_components(split: &FeeSplitTable) -> Result<(), RejectedReason> {
    for component in split.components() {
        if !(0..=BPS_DENOM as i64).contains(&component) {
            return Err(RejectedReason::SplitComponentOutOfRange);
        }
    }
    Ok(())
}

fn check_split_sum(split: &FeeSplitTable) -> Result<(), RejectedReason> {
    // Safe after `check_split_components`: four values in [0, 10000] cannot
    // overflow i64.
    let sum: i64 = split.components().iter().sum();
    if sum != BPS_DENOM as i64 {
        return Err(RejectedReason::SplitDoesNotSumTo10000);
    }
    Ok(())
}

/// Outcome of the pure split-with-dust-carry core: the four bucket allocations,
/// the carried-out dust, and the new per-bucket remainders.
struct SplitOutcome {
    buyburn: u128,
    stakers: u128,
    reserve: u128,
    hosts: u128,
    dust_out: u128,
    remainders: (u128, u128, u128, u128),
}

/// Pure split-with-dust-carry core of [`route_fee`]: the consensus arithmetic.
///
/// Given a fee `amount`, a `split` (each bps in `[0, BPS_DENOM]`, summing to
/// `BPS_DENOM`), and the carried-in per-bucket remainders `prev` (each
/// `< BPS_DENOM`, summing to a multiple of `BPS_DENOM`), allocate each bucket as
/// `floor((amount*bps + prev_bucket) / BPS_DENOM)`, carry the new remainders, and
/// fold the four remainders into `dust_out = Σremainders / BPS_DENOM`.
///
/// **Conservation** (covered by unit/proptest/differential tests): with
/// `dust_in = Σprev / BPS_DENOM`,
/// `amount + dust_in == buyburn + stakers + reserve + hosts + dust_out`.
///
/// The helper validates the split before casting signed bps to `u128`. It is
/// total and overflow-safe via [`checked_mul`] / [`checked_add`]: a product or
/// sum past `u128` fails closed with [`RejectedReason::ArithmeticOverflow`].
/// Heap-free, so Kani discharges it directly on this running code.
fn split_with_dust(
    amount: u128,
    split: &FeeSplitTable,
    prev: (u128, u128, u128, u128),
) -> Result<SplitOutcome, RejectedReason> {
    check_split_components(split)?;
    check_split_sum(split)?;

    let buyburn_num = checked_add(checked_mul(amount, split.buyburn_bps as u128)?, prev.0)?;
    let stakers_num = checked_add(checked_mul(amount, split.stakers_bps as u128)?, prev.1)?;
    let reserve_num = checked_add(checked_mul(amount, split.reserve_bps as u128)?, prev.2)?;
    let hosts_num = checked_add(checked_mul(amount, split.hosts_bps as u128)?, prev.3)?;
    let remainders = (
        buyburn_num % BPS_DENOM,
        stakers_num % BPS_DENOM,
        reserve_num % BPS_DENOM,
        hosts_num % BPS_DENOM,
    );
    let dust_out = dust_from_remainders(remainders)?;
    Ok(SplitOutcome {
        buyburn: buyburn_num / BPS_DENOM,
        stakers: stakers_num / BPS_DENOM,
        reserve: reserve_num / BPS_DENOM,
        hosts: hosts_num / BPS_DENOM,
        dust_out,
        remainders,
    })
}

/// Route `amount` of protocol fees (in `asset`) for `source` through `split`,
/// carrying dust from / into `acc`.
///
/// The validation order is fixed and mirrors the Python reference exactly so
/// the two runtimes reject identical inputs with identical codes:
/// 1. amount range, 2. split-component range, 3. split sum, 4. known domain,
/// 5. domain floors, 6. floor split with dust carry, 7. accumulate.
pub fn route_fee(
    source: &str,
    asset: &str,
    amount: u128,
    split: &FeeSplitTable,
    acc: &FeeAccumulator,
) -> Result<Accepted, RejectedReason> {
    // 1) Amount range. (Negative is impossible for u128; the trace/CLI layer
    //    maps a negative JSON amount to `negative_amount` before this point.)
    if amount > MAX_FEE_AMOUNT {
        return Err(RejectedReason::AmountTooLarge);
    }

    // 2) Split-component range.
    check_split_components(split)?;

    // 3) Split must sum to exactly 10000. (Components are in [0, 10000], so the
    //    sum of four fits i64 with no overflow.)
    check_split_sum(split)?;

    // 4) Domain must be known.
    let domain = Domain::from_label(source).ok_or(RejectedReason::UnknownDomain)?;

    // 5) Domain safety floors.
    check_domain_constraints(domain, split)?;

    // 6) Deterministic per-bucket remainder split. Each bucket carries only its
    // own scaled fractional entitlement, so small-fee granularity cannot move
    // reserve/host/staker value into a dominant bucket.
    let prev = entry_remainders(dust_entry(&acc.dust_by_stream, source, asset), split);
    let SplitOutcome {
        buyburn,
        stakers,
        reserve,
        hosts,
        dust_out,
        remainders: dust_remainders,
    } = split_with_dust(amount, split, prev)?;

    // 7) Accumulate, with a MAX guard that keeps parity with the Python reference.
    let cum_buyburn = checked_add(acc.buyburn_for(asset), buyburn)?;
    let cum_stakers = checked_add(acc.stakers_for(asset), stakers)?;
    let cum_reserve = checked_add(acc.reserve_for(asset), reserve)?;
    let cum_hosts = checked_add(acc.hosts_for(asset), hosts)?;
    for v in [cum_buyburn, cum_stakers, cum_reserve, cum_hosts] {
        if v > MAX_FEE_AMOUNT {
            return Err(RejectedReason::ArithmeticOverflow);
        }
    }

    let receipt = FeeReceipt {
        source: source.to_string(),
        asset: asset.to_string(),
        amount,
        buyburn,
        stakers,
        reserve,
        hosts,
        dust: dust_out,
    };
    if !receipt_conserves(amount, acc.dust_for(source, asset), &receipt)? {
        return Err(RejectedReason::ConservationViolation);
    }

    Ok(Accepted {
        receipt,
        accumulator: FeeAccumulator {
            dust_by_stream: set_dust_amount(
                &acc.dust_by_stream,
                source,
                asset,
                dust_out,
                dust_remainders,
            ),
            cum_buyburn: set_asset_amount(&acc.cum_buyburn, asset, cum_buyburn),
            cum_stakers: set_asset_amount(&acc.cum_stakers, asset, cum_stakers),
            cum_reserve: set_asset_amount(&acc.cum_reserve, asset, cum_reserve),
            cum_hosts: set_asset_amount(&acc.cum_hosts, asset, cum_hosts),
        },
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn route(source: &str, amount: u128, table: FeeSplitTable) -> Result<Accepted, RejectedReason> {
        route_fee(source, "zUSD", amount, &table, &FeeAccumulator::default())
    }

    #[test]
    fn dex_exact_split_no_dust() {
        let a = route("dex", 10_000, canonical_split_table(Domain::Dex)).unwrap();
        let r = &a.receipt;
        assert_eq!(
            (r.buyburn, r.stakers, r.reserve, r.hosts, r.dust),
            (6_000, 0, 2_000, 2_000, 0)
        );
        assert_eq!(a.accumulator.buyburn_for("zUSD"), 6_000);
    }

    #[test]
    fn redemption_no_buyburn_no_hosts() {
        let a = route(
            "redemption",
            10_000,
            canonical_split_table(Domain::Redemption),
        )
        .unwrap();
        assert_eq!(a.receipt.buyburn, 0);
        assert_eq!(a.receipt.hosts, 0);
        assert_eq!((a.receipt.stakers, a.receipt.reserve), (6_000, 4_000));
    }

    #[test]
    fn repeated_tiny_dex_fees_preserve_long_run_split() {
        let mut acc = FeeAccumulator::default();
        for _ in 0..10 {
            acc = route_fee("dex", "zUSD", 1, &canonical_split_table(Domain::Dex), &acc)
                .unwrap()
                .accumulator;
        }
        assert_eq!(acc.buyburn_for("zUSD"), 6);
        assert_eq!(acc.stakers_for("zUSD"), 0);
        assert_eq!(acc.reserve_for("zUSD"), 2);
        assert_eq!(acc.hosts_for("zUSD"), 2);
        assert_eq!(acc.dust_for("dex", "zUSD"), 0);
    }

    #[test]
    fn from_parts_rejects_duplicate_keys_and_invalid_amounts() {
        assert_eq!(
            FeeAccumulator::from_parts(
                vec![],
                vec![
                    AssetAmount {
                        asset: "zUSD".to_string(),
                        amount: 1
                    },
                    AssetAmount {
                        asset: "zUSD".to_string(),
                        amount: 2
                    },
                ],
                vec![],
                vec![],
                vec![],
            ),
            Err("duplicate_asset_entry")
        );
        assert_eq!(
            FeeAccumulator::from_parts(
                vec![
                    DustEntry {
                        source: "dex".to_string(),
                        asset: "zUSD".to_string(),
                        amount: 1,
                        buyburn_remainder: 6_000,
                        stakers_remainder: 0,
                        reserve_remainder: 2_000,
                        hosts_remainder: 2_000,
                    },
                    DustEntry {
                        source: "dex".to_string(),
                        asset: "zUSD".to_string(),
                        amount: 1,
                        buyburn_remainder: 5_000,
                        stakers_remainder: 0,
                        reserve_remainder: 3_000,
                        hosts_remainder: 2_000,
                    },
                ],
                vec![],
                vec![],
                vec![],
                vec![],
            ),
            Err("duplicate_dust_entry")
        );
        assert_eq!(
            FeeAccumulator::from_parts(
                vec![],
                vec![AssetAmount {
                    asset: "zUSD".to_string(),
                    amount: 0
                }],
                vec![],
                vec![],
                vec![],
            ),
            Err("invalid_accumulator_amount")
        );
    }

    #[test]
    fn dust_example_12347() {
        let a = route("dex", 12_347, canonical_split_table(Domain::Dex)).unwrap();
        let r = &a.receipt;
        assert_eq!(
            (r.buyburn, r.stakers, r.reserve, r.hosts, r.dust),
            (7_408, 0, 2_469, 2_469, 1)
        );
        assert_eq!(
            r.amount,
            r.buyburn + r.stakers + r.reserve + r.hosts + r.dust
        );
    }

    #[test]
    fn fractional_aggregate_dust_rejects_in_release_too() {
        assert_eq!(
            dust_from_remainders((1, 0, 0, 0)),
            Err(RejectedReason::ArithmeticOverflow)
        );
    }

    #[test]
    fn receipt_conservation_guard_detects_corruption() {
        let receipt = FeeReceipt {
            source: "dex".to_string(),
            asset: "zUSD".to_string(),
            amount: 100,
            buyburn: 60,
            stakers: 0,
            reserve: 20,
            hosts: 19,
            dust: 0,
        };
        assert_eq!(receipt_conserves(100, 0, &receipt), Ok(false));
    }

    #[test]
    fn dust_is_scoped_by_source_and_asset() {
        let first = route_fee(
            "dex",
            "zUSD",
            1,
            &canonical_split_table(Domain::Dex),
            &FeeAccumulator::default(),
        )
        .unwrap();
        assert_eq!(first.accumulator.dust_for("dex", "zUSD"), 1);

        let second = route_fee(
            "dex",
            "AGRS",
            9_999,
            &canonical_split_table(Domain::Dex),
            &first.accumulator,
        )
        .unwrap();
        let r = &second.receipt;
        assert_eq!(r.buyburn + r.stakers + r.reserve + r.hosts + r.dust, 9_999);
        assert_eq!(second.accumulator.dust_for("dex", "zUSD"), 1);
        assert_eq!(second.accumulator.dust_for("dex", "AGRS"), r.dust);

        let third = route_fee(
            "perps",
            "zUSD",
            9_999,
            &canonical_split_table(Domain::Perps),
            &second.accumulator,
        )
        .unwrap();
        let r = &third.receipt;
        assert_eq!(r.buyburn + r.stakers + r.reserve + r.hosts + r.dust, 9_999);
        assert_eq!(third.accumulator.dust_for("dex", "zUSD"), 1);
    }

    #[test]
    fn rejections_have_stable_codes() {
        let dex = canonical_split_table(Domain::Dex);
        assert_eq!(
            route("dex", MAX_FEE_AMOUNT + 1, dex),
            Err(RejectedReason::AmountTooLarge)
        );
        assert_eq!(
            route(
                "dex",
                1_000,
                FeeSplitTable {
                    buyburn_bps: 10_001,
                    stakers_bps: 0,
                    reserve_bps: 0,
                    hosts_bps: 0
                }
            ),
            Err(RejectedReason::SplitComponentOutOfRange)
        );
        assert_eq!(
            route(
                "dex",
                1_000,
                FeeSplitTable {
                    buyburn_bps: 6_000,
                    stakers_bps: 0,
                    reserve_bps: 2_000,
                    hosts_bps: 1_999
                }
            ),
            Err(RejectedReason::SplitDoesNotSumTo10000)
        );
        assert_eq!(
            route(
                "lending",
                1_000,
                FeeSplitTable {
                    buyburn_bps: 2_500,
                    stakers_bps: 2_500,
                    reserve_bps: 2_500,
                    hosts_bps: 2_500
                }
            ),
            Err(RejectedReason::UnknownDomain)
        );
        assert_eq!(
            route(
                "redemption",
                1_000,
                FeeSplitTable {
                    buyburn_bps: 1,
                    stakers_bps: 5_999,
                    reserve_bps: 4_000,
                    hosts_bps: 0
                }
            ),
            Err(RejectedReason::DomainConstraintViolated(
                DomainConstraint::RedemptionBuyburnMustBeZero
            ))
        );
        assert_eq!(
            route(
                "dex",
                1_000,
                FeeSplitTable {
                    buyburn_bps: 4_999,
                    stakers_bps: 1,
                    reserve_bps: 3_000,
                    hosts_bps: 2_000
                }
            ),
            Err(RejectedReason::DomainConstraintViolated(
                DomainConstraint::BuyburnBelowFloor
            ))
        );
    }

    #[test]
    fn accumulator_overflow_is_rejected() {
        let acc = FeeAccumulator {
            cum_buyburn: vec![AssetAmount {
                asset: "zUSD".to_string(),
                amount: MAX_FEE_AMOUNT,
            }],
            ..Default::default()
        };
        let res = route_fee(
            "dex",
            "zUSD",
            10_000,
            &canonical_split_table(Domain::Dex),
            &acc,
        );
        assert_eq!(res, Err(RejectedReason::ArithmeticOverflow));
    }

    #[test]
    fn canonical_split_core_exhausts_one_bps_quantum_and_dust_patterns() {
        let prev_patterns = [
            (0, 0, 0, 0),
            (2_500, 2_500, 2_500, 2_500),
            (5_000, 5_000, 5_000, 5_000),
            (7_500, 7_500, 7_500, 7_500),
            (9_999, 1, 0, 0),
            (0, 9_999, 1, 0),
            (0, 0, 9_999, 1),
            (9_999, 9_999, 9_999, 3),
        ];
        for domain in [
            Domain::Dex,
            Domain::Perps,
            Domain::Borrow,
            Domain::Redemption,
        ] {
            let split = canonical_split_table(domain);
            for amount in 0..=BPS_DENOM {
                for prev in prev_patterns {
                    let sum_prev = prev.0 + prev.1 + prev.2 + prev.3;
                    assert_eq!(sum_prev % BPS_DENOM, 0);
                    let dust_in = sum_prev / BPS_DENOM;
                    let out = split_with_dust(amount, &split, prev)
                        .expect("canonical split with valid carried dust accepts");
                    assert_eq!(
                        amount + dust_in,
                        out.buyburn + out.stakers + out.reserve + out.hosts + out.dust_out
                    );
                }
            }
        }
    }

    proptest! {
        // route_fee never panics and, when it accepts, conserves value and
        // produces non-negative buckets with bounded dust.
        #[test]
        fn conservation_and_no_panic(
            amount in 0u128..=MAX_FEE_AMOUNT,
            dust_in in 0u128..4,
            domain_idx in 0usize..4,
            b in -1i64..=10_001,
            s in -1i64..=10_001,
            r in -1i64..=10_001,
            h in -1i64..=10_001,
        ) {
            let domain = ["dex", "perps", "borrow", "redemption"][domain_idx];
            let table = FeeSplitTable { buyburn_bps: b, stakers_bps: s, reserve_bps: r, hosts_bps: h };
            let acc = FeeAccumulator {
                dust_by_stream: set_dust_amount(&[], domain, "zUSD", dust_in, (0, 0, 0, 0)),
                ..Default::default()
            };
            match route_fee(domain, "zUSD", amount, &table, &acc) {
                Ok(a) => {
                    let recv = &a.receipt;
                    prop_assert_eq!(
                        amount + dust_in,
                        recv.buyburn + recv.stakers + recv.reserve + recv.hosts + recv.dust
                    );
                    prop_assert!(recv.dust < 4); // 4 buckets => remainder < 4
                    prop_assert_eq!(a.accumulator.dust_for(domain, "zUSD"), recv.dust);
                }
                Err(_) => { /* a typed rejection is always acceptable */ }
            }
        }

        // The canonical MVP tables are always accepted and conserve value.
        #[test]
        fn canonical_tables_always_accept(
            amount in 0u128..=MAX_FEE_AMOUNT,
            domain_idx in 0usize..4,
        ) {
            let domains = [Domain::Dex, Domain::Perps, Domain::Borrow, Domain::Redemption];
            let domain = domains[domain_idx];
            let a = route_fee(domain.label(), "zUSD", amount, &canonical_split_table(domain), &FeeAccumulator::default()).unwrap();
            let recv = &a.receipt;
            prop_assert_eq!(amount, recv.buyburn + recv.stakers + recv.reserve + recv.hosts + recv.dust);
            if matches!(domain, Domain::Redemption) {
                prop_assert_eq!(recv.buyburn, 0);
                prop_assert_eq!(recv.hosts, 0);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// CBC_CORE_V0: Kani contracts on the runtime split arithmetic.
//
// `split_with_dust` is the pure split-with-dust-carry core the running
// `route_fee` calls: the consensus arithmetic where value-creation / dust-loss
// bugs would live. Kani discharges it directly (heap-free: no String/Vec/sha2).
// `dust_from_remainders` is the release-mode fractional-aggregate guard (a real
// `Result` error, not a debug_assert). The string-canonicalization, per-stream
// dust map, and accumulation/MAX guards of `route_fee` (kani-intractable) stay
// covered by the deterministic one-quantum conservation test above, the
// proptest invariants above, and the Python<->Rust differential (including the
// pre-seeded-accumulator + boundary-dust cases). Run:
// `cargo kani -p zenodex-runtime-core --harness fee_router::kani_contracts`.
// ---------------------------------------------------------------------------
#[cfg(kani)]
mod kani_contracts {
    use super::*;

    /// A symbolic per-bucket remainder: `< BPS_DENOM` (the in-domain shape,
    /// where each stored remainder is `some_num % BPS_DENOM`).
    fn arb_remainder() -> u128 {
        let r = u128::from(kani::any::<u16>());
        kani::assume(r < BPS_DENOM);
        r
    }

    /// `dust_from_remainders` TOTALITY + EXACTNESS. Total for ANY u128 inputs
    /// (checked_add guards overflow; `% / BPS_DENOM` is a nonzero constant so no
    /// div-by-zero). In-domain (each remainder `< BPS_DENOM`, so their sum cannot
    /// overflow) it returns `Ok(sum / BPS_DENOM)` iff `sum % BPS_DENOM == 0`,
    /// else `ArithmeticOverflow`, with no debug_assert or panic (the
    /// release-mode fractional-aggregate guard is a real Result error).
    #[kani::proof]
    fn dust_from_remainders_total_and_exact() {
        // Totality over the full domain.
        let _ = dust_from_remainders((kani::any(), kani::any(), kani::any(), kani::any()));
        // Exactness in-domain.
        let r = (
            arb_remainder(),
            arb_remainder(),
            arb_remainder(),
            arb_remainder(),
        );
        let sum = r.0 + r.1 + r.2 + r.3; // < 4*BPS_DENOM, no overflow
        match dust_from_remainders(r) {
            Ok(d) => {
                assert_eq!(sum % BPS_DENOM, 0);
                assert_eq!(d, sum / BPS_DENOM);
            }
            Err(reason) => {
                assert_eq!(reason, RejectedReason::ArithmeticOverflow);
                assert_ne!(sum % BPS_DENOM, 0);
            }
        }
    }

    /// TOTALITY: `split_with_dust` never panics / overflows / wraps for ANY
    /// `amount`, ANY split components, ANY carried-in remainders. Split validation,
    /// `checked_mul`, and `checked_add` fail closed for out-of-domain values.
    #[kani::proof]
    fn split_is_total() {
        let split = FeeSplitTable {
            buyburn_bps: kani::any(),
            stakers_bps: kani::any(),
            reserve_bps: kani::any(),
            hosts_bps: kani::any(),
        };
        let _ = split_with_dust(
            kani::any(),
            &split,
            (kani::any(), kani::any(), kani::any(), kani::any()),
        );
    }

    /// NON-VACUITY. An in-domain DEX split accepts and can emit nonzero dust;
    /// the fractional-aggregate guard can reject. (Kani fails an unsatisfiable
    /// cover, so these are not vacuous.)
    #[kani::proof]
    fn covers_are_reachable() {
        let split = canonical_split_table(Domain::Dex);
        let amount = u128::from(kani::any::<u16>());
        kani::assume(amount <= BPS_DENOM);
        let prev = (
            arb_remainder(),
            arb_remainder(),
            arb_remainder(),
            arb_remainder(),
        );
        let sum_prev = prev.0 + prev.1 + prev.2 + prev.3;
        kani::assume(sum_prev % BPS_DENOM == 0);
        let res = split_with_dust(amount, &split, prev);
        kani::cover!(res.is_ok());
        kani::cover!(matches!(&res, Ok(o) if o.dust_out > 0));
        kani::cover!(dust_from_remainders((1, 0, 0, 0)).is_err());
    }
}
