//! Protocol fee router — 4-way split (`buyburn` / `stakers` / `reserve` /
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

use crate::arith::{checked_add, mul_div_floor};
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
const ACCUMULATOR_VERSION: u32 = 1;

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
/// remainder carried out (equal to the new accumulator's `dust`).
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

/// Carried fee-router state. `cum_buyburn` is the buyback-accrual figure
/// (accrual only; burn execution is a later module).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct FeeAccumulator {
    pub dust: u128,
    pub cum_buyburn: u128,
    pub cum_stakers: u128,
    pub cum_reserve: u128,
    pub cum_hosts: u128,
}

impl FeeAccumulator {
    /// Canonical state root (`0x`-prefixed SHA-256). Mirrors
    /// `FeeAccumulator.state_root` in the Python reference.
    pub fn state_root(&self) -> String {
        let mut buf = domain_sep_bytes(ACCUMULATOR_LABEL, ACCUMULATOR_VERSION);
        buf.extend_from_slice(b"DST");
        buf.extend(encode_uvarint(self.dust));
        buf.extend_from_slice(b"CBB");
        buf.extend(encode_uvarint(self.cum_buyburn));
        buf.extend_from_slice(b"CST");
        buf.extend(encode_uvarint(self.cum_stakers));
        buf.extend_from_slice(b"CRS");
        buf.extend(encode_uvarint(self.cum_reserve));
        buf.extend_from_slice(b"CHS");
        buf.extend(encode_uvarint(self.cum_hosts));
        sha256_hex(&buf)
    }
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
    for v in split.components() {
        if !(0..=BPS_DENOM as i64).contains(&v) {
            return Err(RejectedReason::SplitComponentOutOfRange);
        }
    }

    // 3) Split must sum to exactly 10000. (Components are in [0, 10000], so the
    //    sum of four fits i64 with no overflow.)
    let sum: i64 = split.components().iter().sum();
    if sum != BPS_DENOM as i64 {
        return Err(RejectedReason::SplitDoesNotSumTo10000);
    }

    // 4) Domain must be known.
    let domain = Domain::from_label(source).ok_or(RejectedReason::UnknownDomain)?;

    // 5) Domain safety floors.
    check_domain_constraints(domain, split)?;

    // 6) Deterministic floor split with dust carry. bps are now known 0..=10000.
    let total = checked_add(amount, acc.dust)?;
    let buyburn = mul_div_floor(total, split.buyburn_bps as u128, BPS_DENOM)?;
    let stakers = mul_div_floor(total, split.stakers_bps as u128, BPS_DENOM)?;
    let reserve = mul_div_floor(total, split.reserve_bps as u128, BPS_DENOM)?;
    let hosts = mul_div_floor(total, split.hosts_bps as u128, BPS_DENOM)?;
    let distributed = buyburn + stakers + reserve + hosts; // <= total by floor-div
    debug_assert!(distributed <= total, "fee split over-distributed");
    let dust_out = total - distributed;

    // 7) Accumulate, with a MAX guard that keeps parity with the Python reference.
    let cum_buyburn = checked_add(acc.cum_buyburn, buyburn)?;
    let cum_stakers = checked_add(acc.cum_stakers, stakers)?;
    let cum_reserve = checked_add(acc.cum_reserve, reserve)?;
    let cum_hosts = checked_add(acc.cum_hosts, hosts)?;
    for v in [cum_buyburn, cum_stakers, cum_reserve, cum_hosts] {
        if v > MAX_FEE_AMOUNT {
            return Err(RejectedReason::ArithmeticOverflow);
        }
    }

    Ok(Accepted {
        receipt: FeeReceipt {
            source: source.to_string(),
            asset: asset.to_string(),
            amount,
            buyburn,
            stakers,
            reserve,
            hosts,
            dust: dust_out,
        },
        accumulator: FeeAccumulator {
            dust: dust_out,
            cum_buyburn,
            cum_stakers,
            cum_reserve,
            cum_hosts,
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
        assert_eq!(a.accumulator.cum_buyburn, 6_000);
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
            cum_buyburn: MAX_FEE_AMOUNT,
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
            let acc = FeeAccumulator { dust: dust_in, ..Default::default() };
            match route_fee(domain, "zUSD", amount, &table, &acc) {
                Ok(a) => {
                    let recv = &a.receipt;
                    prop_assert_eq!(
                        amount + dust_in,
                        recv.buyburn + recv.stakers + recv.reserve + recv.hosts + recv.dust
                    );
                    prop_assert!(recv.dust < 4); // 4 buckets => remainder < 4
                    prop_assert_eq!(a.accumulator.dust, recv.dust);
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
