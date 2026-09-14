//! v8 CPMM settlement quotes with checked `u128` intermediates.
//!
//! These functions mirror `src/kernels/python/cpmm_swap_v8.py` composed with
//! `src/kernels/python/settlement_swap_runtime_v1.py` for the isolated Spot
//! profile: the whole ceil-rounded fee stays in pool reserves (protocol share
//! zero), exact-in output is floored, exact-out gross input is the minimal
//! sufficient value and the 200-bps overdelivery ceiling is retained.
//!
//! Bound argument for the state-admitted domain (reserves and swap amounts at
//! most `3e9 < 2^32`, fee at most `10_000 < 2^14`):
//!
//! ```text
//! exact-in:  reserve_in * reserve_out           <= 9e18   < 2^63
//!            amount_in * fee_bps                <= 3e13   < 2^45
//!            reserve_out * net_in               <= 9e18   < 2^63
//! exact-out: reserve_in * amount_out            <= 9e18   < 2^63
//!            net_in_required                    <= 9e18            (denominator >= 1)
//!            net_in_required * 10_000           <= 9e22   < 2^77
//!            amount_in                          <= 9e22            (fee denominator >= 1)
//!            amount_in * fee_bps                <= 9e26   < 2^90
//!            reserve_out * net_in_actual        <= 2.7e32 < 2^108
//!            reserve_in_after * reserve_out_after <= 2.7e32 < 2^108
//!            overdelivery_gap * 10_000          <= 3e13   < 2^45
//! ```
//!
//! Every operation is still checked. Overflow yields
//! `SpotQuoteErrorV2::Arithmetic` and never a panic; the unit tests evaluate the
//! extreme corners of the domain and assert that this variant is unreachable.
//! No `U256` type is needed because the largest intermediate is below `2^108`.

pub const BPS_DENOM_V2: u128 = 10_000;
pub const DEX_POOL_RESERVE_MAX_V2: u128 = 3_000_000_000;
pub const DEX_SWAP_AMOUNT_MAX_V2: u128 = 3_000_000_000;
pub const CPMM_EXACT_OUT_MAX_OVERDELIVERY_GAP_BPS_V2: u128 = 200;

/// Closed quote failure family. The plan maps every variant to
/// `QUOTE_REJECTED`, exactly as the Python planner maps any `ValueError` or
/// `ArithmeticError` from the settlement quote helpers.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SpotQuoteErrorV2 {
    ReserveDomain,
    AmountDomain,
    FeeDomain,
    ReserveInDomainAfterSwap,
    ZeroNetInput,
    ZeroOutput,
    OutputExceedsReserve,
    DrainsReserveOut,
    FullFee,
    InsufficientGrossInput,
    OverdeliveryGap,
    ProductDecreased,
    Arithmetic,
}

impl SpotQuoteErrorV2 {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ReserveDomain => "RESERVE_DOMAIN",
            Self::AmountDomain => "AMOUNT_DOMAIN",
            Self::FeeDomain => "FEE_DOMAIN",
            Self::ReserveInDomainAfterSwap => "RESERVE_IN_DOMAIN_AFTER_SWAP",
            Self::ZeroNetInput => "ZERO_NET_INPUT",
            Self::ZeroOutput => "ZERO_OUTPUT",
            Self::OutputExceedsReserve => "OUTPUT_EXCEEDS_RESERVE",
            Self::DrainsReserveOut => "DRAINS_RESERVE_OUT",
            Self::FullFee => "FULL_FEE",
            Self::InsufficientGrossInput => "INSUFFICIENT_GROSS_INPUT",
            Self::OverdeliveryGap => "OVERDELIVERY_GAP",
            Self::ProductDecreased => "PRODUCT_DECREASED",
            Self::Arithmetic => "ARITHMETIC",
        }
    }
}

pub type SpotQuoteResultV2<T> = Result<T, SpotQuoteErrorV2>;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SpotSwapModeV2 {
    ExactIn,
    ExactOut,
}

impl SpotSwapModeV2 {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ExactIn => "exact_in",
            Self::ExactOut => "exact_out",
        }
    }
}

/// One settlement quote plus the resulting reserves.
///
/// `amount_out_quote` equals `amount_out` for exact-in quotes. For exact-out
/// quotes it is the floored exact-in output of the gross input, and
/// `overdelivery_gap_bps` is the ceil-rounded gap it leaves above the request.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SpotSwapQuoteV2 {
    pub mode: SpotSwapModeV2,
    pub amount_in: u128,
    pub amount_out: u128,
    pub fee_paid: u128,
    pub net_in: u128,
    pub reserve_in_before: u128,
    pub reserve_out_before: u128,
    pub reserve_in_after: u128,
    pub reserve_out_after: u128,
    pub k_before: u128,
    pub k_after: u128,
    pub amount_out_quote: u128,
    pub overdelivery_gap_bps: u128,
}

fn checked_mul(left: u128, right: u128) -> SpotQuoteResultV2<u128> {
    left.checked_mul(right).ok_or(SpotQuoteErrorV2::Arithmetic)
}

fn checked_add(left: u128, right: u128) -> SpotQuoteResultV2<u128> {
    left.checked_add(right).ok_or(SpotQuoteErrorV2::Arithmetic)
}

fn checked_sub(left: u128, right: u128) -> SpotQuoteResultV2<u128> {
    left.checked_sub(right).ok_or(SpotQuoteErrorV2::Arithmetic)
}

/// `ceil(numerator / denominator)` without forming `numerator + denominator`.
fn ceil_div(numerator: u128, denominator: u128) -> SpotQuoteResultV2<u128> {
    if denominator == 0 {
        return Err(SpotQuoteErrorV2::Arithmetic);
    }
    let quotient = numerator / denominator;
    if numerator % denominator == 0 {
        Ok(quotient)
    } else {
        checked_add(quotient, 1)
    }
}

/// `fee_total = ceil(gross_in * fee_bps / 10_000)` on the gross input.
fn fee_total(gross_in: u128, fee_bps: u128) -> SpotQuoteResultV2<u128> {
    ceil_div(checked_mul(gross_in, fee_bps)?, BPS_DENOM_V2)
}

fn require_domain(value: u128, maximum: u128, error: SpotQuoteErrorV2) -> SpotQuoteResultV2<()> {
    if value == 0 || value > maximum {
        return Err(error);
    }
    Ok(())
}

fn require_common_domain(
    reserve_in: u128,
    reserve_out: u128,
    fee_bps: u128,
) -> SpotQuoteResultV2<()> {
    require_domain(
        reserve_in,
        DEX_POOL_RESERVE_MAX_V2,
        SpotQuoteErrorV2::ReserveDomain,
    )?;
    require_domain(
        reserve_out,
        DEX_POOL_RESERVE_MAX_V2,
        SpotQuoteErrorV2::ReserveDomain,
    )?;
    if fee_bps > BPS_DENOM_V2 {
        return Err(SpotQuoteErrorV2::FeeDomain);
    }
    Ok(())
}

/// Exact-in quote: gross fee retained, floored output, next input domain kept.
pub fn quote_cpmm_swap_exact_in_v2(
    reserve_in: u128,
    reserve_out: u128,
    amount_in: u128,
    fee_bps: u128,
) -> SpotQuoteResultV2<SpotSwapQuoteV2> {
    require_common_domain(reserve_in, reserve_out, fee_bps)?;
    require_domain(
        amount_in,
        DEX_SWAP_AMOUNT_MAX_V2,
        SpotQuoteErrorV2::AmountDomain,
    )?;
    let reserve_in_after = checked_add(reserve_in, amount_in)?;
    if reserve_in_after > DEX_POOL_RESERVE_MAX_V2 {
        return Err(SpotQuoteErrorV2::ReserveInDomainAfterSwap);
    }
    let k_before = checked_mul(reserve_in, reserve_out)?;
    let fee_paid = fee_total(amount_in, fee_bps)?;
    let net_in = checked_sub(amount_in, fee_paid)?;
    if net_in == 0 {
        return Err(SpotQuoteErrorV2::ZeroNetInput);
    }
    let denominator = checked_add(reserve_in, net_in)?;
    let amount_out = checked_mul(reserve_out, net_in)? / denominator;
    if amount_out == 0 {
        return Err(SpotQuoteErrorV2::ZeroOutput);
    }
    if amount_out > reserve_out {
        return Err(SpotQuoteErrorV2::OutputExceedsReserve);
    }
    let reserve_out_after = checked_sub(reserve_out, amount_out)?;
    let k_after = checked_mul(reserve_in_after, reserve_out_after)?;
    if k_after < k_before {
        return Err(SpotQuoteErrorV2::ProductDecreased);
    }
    Ok(SpotSwapQuoteV2 {
        mode: SpotSwapModeV2::ExactIn,
        amount_in,
        amount_out,
        fee_paid,
        net_in,
        reserve_in_before: reserve_in,
        reserve_out_before: reserve_out,
        reserve_in_after,
        reserve_out_after,
        k_before,
        k_after,
        amount_out_quote: amount_out,
        overdelivery_gap_bps: 0,
    })
}

/// Exact-out quote: minimal sufficient gross input under the 200-bps gap policy.
pub fn quote_cpmm_swap_exact_out_v2(
    reserve_in: u128,
    reserve_out: u128,
    amount_out: u128,
    fee_bps: u128,
) -> SpotQuoteResultV2<SpotSwapQuoteV2> {
    require_common_domain(reserve_in, reserve_out, fee_bps)?;
    require_domain(
        amount_out,
        DEX_SWAP_AMOUNT_MAX_V2,
        SpotQuoteErrorV2::AmountDomain,
    )?;
    if amount_out >= reserve_out {
        return Err(SpotQuoteErrorV2::DrainsReserveOut);
    }
    if fee_bps == BPS_DENOM_V2 {
        return Err(SpotQuoteErrorV2::FullFee);
    }
    let numerator = checked_mul(reserve_in, amount_out)?;
    let denominator = checked_sub(reserve_out, amount_out)?;
    let net_in_required = ceil_div(numerator, denominator)?;
    if net_in_required == 0 {
        return Err(SpotQuoteErrorV2::ZeroNetInput);
    }
    let fee_denominator = checked_sub(BPS_DENOM_V2, fee_bps)?;
    let amount_in = ceil_div(checked_mul(net_in_required, BPS_DENOM_V2)?, fee_denominator)?;
    if amount_in == 0 {
        return Err(SpotQuoteErrorV2::ZeroNetInput);
    }
    let k_before = checked_mul(reserve_in, reserve_out)?;
    let fee_paid = fee_total(amount_in, fee_bps)?;
    let net_in = checked_sub(amount_in, fee_paid)?;
    if net_in == 0 {
        return Err(SpotQuoteErrorV2::ZeroNetInput);
    }
    let denom_price = checked_add(reserve_in, net_in)?;
    let amount_out_quote = checked_mul(reserve_out, net_in)? / denom_price;
    if amount_out_quote < amount_out {
        return Err(SpotQuoteErrorV2::InsufficientGrossInput);
    }
    let reserve_in_after = checked_add(reserve_in, amount_in)?;
    let reserve_out_after = checked_sub(reserve_out, amount_out)?;
    let k_after = checked_mul(reserve_in_after, reserve_out_after)?;
    let overdelivery_gap = checked_sub(amount_out_quote, amount_out)?;
    let overdelivery_gap_bps = ceil_div(checked_mul(overdelivery_gap, BPS_DENOM_V2)?, amount_out)?;
    if overdelivery_gap_bps > CPMM_EXACT_OUT_MAX_OVERDELIVERY_GAP_BPS_V2 {
        return Err(SpotQuoteErrorV2::OverdeliveryGap);
    }
    if k_after < k_before {
        return Err(SpotQuoteErrorV2::ProductDecreased);
    }
    Ok(SpotSwapQuoteV2 {
        mode: SpotSwapModeV2::ExactOut,
        amount_in,
        amount_out,
        fee_paid,
        net_in,
        reserve_in_before: reserve_in,
        reserve_out_before: reserve_out,
        reserve_in_after,
        reserve_out_after,
        k_before,
        k_after,
        amount_out_quote,
        overdelivery_gap_bps,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const MAX: u128 = DEX_POOL_RESERVE_MAX_V2;

    #[test]
    fn given_python_fixture_pool_when_exact_in_ten_at_thirty_bps_then_out_is_eight_fee_one() {
        let quote = quote_cpmm_swap_exact_in_v2(1_000, 1_000, 10, 30).expect("quote");
        assert_eq!(
            (quote.amount_in, quote.amount_out, quote.fee_paid),
            (10, 8, 1)
        );
        assert_eq!(
            (quote.reserve_in_after, quote.reserve_out_after),
            (1_010, 992)
        );
        assert_eq!(quote.net_in, 9);
        assert!(quote.k_after >= quote.k_before);
    }

    #[test]
    fn given_python_fixture_pool_when_exact_out_seven_at_thirty_bps_then_debit_is_nine_fee_one() {
        // Carried from test_given_maximum_ten_when_exact_output_seven_then_actual_debit_is_nine.
        let quote = quote_cpmm_swap_exact_out_v2(1_000, 1_000, 7, 30).expect("quote");
        assert_eq!(
            (quote.amount_in, quote.amount_out, quote.fee_paid),
            (9, 7, 1)
        );
        assert_eq!(quote.reserve_in_after, 1_009);
        assert_eq!(quote.overdelivery_gap_bps, 0);
    }

    #[test]
    fn given_zero_fee_then_whole_input_is_priced_and_no_fee_row_is_needed() {
        let quote = quote_cpmm_swap_exact_in_v2(10_000, 20_000, 10, 0).expect("quote");
        assert_eq!(
            (quote.fee_paid, quote.net_in, quote.amount_out),
            (0, 10, 19)
        );
    }

    #[test]
    fn given_full_fee_then_both_modes_reject_before_pricing() {
        assert_eq!(
            quote_cpmm_swap_exact_in_v2(1_000, 1_000, 10, BPS_DENOM_V2),
            Err(SpotQuoteErrorV2::ZeroNetInput)
        );
        assert_eq!(
            quote_cpmm_swap_exact_out_v2(1_000, 1_000, 7, BPS_DENOM_V2),
            Err(SpotQuoteErrorV2::FullFee)
        );
        assert_eq!(
            quote_cpmm_swap_exact_in_v2(1_000, 1_000, 10, BPS_DENOM_V2 + 1),
            Err(SpotQuoteErrorV2::FeeDomain)
        );
    }

    #[test]
    fn given_dust_then_zero_net_and_zero_output_reject_while_one_atom_output_accepts() {
        assert_eq!(
            quote_cpmm_swap_exact_in_v2(10_000, 20_000, 1, 30),
            Err(SpotQuoteErrorV2::ZeroNetInput)
        );
        assert_eq!(
            quote_cpmm_swap_exact_in_v2(20_000, 10_000, 1, 0),
            Err(SpotQuoteErrorV2::ZeroOutput)
        );
        let dust = quote_cpmm_swap_exact_in_v2(10_000, 20_000, 1, 0).expect("dust quote");
        assert_eq!(dust.amount_out, 1);
        assert_eq!(
            quote_cpmm_swap_exact_in_v2(1, 1, 0, 0),
            Err(SpotQuoteErrorV2::AmountDomain)
        );
        assert_eq!(
            quote_cpmm_swap_exact_out_v2(1, 1, 0, 0),
            Err(SpotQuoteErrorV2::AmountDomain)
        );
    }

    #[test]
    fn given_reserve_domain_maximum_then_exact_neighbor_accepts_and_next_atom_rejects() {
        let boundary = quote_cpmm_swap_exact_in_v2(MAX - 10, MAX, 10, 0).expect("boundary");
        assert_eq!(boundary.reserve_in_after, MAX);
        assert_eq!(boundary.amount_out, 10);
        assert_eq!(
            quote_cpmm_swap_exact_in_v2(MAX - 10, MAX, 11, 0),
            Err(SpotQuoteErrorV2::ReserveInDomainAfterSwap)
        );
        assert_eq!(
            quote_cpmm_swap_exact_in_v2(MAX + 1, MAX, 1, 0),
            Err(SpotQuoteErrorV2::ReserveDomain)
        );
        assert_eq!(
            quote_cpmm_swap_exact_in_v2(1, MAX, DEX_SWAP_AMOUNT_MAX_V2 + 1, 0),
            Err(SpotQuoteErrorV2::AmountDomain)
        );
        assert_eq!(
            quote_cpmm_swap_exact_in_v2(0, MAX, 1, 0),
            Err(SpotQuoteErrorV2::ReserveDomain)
        );
    }

    #[test]
    fn given_exact_out_that_drains_or_overdelivers_then_typed_rejection() {
        assert_eq!(
            quote_cpmm_swap_exact_out_v2(1_000, 1_000, 1_000, 30),
            Err(SpotQuoteErrorV2::DrainsReserveOut)
        );
        // 31/53 pool, fee 0, wanted 2: gross 2 yields 3 out, a 5000-bps gap.
        assert_eq!(
            quote_cpmm_swap_exact_out_v2(31, 53, 2, 0),
            Err(SpotQuoteErrorV2::OverdeliveryGap)
        );
        let exact = quote_cpmm_swap_exact_out_v2(31, 53, 1, 0).expect("exact fit");
        assert_eq!((exact.amount_in, exact.amount_out_quote), (1, 1));
    }

    #[test]
    fn extreme_domain_corners_never_reach_the_arithmetic_variant() {
        // Evaluates the bound argument in the module docs at every corner of
        // the admitted domain; any checked-overflow path would surface here.
        let corners = [1_u128, 2, MAX - 1, MAX];
        let fees = [0_u128, 1, 30, 9_999, BPS_DENOM_V2];
        for reserve_in in corners {
            for reserve_out in corners {
                for fee_bps in fees {
                    for amount in [1_u128, reserve_out.saturating_sub(1).max(1), MAX] {
                        let exact_in =
                            quote_cpmm_swap_exact_in_v2(reserve_in, reserve_out, amount, fee_bps);
                        assert_ne!(exact_in, Err(SpotQuoteErrorV2::Arithmetic));
                        let exact_out =
                            quote_cpmm_swap_exact_out_v2(reserve_in, reserve_out, amount, fee_bps);
                        assert_ne!(exact_out, Err(SpotQuoteErrorV2::Arithmetic));
                    }
                }
            }
        }
        // The single largest intermediate: reserve_out * net_in_actual for the
        // widest exact-out request at 9_999 bps stays below 2^108.
        let largest = quote_cpmm_swap_exact_out_v2(MAX, MAX, MAX - 1, 9_999);
        assert_ne!(largest, Err(SpotQuoteErrorV2::Arithmetic));
        let max_gross_input: u128 = 90_000_000_000_000_000_000_000;
        let widest_product = MAX.checked_mul(max_gross_input).expect("fits u128");
        let bound: u128 = 1 << 108;
        assert!(widest_product < bound);
    }

    #[test]
    fn ceil_division_matches_python_formula_without_forming_the_sum() {
        assert_eq!(ceil_div(0, 7), Ok(0));
        assert_eq!(ceil_div(7, 7), Ok(1));
        assert_eq!(ceil_div(8, 7), Ok(2));
        assert_eq!(ceil_div(u128::MAX, 1), Ok(u128::MAX));
        assert_eq!(ceil_div(u128::MAX, 2), Ok((u128::MAX / 2) + 1));
        assert_eq!(ceil_div(1, 0), Err(SpotQuoteErrorV2::Arithmetic));
    }
}
