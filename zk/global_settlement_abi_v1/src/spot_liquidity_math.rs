use serde::{Deserialize, Serialize};

use crate::spot_liquidity_policy::{G1SpotLpPolicyCandidateV1, G1_SPOT_LP_MAX_POOL_ATOMS_V1};

const BPS_DENOMINATOR_V1: u128 = 10_000;

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum SpotPoolStatusV1 {
    ACTIVE,
    CLOSED,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SpotPoolMathStateV1 {
    pub reserve0_atoms: u128,
    pub reserve1_atoms: u128,
    pub lp_supply_atoms: u128,
    pub status: SpotPoolStatusV1,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum SpotLpRejectV1 {
    INVALID_POLICY,
    ZERO_AMOUNT,
    LIMIT_EXCEEDED,
    ARITHMETIC_OVERFLOW,
    FEE_CONSUMES_INPUT,
    ZERO_OUTPUT,
    ZERO_LP_MINT,
    ZERO_WITHDRAWAL,
    POOL_NOT_ACTIVE,
    INCONSISTENT_POOL_STATE,
    LP_BURN_EXCEEDS_SUPPLY,
}

pub type SpotLpResultV1<T> = Result<T, SpotLpRejectV1>;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
pub struct SpotExactInQuoteV1 {
    pub gross_input_atoms: u128,
    pub fee_atoms: u128,
    pub net_input_atoms: u128,
    pub output_atoms: u128,
    pub post_reserve_in_atoms: u128,
    pub post_reserve_out_atoms: u128,
    pub k_before: u128,
    pub k_after: u128,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
pub struct SpotExactOutQuoteV1 {
    pub requested_output_atoms: u128,
    pub required_input_atoms: u128,
    pub fee_atoms: u128,
    pub net_input_atoms: u128,
    pub quoted_output_atoms: u128,
    pub pool_retained_output_atoms: u128,
    pub post_reserve_in_atoms: u128,
    pub post_reserve_out_atoms: u128,
    pub k_before: u128,
    pub k_after: u128,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
pub struct LpDepositQuoteV1 {
    pub lp_minted_atoms: u128,
    pub amount0_used_atoms: u128,
    pub amount1_used_atoms: u128,
    pub amount0_refund_atoms: u128,
    pub amount1_refund_atoms: u128,
    pub post_pool: SpotPoolMathStateV1,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
pub struct LpWithdrawalQuoteV1 {
    pub amount0_out_atoms: u128,
    pub amount1_out_atoms: u128,
    pub amount0_rounding_numerator: u128,
    pub amount1_rounding_numerator: u128,
    pub rounding_denominator: u128,
    pub terminal_closed: bool,
    pub post_pool: SpotPoolMathStateV1,
}

fn require_policy_v1(policy: &G1SpotLpPolicyCandidateV1) -> SpotLpResultV1<()> {
    policy
        .validate()
        .map_err(|_| SpotLpRejectV1::INVALID_POLICY)
}

fn require_positive_bounded_v1(value: u128) -> SpotLpResultV1<()> {
    if value == 0 {
        return Err(SpotLpRejectV1::ZERO_AMOUNT);
    }
    if value > G1_SPOT_LP_MAX_POOL_ATOMS_V1 {
        return Err(SpotLpRejectV1::LIMIT_EXCEEDED);
    }
    Ok(())
}

fn checked_product_v1(left: u128, right: u128) -> SpotLpResultV1<u128> {
    left.checked_mul(right)
        .ok_or(SpotLpRejectV1::ARITHMETIC_OVERFLOW)
}

fn checked_bounded_add_v1(left: u128, right: u128) -> SpotLpResultV1<u128> {
    left.checked_add(right)
        .filter(|value| *value <= G1_SPOT_LP_MAX_POOL_ATOMS_V1)
        .ok_or(SpotLpRejectV1::LIMIT_EXCEEDED)
}

fn ceil_div_v1(numerator: u128, denominator: u128) -> SpotLpResultV1<u128> {
    if denominator == 0 {
        return Err(SpotLpRejectV1::INCONSISTENT_POOL_STATE);
    }
    let quotient = numerator / denominator;
    quotient
        .checked_add(u128::from(numerator % denominator != 0))
        .ok_or(SpotLpRejectV1::ARITHMETIC_OVERFLOW)
}

fn mul_div_floor_v1(left: u128, right: u128, denominator: u128) -> SpotLpResultV1<u128> {
    if denominator == 0 {
        return Err(SpotLpRejectV1::INCONSISTENT_POOL_STATE);
    }
    Ok(checked_product_v1(left, right)? / denominator)
}

fn mul_div_ceil_v1(left: u128, right: u128, denominator: u128) -> SpotLpResultV1<u128> {
    ceil_div_v1(checked_product_v1(left, right)?, denominator)
}

fn isqrt_floor_v1(value: u128) -> u128 {
    if value < 2 {
        return value;
    }
    let mut lower = 1u128;
    let mut upper = 1u128 << 64;
    while lower + 1 < upper {
        let middle = lower + (upper - lower) / 2;
        if middle <= value / middle {
            lower = middle;
        } else {
            upper = middle;
        }
    }
    lower
}

fn require_active_pool_v1(pool: &SpotPoolMathStateV1) -> SpotLpResultV1<()> {
    if pool.status != SpotPoolStatusV1::ACTIVE {
        return Err(SpotLpRejectV1::POOL_NOT_ACTIVE);
    }
    if pool.reserve0_atoms == 0 || pool.reserve1_atoms == 0 || pool.lp_supply_atoms == 0 {
        return Err(SpotLpRejectV1::INCONSISTENT_POOL_STATE);
    }
    if pool.reserve0_atoms > G1_SPOT_LP_MAX_POOL_ATOMS_V1
        || pool.reserve1_atoms > G1_SPOT_LP_MAX_POOL_ATOMS_V1
        || pool.lp_supply_atoms > G1_SPOT_LP_MAX_POOL_ATOMS_V1
    {
        return Err(SpotLpRejectV1::LIMIT_EXCEEDED);
    }
    Ok(())
}

pub fn spot_exact_in_quote_v1(
    policy: &G1SpotLpPolicyCandidateV1,
    reserve_in_atoms: u128,
    reserve_out_atoms: u128,
    gross_input_atoms: u128,
) -> SpotLpResultV1<SpotExactInQuoteV1> {
    require_policy_v1(policy)?;
    require_positive_bounded_v1(reserve_in_atoms)?;
    require_positive_bounded_v1(reserve_out_atoms)?;
    require_positive_bounded_v1(gross_input_atoms)?;

    let post_reserve_in_atoms = checked_bounded_add_v1(reserve_in_atoms, gross_input_atoms)?;
    let fee_atoms = mul_div_ceil_v1(
        gross_input_atoms,
        u128::from(policy.swap_fee_bps),
        BPS_DENOMINATOR_V1,
    )?;
    if fee_atoms >= gross_input_atoms {
        return Err(SpotLpRejectV1::FEE_CONSUMES_INPUT);
    }
    let net_input_atoms = gross_input_atoms - fee_atoms;
    let denominator = reserve_in_atoms
        .checked_add(net_input_atoms)
        .ok_or(SpotLpRejectV1::ARITHMETIC_OVERFLOW)?;
    let output_atoms = mul_div_floor_v1(reserve_out_atoms, net_input_atoms, denominator)?;
    if output_atoms == 0 {
        return Err(SpotLpRejectV1::ZERO_OUTPUT);
    }
    let post_reserve_out_atoms = reserve_out_atoms - output_atoms;
    let k_before = checked_product_v1(reserve_in_atoms, reserve_out_atoms)?;
    let k_after = checked_product_v1(post_reserve_in_atoms, post_reserve_out_atoms)?;
    if k_after < k_before {
        return Err(SpotLpRejectV1::INCONSISTENT_POOL_STATE);
    }
    Ok(SpotExactInQuoteV1 {
        gross_input_atoms,
        fee_atoms,
        net_input_atoms,
        output_atoms,
        post_reserve_in_atoms,
        post_reserve_out_atoms,
        k_before,
        k_after,
    })
}

pub fn spot_exact_out_quote_v1(
    policy: &G1SpotLpPolicyCandidateV1,
    reserve_in_atoms: u128,
    reserve_out_atoms: u128,
    requested_output_atoms: u128,
) -> SpotLpResultV1<SpotExactOutQuoteV1> {
    require_policy_v1(policy)?;
    require_positive_bounded_v1(reserve_in_atoms)?;
    require_positive_bounded_v1(reserve_out_atoms)?;
    require_positive_bounded_v1(requested_output_atoms)?;
    if requested_output_atoms >= reserve_out_atoms {
        return Err(SpotLpRejectV1::LIMIT_EXCEEDED);
    }

    let net_required_atoms = mul_div_ceil_v1(
        reserve_in_atoms,
        requested_output_atoms,
        reserve_out_atoms - requested_output_atoms,
    )?;
    if net_required_atoms > G1_SPOT_LP_MAX_POOL_ATOMS_V1 {
        return Err(SpotLpRejectV1::LIMIT_EXCEEDED);
    }
    let fee_denominator = BPS_DENOMINATOR_V1 - u128::from(policy.swap_fee_bps);
    let required_input_atoms =
        mul_div_ceil_v1(net_required_atoms, BPS_DENOMINATOR_V1, fee_denominator)?;
    let exact_in = spot_exact_in_quote_v1(
        policy,
        reserve_in_atoms,
        reserve_out_atoms,
        required_input_atoms,
    )?;
    if exact_in.output_atoms < requested_output_atoms {
        return Err(SpotLpRejectV1::INCONSISTENT_POOL_STATE);
    }
    let post_reserve_out_atoms = reserve_out_atoms - requested_output_atoms;
    let k_before = exact_in.k_before;
    let k_after = checked_product_v1(exact_in.post_reserve_in_atoms, post_reserve_out_atoms)?;
    if k_after < k_before {
        return Err(SpotLpRejectV1::INCONSISTENT_POOL_STATE);
    }
    Ok(SpotExactOutQuoteV1 {
        requested_output_atoms,
        required_input_atoms,
        fee_atoms: exact_in.fee_atoms,
        net_input_atoms: exact_in.net_input_atoms,
        quoted_output_atoms: exact_in.output_atoms,
        pool_retained_output_atoms: exact_in.output_atoms - requested_output_atoms,
        post_reserve_in_atoms: exact_in.post_reserve_in_atoms,
        post_reserve_out_atoms,
        k_before,
        k_after,
    })
}

pub fn lp_create_quote_v1(
    policy: &G1SpotLpPolicyCandidateV1,
    amount0_atoms: u128,
    amount1_atoms: u128,
) -> SpotLpResultV1<LpDepositQuoteV1> {
    require_policy_v1(policy)?;
    require_positive_bounded_v1(amount0_atoms)?;
    require_positive_bounded_v1(amount1_atoms)?;
    let lp_minted_atoms = isqrt_floor_v1(checked_product_v1(amount0_atoms, amount1_atoms)?);
    if lp_minted_atoms == 0 {
        return Err(SpotLpRejectV1::ZERO_LP_MINT);
    }
    Ok(LpDepositQuoteV1 {
        lp_minted_atoms,
        amount0_used_atoms: amount0_atoms,
        amount1_used_atoms: amount1_atoms,
        amount0_refund_atoms: 0,
        amount1_refund_atoms: 0,
        post_pool: SpotPoolMathStateV1 {
            reserve0_atoms: amount0_atoms,
            reserve1_atoms: amount1_atoms,
            lp_supply_atoms: lp_minted_atoms,
            status: SpotPoolStatusV1::ACTIVE,
        },
    })
}

pub fn lp_add_quote_v1(
    policy: &G1SpotLpPolicyCandidateV1,
    pool: &SpotPoolMathStateV1,
    amount0_desired_atoms: u128,
    amount1_desired_atoms: u128,
) -> SpotLpResultV1<LpDepositQuoteV1> {
    require_policy_v1(policy)?;
    require_active_pool_v1(pool)?;
    require_positive_bounded_v1(amount0_desired_atoms)?;
    require_positive_bounded_v1(amount1_desired_atoms)?;

    let from_amount0 = mul_div_floor_v1(
        amount0_desired_atoms,
        pool.lp_supply_atoms,
        pool.reserve0_atoms,
    )?;
    let from_amount1 = mul_div_floor_v1(
        amount1_desired_atoms,
        pool.lp_supply_atoms,
        pool.reserve1_atoms,
    )?;
    let lp_minted_atoms = from_amount0.min(from_amount1);
    if lp_minted_atoms == 0 {
        return Err(SpotLpRejectV1::ZERO_LP_MINT);
    }
    let amount0_used_atoms =
        mul_div_ceil_v1(lp_minted_atoms, pool.reserve0_atoms, pool.lp_supply_atoms)?;
    let amount1_used_atoms =
        mul_div_ceil_v1(lp_minted_atoms, pool.reserve1_atoms, pool.lp_supply_atoms)?;
    if amount0_used_atoms > amount0_desired_atoms || amount1_used_atoms > amount1_desired_atoms {
        return Err(SpotLpRejectV1::INCONSISTENT_POOL_STATE);
    }
    let reserve0_atoms = checked_bounded_add_v1(pool.reserve0_atoms, amount0_used_atoms)?;
    let reserve1_atoms = checked_bounded_add_v1(pool.reserve1_atoms, amount1_used_atoms)?;
    let lp_supply_atoms = checked_bounded_add_v1(pool.lp_supply_atoms, lp_minted_atoms)?;
    Ok(LpDepositQuoteV1 {
        lp_minted_atoms,
        amount0_used_atoms,
        amount1_used_atoms,
        amount0_refund_atoms: amount0_desired_atoms - amount0_used_atoms,
        amount1_refund_atoms: amount1_desired_atoms - amount1_used_atoms,
        post_pool: SpotPoolMathStateV1 {
            reserve0_atoms,
            reserve1_atoms,
            lp_supply_atoms,
            status: SpotPoolStatusV1::ACTIVE,
        },
    })
}

pub fn lp_remove_quote_v1(
    policy: &G1SpotLpPolicyCandidateV1,
    pool: &SpotPoolMathStateV1,
    lp_burn_atoms: u128,
) -> SpotLpResultV1<LpWithdrawalQuoteV1> {
    require_policy_v1(policy)?;
    require_active_pool_v1(pool)?;
    require_positive_bounded_v1(lp_burn_atoms)?;
    if lp_burn_atoms > pool.lp_supply_atoms {
        return Err(SpotLpRejectV1::LP_BURN_EXCEEDS_SUPPLY);
    }
    if lp_burn_atoms == pool.lp_supply_atoms {
        return Ok(LpWithdrawalQuoteV1 {
            amount0_out_atoms: pool.reserve0_atoms,
            amount1_out_atoms: pool.reserve1_atoms,
            amount0_rounding_numerator: 0,
            amount1_rounding_numerator: 0,
            rounding_denominator: pool.lp_supply_atoms,
            terminal_closed: true,
            post_pool: SpotPoolMathStateV1 {
                reserve0_atoms: 0,
                reserve1_atoms: 0,
                lp_supply_atoms: 0,
                status: SpotPoolStatusV1::CLOSED,
            },
        });
    }

    let product0 = checked_product_v1(lp_burn_atoms, pool.reserve0_atoms)?;
    let product1 = checked_product_v1(lp_burn_atoms, pool.reserve1_atoms)?;
    let amount0_out_atoms = product0 / pool.lp_supply_atoms;
    let amount1_out_atoms = product1 / pool.lp_supply_atoms;
    if amount0_out_atoms == 0 && amount1_out_atoms == 0 {
        return Err(SpotLpRejectV1::ZERO_WITHDRAWAL);
    }
    Ok(LpWithdrawalQuoteV1 {
        amount0_out_atoms,
        amount1_out_atoms,
        amount0_rounding_numerator: product0 % pool.lp_supply_atoms,
        amount1_rounding_numerator: product1 % pool.lp_supply_atoms,
        rounding_denominator: pool.lp_supply_atoms,
        terminal_closed: false,
        post_pool: SpotPoolMathStateV1 {
            reserve0_atoms: pool.reserve0_atoms - amount0_out_atoms,
            reserve1_atoms: pool.reserve1_atoms - amount1_out_atoms,
            lp_supply_atoms: pool.lp_supply_atoms - lp_burn_atoms,
            status: SpotPoolStatusV1::ACTIVE,
        },
    })
}
