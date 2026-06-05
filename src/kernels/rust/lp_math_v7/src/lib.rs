//! Rust port of `src/kernels/python/lp_math_v7.py`.
//!
//! The Python authority uses arbitrary-precision intermediates while enforcing
//! `u128` consensus inputs and outputs. This Rust leaf mirrors that boundary
//! and rejects checked-arithmetic overflow instead of wrapping.
#![forbid(unsafe_code)]

pub const MIN_LP_LOCK: u128 = 1000;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LpError {
    NonPositiveAmount,
    NonPositiveMinLpLock,
    InsufficientInitialLiquidity,
    InvalidSqrtWitnessTooLarge,
    InvalidSqrtWitnessTooSmall,
    InconsistentInitialState,
    EmptyPoolWithSupply,
    ZeroLiquidity,
    BelowMinLiquidity,
    BurnAmountExceedsSupply,
    Overflow,
}

impl LpError {
    pub const fn code(self) -> &'static str {
        match self {
            LpError::NonPositiveAmount => "non_positive_amount",
            LpError::NonPositiveMinLpLock => "non_positive_min_lp_lock",
            LpError::InsufficientInitialLiquidity => "insufficient_initial_liquidity",
            LpError::InvalidSqrtWitnessTooLarge => "invalid_sqrt_witness_too_large",
            LpError::InvalidSqrtWitnessTooSmall => "invalid_sqrt_witness_too_small",
            LpError::InconsistentInitialState => "inconsistent_initial_state",
            LpError::EmptyPoolWithSupply => "empty_pool_with_supply",
            LpError::ZeroLiquidity => "zero_liquidity",
            LpError::BelowMinLiquidity => "below_min_liquidity",
            LpError::BurnAmountExceedsSupply => "burn_amount_exceeds_supply",
            LpError::Overflow => "overflow",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OptimalLiquidityResult {
    pub amount0_used: u128,
    pub amount1_used: u128,
    pub amount0_refund: u128,
    pub amount1_refund: u128,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MintLiquidityResult {
    pub liquidity_minted: u128,
    pub amount0_used: u128,
    pub amount1_used: u128,
    pub amount0_refund: u128,
    pub amount1_refund: u128,
    pub new_reserve0: u128,
    pub new_reserve1: u128,
    pub new_total_supply: u128,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BurnLiquidityResult {
    pub amount0_out: u128,
    pub amount1_out: u128,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct U256 {
    limbs: [u64; 4],
}

impl U256 {
    const ZERO: Self = Self { limbs: [0; 4] };

    fn from_u128(value: u128) -> Self {
        Self {
            limbs: [value as u64, (value >> 64) as u64, 0, 0],
        }
    }

    fn mul_u128(a: u128, b: u128) -> Self {
        let a_limbs = [a as u64, (a >> 64) as u64];
        let b_limbs = [b as u64, (b >> 64) as u64];
        let mut out = [0u64; 4];

        for (i, &a_limb) in a_limbs.iter().enumerate() {
            let mut carry = 0u128;
            for (j, &b_limb) in b_limbs.iter().enumerate() {
                let k = i + j;
                let sum = out[k] as u128 + (a_limb as u128 * b_limb as u128) + carry;
                out[k] = sum as u64;
                carry = sum >> 64;
            }

            let mut k = i + 2;
            while carry != 0 && k < out.len() {
                let sum = out[k] as u128 + carry;
                out[k] = sum as u64;
                carry = sum >> 64;
                k += 1;
            }
            debug_assert_eq!(carry, 0);
        }

        Self { limbs: out }
    }

    fn square_next_gt_product(value: u128, product: Self) -> bool {
        if value == u128::MAX {
            return true;
        }
        Self::mul_u128(value + 1, value + 1) > product
    }

    fn bit(self, bit: usize) -> bool {
        ((self.limbs[bit / 64] >> (bit % 64)) & 1) == 1
    }

    fn set_bit(&mut self, bit: usize) {
        self.limbs[bit / 64] |= 1u64 << (bit % 64);
    }

    fn shl1(self) -> Self {
        let mut out = [0u64; 4];
        let mut carry = 0u64;
        for (idx, limb) in self.limbs.iter().enumerate() {
            out[idx] = (*limb << 1) | carry;
            carry = *limb >> 63;
        }
        Self { limbs: out }
    }

    fn sub(self, rhs: Self) -> Self {
        debug_assert!(self >= rhs);
        let mut out = [0u64; 4];
        let mut borrow = 0u128;
        for (idx, out_limb) in out.iter_mut().enumerate() {
            let lhs = self.limbs[idx] as u128;
            let rhs_limb = rhs.limbs[idx] as u128 + borrow;
            if lhs >= rhs_limb {
                *out_limb = (lhs - rhs_limb) as u64;
                borrow = 0;
            } else {
                *out_limb = ((1u128 << 64) + lhs - rhs_limb) as u64;
                borrow = 1;
            }
        }
        debug_assert_eq!(borrow, 0);
        Self { limbs: out }
    }

    fn div_u128(self, divisor: u128) -> (Self, u128) {
        debug_assert_ne!(divisor, 0);
        let divisor = Self::from_u128(divisor);
        let mut quotient = Self::ZERO;
        let mut remainder = Self::ZERO;

        for bit in (0..256).rev() {
            remainder = remainder.shl1();
            if self.bit(bit) {
                remainder.limbs[0] |= 1;
            }
            if remainder >= divisor {
                remainder = remainder.sub(divisor);
                quotient.set_bit(bit);
            }
        }

        debug_assert_eq!(remainder.limbs[2], 0);
        debug_assert_eq!(remainder.limbs[3], 0);
        let rem = remainder.limbs[0] as u128 | ((remainder.limbs[1] as u128) << 64);
        (quotient, rem)
    }

    fn as_u128(self) -> Option<u128> {
        if self.limbs[2] != 0 || self.limbs[3] != 0 {
            return None;
        }
        Some(self.limbs[0] as u128 | ((self.limbs[1] as u128) << 64))
    }
}

impl Ord for U256 {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        for idx in (0..4).rev() {
            match self.limbs[idx].cmp(&other.limbs[idx]) {
                std::cmp::Ordering::Equal => {}
                non_equal => return non_equal,
            }
        }
        std::cmp::Ordering::Equal
    }
}

impl PartialOrd for U256 {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

fn checked_add(a: u128, b: u128) -> Result<u128, LpError> {
    a.checked_add(b).ok_or(LpError::Overflow)
}

fn checked_sub(a: u128, b: u128) -> Result<u128, LpError> {
    a.checked_sub(b).ok_or(LpError::Overflow)
}

fn div_u256_by_u128_to_u128(numerator: U256, divisor: u128) -> Result<u128, LpError> {
    if divisor == 0 {
        return Err(LpError::Overflow);
    }
    let (quotient, _) = numerator.div_u128(divisor);
    quotient.as_u128().ok_or(LpError::Overflow)
}

pub fn isqrt_floor(n: u128) -> u128 {
    isqrt_floor_u256(U256::from_u128(n))
}

fn isqrt_floor_u256(n: U256) -> u128 {
    let mut lo = 0u128;
    let mut hi = u128::MAX;
    while lo < hi {
        let mid = lo + ((hi - lo) / 2) + 1;
        if U256::mul_u128(mid, mid) <= n {
            lo = mid;
        } else {
            hi = mid - 1;
        }
    }
    lo
}

pub fn optimal_liquidity(
    reserve0: u128,
    reserve1: u128,
    amount0_desired: u128,
    amount1_desired: u128,
) -> Result<OptimalLiquidityResult, LpError> {
    if amount0_desired == 0 || amount1_desired == 0 {
        return Err(LpError::NonPositiveAmount);
    }

    if reserve0 == 0 || reserve1 == 0 {
        return Ok(OptimalLiquidityResult {
            amount0_used: amount0_desired,
            amount1_used: amount1_desired,
            amount0_refund: 0,
            amount1_refund: 0,
        });
    }

    let lhs = U256::mul_u128(amount0_desired, reserve1);
    let rhs = U256::mul_u128(amount1_desired, reserve0);
    let (amount0_used, amount1_used) = if lhs <= rhs {
        let num = U256::mul_u128(amount0_desired, reserve1);
        (amount0_desired, div_u256_by_u128_to_u128(num, reserve0)?)
    } else {
        let num = U256::mul_u128(amount1_desired, reserve0);
        (div_u256_by_u128_to_u128(num, reserve1)?, amount1_desired)
    };

    Ok(OptimalLiquidityResult {
        amount0_used,
        amount1_used,
        amount0_refund: checked_sub(amount0_desired, amount0_used)?,
        amount1_refund: checked_sub(amount1_desired, amount1_used)?,
    })
}

pub fn mint_liquidity_initial(
    amount0: u128,
    amount1: u128,
    min_lp_lock: u128,
) -> Result<(u128, u128), LpError> {
    if amount0 == 0 || amount1 == 0 {
        return Err(LpError::NonPositiveAmount);
    }
    if min_lp_lock == 0 {
        return Err(LpError::NonPositiveMinLpLock);
    }

    let product = U256::mul_u128(amount0, amount1);
    let sqrt_product = isqrt_floor_u256(product);
    mint_from_sqrt_product(sqrt_product, min_lp_lock)
}

pub fn mint_liquidity_initial_witness(
    amount0: u128,
    amount1: u128,
    sqrt_product: u128,
    min_lp_lock: u128,
) -> Result<(u128, u128), LpError> {
    if amount0 == 0 || amount1 == 0 || sqrt_product == 0 {
        return Err(LpError::NonPositiveAmount);
    }
    if min_lp_lock == 0 {
        return Err(LpError::NonPositiveMinLpLock);
    }

    let product = U256::mul_u128(amount0, amount1);
    let sp_squared = U256::mul_u128(sqrt_product, sqrt_product);
    if sp_squared > product {
        return Err(LpError::InvalidSqrtWitnessTooLarge);
    }

    if !U256::square_next_gt_product(sqrt_product, product) {
        return Err(LpError::InvalidSqrtWitnessTooSmall);
    }

    mint_from_sqrt_product(sqrt_product, min_lp_lock)
}

fn mint_from_sqrt_product(sqrt_product: u128, min_lp_lock: u128) -> Result<(u128, u128), LpError> {
    if sqrt_product <= min_lp_lock {
        return Err(LpError::InsufficientInitialLiquidity);
    }
    let minted = checked_sub(sqrt_product, min_lp_lock)?;
    let total_supply = checked_add(minted, min_lp_lock)?;
    Ok((minted, total_supply))
}

pub fn mint_liquidity(
    reserve0: u128,
    reserve1: u128,
    total_supply: u128,
    amount0_desired: u128,
    amount1_desired: u128,
    min_liquidity: u128,
) -> Result<MintLiquidityResult, LpError> {
    if amount0_desired == 0 || amount1_desired == 0 {
        return Err(LpError::NonPositiveAmount);
    }

    if total_supply == 0 {
        if reserve0 != 0 || reserve1 != 0 {
            return Err(LpError::InconsistentInitialState);
        }
        let (minted, new_total_supply) =
            mint_liquidity_initial(amount0_desired, amount1_desired, MIN_LP_LOCK)?;
        return Ok(MintLiquidityResult {
            liquidity_minted: minted,
            amount0_used: amount0_desired,
            amount1_used: amount1_desired,
            amount0_refund: 0,
            amount1_refund: 0,
            new_reserve0: amount0_desired,
            new_reserve1: amount1_desired,
            new_total_supply,
        });
    }

    if reserve0 == 0 || reserve1 == 0 {
        return Err(LpError::EmptyPoolWithSupply);
    }

    let opt = optimal_liquidity(reserve0, reserve1, amount0_desired, amount1_desired)?;
    let liquidity0 =
        div_u256_by_u128_to_u128(U256::mul_u128(opt.amount0_used, total_supply), reserve0)?;
    let liquidity1 =
        div_u256_by_u128_to_u128(U256::mul_u128(opt.amount1_used, total_supply), reserve1)?;
    let minted = liquidity0.min(liquidity1);
    if minted == 0 {
        return Err(LpError::ZeroLiquidity);
    }
    if minted < min_liquidity {
        return Err(LpError::BelowMinLiquidity);
    }

    Ok(MintLiquidityResult {
        liquidity_minted: minted,
        amount0_used: opt.amount0_used,
        amount1_used: opt.amount1_used,
        amount0_refund: opt.amount0_refund,
        amount1_refund: opt.amount1_refund,
        new_reserve0: checked_add(reserve0, opt.amount0_used)?,
        new_reserve1: checked_add(reserve1, opt.amount1_used)?,
        new_total_supply: checked_add(total_supply, minted)?,
    })
}

pub fn burn_liquidity(
    lp_amount: u128,
    reserve0: u128,
    reserve1: u128,
    total_supply: u128,
) -> Result<BurnLiquidityResult, LpError> {
    if lp_amount == 0 || total_supply == 0 {
        return Err(LpError::NonPositiveAmount);
    }
    if lp_amount > total_supply {
        return Err(LpError::BurnAmountExceedsSupply);
    }

    Ok(BurnLiquidityResult {
        amount0_out: div_u256_by_u128_to_u128(U256::mul_u128(lp_amount, reserve0), total_supply)?,
        amount1_out: div_u256_by_u128_to_u128(U256::mul_u128(lp_amount, reserve1), total_supply)?,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn optimal_liquidity_matches_left_right_and_empty_branches() {
        assert_eq!(
            optimal_liquidity(0, 20, 3, 4).unwrap(),
            OptimalLiquidityResult {
                amount0_used: 3,
                amount1_used: 4,
                amount0_refund: 0,
                amount1_refund: 0,
            }
        );
        assert_eq!(
            optimal_liquidity(1000, 2000, 400, 900).unwrap(),
            OptimalLiquidityResult {
                amount0_used: 400,
                amount1_used: 800,
                amount0_refund: 0,
                amount1_refund: 100,
            }
        );
        assert_eq!(
            optimal_liquidity(1000, 2000, 800, 300).unwrap(),
            OptimalLiquidityResult {
                amount0_used: 150,
                amount1_used: 300,
                amount0_refund: 650,
                amount1_refund: 0,
            }
        );
    }

    #[test]
    fn initial_mint_and_witness_contracts_match_floor_sqrt() {
        assert_eq!(isqrt_floor(10_000_000), 3162);
        assert_eq!(
            mint_liquidity_initial(10_000, 10_000, MIN_LP_LOCK).unwrap(),
            (9000, 10_000)
        );
        assert_eq!(
            mint_liquidity_initial_witness(12_345, 67_890, 28_949, MIN_LP_LOCK).unwrap(),
            (27_949, 28_949)
        );
        assert_eq!(
            mint_liquidity_initial_witness(12_345, 67_890, 28_950, MIN_LP_LOCK),
            Err(LpError::InvalidSqrtWitnessTooLarge)
        );
        assert_eq!(
            mint_liquidity_initial_witness(12_345, 67_890, 28_948, MIN_LP_LOCK),
            Err(LpError::InvalidSqrtWitnessTooSmall)
        );
    }

    #[test]
    fn mint_liquidity_matches_ratio_and_min_liquidity_guards() {
        assert_eq!(
            mint_liquidity(1000, 2000, 10_000, 400, 900, 0).unwrap(),
            MintLiquidityResult {
                liquidity_minted: 4000,
                amount0_used: 400,
                amount1_used: 800,
                amount0_refund: 0,
                amount1_refund: 100,
                new_reserve0: 1400,
                new_reserve1: 2800,
                new_total_supply: 14_000,
            }
        );
        assert_eq!(
            mint_liquidity(1000, 2000, 10_000, 400, 900, 4001),
            Err(LpError::BelowMinLiquidity)
        );
    }

    #[test]
    fn burn_liquidity_uses_floor_rounding() {
        assert_eq!(
            burn_liquidity(333, 1000, 2000, 1000).unwrap(),
            BurnLiquidityResult {
                amount0_out: 333,
                amount1_out: 666,
            }
        );
        assert_eq!(
            burn_liquidity(1001, 1000, 2000, 1000),
            Err(LpError::BurnAmountExceedsSupply)
        );
    }

    #[test]
    fn u128_boundary_uses_wide_intermediates_and_overflows_fail_closed() {
        let x = 1u128 << 64;
        assert_eq!(
            optimal_liquidity(x, x, x, x),
            Ok(OptimalLiquidityResult {
                amount0_used: x,
                amount1_used: x,
                amount0_refund: 0,
                amount1_refund: 0,
            })
        );
        assert_eq!(
            mint_liquidity_initial(x, x, MIN_LP_LOCK),
            Ok((x - MIN_LP_LOCK, x))
        );
        assert_eq!(
            mint_liquidity_initial(u128::MAX, u128::MAX, MIN_LP_LOCK),
            Ok((u128::MAX - MIN_LP_LOCK, u128::MAX))
        );
        assert_eq!(
            mint_liquidity_initial_witness(u128::MAX, u128::MAX, u128::MAX, MIN_LP_LOCK),
            Ok((u128::MAX - MIN_LP_LOCK, u128::MAX))
        );
        assert_eq!(
            burn_liquidity(x, x, x, x),
            Ok(BurnLiquidityResult {
                amount0_out: x,
                amount1_out: x,
            })
        );
        assert_eq!(
            mint_liquidity(1, 1, u128::MAX, 2, 2, 0),
            Err(LpError::Overflow)
        );
    }

    #[test]
    fn u256_helpers_match_known_products_and_divisions() {
        let x = 1u128 << 64;
        assert_eq!(
            U256::mul_u128(u128::MAX, u128::MAX),
            U256 {
                limbs: [1, 0, u64::MAX - 1, u64::MAX],
            }
        );

        let (quotient, remainder) = U256::mul_u128(x, x).div_u128(x);
        assert_eq!(quotient.as_u128(), Some(x));
        assert_eq!(remainder, 0);
    }
}

#[cfg(kani)]
mod contracts {
    use super::*;

    fn small_u128() -> u128 {
        let v: u8 = kani::any();
        v as u128
    }

    #[kani::proof]
    fn initial_witness_accepts_only_floor_sqrt() {
        let amount0 = small_u128();
        let amount1 = small_u128();
        let sqrt_product = small_u128();
        let min_lp_lock = 1;
        if let Ok((minted, total_supply)) =
            mint_liquidity_initial_witness(amount0, amount1, sqrt_product, min_lp_lock)
        {
            let product = amount0 * amount1;
            assert!(sqrt_product * sqrt_product <= product);
            assert!(product < (sqrt_product + 1) * (sqrt_product + 1));
            assert_eq!(minted + min_lp_lock, total_supply);
            assert_eq!(total_supply, sqrt_product);
        }
    }

    #[kani::proof]
    fn concrete_empty_optimal_liquidity_is_non_vacuous() {
        assert_eq!(
            optimal_liquidity(0, 20, 3, 4),
            Ok(OptimalLiquidityResult {
                amount0_used: 3,
                amount1_used: 4,
                amount0_refund: 0,
                amount1_refund: 0,
            })
        );
    }

    #[kani::proof]
    fn concrete_initial_witness_high_width_boundary_is_non_vacuous() {
        let x = 1u128 << 64;
        assert_eq!(
            mint_liquidity_initial_witness(x, x, x, MIN_LP_LOCK),
            Ok((x - MIN_LP_LOCK, x))
        );
    }

    #[kani::proof]
    fn concrete_u256_product_high_width_is_non_vacuous() {
        let x = 1u128 << 64;
        assert_eq!(
            U256::mul_u128(x, x),
            U256 {
                limbs: [0, 0, 1, 0]
            }
        );
        assert!(U256::square_next_gt_product(
            u128::MAX,
            U256::mul_u128(u128::MAX, u128::MAX)
        ));
    }

    #[kani::proof]
    fn checked_arithmetic_helpers_fail_closed() {
        assert_eq!(checked_add(u128::MAX, 1), Err(LpError::Overflow));
        assert_eq!(checked_sub(0, 1), Err(LpError::Overflow));
    }
}
