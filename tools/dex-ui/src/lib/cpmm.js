/**
 * ZenoDEX - CPMM (Constant Product Market Maker) Library
 * Client-side calculations for swap previews
 */

/** Default fee rate (0.3%) */
export const DEFAULT_FEE_RATE = 0.003;

/** TDEX burn rate (0.5% on transfers) */
export const TDEX_BURN_RATE = 0.005;

/** Buyback contribution rate (0.3% of swap value) */
export const BUYBACK_RATE = 0.003;

/**
 * Calculate the output amount for a swap
 * @param {number} reserveIn - Reserve of input token
 * @param {number} reserveOut - Reserve of output token
 * @param {number} amountIn - Amount of input token
 * @param {number} feeRate - Fee rate (default 0.3%)
 * @returns {number} Output amount
 */
export function calcSwapOutput(reserveIn, reserveOut, amountIn, feeRate = DEFAULT_FEE_RATE) {
    if (reserveIn <= 0 || reserveOut <= 0 || amountIn <= 0) {
        return 0;
    }
    const amountInWithFee = amountIn * (1 - feeRate);
    return (reserveOut * amountInWithFee) / (reserveIn + amountInWithFee);
}

/**
 * Calculate the input amount required for a desired output
 * @param {number} reserveIn - Reserve of input token
 * @param {number} reserveOut - Reserve of output token
 * @param {number} amountOut - Desired output amount
 * @param {number} feeRate - Fee rate (default 0.3%)
 * @returns {number} Required input amount
 */
export function calcSwapInput(reserveIn, reserveOut, amountOut, feeRate = DEFAULT_FEE_RATE) {
    if (reserveIn <= 0 || reserveOut <= 0 || amountOut <= 0 || amountOut >= reserveOut) {
        return Infinity;
    }
    const numerator = reserveIn * amountOut;
    const denominator = (reserveOut - amountOut) * (1 - feeRate);
    return numerator / denominator;
}

/**
 * Calculate price impact of a swap
 * @param {number} reserveIn - Reserve of input token
 * @param {number} reserveOut - Reserve of output token
 * @param {number} amountIn - Amount of input token
 * @returns {number} Price impact as a decimal (0.01 = 1%)
 */
export function calcPriceImpact(reserveIn, reserveOut, amountIn) {
    if (reserveIn <= 0 || reserveOut <= 0 || amountIn <= 0) {
        return 0;
    }
    const spotPrice = reserveOut / reserveIn;
    const output = calcSwapOutput(reserveIn, reserveOut, amountIn);
    const execPrice = output / amountIn;
    return Math.abs((spotPrice - execPrice) / spotPrice);
}

/**
 * Calculate the spot price (without slippage)
 * @param {number} reserveIn - Reserve of input token
 * @param {number} reserveOut - Reserve of output token
 * @returns {number} Spot price (output per input)
 */
export function getSpotPrice(reserveIn, reserveOut) {
    if (reserveIn <= 0) return 0;
    return reserveOut / reserveIn;
}

/**
 * Calculate LP tokens to mint when adding liquidity
 * @param {number} amount0 - Amount of token 0 to add
 * @param {number} amount1 - Amount of token 1 to add
 * @param {number} reserve0 - Current reserve of token 0
 * @param {number} reserve1 - Current reserve of token 1
 * @param {number} totalLpSupply - Current total LP supply
 * @returns {number} LP tokens to mint
 */
export function calcLpTokensMint(amount0, amount1, reserve0, reserve1, totalLpSupply) {
    if (totalLpSupply === 0) {
        // Initial liquidity - use geometric mean
        return Math.sqrt(amount0 * amount1);
    }
    // Proportional minting
    const share0 = (amount0 / reserve0) * totalLpSupply;
    const share1 = (amount1 / reserve1) * totalLpSupply;
    return Math.min(share0, share1);
}

/**
 * Calculate tokens received when removing liquidity
 * @param {number} lpAmount - LP tokens to burn
 * @param {number} reserve0 - Current reserve of token 0
 * @param {number} reserve1 - Current reserve of token 1
 * @param {number} totalLpSupply - Current total LP supply
 * @returns {{amount0: number, amount1: number}} Tokens received
 */
export function calcLpTokensBurn(lpAmount, reserve0, reserve1, totalLpSupply) {
    if (totalLpSupply <= 0) {
        return { amount0: 0, amount1: 0 };
    }
    const share = lpAmount / totalLpSupply;
    return {
        amount0: reserve0 * share,
        amount1: reserve1 * share,
    };
}

/**
 * Calculate TDEX burn amount on transfer
 * @param {number} amount - Amount being transferred
 * @returns {{burn: number, netTransfer: number}}
 */
export function calcTdexBurn(amount) {
    const burn = amount * TDEX_BURN_RATE;
    return {
        burn,
        netTransfer: amount - burn,
    };
}

/**
 * Calculate pool share percentage
 * @param {number} lpAmount - User's LP tokens
 * @param {number} totalLpSupply - Total LP supply
 * @returns {number} Share as a decimal (0.01 = 1%)
 */
export function calcPoolShare(lpAmount, totalLpSupply) {
    if (totalLpSupply <= 0) return 0;
    return lpAmount / totalLpSupply;
}

/**
 * Format a number with appropriate precision
 * @param {number} value - Number to format
 * @param {number} decimals - Max decimal places
 * @returns {string} Formatted string
 */
export function formatNumber(value, decimals = 6) {
    if (value === 0) return '0';
    if (Math.abs(value) < 0.000001) return '<0.000001';
    if (Math.abs(value) >= 1000000) {
        return (value / 1000000).toFixed(2) + 'M';
    }
    if (Math.abs(value) >= 1000) {
        return (value / 1000).toFixed(2) + 'K';
    }
    return value.toLocaleString(undefined, { maximumFractionDigits: decimals });
}

/**
 * Format a percentage
 * @param {number} value - Decimal value (0.01 = 1%)
 * @param {number} decimals - Decimal places
 * @returns {string} Formatted percentage
 */
export function formatPercent(value, decimals = 2) {
    return (value * 100).toFixed(decimals) + '%';
}
