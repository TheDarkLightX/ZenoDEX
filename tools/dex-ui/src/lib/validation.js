/**
 * ZenoDEX - Client-side Validation
 * Mirrors Tau spec validations for UX feedback
 */

/**
 * Validate a swap before submission
 * @param {Object} swap - Swap parameters
 * @returns {{ok: boolean, error?: string}}
 */
export function validateSwap(swap) {
    const { amountIn, amountOut, reserveIn, reserveOut, priceImpact } = swap;

    // Amount bounds
    if (!amountIn || amountIn <= 0) {
        return { ok: false, error: 'Enter an amount' };
    }

    // Reserve check
    if (!reserveIn || reserveIn <= 0 || !reserveOut || reserveOut <= 0) {
        return { ok: false, error: 'Pool has no liquidity' };
    }

    // Liquidity check
    if (amountOut >= reserveOut) {
        return { ok: false, error: 'Insufficient liquidity' };
    }

    // Note: slippage tolerance is an execution-time constraint (min_out), not a pure function of spot-vs-exec
    // price impact (which here includes fees). We therefore avoid blocking swaps solely because
    // `priceImpact > slippageTolerance`; higher-level interlocks (slippage advisor + confirmations) handle this.

    // High impact warning (not an error)
    if (priceImpact > 0.01) {
        return { ok: true, warning: `High price impact: ${(priceImpact * 100).toFixed(2)}%` };
    }

    return { ok: true };
}

/**
 * Validate liquidity addition
 * @param {Object} params - Liquidity parameters
 * @returns {{ok: boolean, error?: string}}
 */
export function validateAddLiquidity(params) {
    const { amount0, amount1, balance0, balance1 } = params;

    if (!amount0 || amount0 <= 0 || !amount1 || amount1 <= 0) {
        return { ok: false, error: 'Enter amounts for both tokens' };
    }

    if (balance0 !== undefined && amount0 > balance0) {
        return { ok: false, error: 'Insufficient balance for token 0' };
    }

    if (balance1 !== undefined && amount1 > balance1) {
        return { ok: false, error: 'Insufficient balance for token 1' };
    }

    return { ok: true };
}

/**
 * Validate liquidity removal
 * @param {Object} params - Removal parameters
 * @returns {{ok: boolean, error?: string}}
 */
export function validateRemoveLiquidity(params) {
    const { lpAmount, lpBalance } = params;

    if (!lpAmount || lpAmount <= 0) {
        return { ok: false, error: 'Enter LP token amount' };
    }

    if (lpBalance !== undefined && lpAmount > lpBalance) {
        return { ok: false, error: 'Insufficient LP token balance' };
    }

    return { ok: true };
}

/**
 * Validate TDEX transfer
 * @param {Object} params - Transfer parameters
 * @returns {{ok: boolean, error?: string, burn?: number}}
 */
export function validateTdexTransfer(params) {
    const { amount, balance, currentSupply, minSupply } = params;

    if (!amount || amount <= 0) {
        return { ok: false, error: 'Enter an amount' };
    }

    if (balance !== undefined && amount > balance) {
        return { ok: false, error: 'Insufficient TDEX balance' };
    }

    // Calculate burn
    const burn = amount * 0.005;
    const netTransfer = amount - burn;

    // Check if burn would violate floor
    if (currentSupply !== undefined && minSupply !== undefined) {
        const newSupply = currentSupply - burn;
        if (newSupply < minSupply) {
            return { ok: false, error: 'Transfer would exceed burn floor' };
        }
    }

    return { ok: true, burn, netTransfer };
}

/**
 * Get slippage tolerance options
 * @returns {Array<{value: number, label: string}>}
 */
export function getSlippageOptions() {
    return [
        { value: 0.001, label: '0.1%' },
        { value: 0.005, label: '0.5%' },
        { value: 0.01, label: '1%' },
        { value: 0.03, label: '3%' },
    ];
}

/**
 * Get price impact severity
 * @param {number} impact - Price impact as decimal
 * @returns {'low' | 'medium' | 'high'}
 */
export function getPriceImpactSeverity(impact) {
    if (impact < 0.01) return 'low';
    if (impact < 0.05) return 'medium';
    return 'high';
}
