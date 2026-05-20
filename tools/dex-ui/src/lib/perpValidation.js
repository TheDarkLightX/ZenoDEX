/**
 * ZenoDEX - Perpetuals Validation
 *
 * Client-side port of guard logic from src/core/perp_v2/guards.py.
 * Used for pre-flight validation in the UI before submitting to the backend.
 */

import {
    absVal,
    initMarginReq,
    isOracleFresh,
    maintMarginReq,
    effectiveLeverage,
} from './perpMath.js';

// -- Epoch phase enum ---------------------------------------------------------

export const EpochPhase = Object.freeze({
    OPEN: 'Open',
    PRICE_PUBLISHED: 'PricePublished',
    SETTLED: 'Settled',
});

// -- Risk tiers for poka-yoke UI friction ------------------------------------

/**
 * Determine the risk tier for an order based on leverage and margin health.
 *
 * @param {number} leverage - Effective leverage after the trade
 * @param {number} marginRatioVal - Collateral / maint_margin_req ratio
 * @param {boolean} breakerActive - Whether circuit breaker is active
 * @returns {{ tier: string, label: string, color: string }}
 */
export function getRiskTier(leverage, marginRatioVal, breakerActive) {
    if (breakerActive) {
        return { tier: 'breaker', label: 'Circuit Breaker Active', color: 'var(--perp-extreme)' };
    }
    if (leverage > 10 || marginRatioVal < 1.2) {
        return { tier: 'extreme', label: 'Extreme Risk', color: 'var(--perp-extreme)' };
    }
    if (leverage > 5 || marginRatioVal < 1.5) {
        return { tier: 'high', label: 'High Risk', color: 'var(--perp-short)' };
    }
    if (leverage > 3 || marginRatioVal < 2.0) {
        return { tier: 'medium', label: 'Medium Risk', color: 'var(--perp-warning)' };
    }
    return { tier: 'low', label: 'Low Risk', color: 'var(--perp-long)' };
}

// -- Guard validations --------------------------------------------------------

/**
 * Validate a deposit collateral action.
 * @param {Object} state - Perp market state
 * @param {bigint} amount - Amount to deposit
 * @returns {{ ok: boolean, error?: string }}
 */
export function validateDeposit(state, amount) {
    if (state.epochPhase !== EpochPhase.OPEN) {
        return { ok: false, error: 'Deposits disabled during settlement' };
    }
    if (amount <= 0n) {
        return { ok: false, error: 'Enter a deposit amount' };
    }
    return { ok: true };
}

/**
 * Validate a withdraw collateral action.
 * @param {Object} state - Perp market state
 * @param {bigint} amount - Amount to withdraw
 * @returns {{ ok: boolean, error?: string }}
 */
export function validateWithdraw(state, amount) {
    if (state.epochPhase !== EpochPhase.OPEN) {
        return { ok: false, error: 'Withdrawals disabled during settlement' };
    }
    if (amount <= 0n) {
        return { ok: false, error: 'Enter a withdrawal amount' };
    }
    if (amount > state.collateralQuote) {
        return { ok: false, error: 'Insufficient collateral' };
    }
    if (state.positionBase !== 0n) {
        if (!isOracleFresh(state.nowEpoch, state.oracleLastUpdateEpoch, state.maxOracleStalenessEpochs, state.oracleSeen)) {
            return { ok: false, error: 'Oracle is stale' };
        }
        const remaining = state.collateralQuote - amount;
        const mreq = maintMarginReq(state.positionBase, state.indexPriceE8, state.maintenanceMarginBps, state.depegBufferBps);
        if (remaining < mreq) {
            return { ok: false, error: 'Would violate maintenance margin' };
        }
    }
    return { ok: true };
}

/**
 * Validate a set_position (open/close/modify) action.
 * @param {Object} state - Perp market state
 * @param {bigint} newPositionBase - Desired new position
 * @returns {{ ok: boolean, error?: string, warning?: string, riskTier?: Object }}
 */
export function validateSetPosition(state, newPositionBase) {
    if (state.epochPhase !== EpochPhase.OPEN) {
        return { ok: false, error: 'Trading disabled during settlement' };
    }
    if (!state.oracleSeen) {
        return { ok: false, error: 'No oracle data available' };
    }
    if (absVal(newPositionBase) > state.maxPositionAbs) {
        return { ok: false, error: 'Exceeds maximum position size' };
    }

    // Breaker mode: reduce-only
    if (state.breakerActive) {
        if (state.positionBase === 0n && newPositionBase !== 0n) {
            return { ok: false, error: 'No new positions during circuit breaker' };
        }
        if (absVal(newPositionBase) > absVal(state.positionBase)) {
            return { ok: false, error: 'Reduce-only during circuit breaker' };
        }
        if (newPositionBase !== 0n) {
            if ((state.positionBase >= 0n) !== (newPositionBase >= 0n)) {
                return { ok: false, error: 'No direction change during circuit breaker' };
            }
        }
        return { ok: true, riskTier: getRiskTier(0, Infinity, true) };
    }

    // Normal mode: oracle freshness + initial margin
    if (!isOracleFresh(state.nowEpoch, state.oracleLastUpdateEpoch, state.maxOracleStalenessEpochs, state.oracleSeen)) {
        return { ok: false, error: 'Oracle is stale' };
    }
    if (newPositionBase === 0n) {
        return { ok: true, riskTier: getRiskTier(0, Infinity, false) };
    }
    const imReq = initMarginReq(newPositionBase, state.indexPriceE8, state.initialMarginBps);
    if (state.collateralQuote < imReq) {
        return { ok: false, error: 'Insufficient margin' };
    }

    // Compute risk tier
    const leverage = effectiveLeverage(newPositionBase, state.indexPriceE8, state.collateralQuote);
    const mreq = maintMarginReq(newPositionBase, state.indexPriceE8, state.maintenanceMarginBps, state.depegBufferBps);
    const mRatio = mreq > 0n ? Number(state.collateralQuote) / Number(mreq) : Infinity;
    const riskTier = getRiskTier(leverage, mRatio, false);

    const result = { ok: true, riskTier };
    if (riskTier.tier === 'high' || riskTier.tier === 'extreme') {
        result.warning = `${riskTier.label}: ${leverage.toFixed(1)}x leverage`;
    }
    return result;
}

/**
 * Validate an insurance deposit action.
 * @param {bigint} amount
 * @returns {{ ok: boolean, error?: string }}
 */
export function validateInsuranceDeposit(amount) {
    if (amount <= 0n) {
        return { ok: false, error: 'Enter a deposit amount' };
    }
    return { ok: true };
}
