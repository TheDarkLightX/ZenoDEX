/**
 * ZenoDEX - Perpetuals Math Library
 *
 * Client-side port of src/core/perp_v2/math.py.
 * All arithmetic uses BigInt for overflow safety and determinism.
 * Functions accept and return BigInt unless otherwise noted.
 *
 * Conventions (same as Python backend):
 * - *_e8 prices are quote-per-base scaled by 1e8
 * - *_bps rates are basis points (1/10_000)
 * - position_base is signed (long > 0, short < 0)
 * - *_quote values are integer quote units
 */

// Domain constants (from YAML type bounds)
export const PRICE_SCALE = 100_000_000n;
export const BPS_SCALE = 10_000n;
export const MAX_EPOCH = 1_000_000n;
export const MAX_COLLATERAL = 1_000_000_000_000_000n;
export const MAX_FUNDING_CUMULATIVE = 1_000_000_000_000_000n;

// -- Basic helpers ------------------------------------------------------------

/** Absolute value of a BigInt. */
export function absVal(x) {
    return x >= 0n ? x : -x;
}

/** Convert a Number to BigInt, rounding toward zero. */
export function toBigInt(v) {
    if (typeof v === 'bigint') return v;
    if (typeof v === 'string') {
        const s = v.trim();
        // Prefer exact parse for integer strings to avoid JS number precision loss.
        if (/^-?[0-9]+$/.test(s)) return BigInt(s);
    }
    return BigInt(Math.trunc(Number(v)));
}

// -- Oracle helpers -----------------------------------------------------------

/**
 * True when the oracle has been seen and is not stale.
 * @param {bigint} nowEpoch
 * @param {bigint} oracleLastUpdateEpoch
 * @param {bigint} maxOracleStalenessEpochs
 * @param {boolean} oracleSeen
 * @returns {boolean}
 */
export function isOracleFresh(nowEpoch, oracleLastUpdateEpoch, maxOracleStalenessEpochs, oracleSeen) {
    if (!oracleSeen) return false;
    if (nowEpoch < oracleLastUpdateEpoch) return false;
    return (nowEpoch - oracleLastUpdateEpoch) <= maxOracleStalenessEpochs;
}

/**
 * True when clearing-to-index price move exceeds bound.
 * Uses cross-multiplication: |clearing - index| * 10000 > max_move_bps * index.
 */
export function oracleMoveViolated(clearingPriceE8, indexPriceE8, maxOracleMoveBps, oracleSeen) {
    if (!oracleSeen) return false;
    const diff = absVal(clearingPriceE8 - indexPriceE8);
    return diff * BPS_SCALE > maxOracleMoveBps * indexPriceE8;
}

/**
 * Settlement price for mark-to-market.
 * Clamps to index ± delta if oracle bound violated (ceil-div for quantization safety).
 */
export function settlePrice(clearingPriceE8, indexPriceE8, maxOracleMoveBps, oracleSeen) {
    if (!oracleMoveViolated(clearingPriceE8, indexPriceE8, maxOracleMoveBps, oracleSeen)) {
        return clearingPriceE8;
    }
    const maxDelta = (indexPriceE8 * maxOracleMoveBps + (BPS_SCALE - 1n)) / BPS_SCALE;
    if (clearingPriceE8 >= indexPriceE8) {
        return indexPriceE8 + maxDelta;
    }
    return indexPriceE8 - maxDelta;
}

// -- Position / margin helpers ------------------------------------------------

/** Absolute notional in quote: floor(|pos| * price_e8 / 1e8). */
export function notionalQuote(positionBase, priceE8) {
    return (absVal(positionBase) * priceE8) / PRICE_SCALE;
}

/** Margin in quote: floor(notional * margin_bps / 10_000). */
export function marginRequirement(notional, marginBps) {
    return (notional * marginBps) / BPS_SCALE;
}

/** Maintenance margin in quote (includes depeg buffer). */
export function maintMarginReq(positionBase, priceE8, maintBps, depegBps) {
    return marginRequirement(notionalQuote(positionBase, priceE8), maintBps + depegBps);
}

/** Initial margin in quote. */
export function initMarginReq(positionBase, priceE8, initBps) {
    return marginRequirement(notionalQuote(positionBase, priceE8), initBps);
}

// -- PnL helpers (symmetric) --------------------------------------------------

/** Unsigned PnL: floor(|pos| * |settle-index| / 1e8). */
export function pnlMagnitude(positionBase, settlePriceE8, indexPriceE8) {
    return (absVal(positionBase) * absVal(settlePriceE8 - indexPriceE8)) / PRICE_SCALE;
}

/** True when position direction matches price-change direction (profit). */
export function pnlSameSign(positionBase, settlePriceE8, indexPriceE8) {
    return (positionBase >= 0n) === (settlePriceE8 >= indexPriceE8);
}

/** Signed PnL: +magnitude when profitable, -magnitude when losing. */
export function pnlQuote(positionBase, settlePriceE8, indexPriceE8) {
    const mag = pnlMagnitude(positionBase, settlePriceE8, indexPriceE8);
    return pnlSameSign(positionBase, settlePriceE8, indexPriceE8) ? mag : -mag;
}

// -- Liquidation helpers ------------------------------------------------------

/** True when collateral < effective maintenance requirement. */
export function isLiquidatable(positionBase, collateralAfterPnl, settlePriceE8, maintenanceMarginBps, depegBufferBps) {
    if (positionBase === 0n) return false;
    return collateralAfterPnl < maintMarginReq(positionBase, settlePriceE8, maintenanceMarginBps, depegBufferBps);
}

/** Liquidation penalty (0 when notional < anti-bounty-farming threshold). */
export function liqPenalty(positionBase, settlePriceE8, liquidationPenaltyBps, minNotionalForBounty) {
    const notional = notionalQuote(positionBase, settlePriceE8);
    if (notional < minNotionalForBounty) return 0n;
    return marginRequirement(notional, liquidationPenaltyBps);
}

/** Liquidation penalty capped at remaining collateral after PnL. */
export function liqPenaltyCapped(collateralAfterPnl, positionBase, settlePriceE8, liquidationPenaltyBps, minNotionalForBounty) {
    const raw = liqPenalty(positionBase, settlePriceE8, liquidationPenaltyBps, minNotionalForBounty);
    return collateralAfterPnl < raw ? collateralAfterPnl : raw;
}

/**
 * Estimate the index price at which position becomes liquidatable.
 *
 * Returns the price (e8) at which collateral == maintenance margin,
 * or null if position is flat.
 *
 * At liquidation: collateral = floor(floor(|pos| * liq_price / 1e8) * eff_maint / 10000)
 * Solving: liq_price = collateral * 1e8 * 10000 / (|pos| * eff_maint)
 *
 * @param {bigint} positionBase
 * @param {bigint} collateral
 * @param {bigint} indexPriceE8 - current index (unused in simple model, kept for API compat)
 * @param {bigint} maintBps
 * @param {bigint} depegBps
 * @returns {bigint|null}
 */
export function liquidationPriceE8(positionBase, collateral, indexPriceE8, maintBps, depegBps) {
    if (positionBase === 0n) return null;

    const absPos = absVal(positionBase);
    const effMaintBps = maintBps + depegBps;
    if (effMaintBps === 0n) return null;

    const liq = (collateral * PRICE_SCALE * BPS_SCALE) / (absPos * effMaintBps);
    if (liq <= 0n) return null;
    return liq;
}

// -- Funding helpers (symmetric) ----------------------------------------------

/** Unsigned funding: floor(notional * |rate_bps| / 10_000). */
export function fundingMagnitude(positionBase, indexPriceE8, rateBps) {
    return (notionalQuote(positionBase, indexPriceE8) * absVal(rateBps)) / BPS_SCALE;
}

/** True when position and rate have same sign (account is payer). */
export function fundingSameSign(positionBase, rateBps) {
    return (positionBase >= 0n) === (rateBps >= 0n);
}

/** Signed funding: +magnitude for payer, -magnitude for payee. */
export function fundingPayment(positionBase, indexPriceE8, rateBps) {
    const mag = fundingMagnitude(positionBase, indexPriceE8, rateBps);
    return fundingSameSign(positionBase, rateBps) ? mag : -mag;
}

// -- Display helpers (Number output for UI) -----------------------------------

/**
 * Format a BigInt e8 price to a human-readable Number.
 * @param {bigint} priceE8
 * @returns {number}
 */
export function e8ToNumber(priceE8) {
    return Number(priceE8) / Number(PRICE_SCALE);
}

/**
 * Convert a human-readable price Number to BigInt e8.
 * @param {number} price
 * @returns {bigint}
 */
export function numberToE8(price) {
    return BigInt(Math.round(price * Number(PRICE_SCALE)));
}

/**
 * Format basis points as a percentage string.
 * @param {bigint|number} bps
 * @returns {string}
 */
export function bpsToPercent(bps) {
    return (Number(bps) / 100).toFixed(2) + '%';
}

/**
 * Compute effective leverage from position and collateral.
 * @param {bigint} positionBase
 * @param {bigint} priceE8
 * @param {bigint} collateral
 * @returns {number} leverage as a float (e.g. 5.0)
 */
export function effectiveLeverage(positionBase, priceE8, collateral) {
    if (collateral === 0n) return Infinity;
    const notional = notionalQuote(positionBase, priceE8);
    if (notional === 0n) return 0;
    return Number(notional) / Number(collateral);
}

/**
 * Compute margin ratio (collateral / maint_margin_req).
 * @returns {number} ratio (>1 = safe, <1 = liquidatable)
 */
export function marginRatio(positionBase, priceE8, collateral, maintBps, depegBps) {
    if (positionBase === 0n) return Infinity;
    const mreq = maintMarginReq(positionBase, priceE8, maintBps, depegBps);
    if (mreq === 0n) return Infinity;
    return Number(collateral) / Number(mreq);
}
