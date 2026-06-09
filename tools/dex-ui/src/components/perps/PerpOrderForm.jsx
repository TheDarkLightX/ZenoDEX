import { useState, useMemo, useCallback } from 'react';
import { toBigInt, effectiveLeverage } from '../../lib/perpMath.js';
import { validateSetPosition } from '../../lib/perpValidation.js';
import './PerpOrderForm.css';

const LEVERAGE_PRESETS = [1, 2, 5, 10, 20];

/**
 * PerpOrderForm - Long/Short position entry form
 *
 * Poka-yoke safety tiers:
 * - Low (<3x): Standard submit
 * - Medium (3-5x): Orange warning banner
 * - High (5-10x): Confirmation modal
 * - Extreme (>10x): Type "CONFIRM" to proceed
 * - Breaker: Full red banner, reduce-only enforced
 */
function PerpOrderForm({ market, position, wallet, writeEnabled, writeLockReason, onSubmit, onShowConfirm, isObserver = false }) {
    const [side, setSide] = useState('long');
    const [sizeInput, setSizeInput] = useState('');
    const [targetLeverage, setTargetLeverage] = useState(1);

    const currentPosBase = position?.positionBase ?? 0;

    // Max size derivable from collateral × leverage × price (in base units).
    // Used by the leverage presets and the size quick-fill row.
    const maxSizeForLeverage = useMemo(() => {
        if (!market) return 0;
        const collateral = Number(position?.collateralQuote ?? 0);
        const indexPrice = Number(market.indexPriceE8 ?? 0) / 100_000_000;
        if (collateral <= 0 || indexPrice <= 0 || targetLeverage <= 0) return 0;
        return Math.floor((collateral * targetLeverage) / indexPrice);
    }, [market, position, targetLeverage]);

    const applyLeveragePreset = useCallback((lev) => {
        setTargetLeverage(lev);
        if (!market) return;
        const collateral = Number(position?.collateralQuote ?? 0);
        const indexPrice = Number(market.indexPriceE8 ?? 0) / 100_000_000;
        if (collateral <= 0 || indexPrice <= 0) return;
        const nextSize = Math.floor((collateral * lev) / indexPrice);
        if (nextSize > 0) setSizeInput(String(nextSize));
    }, [market, position]);

    const applySizeFraction = useCallback((fraction) => {
        if (maxSizeForLeverage <= 0) return;
        const nextSize = Math.max(1, Math.floor(maxSizeForLeverage * fraction));
        setSizeInput(String(nextSize));
    }, [maxSizeForLeverage]);

    // Compute the new position based on input
    const newPositionBase = useMemo(() => {
        const size = parseInt(sizeInput, 10);
        if (!size || size <= 0) return null;
        return side === 'long' ? size : -size;
    }, [side, sizeInput]);

    // Validate against market state
    const validation = useMemo(() => {
        if (!market || newPositionBase == null) {
            return { ok: false, error: null };
        }
        const state = {
            epochPhase: market.epochPhase,
            oracleSeen: market.oracleSeen,
            maxPositionAbs: toBigInt(market.maxPositionAbs),
            breakerActive: market.breakerActive,
            positionBase: toBigInt(currentPosBase),
            nowEpoch: toBigInt(market.nowEpoch),
            oracleLastUpdateEpoch: toBigInt(market.oracleLastUpdateEpoch),
            maxOracleStalenessEpochs: toBigInt(market.maxOracleStalenessEpochs),
            indexPriceE8: toBigInt(market.indexPriceE8),
            initialMarginBps: toBigInt(market.initialMarginBps),
            maintenanceMarginBps: toBigInt(market.maintenanceMarginBps),
            depegBufferBps: toBigInt(market.depegBufferBps),
            collateralQuote: toBigInt(position?.collateralQuote ?? 0),
        };
        return validateSetPosition(state, toBigInt(newPositionBase));
    }, [market, position, newPositionBase, currentPosBase]);

    // Compute leverage preview
    const leveragePreview = useMemo(() => {
        if (!market || newPositionBase == null) return null;
        const collateral = toBigInt(position?.collateralQuote ?? 0);
        if (collateral === 0n) return null;
        return effectiveLeverage(
            toBigInt(newPositionBase),
            toBigInt(market.indexPriceE8),
            collateral,
        );
    }, [market, position, newPositionBase]);

    // Notional preview
    const notionalPreview = useMemo(() => {
        if (!market || newPositionBase == null) return null;
        const absPos = Math.abs(newPositionBase);
        return (absPos * market.indexPriceE8) / 100_000_000;
    }, [market, newPositionBase]);

    const handleSubmit = useCallback(() => {
        if (!validation.ok || newPositionBase == null) return;

        const tier = validation.riskTier?.tier || 'low';

        // High/extreme risk: delegate to confirmation modal
        if (tier === 'high' || tier === 'extreme') {
            onShowConfirm?.({
                side,
                size: parseInt(sizeInput, 10),
                newPositionBase,
                leverage: leveragePreview,
                riskTier: validation.riskTier,
            });
            return;
        }

        onSubmit?.({ marketId: market.id, newPositionBase });
    }, [validation, newPositionBase, side, sizeInput, leveragePreview, market, onSubmit, onShowConfirm]);

    const riskColor = validation.riskTier?.color || 'var(--accent-cyan)';

    return (
        <div className="perp-order-form">
            {/* Leverage header — set independently of size, like GMX v2 */}
            <div className="perp-leverage-header">
                <div className="perp-leverage-header-row">
                    <span className="perp-form-label">Leverage</span>
                    <span className="perp-leverage-value" style={{ color: riskColor }}>
                        {leveragePreview != null ? `${leveragePreview.toFixed(1)}x` : `${targetLeverage}x target`}
                    </span>
                </div>
                <div className="perp-leverage-chips" role="group" aria-label="Leverage presets">
                    {LEVERAGE_PRESETS.map((lev) => (
                        <button
                            key={lev}
                            type="button"
                            className={`perp-leverage-chip ${targetLeverage === lev ? 'active' : ''}`}
                            onClick={() => applyLeveragePreset(lev)}
                        >
                            {lev}x
                        </button>
                    ))}
                </div>
            </div>

            {/* Side Toggle */}
            <div className="perp-side-toggle">
                <button
                    className={`perp-side-btn perp-side-long ${side === 'long' ? 'active' : ''}`}
                    onClick={() => setSide('long')}
                >
                    Long
                </button>
                <button
                    className={`perp-side-btn perp-side-short ${side === 'short' ? 'active' : ''}`}
                    onClick={() => setSide('short')}
                >
                    Short
                </button>
            </div>

            {/* Size Input */}
            <div className="perp-form-group">
                <label className="perp-form-label">
                    Size (base units)
                </label>
                <input
                    type="number"
                    className="input perp-size-input"
                    placeholder="0"
                    value={sizeInput}
                    onChange={e => setSizeInput(e.target.value)}
                    min="0"
                    step="1"
                />
                {maxSizeForLeverage > 0 && (
                    <div className="perp-size-presets" role="group" aria-label="Size quick-fill">
                        <button type="button" className="perp-size-preset" onClick={() => applySizeFraction(0.25)}>25%</button>
                        <button type="button" className="perp-size-preset" onClick={() => applySizeFraction(0.5)}>50%</button>
                        <button type="button" className="perp-size-preset" onClick={() => applySizeFraction(0.75)}>75%</button>
                        <button type="button" className="perp-size-preset perp-size-preset-max" onClick={() => applySizeFraction(1)}>MAX</button>
                    </div>
                )}
            </div>

            {/* Preview Stats */}
            {sizeInput && (
                <div className="perp-order-preview animate-fade-in">
                    <div className="perp-preview-row">
                        <span>Notional</span>
                        <span className="perp-preview-value">
                            {notionalPreview != null ? `$${formatQuote(notionalPreview)}` : '--'}
                        </span>
                    </div>
                    <div className="perp-preview-row">
                        <span>Leverage</span>
                        <span className="perp-preview-value" style={{ color: riskColor }}>
                            {leveragePreview != null ? `${leveragePreview.toFixed(1)}x` : '--'}
                        </span>
                    </div>
                    <div className="perp-preview-row">
                        <span>Collateral</span>
                        <span className="perp-preview-value">
                            ${formatQuote(position?.collateralQuote ?? 0)}
                        </span>
                    </div>
                </div>
            )}

            {/* Circuit-breaker status unavailable — honest, non-blocking heads-up.
               null means the backend did not report the halt status (not a
               confirmed "normal"); we surface the uncertainty without blocking
               or alarming. Gated on sizeInput (like the preview/error) so it
               reads naturally once a trade is being composed. Real true/false
               (e.g. demo) skip this. */}
            {market && market.breakerActive == null && sizeInput && (
                <div className="perp-order-info" role="note">
                    Circuit-breaker status is currently unavailable; this trade could fail on-chain if the market is halted.
                </div>
            )}

            {/* Risk Warning */}
            {validation.warning && (
                <div className="perp-risk-warning" style={{ borderColor: riskColor, background: `${riskColor}11` }}>
                    {validation.warning}
                </div>
            )}

            {/* Error */}
            {validation.error && sizeInput && (
                <div className="perp-order-error">{validation.error}</div>
            )}

            {/* Submit */}
            <button
                className={`btn btn-large perp-submit-btn perp-submit-${side}`}
                onClick={handleSubmit}
                disabled={!wallet || isObserver || !writeEnabled || !validation.ok}
            >
                {!wallet ? 'Connect wallet in header to trade →'
                    : isObserver ? 'Observer — operator-managed market'
                    : !writeEnabled ? 'Writes disabled'
                    : !sizeInput ? 'Enter Size'
                    : validation.error ? validation.error
                    : `${side === 'long' ? 'Long' : 'Short'} ${market?.id || ''}`}
            </button>
            {isObserver && (
                <div className="perp-order-error">
                    This is an operator-managed 2-party market. Your wallet is an observer —
                    trading is restricted to the market&apos;s two counterparties.
                </div>
            )}
            {!isObserver && !writeEnabled && (
                <div className="perp-order-error">{writeLockReason}</div>
            )}
        </div>
    );
}

function formatQuote(value) {
    const num = Number(value);
    if (num >= 1_000_000) return (num / 1_000_000).toFixed(2) + 'M';
    if (num >= 1_000) return (num / 1_000).toFixed(2) + 'K';
    return num.toLocaleString(undefined, { maximumFractionDigits: 2 });
}

export default PerpOrderForm;
