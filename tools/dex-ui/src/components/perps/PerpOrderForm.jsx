import { useState, useMemo, useCallback } from 'react';
import { toBigInt, effectiveLeverage } from '../../lib/perpMath.js';
import { validateSetPosition } from '../../lib/perpValidation.js';
import './PerpOrderForm.css';

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
function PerpOrderForm({ market, position, wallet, writeEnabled, writeLockReason, onSubmit, onShowConfirm }) {
    const [side, setSide] = useState('long');
    const [sizeInput, setSizeInput] = useState('');

    const currentPosBase = position?.positionBase ?? 0;

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
                disabled={!wallet || !writeEnabled || !validation.ok}
            >
                {!wallet ? 'Connect Wallet'
                    : !writeEnabled ? 'Preview-only lane'
                    : !sizeInput ? 'Enter Size'
                    : validation.error ? validation.error
                    : `${side === 'long' ? 'Long' : 'Short'} ${market?.id || ''}`}
            </button>
            {!writeEnabled && (
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
