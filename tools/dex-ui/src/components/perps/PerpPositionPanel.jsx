import { e8ToNumber } from '../../lib/perpMath.js';
import './PerpPositionPanel.css';

/**
 * PerpPositionPanel - Current position details
 *
 * Shows: side, size, entry price, unrealized PnL, margin health bar,
 * liquidation price, leverage.
 */
function PerpPositionPanel({ market, position, derived, isObserver = false }) {
    if (!market) {
        return (
            <div className="perp-position-panel perp-position-panel--empty">
                <p className="perp-placeholder">Select a market</p>
            </div>
        );
    }

    if (position && position.positionBase == null) {
        return (
            <div className="perp-position-panel perp-position-panel--empty">
                <h3 className="perp-section-title">Position</h3>
                <p className="perp-placeholder">Authoritative position state unavailable</p>
            </div>
        );
    }

    const hasPosition = position && position.positionBase !== 0;

    if (!hasPosition) {
        return (
            <div className="perp-position-panel perp-position-panel--empty">
                <h3 className="perp-section-title">Position</h3>
                <div className="perp-no-position">
                    <span className="perp-no-position-icon">--</span>
                    <p>No open position in {market.id}</p>
                    <p className="perp-no-position-hint">
                        {isObserver
                            ? 'This is an operator-managed 2-party market — your wallet is an observer and cannot open a position.'
                            : 'Use the order form to open a position'}
                    </p>
                </div>
            </div>
        );
    }

    const side = position.positionBase > 0 ? 'long' : 'short';
    const size = Math.abs(position.positionBase);
    const entryPrice = position.entryPriceE8 != null
        ? e8ToNumber(BigInt(position.entryPriceE8))
        : null;
    const indexPrice = market.indexPriceE8 != null
        ? e8ToNumber(BigInt(market.indexPriceE8))
        : null;

    const pnl = derived?.unrealizedPnl ?? null;
    const pnlPositive = pnl != null && pnl >= 0;
    const liqPrice = derived?.liquidationPrice;
    const leverage = derived?.leverage ?? null;
    const mRatio = derived?.marginRatio ?? null;

    // Margin health: ratio of collateral to maint margin
    // >2.0 = green, 1.5-2.0 = orange, <1.5 = red
    const healthPercent = mRatio != null
        ? Math.min(100, Math.max(0, ((mRatio - 1) / 2) * 100))
        : null;
    const healthColor = mRatio == null
        ? 'var(--text-muted)'
        : mRatio >= 2
            ? 'var(--perp-long)'
            : mRatio >= 1.5
                ? 'var(--perp-warning)'
                : 'var(--perp-short)';

    return (
        <div className="perp-position-panel">
            <div className="perp-position-header">
                <h3 className="perp-section-title">Position</h3>
                <span className={`perp-position-side-badge perp-position-side-badge--${side}`}>
                    {side.toUpperCase()}
                </span>
            </div>

            <div className="perp-position-stats">
                <div className="perp-position-row">
                    <span>Size</span>
                    <span className="perp-position-value">{size.toLocaleString()} base</span>
                </div>
                <div className="perp-position-row">
                    <span>Entry Price</span>
                    <span className="perp-position-value">
                        {entryPrice != null ? `$${formatPrice(entryPrice)}` : '--'}
                    </span>
                </div>
                <div className="perp-position-row">
                    <span>Mark Price</span>
                    <span className="perp-position-value">
                        {indexPrice != null ? `$${formatPrice(indexPrice)}` : '--'}
                    </span>
                </div>
                <div className="perp-position-row">
                    <span>Unrealized PnL</span>
                    <span className={`perp-position-value perp-pnl ${pnlPositive ? 'positive' : 'negative'}`}>
                        {pnl != null ? `${pnlPositive ? '+' : ''}${formatQuote(pnl)}` : '--'}
                    </span>
                </div>
                <div className="perp-position-row">
                    <span>Leverage</span>
                    <span className="perp-position-value">
                        {leverage != null ? `${leverage.toFixed(1)}x` : '--'}
                    </span>
                </div>
                <div className="perp-position-row">
                    <span>Liq. Price</span>
                    <span className="perp-position-value perp-liq-price">
                        {liqPrice != null ? `$${formatPrice(liqPrice)}` : '--'}
                    </span>
                </div>
                <div className="perp-position-row">
                    <span>Collateral</span>
                    <span className="perp-position-value">
                        {position.collateralQuote != null ? formatQuote(position.collateralQuote) : '--'}
                    </span>
                </div>
            </div>

            {/* Margin Health Bar */}
            <div className="perp-margin-health">
                <div className="perp-margin-health-header">
                    <span>Margin Health</span>
                    <span style={{ color: healthColor }}>
                        {mRatio != null ? `${mRatio.toFixed(2)}x` : '--'}
                    </span>
                </div>
                <div className="perp-margin-health-bar">
                    <div
                        className="perp-margin-health-fill"
                        style={{
                            width: `${healthPercent ?? 0}%`,
                            background: healthColor,
                        }}
                    />
                </div>
            </div>
        </div>
    );
}

function formatPrice(price) {
    if (price >= 1000) return price.toLocaleString(undefined, { minimumFractionDigits: 2, maximumFractionDigits: 2 });
    if (price >= 1) return price.toFixed(4);
    return price.toFixed(6);
}

function formatQuote(value) {
    const num = Number(value);
    if (num >= 1_000_000) return '$' + (num / 1_000_000).toFixed(2) + 'M';
    if (num >= 1_000) return '$' + (num / 1_000).toFixed(2) + 'K';
    return '$' + num.toLocaleString(undefined, { maximumFractionDigits: 2 });
}

export default PerpPositionPanel;
