import { e8ToNumber, bpsToPercent } from '../../lib/perpMath.js';
import { EpochPhase } from '../../lib/perpValidation.js';
import './PerpPriceTicker.css';

/**
 * PerpPriceTicker - Market data display
 *
 * Shows: index price, clearing price, funding rate, epoch, breaker status.
 * Color-coded: green=normal, orange=warning, red=breaker.
 */
function PerpPriceTicker({ market }) {
    if (!market) {
        return (
            <div className="perp-price-ticker perp-price-ticker--empty">
                <p className="perp-placeholder">Select a market</p>
            </div>
        );
    }

    const indexPrice = e8ToNumber(BigInt(market.indexPriceE8));
    const clearingPrice = market.clearingPriceE8 ? e8ToNumber(BigInt(market.clearingPriceE8)) : null;
    const statusClass = market.breakerActive ? 'danger' : 'normal';

    return (
        <div className={`perp-price-ticker perp-price-ticker--${statusClass}`}>
            {/* Index Price */}
            <div className="perp-ticker-item perp-ticker-item--primary">
                <span className="perp-ticker-label">Index Price</span>
                <span className="perp-ticker-value perp-ticker-value--large">
                    ${formatPrice(indexPrice)}
                </span>
            </div>

            {/* Clearing Price */}
            <div className="perp-ticker-item">
                <span className="perp-ticker-label">Clearing Price</span>
                <span className="perp-ticker-value">
                    {clearingPrice != null ? `$${formatPrice(clearingPrice)}` : '--'}
                </span>
            </div>

            {/* Funding Rate */}
            <div className="perp-ticker-item">
                <span className="perp-ticker-label">Funding Rate</span>
                <FundingBadge rateBps={market.fundingRateBps} />
            </div>

            {/* Epoch */}
            <div className="perp-ticker-item">
                <span className="perp-ticker-label">Epoch</span>
                <span className="perp-ticker-value">
                    #{market.nowEpoch}
                </span>
            </div>

            {/* Phase */}
            <div className="perp-ticker-item">
                <span className="perp-ticker-label">Phase</span>
                <PhaseBadge phase={market.epochPhase} />
            </div>

            {/* Breaker Status */}
            <div className="perp-ticker-item">
                <span className="perp-ticker-label">Status</span>
                <StatusBadge breakerActive={market.breakerActive} />
            </div>
        </div>
    );
}

function FundingBadge({ rateBps }) {
    const positive = rateBps >= 0;
    return (
        <span className={`perp-ticker-value perp-funding-badge ${positive ? 'positive' : 'negative'}`}>
            {positive ? '+' : ''}{bpsToPercent(rateBps)}
        </span>
    );
}

function PhaseBadge({ phase }) {
    const labels = {
        [EpochPhase.OPEN]: 'Open',
        [EpochPhase.PRICE_PUBLISHED]: 'Price Pub.',
        [EpochPhase.SETTLED]: 'Settled',
    };
    const classes = {
        [EpochPhase.OPEN]: 'phase-open',
        [EpochPhase.PRICE_PUBLISHED]: 'phase-published',
        [EpochPhase.SETTLED]: 'phase-settled',
    };
    return (
        <span className={`perp-phase-badge ${classes[phase] || ''}`}>
            {labels[phase] || phase}
        </span>
    );
}

function StatusBadge({ breakerActive }) {
    if (breakerActive) {
        return <span className="perp-status-badge perp-status-badge--danger">BREAKER</span>;
    }
    return <span className="perp-status-badge perp-status-badge--normal">Normal</span>;
}

function formatPrice(price) {
    if (price >= 1000) return price.toLocaleString(undefined, { minimumFractionDigits: 2, maximumFractionDigits: 2 });
    if (price >= 1) return price.toFixed(4);
    return price.toFixed(6);
}

export default PerpPriceTicker;
