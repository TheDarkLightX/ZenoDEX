import { e8ToNumber, bpsToPercent } from '../../lib/perpMath.js';
import { EpochPhase } from '../../lib/perpValidation.js';
import InfoTip from '../InfoTip.jsx';
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

    const indexPrice = market.indexPriceE8 != null ? e8ToNumber(BigInt(market.indexPriceE8)) : null;
    const clearingPrice = market.clearingPriceE8 != null ? e8ToNumber(BigInt(market.clearingPriceE8)) : null;
    const statusClass = market.breakerActive == null
        ? 'unknown'
        : market.breakerActive
            ? 'danger'
            : 'normal';

    return (
        <div className={`perp-price-ticker perp-price-ticker--${statusClass}`}>
            {/* Index Price */}
            <div className="perp-ticker-item perp-ticker-item--primary">
                <span className="perp-ticker-label">
                    Index Price
                    <InfoTip label="Index Price">External oracle price for the underlying asset. PnL clears to the index — this is what the protocol believes the market price is.</InfoTip>
                </span>
                <span className="perp-ticker-value perp-ticker-value--large">
                    {indexPrice != null ? `$${formatPrice(indexPrice)}` : 'Awaiting oracle'}
                </span>
            </div>

            {/* Clearing Price */}
            <div className="perp-ticker-item">
                <span className="perp-ticker-label">
                    Clearing Price
                    <InfoTip label="Clearing Price">Price at which the current epoch&apos;s positions settled. Set by the oracle authority once per epoch via publish-clearing-price.</InfoTip>
                </span>
                <span className="perp-ticker-value">
                    {clearingPrice != null ? `$${formatPrice(clearingPrice)}` : '--'}
                </span>
            </div>

            {/* Funding Rate */}
            <div className="perp-ticker-item">
                <span className="perp-ticker-label">
                    Funding Rate
                    <InfoTip label="Funding Rate">Per-epoch payment between long and short sides, in bps. Positive = longs pay shorts; negative = shorts pay longs. Pulls the perp toward the index.</InfoTip>
                </span>
                <FundingBadge rateBps={market.fundingRateBps} />
            </div>

            {/* Epoch */}
            <div className="perp-ticker-item">
                <span className="perp-ticker-label">Epoch</span>
                <span className="perp-ticker-value">
                    {market.nowEpoch != null ? `#${market.nowEpoch}` : '—'}
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
    // The clearinghouse-2p wallet payload does not expose a funding rate; show a
    // neutral placeholder rather than "NaN%".
    if (rateBps == null || !Number.isFinite(Number(rateBps))) {
        return <span className="perp-ticker-value perp-funding-badge">—</span>;
    }
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
    if (breakerActive == null) {
        return <span className="perp-status-badge">Unknown</span>;
    }
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
