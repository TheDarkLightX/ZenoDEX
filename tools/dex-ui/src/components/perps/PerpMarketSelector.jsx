import { useMemo } from 'react';
import { e8ToNumber, bpsToPercent } from '../../lib/perpMath.js';
import './PerpMarketSelector.css';

/**
 * PerpMarketSelector - Horizontal market picker ribbon
 *
 * Shows all available perp markets with mini price/change info.
 * Active market is highlighted with accent border.
 */
function PerpMarketSelector({ markets, selectedMarketId, onSelect }) {
    return (
        <div className="perp-market-selector">
            {markets.map(market => (
                <MarketCard
                    key={market.id}
                    market={market}
                    isSelected={market.id === selectedMarketId}
                    onSelect={() => onSelect(market.id)}
                />
            ))}
        </div>
    );
}

function MarketCard({ market, isSelected, onSelect }) {
    const price = useMemo(() => (
        market.indexPriceE8 != null ? e8ToNumber(BigInt(market.indexPriceE8)) : null
    ), [market.indexPriceE8]);
    const fundingRate = market.fundingRateBps;
    const fundingPositive = fundingRate != null && fundingRate >= 0;

    return (
        <button
            className={`perp-market-card ${isSelected ? 'selected' : ''}`}
            onClick={onSelect}
        >
            <div className="perp-market-card-header">
                <span className="perp-market-icon">{market.icon}</span>
                <span className="perp-market-id">{market.id}</span>
                {market.breakerActive && (
                    <span className="perp-market-breaker-badge">BREAKER</span>
                )}
            </div>
            <div className="perp-market-card-price">
                {price != null ? `$${formatPrice(price)}` : 'Awaiting oracle'}
            </div>
            <div className={`perp-market-card-funding ${fundingPositive ? 'positive' : 'negative'}`}>
                {fundingRate != null
                    ? `FR: ${fundingPositive ? '+' : ''}${bpsToPercent(fundingRate)}`
                    : 'FR: —'}
            </div>
        </button>
    );
}

function formatPrice(price) {
    if (price >= 1000) return price.toLocaleString(undefined, { minimumFractionDigits: 2, maximumFractionDigits: 2 });
    if (price >= 1) return price.toFixed(4);
    return price.toFixed(6);
}

export default PerpMarketSelector;
