import { useMemo } from 'react';
import './PerpAccountSummary.css';

/**
 * PerpAccountSummary - Aggregate stats across all markets
 *
 * Shows: total collateral, total unrealized PnL, number of open positions,
 * aggregate margin utilization.
 */
function PerpAccountSummary({ markets, positions }) {
    const summary = useMemo(() => {
        if (!markets?.length || !positions) {
            return { totalCollateral: 0, totalPnl: 0, openCount: 0 };
        }

        let totalCollateral = 0;
        let totalPnl = 0;
        let openCount = 0;

        for (const market of markets) {
            const pos = positions[market.id];
            if (!pos) continue;
            totalCollateral += pos.collateralQuote || 0;
            if (pos.positionBase !== 0 && pos.entryPriceE8) {
                openCount++;
                // Simple PnL estimate
                const absPos = Math.abs(pos.positionBase);
                const priceDiff = market.indexPriceE8 - pos.entryPriceE8;
                const sign = pos.positionBase > 0 ? 1 : -1;
                totalPnl += sign * (absPos * priceDiff) / 100_000_000;
            }
        }

        return { totalCollateral, totalPnl, openCount };
    }, [markets, positions]);

    const pnlPositive = summary.totalPnl >= 0;

    return (
        <div className="perp-account-summary">
            <div className="perp-summary-grid">
                <div className="perp-summary-stat">
                    <span className="perp-summary-label">Total Collateral</span>
                    <span className="perp-summary-value">
                        {formatQuote(summary.totalCollateral)}
                    </span>
                </div>

                <div className="perp-summary-stat">
                    <span className="perp-summary-label">Unrealized PnL</span>
                    <span className={`perp-summary-value perp-summary-pnl ${pnlPositive ? 'positive' : 'negative'}`}>
                        {pnlPositive ? '+' : ''}{formatQuote(summary.totalPnl)}
                    </span>
                </div>

                <div className="perp-summary-stat">
                    <span className="perp-summary-label">Open Positions</span>
                    <span className="perp-summary-value">
                        {summary.openCount}
                    </span>
                </div>

                <div className="perp-summary-stat">
                    <span className="perp-summary-label">Account Value</span>
                    <span className="perp-summary-value">
                        {formatQuote(summary.totalCollateral + summary.totalPnl)}
                    </span>
                </div>
            </div>
        </div>
    );
}

function formatQuote(value) {
    const num = Number(value);
    if (Math.abs(num) >= 1_000_000) return '$' + (num / 1_000_000).toFixed(2) + 'M';
    if (Math.abs(num) >= 1_000) return '$' + (num / 1_000).toFixed(2) + 'K';
    return '$' + num.toLocaleString(undefined, { maximumFractionDigits: 2 });
}

export default PerpAccountSummary;
