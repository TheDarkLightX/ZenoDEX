import { e8ToNumber } from '../../lib/perpMath.js';
import { useWindowed } from '../../lib/useWindowed.js';
import './PerpTradeHistory.css';

/**
 * PerpTradeHistory - Scrollable table of recent perp operations
 *
 * Displays time, market, action, side, size, price, and status
 * for each item in the history array.
 */
function PerpTradeHistory({ history }) {
    const { rows, total, hasMore, showMore } = useWindowed(history, 100);
    if (!history || history.length === 0) {
        return (
            <div className="perp-history panel">
                <h3 className="perp-history-title">Trade History</h3>
                <div className="perp-history-empty">No trade history</div>
            </div>
        );
    }

    return (
        <div className="perp-history panel">
            <h3 className="perp-history-title">Trade History</h3>
            <div className="perp-history-scroll">
                <table className="perp-history-table">
                    <thead>
                        <tr>
                            <th>Time</th>
                            <th>Market</th>
                            <th>Action</th>
                            <th>Side</th>
                            <th>Size</th>
                            <th>Price</th>
                            <th>Status</th>
                        </tr>
                    </thead>
                    <tbody>
                        {rows.map(item => (
                            <tr key={item.id} className="perp-history-row">
                                <td className="perp-history-cell perp-history-cell--time">
                                    {formatTimeAgo(item.timestamp)}
                                </td>
                                <td className="perp-history-cell">
                                    {item.market}
                                </td>
                                <td className="perp-history-cell">
                                    {formatAction(item.action)}
                                </td>
                                <td className="perp-history-cell">
                                    <SideBadge side={item.side} />
                                </td>
                                <td className="perp-history-cell perp-history-cell--mono">
                                    {formatSize(item)}
                                </td>
                                <td className="perp-history-cell perp-history-cell--mono">
                                    {formatPrice(item)}
                                </td>
                                <td className="perp-history-cell">
                                    <StatusBadge status={item.status} />
                                </td>
                            </tr>
                        ))}
                    </tbody>
                </table>
            </div>
            {hasMore && (
                <div className="perp-history-more">
                    <span>Showing {rows.length} of {total}</span>
                    <button type="button" className="btn btn-secondary" onClick={showMore}>Show more</button>
                </div>
            )}
        </div>
    );
}

function formatTimeAgo(timestamp) {
    const seconds = Math.floor((Date.now() - timestamp) / 1000);
    if (seconds < 60) return 'Just now';
    if (seconds < 3600) return `${Math.floor(seconds / 60)}m ago`;
    if (seconds < 86400) return `${Math.floor(seconds / 3600)}h ago`;
    return `${Math.floor(seconds / 86400)}d ago`;
}

const ACTION_LABELS = {
    deposit_collateral: 'Deposit',
    withdraw_collateral: 'Withdraw',
    deposit: 'Deposit',
    withdraw: 'Withdraw',
    set_position: 'Trade',
    deposit_insurance: 'Insure',
    liquidation: 'Liquidation',
    funding: 'Funding',
    trade: 'Trade',
};

function formatAction(action) {
    return ACTION_LABELS[action] || action;
}

function SideBadge({ side }) {
    if (!side) return <span className="perp-history-side perp-history-side--none">--</span>;
    const className = side === 'long' ? 'perp-history-side--long' : 'perp-history-side--short';
    return (
        <span className={`perp-history-side ${className}`}>
            {side === 'long' ? 'Long' : 'Short'}
        </span>
    );
}

function formatSize(item) {
    if (item.sizeAfter != null) {
        return Math.abs(item.sizeAfter).toLocaleString();
    }
    if (item.amount != null) {
        return Number(item.amount).toLocaleString();
    }
    return '--';
}

function formatPrice(item) {
    if (item.priceE8 != null) {
        const price = e8ToNumber(BigInt(item.priceE8));
        if (price >= 1000) return '$' + price.toLocaleString(undefined, { minimumFractionDigits: 2, maximumFractionDigits: 2 });
        if (price >= 1) return '$' + price.toFixed(4);
        return '$' + price.toFixed(6);
    }
    return '--';
}

function StatusBadge({ status }) {
    const className = status === 'confirmed'
        ? 'perp-history-status--confirmed'
        : status === 'pending'
            ? 'perp-history-status--pending'
            : '';

    return (
        <span className={`perp-history-status ${className}`}>
            {status}
        </span>
    );
}

export default PerpTradeHistory;
