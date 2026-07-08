import { useState, useMemo } from 'react';
import { formatNumber } from '../lib/cpmm';
import './TransactionHistory.css';

/**
 * TransactionHistory - Display user's past DEX transactions
 * Features:
 * - Filterable by type (swap, add, remove)
 * - Status indicators (pending, confirmed, failed)
 * - Links to Tau explorer
 */

// Empty by default — populated from live Tau-node history when wired.
const MOCK_TRANSACTIONS = [];

const TYPE_LABELS = {
    swap: 'Swap',
    add_liquidity: 'Add Liquidity',
    remove_liquidity: 'Remove Liquidity',
};

const TYPE_ICONS = {
    swap: '↔️',
    add_liquidity: '➕',
    remove_liquidity: '➖',
};

const STATUS_CLASSES = {
    pending: 'status-pending',
    confirmed: 'status-confirmed',
    failed: 'status-failed',
};

function formatTimeAgo(timestamp) {
    const seconds = Math.floor((Date.now() - timestamp) / 1000);
    if (seconds < 60) return 'Just now';
    if (seconds < 3600) return `${Math.floor(seconds / 60)}m ago`;
    if (seconds < 86400) return `${Math.floor(seconds / 3600)}h ago`;
    return `${Math.floor(seconds / 86400)}d ago`;
}

function TransactionHistory({ wallet }) {
    const [filter, setFilter] = useState('all');

    const filteredTransactions = useMemo(() => {
        if (filter === 'all') return MOCK_TRANSACTIONS;
        return MOCK_TRANSACTIONS.filter(tx => tx.type === filter);
    }, [filter]);

    if (!wallet) {
        return (
            <div className="history-container">
                <div className="history-empty panel">
                    <span className="empty-icon">📋</span>
                    <h3>Connect Wallet</h3>
                    <p>Connect your wallet to view transaction history</p>
                </div>
            </div>
        );
    }

    return (
        <div className="history-container">
            <div className="history-header">
                <h2>Transaction History</h2>
                <div className="history-filters" role="tablist" aria-label="Filter transactions">
                    <button
                        className={`filter-btn ${filter === 'all' ? 'active' : ''}`}
                        onClick={() => setFilter('all')}
                        role="tab"
                        aria-selected={filter === 'all'}
                        type="button"
                    >
                        All
                    </button>
                    <button
                        className={`filter-btn ${filter === 'swap' ? 'active' : ''}`}
                        onClick={() => setFilter('swap')}
                        role="tab"
                        aria-selected={filter === 'swap'}
                        type="button"
                    >
                        Swaps
                    </button>
                    <button
                        className={`filter-btn ${filter === 'add_liquidity' ? 'active' : ''}`}
                        onClick={() => setFilter('add_liquidity')}
                        role="tab"
                        aria-selected={filter === 'add_liquidity'}
                        type="button"
                    >
                        Adds
                    </button>
                    <button
                        className={`filter-btn ${filter === 'remove_liquidity' ? 'active' : ''}`}
                        onClick={() => setFilter('remove_liquidity')}
                        role="tab"
                        aria-selected={filter === 'remove_liquidity'}
                        type="button"
                    >
                        Removes
                    </button>
                </div>
            </div>

            <div className="history-list panel">
                {filteredTransactions.length === 0 ? (
                    <div className="history-empty-list">
                        <span>No transactions found</span>
                    </div>
                ) : (
                    filteredTransactions.map((tx, i) => (
                        <a
                            key={tx.id}
                            className="history-item animate-slide-up"
                            style={{ animationDelay: `${i * 50}ms` }}
                            href={`https://explorer.tau.net/tx/${tx.txHash}`}
                            target="_blank"
                            rel="noopener noreferrer"
                        >
                            <div className="tx-icon">
                                {TYPE_ICONS[tx.type]}
                            </div>
                            <div className="tx-details">
                                <div className="tx-type">
                                    {TYPE_LABELS[tx.type]}
                                    <span className={`tx-status ${STATUS_CLASSES[tx.status]}`}>
                                        {tx.status === 'pending' && '⏳'}
                                        {tx.status === 'confirmed' && '✓'}
                                        {tx.status === 'failed' && '✗'}
                                    </span>
                                </div>
                                <div className="tx-amounts">
                                    {tx.type === 'swap' && (
                                        <>
                                            <span>{formatNumber(tx.tokenIn.amount)} {tx.tokenIn.symbol}</span>
                                            <span className="tx-arrow">→</span>
                                            <span>{formatNumber(tx.tokenOut.amount)} {tx.tokenOut.symbol}</span>
                                        </>
                                    )}
                                    {tx.type === 'add_liquidity' && (
                                        <>
                                            <span>{formatNumber(tx.token0.amount)} {tx.token0.symbol}</span>
                                            <span className="tx-plus">+</span>
                                            <span>{formatNumber(tx.token1.amount)} {tx.token1.symbol}</span>
                                        </>
                                    )}
                                    {tx.type === 'remove_liquidity' && (
                                        <>
                                            <span>{formatNumber(tx.lpBurned)} LP</span>
                                            <span className="tx-arrow">→</span>
                                            <span>{tx.token0.symbol} + {tx.token1.symbol}</span>
                                        </>
                                    )}
                                </div>
                            </div>
                            <div className="tx-time">
                                {formatTimeAgo(tx.timestamp)}
                            </div>
                            <div className="tx-link">
                                🔗
                            </div>
                        </a>
                    ))
                )}
            </div>

            <div className="history-footer">
                <span className="verified-badge">✓ Tau-Verified</span>
                <span className="network-badge">Tau Net Alpha</span>
            </div>
        </div>
    );
}

export default TransactionHistory;
