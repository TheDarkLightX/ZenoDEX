import { useMemo, useState } from 'react';
import { useTransactionCenter } from '../lib/TransactionCenterContext.jsx';
import { getRuntimeConfig } from '../lib/api.js';
import { buildExplorerTxUrl, humanizeErrorCode } from '../sdk/txStatusView.js';
import './TransactionDrawer.css';

function formatAge(timestamp) {
    const delta = Math.max(0, Math.floor((Date.now() - Number(timestamp || 0)) / 1000));
    if (delta < 10) return 'just now';
    if (delta < 60) return `${delta}s`;
    if (delta < 3600) return `${Math.floor(delta / 60)}m`;
    if (delta < 86400) return `${Math.floor(delta / 3600)}h`;
    return `${Math.floor(delta / 86400)}d`;
}

function shortHash(hash) {
    if (!hash || typeof hash !== 'string') return '--';
    return `${hash.slice(0, 10)}...${hash.slice(-8)}`;
}

function statusLabel(status) {
    if (status === 'confirmed') return 'Confirmed';
    if (status === 'failed') return 'Failed';
    return 'Pending';
}

function TransactionDrawer() {
    const [open, setOpen] = useState(false);
    const {
        transactions,
        pendingCount,
        backfilling,
        removeTransaction,
        clearSettled,
    } = useTransactionCenter();

    const visible = useMemo(() => transactions.slice(0, 14), [transactions]);
    // Show a skeleton only when we are genuinely fetching and have nothing yet;
    // once any rows exist we render them and let the backfill reconcile in place.
    const showSkeleton = backfilling && visible.length === 0;

    return (
        <div className={`tx-drawer-shell ${open ? 'open' : ''}`}>
            <button
                type="button"
                className="tx-drawer-toggle"
                onClick={() => setOpen((prev) => !prev)}
                title="Open transaction center"
            >
                <span>Activity</span>
                {pendingCount > 0 && <span className="tx-pending-pill">{pendingCount}</span>}
            </button>

            {open && (
                <aside className="tx-drawer panel animate-slide-up" aria-label="Transaction activity">
                    <div className="tx-drawer-header">
                        <h3>Transaction Activity</h3>
                        <button type="button" className="tx-clear-btn" onClick={clearSettled}>
                            Clear Settled
                        </button>
                    </div>

                    {showSkeleton ? (
                        <div className="tx-list" aria-busy="true" aria-label="Loading transaction history">
                            {[0, 1, 2].map((row) => (
                                <article key={`skeleton-${row}`} className="tx-item tx-item-skeleton" aria-hidden="true">
                                    <div className="tx-item-head">
                                        <div className="tx-title-wrap">
                                            <span className="tx-skeleton-line tx-skeleton-title" />
                                            <span className="tx-skeleton-line tx-skeleton-sub" />
                                        </div>
                                        <span className="tx-skeleton-line tx-skeleton-badge" />
                                    </div>
                                    <div className="tx-item-body">
                                        <span className="tx-skeleton-line tx-skeleton-body" />
                                    </div>
                                </article>
                            ))}
                        </div>
                    ) : visible.length === 0 ? (
                        <div className="tx-empty">
                            <p className="tx-empty-title">No recent transactions for this wallet</p>
                            <p className="tx-empty-hint">
                                Swaps and liquidity actions you submit will appear here, and any
                                committed history for the connected wallet is loaded automatically.
                            </p>
                        </div>
                    ) : (
                        <div className="tx-list">
                            {visible.map((tx) => (
                                <article key={tx.id} className={`tx-item status-${tx.status || 'pending'}`}>
                                    <div className="tx-item-head">
                                        <div className="tx-title-wrap">
                                            <div className="tx-title">{tx.title || 'Transaction'}</div>
                                            <div className="tx-subtitle">
                                                {(tx.product || 'dex').toUpperCase()} • {formatAge(tx.updatedAt || tx.createdAt)}
                                            </div>
                                        </div>
                                        <span className={`tx-drawer-status ${tx.status || 'pending'}`}>
                                            {statusLabel(tx.status)}
                                        </span>
                                    </div>

                                    <div className="tx-item-body">
                                        {tx.marketId && <div className="tx-line">Market: {tx.marketId}</div>}
                                        {tx.routePath && <div className="tx-line">Route: {tx.routePath}</div>}
                                        {tx.error && (() => {
                                            const human = humanizeErrorCode(tx.error);
                                            // Always keep the raw machine code visible; the human
                                            // line is a best-effort gloss, never a replacement.
                                            return (
                                                <div className="tx-line tx-error">
                                                    {human && <span className="tx-error-human">{human}</span>}
                                                    <span className="tx-error-code mono">{tx.error}</span>
                                                </div>
                                            );
                                        })()}
                                        {tx.txHash && (() => {
                                            const explorerUrl = buildExplorerTxUrl(getRuntimeConfig(), tx.txHash);
                                            return (
                                                <div className="tx-line tx-hash-line">
                                                    <span className="mono">{shortHash(tx.txHash)}</span>
                                                    {explorerUrl && (
                                                        <a
                                                            className="tx-link-btn"
                                                            href={explorerUrl}
                                                            target="_blank"
                                                            rel="noopener noreferrer"
                                                        >
                                                            Explorer
                                                        </a>
                                                    )}
                                                </div>
                                            );
                                        })()}
                                    </div>

                                    <div className="tx-item-foot">
                                        <span>{tx.network || 'Tau Net Alpha'}</span>
                                        <button
                                            type="button"
                                            className="tx-dismiss-btn"
                                            onClick={() => removeTransaction(tx.id)}
                                        >
                                            Dismiss
                                        </button>
                                    </div>
                                </article>
                            ))}
                        </div>
                    )}
                </aside>
            )}
        </div>
    );
}

export default TransactionDrawer;
