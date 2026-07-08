import { useMemo, useState, useRef } from 'react';
import { useTransactionCenter } from '../lib/TransactionCenterContext.jsx';
import { useKeyboardShortcuts } from '../lib/useKeyboardShortcuts.js';
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
    const drawerRef = useRef(null);
    const {
        transactions,
        pendingCount,
        removeTransaction,
        clearSettled,
    } = useTransactionCenter();

    const visible = useMemo(() => transactions.slice(0, 14), [transactions]);

    // Close on Escape when open
    useKeyboardShortcuts({
        escape: () => setOpen(false),
    }, { enabled: open });

    return (
        <div className={`tx-drawer-shell ${open ? 'open' : ''}`}>
            <button
                type="button"
                className="tx-drawer-toggle"
                onClick={() => setOpen((prev) => !prev)}
                title="Open transaction center"
                aria-label={`Transaction activity ${pendingCount > 0 ? `(${pendingCount} pending)` : ''}`}
                aria-expanded={open}
                aria-controls="tx-drawer-panel"
            >
                <span>Activity</span>
                {pendingCount > 0 && <span className="tx-pending-pill" aria-label={`${pendingCount} pending`}>{pendingCount}</span>}
            </button>

            {open && (
                <aside
                    ref={drawerRef}
                    id="tx-drawer-panel"
                    className="tx-drawer panel animate-slide-up"
                    aria-label="Transaction activity"
                    role="complementary"
                >
                    <div className="tx-drawer-header">
                        <h3>Transaction Activity</h3>
                        <button
                            type="button"
                            className="tx-clear-btn"
                            onClick={clearSettled}
                            aria-label="Clear settled transactions"
                        >
                            Clear Settled
                        </button>
                    </div>

                    {visible.length === 0 ? (
                        <div className="tx-empty">No transactions yet.</div>
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
                                        {tx.error && <div className="tx-line tx-error">Reason: {tx.error}</div>}
                                        {tx.txHash && (
                                            <div className="tx-line tx-hash-line">
                                                <span className="mono">{shortHash(tx.txHash)}</span>
                                                <a
                                                    className="tx-link-btn"
                                                    href={`https://explorer.tau.net/tx/${tx.txHash}`}
                                                    target="_blank"
                                                    rel="noopener noreferrer"
                                                >
                                                    Explorer
                                                </a>
                                            </div>
                                        )}
                                    </div>

                                    <div className="tx-item-foot">
                                        <span>{tx.network || 'Tau Net Alpha'}</span>
                                        <button
                                            type="button"
                                            className="tx-dismiss-btn"
                                            onClick={() => removeTransaction(tx.id)}
                                            aria-label={`Dismiss transaction ${tx.title || tx.id}`}
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
