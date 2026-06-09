import { createContext, useCallback, useContext, useEffect, useMemo, useState } from 'react';
import { apiGetAccountHistory } from './api.js';

const TransactionCenterContext = createContext({
    transactions: [],
    pendingCount: 0,
    backfilling: false,
    upsertTransaction: () => null,
    removeTransaction: () => {},
    clearSettled: () => {},
    backfillAccount: () => {},
});

function createClientId(prefix = 'tx') {
    const salt = Math.random().toString(16).slice(2, 10);
    return `${prefix}-${Date.now()}-${salt}`;
}

// Mirror App.getInitialWallet(): the only account that survives a reload is the
// one carried in the `walletAddress` URL param. A button-connected wallet lives
// purely in App's local state and is lost on reload (App has no persistence), so
// the URL param is exactly the account whose history must be backfilled.
function readWalletAddressFromUrl() {
    if (typeof window === 'undefined' || !window.location) {
        return '';
    }
    try {
        const raw = String(new URLSearchParams(window.location.search).get('walletAddress') || '').trim();
        if (!/^(0x)?[0-9a-fA-F]{96}$/.test(raw)) {
            return '';
        }
        return raw.toLowerCase().startsWith('0x') ? `0x${raw.slice(2).toLowerCase()}` : `0x${raw.toLowerCase()}`;
    } catch {
        return '';
    }
}

// Map a committed history row from /api/history into the in-memory tx shape.
// Status comes verbatim from the ledger receipt (confirmed/failed/pending) and is
// never upgraded to a confirmation the chain did not make.
function historyEntryToTransaction(entry) {
    if (!entry || typeof entry !== 'object') {
        return null;
    }
    const txHash = typeof entry.tx_hash === 'string' && entry.tx_hash ? entry.tx_hash : '';
    const id = (typeof entry.tx_id === 'string' && entry.tx_id) || txHash;
    if (!id) {
        return null;
    }
    const action = typeof entry.action === 'string' ? entry.action : '';
    const blockMs = Number.isFinite(entry.block_timestamp) ? entry.block_timestamp * 1000 : null;
    const status = entry.status === 'confirmed' || entry.status === 'failed' ? entry.status : 'pending';
    const product = action === 'ADD_LIQUIDITY' || action === 'REMOVE_LIQUIDITY' || action === 'CREATE_POOL'
        ? 'liquidity'
        : 'swap';
    return {
        id,
        status,
        product,
        title: action ? action.replace(/_/g, ' ') : 'Transaction',
        network: 'Tau Net Alpha',
        txHash,
        marketId: typeof entry.pool_id === 'string' ? entry.pool_id : undefined,
        error: typeof entry.error_code === 'string' ? entry.error_code : undefined,
        height: Number.isFinite(entry.height) ? entry.height : undefined,
        backfilled: true,
        createdAt: blockMs,
        updatedAt: blockMs,
    };
}

function normalizeHash(value) {
    return typeof value === 'string' && value ? value.toLowerCase() : '';
}

export function TransactionCenterProvider({ children }) {
    const [transactions, setTransactions] = useState([]);
    // True while a read-only /api/history backfill is in flight. Drives the
    // drawer skeleton and the swap "Refresh status" spinner. It reflects a real
    // network fetch only — it never implies anything about a transaction's status.
    const [backfilling, setBackfilling] = useState(false);

    const upsertTransaction = useCallback((tx) => {
        if (!tx || typeof tx !== 'object') return null;
        const id = String(tx.id || createClientId(tx.product || 'tx'));
        const now = Date.now();

        setTransactions((prev) => {
            const idx = prev.findIndex((item) => item.id === id);
            const existing = idx >= 0 ? prev[idx] : null;
            const next = {
                id,
                status: 'pending',
                product: 'dex',
                network: 'Tau Net Alpha',
                createdAt: existing?.createdAt ?? tx.createdAt ?? now,
                updatedAt: now,
                ...existing,
                ...tx,
            };

            let out;
            if (idx >= 0) {
                out = prev.slice();
                out[idx] = next;
            } else {
                out = [next, ...prev];
            }

            out.sort((a, b) => Number(b.updatedAt || 0) - Number(a.updatedAt || 0));
            return out.slice(0, 120);
        });

        return id;
    }, []);

    // Merge read-only backfilled history with the in-memory session transactions.
    // Dedup key is the committed txHash (so an optimistic entry reconciles with its
    // backfilled twin instead of double-listing), falling back to id. Optimistic
    // (non-backfilled) entries win on conflict so live status/timestamps are kept;
    // we only fill in the canonical txHash/height the session entry may lack.
    const mergeBackfill = useCallback((entries) => {
        if (!Array.isArray(entries) || entries.length === 0) {
            return;
        }
        const mapped = entries
            .map(historyEntryToTransaction)
            .filter((tx) => tx && (tx.id || tx.txHash));
        if (mapped.length === 0) {
            return;
        }

        setTransactions((prev) => {
            const byId = new Map(prev.map((tx) => [tx.id, tx]));
            const byHash = new Map(
                prev.filter((tx) => normalizeHash(tx.txHash)).map((tx) => [normalizeHash(tx.txHash), tx]),
            );

            for (const entry of mapped) {
                const hashKey = normalizeHash(entry.txHash);
                const existing = (hashKey && byHash.get(hashKey)) || byId.get(entry.id) || null;
                if (existing) {
                    // Reconcile: keep the existing (optimistic) row authoritative but
                    // backfill the canonical chain fields it may be missing. A committed
                    // TERMINAL status (confirmed/failed) is chain truth and wins over an
                    // optimistic 'pending' so a known on-chain failure is never hidden.
                    const committedTerminal = entry.status === 'confirmed' || entry.status === 'failed';
                    const adoptStatus = committedTerminal && existing.status === 'pending';
                    const reconciled = {
                        ...existing,
                        txHash: existing.txHash || entry.txHash,
                        height: existing.height ?? entry.height,
                        marketId: existing.marketId ?? entry.marketId,
                        status: adoptStatus ? entry.status : existing.status,
                        error: adoptStatus && entry.error !== undefined ? entry.error : existing.error,
                    };
                    byId.set(existing.id, reconciled);
                    if (hashKey) byHash.set(hashKey, reconciled);
                } else {
                    byId.set(entry.id, entry);
                    if (hashKey) byHash.set(hashKey, entry);
                }
            }

            const out = Array.from(byId.values());
            out.sort((a, b) => Number(b.updatedAt || 0) - Number(a.updatedAt || 0));
            return out.slice(0, 120);
        });
    }, []);

    const backfillAccount = useCallback((accountPubkey) => {
        const account = typeof accountPubkey === 'string' ? accountPubkey.trim() : '';
        if (!/^(0x)?[0-9a-fA-F]{96}$/.test(account)) {
            // Invalid account: nothing to fetch. Leave the flag untouched so a
            // caller can honestly fall back to "status unknown — check history".
            return;
        }
        let cancelled = false;
        // Defer the "in flight" flag out of any synchronous effect-render path so
        // the auto-load effect does not setState during render (cascading-render
        // lint). The fetch is still genuinely in flight; this only reflects that.
        queueMicrotask(() => {
            if (!cancelled) setBackfilling(true);
        });
        apiGetAccountHistory({ account, limit: 50 }, { timeoutMs: 4000 })
            .then((data) => {
                if (cancelled || !data || data.ok !== true || !Array.isArray(data.transactions)) {
                    return;
                }
                mergeBackfill(data.transactions);
            })
            .catch(() => {
                // Fail closed: a backfill error simply leaves the session list intact.
                // No fabricated entries on failure.
            })
            .finally(() => {
                // Only clear the indicator if this invocation is still current; a
                // superseded (cancelled) request must not clear a newer one's flag.
                if (!cancelled) {
                    setBackfilling(false);
                }
            });
        return () => {
            cancelled = true;
        };
    }, [mergeBackfill]);

    // Backfill on initial load and whenever the reload-surviving account changes.
    const urlAccount = readWalletAddressFromUrl();
    useEffect(() => {
        if (!urlAccount) {
            return undefined;
        }
        return backfillAccount(urlAccount);
    }, [urlAccount, backfillAccount]);

    const removeTransaction = useCallback((id) => {
        if (!id) return;
        setTransactions((prev) => prev.filter((tx) => tx.id !== id));
    }, []);

    const clearSettled = useCallback(() => {
        setTransactions((prev) => prev.filter((tx) => tx.status === 'pending'));
    }, []);

    const pendingCount = useMemo(
        () => transactions.reduce((acc, tx) => acc + (tx.status === 'pending' ? 1 : 0), 0),
        [transactions],
    );

    const value = useMemo(() => ({
        transactions,
        pendingCount,
        backfilling,
        upsertTransaction,
        removeTransaction,
        clearSettled,
        backfillAccount,
    }), [transactions, pendingCount, backfilling, upsertTransaction, removeTransaction, clearSettled, backfillAccount]);

    return (
        <TransactionCenterContext.Provider value={value}>
            {children}
        </TransactionCenterContext.Provider>
    );
}

// eslint-disable-next-line react-refresh/only-export-components
export function useTransactionCenter() {
    return useContext(TransactionCenterContext);
}
