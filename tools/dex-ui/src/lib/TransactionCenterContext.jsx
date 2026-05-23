import { createContext, useCallback, useContext, useMemo, useState } from 'react';

const TransactionCenterContext = createContext({
    transactions: [],
    pendingCount: 0,
    upsertTransaction: () => null,
    removeTransaction: () => {},
    clearSettled: () => {},
});

function createClientId(prefix = 'tx') {
    const salt = Math.random().toString(16).slice(2, 10);
    return `${prefix}-${Date.now()}-${salt}`;
}

export function TransactionCenterProvider({ children }) {
    const [transactions, setTransactions] = useState([]);

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
        upsertTransaction,
        removeTransaction,
        clearSettled,
    }), [transactions, pendingCount, upsertTransaction, removeTransaction, clearSettled]);

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
