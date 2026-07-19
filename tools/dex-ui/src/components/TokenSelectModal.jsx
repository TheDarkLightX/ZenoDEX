import { useState, useMemo } from 'react';
import { formatNumber } from '../lib/cpmm';
import './TokenSelectModal.css';

/**
 * TokenSelectModal - Modal for selecting tokens in swap interface
 * 
 * Features:
 * - Search/filter tokens by symbol or name
 * - Display token balances when wallet connected
 * - Prevent selecting same token for both sides
 */

function TokenSelectModal({
    isOpen,
    onClose,
    onSelect,
    excludeToken,
    wallet,
    availableTokens = null,
}) {
    const [searchQuery, setSearchQuery] = useState('');

    const allTokens = useMemo(() => {
        return Array.isArray(availableTokens) ? availableTokens : [];
    }, [availableTokens]);

    // Filter tokens based on search query
    const filteredTokens = useMemo(() => {
        const query = searchQuery.toLowerCase().trim();
        if (!query) return allTokens;

        return allTokens.filter(token =>
            String(token.symbol || '').toLowerCase().includes(query) ||
            String(token.name || '').toLowerCase().includes(query) ||
            String(token.address || token.assetId || token.asset_id || '').toLowerCase().includes(query)
        );
    }, [allTokens, searchQuery]);

    // Get balance for a token from the connected wallet.
    const getBalance = (symbol) => {
        if (!wallet) return null;
        const balances = wallet.balance || {};
        const candidates = [symbol, symbol?.toUpperCase?.(), symbol?.toLowerCase?.()];
        for (const key of candidates) {
            if (key && key in balances) {
                const v = Number(balances[key]);
                if (Number.isFinite(v)) return v;
            }
        }
        return 0;
    };

    // Handle token selection
    const handleSelect = (token) => {
        if (token.symbol === excludeToken?.symbol) return;
        onSelect(token);
        onClose();
        setSearchQuery('');
    };

    if (!isOpen) return null;

    return (
        <div className="token-modal-overlay" onClick={onClose}>
            <div
                className="token-modal animate-slide-up"
                onClick={e => e.stopPropagation()}
            >
                <div className="token-modal-header">
                    <h3>Select Token</h3>
                    <button className="modal-close-btn" onClick={onClose}>
                        ✕
                    </button>
                </div>

                <div className="token-search-container">
                    <input
                        type="text"
                        className="token-search-input"
                        placeholder="Search by name or paste address"
                        value={searchQuery}
                        onChange={(e) => setSearchQuery(e.target.value)}
                        autoFocus
                    />
                </div>

                <div className="token-list">
                    {filteredTokens.length === 0 ? (
                        <div className="token-list-empty">
                            <span>No tokens found</span>
                            <span>Only assets returned by the live pool API can be selected.</span>
                        </div>
                    ) : (
                        filteredTokens.map(token => {
                            const isExcluded = token.symbol === excludeToken?.symbol;
                            const balance = getBalance(token.symbol);

                            return (
                                <button
                                    key={token.symbol}
                                    className={`token-list-item ${isExcluded ? 'excluded' : ''}`}
                                    onClick={() => handleSelect(token)}
                                    disabled={isExcluded}
                                >
                                    <div className="token-item-left">
                                        <span className="token-item-icon">{token.icon}</span>
                                        <div className="token-item-info">
                                            <span className="token-item-symbol">{token.symbol}</span>
                                            <span className="token-item-name">{token.name}</span>
                                        </div>
                                    </div>
                                    <div className="token-item-right">
                                        {balance !== null && (
                                            <span className="token-item-balance">
                                                {formatNumber(balance)}
                                            </span>
                                        )}
                                    </div>
                                </button>
                            );
                        })
                    )}
                </div>
            </div>
        </div>
    );
}

export default TokenSelectModal;
