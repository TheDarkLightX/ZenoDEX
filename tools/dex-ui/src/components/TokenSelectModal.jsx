import { useState, useMemo } from 'react';
import { formatNumber } from '../lib/cpmm';
import Modal from './Modal.jsx';
import './TokenSelectModal.css';

/**
 * TokenSelectModal - Modal for selecting tokens in swap interface
 * 
 * Features:
 * - Search/filter tokens by symbol or name
 * - Display token balances when wallet connected
 * - Import custom tokens by contract address
 * - Prevent selecting same token for both sides
 */

// Default tokens — matches the local testnet asset set.
// Pool / asset IDs come from /api/pools at runtime, not from this list.
const DEFAULT_TOKENS = [
    { symbol: 'ZDEX', name: 'ZenoDEX', icon: '⚡', decimals: 18, address: 'native' },
    { symbol: 'zUSD', name: 'ZenoUSD', icon: '◈', decimals: 18, address: 'native' },
    { symbol: 'tAGRS', name: 'Test Agoras', icon: '✦', decimals: 18, address: 'native' },
    { symbol: 'TASSET0', name: 'Test Asset 0', icon: 'T₀', decimals: 18, address: 'native' },
    { symbol: 'TASSET1', name: 'Test Asset 1', icon: 'T₁', decimals: 18, address: 'native' },
    { symbol: 'TZENO', name: 'Test Zeno', icon: 'TZ', decimals: 18, address: 'native' },
];

function TokenSelectModal({
    isOpen,
    onClose,
    onSelect,
    excludeToken,
    wallet,
    availableTokens = null,
    customTokens = [],
    onImportToken,
    allowImportCustom = true,
    importUnavailableText = 'Custom token import is unavailable in live mode. Create or fund a pool from the Liquidity tab with a canonical asset ID.'
}) {
    const [searchQuery, setSearchQuery] = useState('');
    const [importAddress, setImportAddress] = useState('');
    const [importError, setImportError] = useState('');
    const [showImport, setShowImport] = useState(false);

    // Live mode passes the token list from /api/pools. Demo mode falls back to
    // the local reference set and optional custom imports.
    const allTokens = useMemo(() => {
        const base = Array.isArray(availableTokens) && availableTokens.length > 0
            ? availableTokens
            : DEFAULT_TOKENS;
        return [...base, ...customTokens];
    }, [availableTokens, customTokens]);

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

    // Handle custom token import
    const handleImport = () => {
        if (!importAddress.trim()) {
            setImportError('Enter a contract address');
            return;
        }
        if (!allowImportCustom) {
            setImportError(importUnavailableText);
            return;
        }

        // Basic address validation (in production, validate on-chain)
        if (!/^0x[a-fA-F0-9]{40}$/.test(importAddress.trim()) &&
            !importAddress.includes('...')) {
            setImportError('Invalid contract address format');
            return;
        }

        // Check if already exists
        const exists = allTokens.some(t =>
            String(t.address || t.assetId || t.asset_id || '').toLowerCase() === importAddress.toLowerCase()
        );
        if (exists) {
            setImportError('Token already in list');
            return;
        }

        // In production, fetch token metadata from chain
        // For demo, create a placeholder token
        const newToken = {
            symbol: 'CUSTOM',
            name: 'Custom Token',
            icon: '🪙',
            decimals: 18,
            address: importAddress.trim(),
            isCustom: true,
        };

        if (onImportToken) {
            onImportToken(newToken);
        }

        setImportAddress('');
        setImportError('');
        setShowImport(false);
    };

    if (!isOpen) return null;

    return (
        <Modal open onClose={onClose} title="Select Token" size="md">
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
                            <button
                                className="import-link"
                                onClick={() => {
                                    if (allowImportCustom) {
                                        setShowImport(true);
                                    } else {
                                        setImportError(importUnavailableText);
                                    }
                                }}
                            >
                                {allowImportCustom ? 'Import custom token' : 'Create pool in Liquidity'}
                            </button>
                            {!allowImportCustom && importError && (
                                <span className="import-error">{importError}</span>
                            )}
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
                                        {token.isCustom && (
                                            <span className="token-custom-badge">Custom</span>
                                        )}
                                    </div>
                                </button>
                            );
                        })
                    )}
                </div>

                {/* Import Custom Token Section */}
                <div className="token-import-section">
                    {!allowImportCustom ? (
                        <div className="token-import-unavailable" role="status">
                            {importUnavailableText}
                        </div>
                    ) : !showImport ? (
                        <button
                            className="import-toggle-btn"
                            onClick={() => setShowImport(true)}
                        >
                            + Import Custom Token
                        </button>
                    ) : (
                        <div className="import-form">
                            <input
                                type="text"
                                className="import-address-input"
                                placeholder="Token contract address (0x...)"
                                value={importAddress}
                                onChange={(e) => {
                                    setImportAddress(e.target.value);
                                    setImportError('');
                                }}
                            />
                            {importError && (
                                <span className="import-error">{importError}</span>
                            )}
                            <div className="import-actions">
                                <button
                                    className="btn btn-secondary"
                                    onClick={() => {
                                        setShowImport(false);
                                        setImportAddress('');
                                        setImportError('');
                                    }}
                                >
                                    Cancel
                                </button>
                                <button
                                    className="btn btn-primary"
                                    onClick={handleImport}
                                >
                                    Import
                                </button>
                            </div>
                        </div>
                    )}
                </div>
        </Modal>
    );
}

export default TokenSelectModal;
export { DEFAULT_TOKENS };
