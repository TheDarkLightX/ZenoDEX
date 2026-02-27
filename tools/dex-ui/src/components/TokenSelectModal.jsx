import { useState, useMemo } from 'react';
import { formatNumber } from '../lib/cpmm';
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

// Default available tokens
const DEFAULT_TOKENS = [
    { symbol: 'AGRS', name: 'Agoras', icon: '✦', decimals: 18, address: '0x0000...native' },
    { symbol: 'USDC', name: 'USD Coin', icon: '💵', decimals: 6, address: '0x1234...5678' },
    { symbol: 'WETH', name: 'Wrapped ETH', icon: '⟠', decimals: 18, address: '0x2345...6789' },
    { symbol: 'ZDEX', name: 'ZenoDEX Token', icon: '⚡', decimals: 18, address: '0x3456...7890' },
    { symbol: 'DAI', name: 'Dai Stablecoin', icon: '◈', decimals: 18, address: '0x5678...9012' },
];

// Mock balances (in production, fetch from wallet)
const MOCK_BALANCES = {
    'AGRS': 1234.56,
    'USDC': 5000.00,
    'WETH': 2.5,
    'ZDEX': 10000,
    'DAI': 2500,
};

function TokenSelectModal({
    isOpen,
    onClose,
    onSelect,
    excludeToken,
    wallet,
    customTokens = [],
    onImportToken
}) {
    const [searchQuery, setSearchQuery] = useState('');
    const [importAddress, setImportAddress] = useState('');
    const [importError, setImportError] = useState('');
    const [showImport, setShowImport] = useState(false);

    // Combine default and custom tokens
    const allTokens = useMemo(() => {
        return [...DEFAULT_TOKENS, ...customTokens];
    }, [customTokens]);

    // Filter tokens based on search query
    const filteredTokens = useMemo(() => {
        const query = searchQuery.toLowerCase().trim();
        if (!query) return allTokens;

        return allTokens.filter(token =>
            token.symbol.toLowerCase().includes(query) ||
            token.name.toLowerCase().includes(query) ||
            token.address.toLowerCase().includes(query)
        );
    }, [allTokens, searchQuery]);

    // Get balance for a token
    const getBalance = (symbol) => {
        if (!wallet) return null;
        return MOCK_BALANCES[symbol] ?? 0;
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

        // Basic address validation (in production, validate on-chain)
        if (!/^0x[a-fA-F0-9]{40}$/.test(importAddress.trim()) &&
            !importAddress.includes('...')) {
            setImportError('Invalid contract address format');
            return;
        }

        // Check if already exists
        const exists = allTokens.some(t =>
            t.address.toLowerCase() === importAddress.toLowerCase()
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
                            <button
                                className="import-link"
                                onClick={() => setShowImport(true)}
                            >
                                Import custom token
                            </button>
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
                    {!showImport ? (
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
            </div>
        </div>
    );
}

export default TokenSelectModal;
export { DEFAULT_TOKENS };
