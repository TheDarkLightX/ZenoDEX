import { useState } from 'react';
import './WalletConnect.css';
import { getRuntimeConfig } from '../lib/api.js';
import { browserKeyGenerationAllowed, connectPreferredWallet } from '../sdk/walletSignerPolicy.js';

function walletErrorMessage(error) {
    const message = String(error?.message || error || '').trim();
    const lower = message.toLowerCase();
    if (
        lower.includes('failed to fetch')
        || lower.includes('fetch failed')
        || lower.includes('networkerror')
        || lower.includes('connection refused')
        || lower.includes('err_connection_refused')
    ) {
        return 'Local signer unavailable';
    }
    if (message === 'external_signer_unavailable') {
        return 'External signer unavailable';
    }
    return message || 'External signer unavailable';
}

function WalletConnect({ wallet, onConnect }) {
    const [isConnecting, setIsConnecting] = useState(false);
    const [showDropdown, setShowDropdown] = useState(false);
    const [copyFeedback, setCopyFeedback] = useState(false);
    const [connectionError, setConnectionError] = useState('');

    const handleConnect = async () => {
        setIsConnecting(true);
        setConnectionError('');

        try {
            const runtimeConfig = getRuntimeConfig();
            onConnect(await connectPreferredWallet({
                chainId: runtimeConfig.chainId || 'zeno-ledger-localtest-v0',
                globalObject: typeof window === 'undefined' ? globalThis : window,
                runtimeConfig,
                allowBrowserFallback: browserKeyGenerationAllowed({
                    locationSearch: typeof window === 'undefined' ? '' : window.location.search,
                    runtimeConfig,
                    env: import.meta.env,
                }),
            }));
        } catch (error) {
            console.error('Failed to connect wallet:', error);
            setConnectionError(walletErrorMessage(error));
        } finally {
            setIsConnecting(false);
        }
    };

    const handleDisconnect = () => {
        onConnect(null);
        setShowDropdown(false);
    };

    const handleCopyAddress = () => {
        try {
            navigator.clipboard.writeText(wallet.address);
            setCopyFeedback(true);
            setTimeout(() => setCopyFeedback(false), 2000);
        } catch {
            // Ignore clipboard failures (browser permission / insecure context).
        }
    };

    // Truncate BLS address for display (show first 8 and last 6 chars)
    const truncateAddress = (address) => {
        if (!address) return '';
        return `${address.slice(0, 8)}...${address.slice(-6)}`;
    };

    const formatBalanceOrNA = (value) => {
        const n = Number(value);
        return Number.isFinite(n) ? n.toLocaleString() : 'N/A';
    };

    if (wallet) {
        return (
            <div className="wallet-container">
                <button
                    className="wallet-button connected"
                    onClick={() => setShowDropdown(!showDropdown)}
                    aria-label={`Wallet connected: ${truncateAddress(wallet.address)}. Click for details.`}
                    aria-expanded={showDropdown}
                    aria-haspopup="menu"
                    type="button"
                >
                    <span className="wallet-status-dot" aria-hidden="true"></span>
                    <span className="wallet-address">{truncateAddress(wallet.address)}</span>
                    <span className="wallet-chevron" aria-hidden="true">▾</span>
                </button>

                {showDropdown && (
                    <div className="wallet-dropdown animate-fade-in" role="menu" aria-label="Wallet menu">
                        <div className="dropdown-header">
                            <span className="connected-badge">
                                <span className="connected-dot"></span>
                                {wallet.browserLastResort ? 'Browser fallback signer' : 'External signer'}
                            </span>
                        </div>

                        <div className="dropdown-section">
                            <div className="dropdown-item">
                                <span className="item-label">Address</span>
                                <span className="item-value mono">{truncateAddress(wallet.address)}</span>
                            </div>

                            <div className="dropdown-item">
                                <span className="item-label">ZDEX Balance</span>
                                <span className="item-value">{formatBalanceOrNA(wallet.balance?.ZDEX)} ⚡</span>
                            </div>

                            <div className="dropdown-item">
                                <span className="item-label">zUSD Balance</span>
                                <span className="item-value">{formatBalanceOrNA(wallet.balance?.zUSD)} ◈</span>
                            </div>
                        </div>

                        <div className="dropdown-divider"></div>

                        <button className="dropdown-action" onClick={handleCopyAddress}>
                            {copyFeedback ? '✓ Copied!' : '📋 Copy Address'}
                        </button>

                        <a
                            className="dropdown-action"
                            href="https://explorer.tau.net"
                            target="_blank"
                            rel="noopener noreferrer"
                        >
                            🔍 View on Explorer
                        </a>

                        <div className="dropdown-divider"></div>

                        <button className="dropdown-action disconnect" onClick={handleDisconnect}>
                            ⏏️ Disconnect
                        </button>
                    </div>
                )}
            </div>
        );
    }

    return (
        <div className="wallet-connect-shell">
            <button
                className="btn btn-primary wallet-connect-btn"
                onClick={handleConnect}
                disabled={isConnecting}
                title={connectionError || 'Connect external signer'}
            >
                {isConnecting ? (
                    <>
                        <span className="spinner"></span>
                        Connecting...
                    </>
                ) : (
                    <>
                        <span className="wallet-icon">🔗</span>
                        Connect Wallet
                    </>
                )}
            </button>
            {connectionError && (
                <div className="wallet-connect-error" role="status">
                    {connectionError}
                </div>
            )}
        </div>
    );
}

export default WalletConnect;
