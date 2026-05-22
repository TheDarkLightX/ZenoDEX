import { useState } from 'react';
import './WalletConnect.css';

// Tau Net Alpha uses BLS public keys (96 hex chars = 48 bytes)
function generateMockTauAddress() {
    const chars = '0123456789abcdef';
    return Array.from({ length: 96 }, () => chars[Math.floor(Math.random() * 16)]).join('');
}

function WalletConnect({ wallet, onConnect }) {
    const [isConnecting, setIsConnecting] = useState(false);
    const [showDropdown, setShowDropdown] = useState(false);
    const [copyFeedback, setCopyFeedback] = useState(false);

    const handleConnect = async () => {
        setIsConnecting(true);

        try {
            // Simulate wallet connection delay
            await new Promise(resolve => setTimeout(resolve, 1500));

            // Generate Tau Net Alpha compatible address (BLS public key format)
            const address = generateMockTauAddress();

            onConnect({
                address,
                chainId: 'tau-alpha',
                balance: {
                    AGRS: 1234.56,
                    ZDEX: 5000,
                    USD: 10000,
                    TASSET0: 1_000_000,
                    TASSET1: 1_000_000,
                    TZENO: 1_000_000,
                },
            });
        } catch (error) {
            console.error('Failed to connect wallet:', error);
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

    if (wallet) {
        return (
            <div className="wallet-container">
                <button
                    className="wallet-button connected"
                    onClick={() => setShowDropdown(!showDropdown)}
                >
                    <span className="wallet-status-dot"></span>
                    <span className="wallet-address">{truncateAddress(wallet.address)}</span>
                    <span className="wallet-chevron">▾</span>
                </button>

                {showDropdown && (
                    <div className="wallet-dropdown animate-fade-in">
                        <div className="dropdown-header">
                            <span className="connected-badge">
                                <span className="connected-dot"></span>
                                Tau Net Alpha
                            </span>
                        </div>

                        <div className="dropdown-section">
                            <div className="dropdown-item">
                                <span className="item-label">Address</span>
                                <span className="item-value mono">{truncateAddress(wallet.address)}</span>
                            </div>

                            <div className="dropdown-item">
                                <span className="item-label">AGRS Balance</span>
                                <span className="item-value">{wallet.balance?.AGRS?.toLocaleString() || 0} ✦</span>
                            </div>

                            <div className="dropdown-item">
                                <span className="item-label">ZDEX Balance</span>
                                <span className="item-value">{wallet.balance?.ZDEX?.toLocaleString() || 0} ⚡</span>
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
        <button
            className="btn btn-primary wallet-connect-btn"
            onClick={handleConnect}
            disabled={isConnecting}
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
    );
}

export default WalletConnect;
