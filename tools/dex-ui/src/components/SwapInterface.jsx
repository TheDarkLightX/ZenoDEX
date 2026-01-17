import { useState, useMemo, useEffect, useCallback } from 'react';
import { calcSwapOutput, calcPriceImpact, getSpotPrice, formatNumber, formatPercent } from '../lib/cpmm';
import { validateSwap, getSlippageOptions, getPriceImpactSeverity } from '../lib/validation';
import './SwapInterface.css';

// Token data (AGRS is the native Tau Net token)
const TOKENS = [
    { symbol: 'AGRS', name: 'Agoras', icon: '✦', decimals: 18 },
    { symbol: 'USDC', name: 'USD Coin', icon: '💵', decimals: 6 },
    { symbol: 'WETH', name: 'Wrapped ETH', icon: '⟠', decimals: 18 },
];

// Mock pool reserves
const MOCK_POOLS = {
    'AGRS-USDC': { reserve0: 1000000, reserve1: 2500000 },
    'AGRS-WETH': { reserve0: 1000000, reserve1: 500 },
    'USDC-WETH': { reserve0: 2500000, reserve1: 1000 },
};

// Mock user balances
const MOCK_BALANCES = {
    'AGRS': 1234.56,
    'USDC': 5000.00,
    'WETH': 2.5,
};

// Tooltip component
function Tooltip({ text, children }) {
    const [show, setShow] = useState(false);
    return (
        <span
            className="tooltip-container"
            onMouseEnter={() => setShow(true)}
            onMouseLeave={() => setShow(false)}
        >
            {children}
            {show && <span className="tooltip-text">{text}</span>}
        </span>
    );
}

function SwapInterface({ wallet }) {
    const [fromToken, setFromToken] = useState(TOKENS[0]);
    const [toToken, setToToken] = useState(TOKENS[1]);
    const [amountIn, setAmountIn] = useState('');
    const [slippage, setSlippage] = useState(0.005);
    const [showSettings, setShowSettings] = useState(false);
    const [showConfirm, setShowConfirm] = useState(false);
    const [isRefreshing, setIsRefreshing] = useState(false);
    const [lastRefresh, setLastRefresh] = useState(Date.now());

    // Auto-refresh prices every 15 seconds
    useEffect(() => {
        const interval = setInterval(() => {
            setIsRefreshing(true);
            setLastRefresh(Date.now());
            setTimeout(() => setIsRefreshing(false), 500);
        }, 15000);
        return () => clearInterval(interval);
    }, []);

    // Get pool key
    const poolKey = useMemo(() => {
        const sorted = [fromToken.symbol, toToken.symbol].sort();
        return `${sorted[0]}-${sorted[1]}`;
    }, [fromToken, toToken]);

    // Get reserves (considering direction)
    const reserves = useMemo(() => {
        const pool = MOCK_POOLS[poolKey];
        if (!pool) return null;
        const isForward = [fromToken.symbol, toToken.symbol].sort()[0] === fromToken.symbol;
        return isForward
            ? { reserveIn: pool.reserve0, reserveOut: pool.reserve1 }
            : { reserveIn: pool.reserve1, reserveOut: pool.reserve0 };
    }, [poolKey, fromToken, toToken]);

    // Get user balance for from token
    const fromBalance = wallet ? (MOCK_BALANCES[fromToken.symbol] || 0) : 0;
    const toBalance = wallet ? (MOCK_BALANCES[toToken.symbol] || 0) : 0;

    // Calculate output and price impact
    const swapPreview = useMemo(() => {
        if (!amountIn || !reserves) return null;
        const input = parseFloat(amountIn);
        if (isNaN(input) || input <= 0) return null;

        const output = calcSwapOutput(reserves.reserveIn, reserves.reserveOut, input);
        const priceImpact = calcPriceImpact(reserves.reserveIn, reserves.reserveOut, input);
        const spotPrice = getSpotPrice(reserves.reserveIn, reserves.reserveOut);
        const minOutput = output * (1 - slippage);

        return { output, priceImpact, spotPrice, minOutput };
    }, [amountIn, reserves, slippage, lastRefresh]);

    // Validation with helpful messages
    const validation = useMemo(() => {
        if (!amountIn) return { ok: false, error: '' };
        const input = parseFloat(amountIn);

        if (isNaN(input) || input <= 0) {
            return { ok: false, error: 'Enter a valid amount' };
        }

        if (wallet && input > fromBalance) {
            return { ok: false, error: `Insufficient ${fromToken.symbol} balance` };
        }

        if (!reserves) {
            return { ok: false, error: 'Pool not found' };
        }

        if (!swapPreview) return { ok: false, error: '' };

        return validateSwap({
            amountIn: input,
            amountOut: swapPreview.output,
            reserveIn: reserves.reserveIn,
            reserveOut: reserves.reserveOut,
            maxSlippage: slippage,
            priceImpact: swapPreview.priceImpact,
        });
    }, [amountIn, reserves, swapPreview, slippage, wallet, fromBalance, fromToken.symbol]);

    // Auto-calculate optimal slippage based on liquidity
    const suggestedSlippage = useMemo(() => {
        if (!swapPreview) return 0.005;
        if (swapPreview.priceImpact > 0.05) return 0.03;
        if (swapPreview.priceImpact > 0.01) return 0.01;
        return 0.005;
    }, [swapPreview]);

    const handleSwapTokens = () => {
        setFromToken(toToken);
        setToToken(fromToken);
        setAmountIn('');
    };

    const handleMaxAmount = () => {
        if (wallet && fromBalance > 0) {
            // Leave a small amount for gas if native token
            const maxAmount = fromToken.symbol === 'AGRS'
                ? Math.max(0, fromBalance - 0.01)
                : fromBalance;
            setAmountIn(maxAmount.toString());
        }
    };

    const handleSwapClick = () => {
        if (!validation.ok || !wallet) return;

        // Show confirmation for high-impact swaps (poka-yoke)
        if (swapPreview && swapPreview.priceImpact > 0.01) {
            setShowConfirm(true);
        } else {
            executeSwap();
        }
    };

    const executeSwap = useCallback(() => {
        setShowConfirm(false);
        // In production, this would submit to the P2P network
        alert(`✓ Swap submitted!\n\n${amountIn} ${fromToken.symbol} → ${formatNumber(swapPreview.output)} ${toToken.symbol}`);
        setAmountIn('');
    }, [amountIn, fromToken, toToken, swapPreview]);

    const getButtonText = () => {
        if (!wallet) return 'Connect Wallet';
        if (!amountIn) return 'Enter Amount';
        if (validation.error) return validation.error;
        if (!validation.ok) return 'Invalid Swap';
        return 'Swap';
    };

    const impactSeverity = swapPreview ? getPriceImpactSeverity(swapPreview.priceImpact) : 'low';

    return (
        <div className="swap-panel panel">
            <div className="swap-header">
                <h2>Swap</h2>
                <div className="swap-header-actions">
                    <span className={`refresh-indicator ${isRefreshing ? 'active' : ''}`} title="Prices refresh every 15s">
                        🔄
                    </span>
                    <button
                        className="settings-btn"
                        onClick={() => setShowSettings(!showSettings)}
                        title="Transaction settings"
                    >
                        ⚙️
                    </button>
                </div>
            </div>

            {showSettings && (
                <div className="settings-panel animate-slide-up">
                    <div className="settings-row">
                        <span className="label">
                            <Tooltip text="Maximum price movement you're willing to accept">
                                Slippage Tolerance ℹ️
                            </Tooltip>
                        </span>
                        {suggestedSlippage !== slippage && (
                            <button
                                className="suggested-btn"
                                onClick={() => setSlippage(suggestedSlippage)}
                            >
                                Use suggested ({formatPercent(suggestedSlippage)})
                            </button>
                        )}
                    </div>
                    <div className="slippage-options">
                        {getSlippageOptions().map(opt => (
                            <button
                                key={opt.value}
                                className={`slippage-btn ${slippage === opt.value ? 'active' : ''}`}
                                onClick={() => setSlippage(opt.value)}
                            >
                                {opt.label}
                            </button>
                        ))}
                    </div>
                </div>
            )}

            {/* From Token */}
            <div className={`swap-input-container ${validation.error && amountIn ? 'has-error' : ''}`}>
                <div className="swap-input-header">
                    <span className="label">From</span>
                    <span className="balance" onClick={handleMaxAmount} style={{ cursor: wallet ? 'pointer' : 'default' }}>
                        Balance: {wallet ? formatNumber(fromBalance) : '-'}
                        {wallet && fromBalance > 0 && <span className="max-label"> (MAX)</span>}
                    </span>
                </div>
                <div className="swap-input-row">
                    <input
                        type="number"
                        className="input input-large swap-amount-input"
                        placeholder="0.0"
                        value={amountIn}
                        onChange={(e) => setAmountIn(e.target.value)}
                        min="0"
                        step="any"
                    />
                    <div className="token-selector">
                        <span className="token-icon-small">{fromToken.icon}</span>
                        <span>{fromToken.symbol}</span>
                    </div>
                </div>
                {validation.error && amountIn && (
                    <div className="input-error-hint">{validation.error}</div>
                )}
            </div>

            {/* Swap Direction Button */}
            <div className="swap-direction">
                <button className="swap-direction-btn" onClick={handleSwapTokens} title="Swap tokens">
                    ↕️
                </button>
            </div>

            {/* To Token */}
            <div className="swap-input-container">
                <div className="swap-input-header">
                    <span className="label">To (estimated)</span>
                    <span className="balance">Balance: {wallet ? formatNumber(toBalance) : '-'}</span>
                </div>
                <div className="swap-input-row">
                    <input
                        type="text"
                        className="input input-large swap-amount-input"
                        placeholder="0.0"
                        value={swapPreview ? formatNumber(swapPreview.output) : ''}
                        readOnly
                    />
                    <div className="token-selector">
                        <span className="token-icon-small">{toToken.icon}</span>
                        <span>{toToken.symbol}</span>
                    </div>
                </div>
            </div>

            {/* Swap Details */}
            {swapPreview && (
                <div className="swap-details animate-fade-in">
                    <div className="swap-detail-row">
                        <Tooltip text="Current exchange rate between tokens">
                            <span>Rate</span>
                        </Tooltip>
                        <span>1 {fromToken.symbol} = {formatNumber(swapPreview.spotPrice, 4)} {toToken.symbol}</span>
                    </div>
                    <div className="swap-detail-row">
                        <Tooltip text="Difference between market price and execution price due to trade size">
                            <span>Price Impact</span>
                        </Tooltip>
                        <span className={`impact-${impactSeverity}`}>
                            {formatPercent(swapPreview.priceImpact)}
                            {impactSeverity === 'high' && ' ⚠️'}
                        </span>
                    </div>
                    <div className="swap-detail-row">
                        <Tooltip text="Minimum you'll receive after slippage">
                            <span>Minimum Received</span>
                        </Tooltip>
                        <span>{formatNumber(swapPreview.minOutput)} {toToken.symbol}</span>
                    </div>
                    <div className="swap-detail-row">
                        <Tooltip text="Fee paid to liquidity providers">
                            <span>Fee (0.3%)</span>
                        </Tooltip>
                        <span>{formatNumber(parseFloat(amountIn) * 0.003)} {fromToken.symbol}</span>
                    </div>
                </div>
            )}

            {/* High Impact Warning */}
            {swapPreview && impactSeverity === 'high' && (
                <div className="swap-warning">
                    ⚠️ High price impact! Consider trading a smaller amount or adding liquidity.
                </div>
            )}

            {/* Medium Impact Notice */}
            {swapPreview && impactSeverity === 'medium' && (
                <div className="swap-notice">
                    ℹ️ Moderate price impact ({formatPercent(swapPreview.priceImpact)})
                </div>
            )}

            {/* Swap Button */}
            <button
                className={`btn btn-primary btn-large swap-btn ${impactSeverity === 'high' ? 'btn-warning' : ''}`}
                onClick={handleSwapClick}
                disabled={!wallet || !validation.ok}
            >
                {getButtonText()}
            </button>

            {/* Confirmation Modal (Poka-yoke for high impact swaps) */}
            {showConfirm && (
                <div className="confirm-overlay" onClick={() => setShowConfirm(false)}>
                    <div className="confirm-modal animate-slide-up" onClick={e => e.stopPropagation()}>
                        <h3>⚠️ Confirm Swap</h3>
                        <p>This swap has a <strong className="impact-high">{formatPercent(swapPreview.priceImpact)}</strong> price impact.</p>
                        <div className="confirm-details">
                            <div className="confirm-row">
                                <span>You pay:</span>
                                <span>{amountIn} {fromToken.symbol}</span>
                            </div>
                            <div className="confirm-row">
                                <span>You receive (min):</span>
                                <span>{formatNumber(swapPreview.minOutput)} {toToken.symbol}</span>
                            </div>
                        </div>
                        <p className="confirm-warning">
                            Are you sure you want to proceed? You may receive significantly less than expected.
                        </p>
                        <div className="confirm-actions">
                            <button className="btn btn-secondary" onClick={() => setShowConfirm(false)}>
                                Cancel
                            </button>
                            <button className="btn btn-primary btn-warning" onClick={executeSwap}>
                                Proceed Anyway
                            </button>
                        </div>
                    </div>
                </div>
            )}

            <div className="swap-footer">
                <span className="verified-badge">✓ Tau-Verified</span>
                <span className="network-badge">Tau Net Alpha</span>
            </div>
        </div>
    );
}

export default SwapInterface;
