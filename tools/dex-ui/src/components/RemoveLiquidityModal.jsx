import { useState, useMemo, useCallback } from 'react';
import { calcLpTokensBurn, formatNumber, formatPercent } from '../lib/cpmm';
import { validateRemoveLiquidity } from '../lib/validation';
import Modal from './Modal.jsx';
import './RemoveLiquidityModal.css';

/**
 * RemoveLiquidityModal - Poka-yoke modal for removing liquidity from a pool
 * Features:
 * - LP token slider with 25%/50%/75%/MAX presets
 * - Preview of tokens received
 * - Slippage protection
 * - Confirmation for full removal
 */
function RemoveLiquidityModal({ pool, wallet, lpBalance = 0, onClose, onSubmit }) {
    const [lpAmount, setLpAmount] = useState('');
    const [slippage, setSlippage] = useState(0.005);
    const [showConfirm, setShowConfirm] = useState(false);
    const [typedConfirmText, setTypedConfirmText] = useState('');

    // Pool data
    const { token0, token1, reserve0, reserve1, totalLpSupply = 1000000 } = pool;

    // Calculate percentage of LP tokens
    const lpPercent = useMemo(() => {
        if (!lpBalance || lpBalance <= 0) return 0;
        const amt = parseFloat(lpAmount) || 0;
        return amt / lpBalance;
    }, [lpAmount, lpBalance]);

    // Calculate tokens to receive
    const preview = useMemo(() => {
        const amt = parseFloat(lpAmount) || 0;
        if (amt <= 0) return null;

        const { amount0, amount1 } = calcLpTokensBurn(amt, reserve0, reserve1, totalLpSupply);
        const minAmount0 = amount0 * (1 - slippage);
        const minAmount1 = amount1 * (1 - slippage);

        return {
            amount0,
            amount1,
            minAmount0,
            minAmount1,
        };
    }, [lpAmount, reserve0, reserve1, totalLpSupply, slippage]);

    // Validation
    const validation = useMemo(() => {
        const amt = parseFloat(lpAmount) || 0;
        return validateRemoveLiquidity({
            lpAmount: amt,
            lpBalance,
        });
    }, [lpAmount, lpBalance]);

    // Preset buttons
    const handlePreset = useCallback((percent) => {
        if (!lpBalance || lpBalance <= 0) return;
        const amount = lpBalance * percent;
        setLpAmount(amount.toFixed(6));
    }, [lpBalance]);

    // Handle slider change
    const handleSlider = useCallback((e) => {
        const percent = parseFloat(e.target.value) / 100;
        const amount = lpBalance * percent;
        setLpAmount(amount.toFixed(6));
    }, [lpBalance]);

    const handleSubmit = useCallback(() => {
        setShowConfirm(false);
        setTypedConfirmText('');
        onSubmit?.({
            pool,
            lpAmount: parseFloat(lpAmount),
            expectedAmount0: preview?.amount0,
            expectedAmount1: preview?.amount1,
            minAmount0: preview?.minAmount0,
            minAmount1: preview?.minAmount1,
        });
        onClose();
    }, [lpAmount, preview, pool, onSubmit, onClose]);

    // Submit handler
    const handleRemoveClick = useCallback(() => {
        if (!validation.ok) return;

        // Confirm for full removal (>95%)
        if (lpPercent > 0.95) {
            setTypedConfirmText('');
            setShowConfirm(true);
        } else {
            handleSubmit();
        }
    }, [validation.ok, lpPercent, handleSubmit]);

    const getButtonText = () => {
        if (!wallet) return 'Connect Wallet';
        if (lpBalance <= 0) return 'No LP Tokens';
        if (!lpAmount || parseFloat(lpAmount) <= 0) return 'Enter Amount';
        if (validation.error) return validation.error;
        return 'Remove Liquidity';
    };

    return (
        <Modal open onClose={onClose} title="Remove Liquidity" size="md">
            <div className="modal-body">
                    {/* Pool Info */}
                    <div className="pool-info-banner">
                        <span className="pool-icons">
                            {token0.icon} {token1.icon}
                        </span>
                        <span className="pool-name">{token0.symbol} / {token1.symbol}</span>
                    </div>

                    {/* LP Balance */}
                    <div className="lp-balance-card">
                        <div className="lp-balance-label">Your LP Balance</div>
                        <div className="lp-balance-value">{formatNumber(lpBalance)} LP</div>
                    </div>

                    {/* Amount to Remove */}
                    <div className="remove-amount-section">
                        <div className="remove-header">
                            <span>Amount to Remove</span>
                            <span className="remove-percent">{formatPercent(lpPercent)}</span>
                        </div>

                        {/* Slider */}
                        <input
                            type="range"
                            className="lp-slider"
                            min="0"
                            max="100"
                            value={Math.round(lpPercent * 100)}
                            onChange={handleSlider}
                            disabled={!lpBalance || lpBalance <= 0}
                        />

                        {/* Presets */}
                        <div className="preset-buttons">
                            <button
                                className={`preset-btn ${lpPercent === 0.25 ? 'active' : ''}`}
                                onClick={() => handlePreset(0.25)}
                                disabled={!lpBalance}
                            >
                                25%
                            </button>
                            <button
                                className={`preset-btn ${lpPercent === 0.5 ? 'active' : ''}`}
                                onClick={() => handlePreset(0.5)}
                                disabled={!lpBalance}
                            >
                                50%
                            </button>
                            <button
                                className={`preset-btn ${lpPercent === 0.75 ? 'active' : ''}`}
                                onClick={() => handlePreset(0.75)}
                                disabled={!lpBalance}
                            >
                                75%
                            </button>
                            <button
                                className={`preset-btn ${lpPercent >= 0.99 ? 'active' : ''}`}
                                onClick={() => handlePreset(1)}
                                disabled={!lpBalance}
                            >
                                MAX
                            </button>
                        </div>

                        {/* Input */}
                        <div className="lp-input-row">
                            <input
                                type="number"
                                className="input input-lp"
                                placeholder="0.0"
                                value={lpAmount}
                                onChange={e => setLpAmount(e.target.value)}
                                min="0"
                                max={lpBalance}
                                step="any"
                            />
                            <span className="lp-suffix">LP Tokens</span>
                        </div>
                    </div>

                    {/* Preview */}
                    {preview && (
                        <div className="receive-preview animate-fade-in">
                            <div className="preview-title">You Will Receive</div>
                            <div className="receive-row">
                                <span className="token-icon">{token0.icon}</span>
                                <span className="receive-amount">{formatNumber(preview.amount0)}</span>
                                <span className="receive-symbol">{token0.symbol}</span>
                            </div>
                            <div className="receive-row">
                                <span className="token-icon">{token1.icon}</span>
                                <span className="receive-amount">{formatNumber(preview.amount1)}</span>
                                <span className="receive-symbol">{token1.symbol}</span>
                            </div>
                            <div className="receive-min">
                                Min: {formatNumber(preview.minAmount0)} {token0.symbol} + {formatNumber(preview.minAmount1)} {token1.symbol}
                                <span className="slippage-info"> (slippage {formatPercent(slippage)})</span>
                            </div>
                        </div>
                    )}

                    {/* Slippage Settings */}
                    <div className="slippage-section">
                        <span className="slippage-label">Slippage Tolerance</span>
                        <div className="slippage-options">
                            {[0.005, 0.01, 0.03].map(val => (
                                <button
                                    key={val}
                                    className={`slippage-btn ${slippage === val ? 'active' : ''}`}
                                    onClick={() => setSlippage(val)}
                                >
                                    {formatPercent(val)}
                                </button>
                            ))}
                        </div>
                    </div>

                    {/* Error display */}
                    {validation.error && lpAmount && (
                        <div className="error-banner">{validation.error}</div>
                    )}
                </div>

                <div className="modal-footer">
                    <button className="btn btn-secondary" onClick={onClose}>
                        Cancel
                    </button>
                    <button
                        className={`btn btn-primary ${lpPercent > 0.95 ? 'btn-warning' : ''}`}
                        onClick={handleRemoveClick}
                        disabled={!wallet || !validation.ok || lpBalance <= 0}
                    >
                        {getButtonText()}
                    </button>
                </div>

                {/* Confirmation Modal for Full Removal */}
                {showConfirm && (
                    <Modal open onClose={() => { setShowConfirm(false); setTypedConfirmText(''); }} title="⚠️ Full Position Removal" size="sm">
                        <p>
                            You are removing <strong>{formatPercent(lpPercent)}</strong> of your liquidity position.
                            This will close your position in this pool.
                        </p>
                        {lpPercent >= 0.99 && (
                            <div className="confirm-typed">
                                <p className="confirm-warning">
                                    Type <strong>REMOVE</strong> to confirm.
                                </p>
                                <input
                                    type="text"
                                    value={typedConfirmText}
                                    onChange={(e) => setTypedConfirmText(e.target.value)}
                                    placeholder="REMOVE"
                                />
                            </div>
                        )}
                        <div className="confirm-details">
                            <div className="confirm-row">
                                <span>Returning:</span>
                                <span>{formatNumber(preview?.amount0)} {token0.symbol}</span>
                            </div>
                            <div className="confirm-row">
                                <span>Returning:</span>
                                <span>{formatNumber(preview?.amount1)} {token1.symbol}</span>
                            </div>
                        </div>
                        <div className="confirm-actions">
                            <button className="btn btn-secondary" onClick={() => { setShowConfirm(false); setTypedConfirmText(''); }}>
                                Cancel
                            </button>
                            <button
                                className="btn btn-primary btn-warning"
                                onClick={handleSubmit}
                                disabled={lpPercent >= 0.99 && String(typedConfirmText || '').trim().toUpperCase() !== 'REMOVE'}
                            >
                                Remove All
                            </button>
                        </div>
                    </Modal>
                )}
        </Modal>
    );
}

export default RemoveLiquidityModal;
