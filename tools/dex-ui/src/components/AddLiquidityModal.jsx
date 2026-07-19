import { useState, useMemo, useCallback } from 'react';
import { calcLpTokensMint, calcPoolShare, formatNumber, formatPercent, getSpotPrice } from '../lib/cpmm';
import { validateAddLiquidity } from '../lib/validation';
import './AddLiquidityModal.css';

const LIVE_POOL_SNAPSHOT_ERROR = 'live_pool_snapshot_unavailable';

/**
 * AddLiquidityModal - Poka-yoke modal for adding liquidity to a pool
 * Features:
 * - Dual token input with auto-ratio calculation
 * - Balance validation and MAX buttons
 * - LP token preview with pool share
 * - Confirmation for imbalanced adds
 */
function AddLiquidityModal({ pool, wallet, onClose, onSubmit }) {
    const [amount0, setAmount0] = useState('');
    const [amount1, setAmount1] = useState('');
    const [lockedRatio, setLockedRatio] = useState(true);
    const [showConfirm, setShowConfirm] = useState(false);
    const [typedConfirmText, setTypedConfirmText] = useState('');

    // Pool data
    const { token0, token1, reserve0, reserve1, totalLpSupply } = pool;
    const livePoolSnapshotReady = Number.isFinite(reserve0) && reserve0 > 0
        && Number.isFinite(reserve1) && reserve1 > 0
        && Number.isFinite(totalLpSupply) && totalLpSupply > 0;

    // User balances are supplied by the connected wallet snapshot.
    const balance0 = wallet?.balance?.[token0.symbol] ?? 0;
    const balance1 = wallet?.balance?.[token1.symbol] ?? 0;

    // Current pool ratio
    const poolRatio = useMemo(() => {
        if (!livePoolSnapshotReady) return null;
        return reserve1 / reserve0;
    }, [livePoolSnapshotReady, reserve0, reserve1]);

    // Calculate LP tokens and preview
    const preview = useMemo(() => {
        const amt0 = parseFloat(amount0) || 0;
        const amt1 = parseFloat(amount1) || 0;

        if (!livePoolSnapshotReady || poolRatio == null || amt0 <= 0 || amt1 <= 0) {
            return null;
        }

        const lpTokens = calcLpTokensMint(amt0, amt1, reserve0, reserve1, totalLpSupply);
        const newShare = calcPoolShare(lpTokens, totalLpSupply + lpTokens);
        const spotPrice = getSpotPrice(reserve0, reserve1);

        // Check if amounts are balanced
        const expectedAmt1 = amt0 * poolRatio;
        const imbalanceRatio = Math.abs(amt1 - expectedAmt1) / expectedAmt1;
        const isImbalanced = imbalanceRatio > 0.01; // >1% imbalance

        return {
            lpTokens,
            poolShare: newShare,
            spotPrice,
            imbalanceRatio,
            isImbalanced,
        };
    }, [amount0, amount1, livePoolSnapshotReady, reserve0, reserve1, totalLpSupply, poolRatio]);

    // Validation
    const validation = useMemo(() => {
        if (!livePoolSnapshotReady) {
            return { ok: false, error: LIVE_POOL_SNAPSHOT_ERROR };
        }
        const amt0 = parseFloat(amount0) || 0;
        const amt1 = parseFloat(amount1) || 0;

        return validateAddLiquidity({
            amount0: amt0,
            amount1: amt1,
            balance0,
            balance1,
        });
    }, [amount0, amount1, balance0, balance1, livePoolSnapshotReady]);

    // Handle amount0 change with auto-ratio
    const handleAmount0Change = useCallback((value) => {
        setAmount0(value);
        if (lockedRatio && value && poolRatio != null) {
            const amt0 = parseFloat(value) || 0;
            setAmount1((amt0 * poolRatio).toFixed(6));
        }
    }, [lockedRatio, poolRatio]);

    // Handle amount1 change with auto-ratio
    const handleAmount1Change = useCallback((value) => {
        setAmount1(value);
        if (lockedRatio && value && poolRatio != null && poolRatio > 0) {
            const amt1 = parseFloat(value) || 0;
            setAmount0((amt1 / poolRatio).toFixed(6));
        }
    }, [lockedRatio, poolRatio]);

    // MAX buttons
    const handleMax0 = useCallback(() => {
        handleAmount0Change(String(balance0));
    }, [balance0, handleAmount0Change]);

    const handleMax1 = useCallback(() => {
        handleAmount1Change(String(balance1));
    }, [balance1, handleAmount1Change]);

    const handleSubmit = useCallback(() => {
        if (!validation.ok || !preview) return;
        setShowConfirm(false);
        setTypedConfirmText('');
        onSubmit?.({
            pool,
            amount0: parseFloat(amount0),
            amount1: parseFloat(amount1),
            lpTokensExpected: preview?.lpTokens,
        });
        onClose();
    }, [amount0, amount1, preview, pool, onSubmit, onClose, validation.ok]);

    // Submit handler with confirmation for imbalanced adds
    const handleAddClick = useCallback(() => {
        if (!validation.ok) return;

        if (preview?.isImbalanced) {
            setTypedConfirmText('');
            setShowConfirm(true);
        } else {
            handleSubmit();
        }
    }, [validation.ok, preview, handleSubmit]);

    const getButtonText = () => {
        if (!wallet) return 'Connect Wallet';
        if (!livePoolSnapshotReady) return 'Live pool data unavailable';
        if (!amount0 || !amount1) return 'Enter Amounts';
        if (validation.error) return validation.error;
        return 'Add Liquidity';
    };

    return (
        <div className="modal-overlay" onClick={onClose}>
            <div className="modal-container animate-slide-up" onClick={e => e.stopPropagation()}>
                <div className="modal-header">
                    <h2>Add Liquidity</h2>
                    <button className="modal-close" onClick={onClose}>✕</button>
                </div>

                <div className="modal-body">
                    {/* Pool Info */}
                    <div className="pool-info-banner">
                        <span className="pool-icons">
                            {token0.icon} {token1.icon}
                        </span>
                        <span className="pool-name">{token0.symbol} / {token1.symbol}</span>
                        <span className="pool-ratio">
                            {poolRatio == null
                                ? 'Live ratio unavailable'
                                : `1 ${token0.symbol} = ${formatNumber(poolRatio, 4)} ${token1.symbol}`}
                        </span>
                    </div>

                    {/* Token 0 Input */}
                    <div className={`input-group ${validation.error?.includes('token 0') ? 'has-error' : ''}`}>
                        <div className="input-header">
                            <span className="input-label">{token0.symbol}</span>
                            <span className="input-balance" onClick={handleMax0}>
                                Balance: {formatNumber(balance0)}
                                {balance0 > 0 && <span className="max-tag"> MAX</span>}
                            </span>
                        </div>
                        <div className="input-row">
                            <input
                                type="number"
                                className="input input-amount"
                                placeholder="0.0"
                                value={amount0}
                                onChange={e => handleAmount0Change(e.target.value)}
                                min="0"
                                step="any"
                            />
                            <div className="token-badge">
                                <span>{token0.icon}</span>
                                <span>{token0.symbol}</span>
                            </div>
                        </div>
                    </div>

                    {/* Ratio Lock Toggle */}
                    <div className="ratio-control">
                        <button
                            className={`ratio-btn ${lockedRatio ? 'active' : ''}`}
                            onClick={() => setLockedRatio(!lockedRatio)}
                            title={lockedRatio ? 'Click to unlock ratio' : 'Click to lock ratio'}
                        >
                            {lockedRatio ? '🔗 Balanced' : '🔓 Custom'}
                        </button>
                    </div>

                    {/* Token 1 Input */}
                    <div className={`input-group ${validation.error?.includes('token 1') ? 'has-error' : ''}`}>
                        <div className="input-header">
                            <span className="input-label">{token1.symbol}</span>
                            <span className="input-balance" onClick={handleMax1}>
                                Balance: {formatNumber(balance1)}
                                {balance1 > 0 && <span className="max-tag"> MAX</span>}
                            </span>
                        </div>
                        <div className="input-row">
                            <input
                                type="number"
                                className="input input-amount"
                                placeholder="0.0"
                                value={amount1}
                                onChange={e => handleAmount1Change(e.target.value)}
                                min="0"
                                step="any"
                            />
                            <div className="token-badge">
                                <span>{token1.icon}</span>
                                <span>{token1.symbol}</span>
                            </div>
                        </div>
                    </div>

                    {/* Preview */}
                    {preview && (
                        <div className="lp-preview animate-fade-in">
                            <div className="preview-row">
                                <span>LP Tokens to Receive</span>
                                <span className="preview-value">{formatNumber(preview.lpTokens)}</span>
                            </div>
                            <div className="preview-row">
                                <span>Pool Share</span>
                                <span className="preview-value">{formatPercent(preview.poolShare)}</span>
                            </div>
                            {preview.isImbalanced && (
                                <div className="imbalance-warning">
                                    ⚠️ Imbalanced add ({formatPercent(preview.imbalanceRatio)} off ratio)
                                    — you may receive fewer LP tokens
                                </div>
                            )}
                        </div>
                    )}

                    {/* Error display */}
                    {validation.error && amount0 && amount1 && (
                        <div className="error-banner">{validation.error}</div>
                    )}
                </div>

                <div className="modal-footer">
                    <button className="btn btn-secondary" onClick={onClose}>
                        Cancel
                    </button>
                    <button
                        className={`btn btn-primary ${preview?.isImbalanced ? 'btn-warning' : ''}`}
                        onClick={handleAddClick}
                        disabled={!wallet || !validation.ok}
                    >
                        {getButtonText()}
                    </button>
                </div>

                {/* Confirmation Modal for Imbalanced Adds */}
                {showConfirm && (
                    <div className="confirm-overlay" onClick={() => { setShowConfirm(false); setTypedConfirmText(''); }}>
                        <div className="confirm-modal animate-slide-up" onClick={e => e.stopPropagation()}>
                            <h3>⚠️ Imbalanced Liquidity</h3>
                            <p>
                                Your deposit is <strong>{formatPercent(preview.imbalanceRatio)}</strong> off
                                the optimal ratio. This may result in fewer LP tokens than expected.
                            </p>
                            {preview.imbalanceRatio >= 0.05 && (
                                <div className="confirm-typed">
                                    <p className="confirm-warning">
                                        Type <strong>ADD</strong> to confirm a highly imbalanced deposit.
                                    </p>
                                    <input
                                        type="text"
                                        value={typedConfirmText}
                                        onChange={(e) => setTypedConfirmText(e.target.value)}
                                        placeholder="ADD"
                                    />
                                </div>
                            )}
                            <div className="confirm-details">
                                <div className="confirm-row">
                                    <span>You deposit:</span>
                                    <span>{formatNumber(parseFloat(amount0))} {token0.symbol}</span>
                                </div>
                                <div className="confirm-row">
                                    <span>You deposit:</span>
                                    <span>{formatNumber(parseFloat(amount1))} {token1.symbol}</span>
                                </div>
                                <div className="confirm-row">
                                    <span>You receive:</span>
                                    <span>{formatNumber(preview.lpTokens)} LP Tokens</span>
                                </div>
                            </div>
                            <div className="confirm-actions">
                                <button className="btn btn-secondary" onClick={() => { setShowConfirm(false); setTypedConfirmText(''); }}>
                                    Cancel
                                </button>
                                <button
                                    className="btn btn-primary btn-warning"
                                    onClick={handleSubmit}
                                    disabled={preview.imbalanceRatio >= 0.05 && String(typedConfirmText || '').trim().toUpperCase() !== 'ADD'}
                                >
                                    Add Anyway
                                </button>
                            </div>
                        </div>
                    </div>
                )}
            </div>
        </div>
    );
}

export default AddLiquidityModal;
