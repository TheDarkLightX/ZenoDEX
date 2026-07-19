import { useState, useMemo, useCallback } from 'react';
import { toBigInt } from '../../lib/perpMath.js';
import { validateDeposit, validateWithdraw } from '../../lib/perpValidation.js';
import './PerpCollateralModal.css';

/**
 * PerpCollateralModal - Deposit/withdraw collateral
 *
 * Follows the AddLiquidityModal pattern: two-tab modal with validation.
 */
function PerpCollateralModal({ market, position, wallet, writeEnabled, writeLockReason, onDeposit, onWithdraw, onClose }) {
    const [tab, setTab] = useState('deposit');
    const [amount, setAmount] = useState('');

    const collateral = position?.collateralQuote ?? null;
    // Look up wallet balance using the market's quote asset (e.g. AGRS, ZDEX).
    const quoteAsset = market?.quoteAsset ?? '';
    const walletBalance = quoteAsset && wallet?.balance?.[quoteAsset] != null
        ? Number(wallet.balance[quoteAsset])
        : null;
    const authoritativeFactsReady = market?.authoritativeWriteFactsReady === true
        && position?.positionBase != null
        && collateral != null;

    const parsedAmount = useMemo(() => {
        const n = parseInt(amount, 10);
        return n > 0 ? n : 0;
    }, [amount]);

    const validation = useMemo(() => {
        if (!market || parsedAmount <= 0) {
            return { ok: false, error: null };
        }
        if (!authoritativeFactsReady) {
            return { ok: false, error: 'Authoritative market risk parameters are unavailable' };
        }

        const state = {
            epochPhase: market.epochPhase,
            collateralQuote: toBigInt(collateral),
            positionBase: toBigInt(position.positionBase),
            nowEpoch: toBigInt(market.nowEpoch),
            oracleLastUpdateEpoch: toBigInt(market.oracleLastUpdateEpoch),
            maxOracleStalenessEpochs: toBigInt(market.maxOracleStalenessEpochs),
            oracleSeen: market.oracleSeen,
            indexPriceE8: toBigInt(market.indexPriceE8),
            maintenanceMarginBps: toBigInt(market.maintenanceMarginBps),
            depegBufferBps: toBigInt(market.depegBufferBps),
        };

        if (tab === 'deposit') {
            return validateDeposit(state, toBigInt(parsedAmount));
        }
        return validateWithdraw(state, toBigInt(parsedAmount));
    }, [market, position, tab, parsedAmount, collateral, authoritativeFactsReady]);

    const handleSubmit = useCallback(() => {
        if (!validation.ok) return;
        if (tab === 'deposit') {
            onDeposit?.(market.id, parsedAmount);
        } else {
            onWithdraw?.(market.id, parsedAmount);
        }
        onClose();
    }, [validation, tab, market, parsedAmount, onDeposit, onWithdraw, onClose]);

    const handleMax = useCallback(() => {
        if (tab === 'deposit') {
            if (Number.isFinite(walletBalance)) setAmount(Math.floor(walletBalance).toString());
        } else if (collateral != null) {
            setAmount(collateral.toString());
        }
    }, [tab, walletBalance, collateral]);

    return (
        <div className="modal-overlay" onClick={onClose}>
            <div className="perp-collateral-modal animate-slide-up" onClick={e => e.stopPropagation()}>
                <div className="modal-header">
                    <h2>Manage Collateral</h2>
                    <button className="modal-close" onClick={onClose}>&times;</button>
                </div>

                {/* Tab Toggle */}
                <div className="perp-collateral-tabs">
                    <button
                        className={`perp-collateral-tab ${tab === 'deposit' ? 'active' : ''}`}
                        onClick={() => { setTab('deposit'); setAmount(''); }}
                    >
                        Deposit
                    </button>
                    <button
                        className={`perp-collateral-tab ${tab === 'withdraw' ? 'active' : ''}`}
                        onClick={() => { setTab('withdraw'); setAmount(''); }}
                    >
                        Withdraw
                    </button>
                </div>

                <div className="modal-body">
                    {/* Balance Info */}
                    <div className="perp-collateral-info">
                        <div className="perp-collateral-info-row">
                            <span>Current Collateral</span>
                            <span className="perp-collateral-balance">
                                {collateral != null ? formatQuote(collateral) : 'N/A'}
                            </span>
                        </div>
                        {tab === 'deposit' && (
                            <div className="perp-collateral-info-row">
                                <span>Wallet Balance</span>
                                <span className="perp-collateral-balance">
                                    {walletBalance != null ? walletBalance.toLocaleString() : 'N/A'} {quoteAsset || ''}
                                </span>
                            </div>
                        )}
                    </div>

                    {/* Amount Input */}
                    <div className="perp-collateral-input-group">
                        <div className="input-header">
                            <span className="input-label">Amount (quote units)</span>
                            <span className="input-balance" onClick={handleMax}>
                                MAX
                            </span>
                        </div>
                        <input
                            type="number"
                            className="input perp-collateral-input"
                            placeholder="0"
                            value={amount}
                            onChange={e => setAmount(e.target.value)}
                            min="0"
                            step="1"
                        />
                    </div>

                    {/* After Preview */}
                    {parsedAmount > 0 && collateral != null && (
                        <div className="perp-collateral-preview animate-fade-in">
                            <div className="perp-collateral-info-row">
                                <span>After {tab}</span>
                                <span className="perp-collateral-balance">
                                    {formatQuote(tab === 'deposit' ? collateral + parsedAmount : collateral - parsedAmount)}
                                </span>
                            </div>
                        </div>
                    )}

                    {/* Error */}
                    {validation.error && amount && (
                        <div className="perp-order-error">{validation.error}</div>
                    )}
                    {!writeEnabled && writeLockReason && (
                        <div className="perp-order-error">{writeLockReason}</div>
                    )}
                </div>

                <div className="modal-footer">
                    <button className="btn btn-secondary" onClick={onClose}>Cancel</button>
                    <button
                        className="btn btn-primary"
                        onClick={handleSubmit}
                        disabled={!wallet || !writeEnabled || !validation.ok}
                    >
                        {!wallet ? 'Connect wallet in header →'
                            : !writeEnabled ? 'Writes disabled'
                            : !amount ? 'Enter Amount'
                            : validation.error ? validation.error
                            : tab === 'deposit' ? 'Deposit' : 'Withdraw'}
                    </button>
                </div>
            </div>
        </div>
    );
}

function formatQuote(value) {
    const num = Number(value);
    if (num >= 1_000_000) return '$' + (num / 1_000_000).toFixed(2) + 'M';
    if (num >= 1_000) return '$' + (num / 1_000).toFixed(2) + 'K';
    return '$' + num.toLocaleString(undefined, { maximumFractionDigits: 2 });
}

export default PerpCollateralModal;
