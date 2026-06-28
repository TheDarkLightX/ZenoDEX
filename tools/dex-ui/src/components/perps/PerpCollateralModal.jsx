import { useState, useMemo, useCallback } from 'react';
import { toBigInt } from '../../lib/perpMath.js';
import { validateDeposit, validateWithdraw } from '../../lib/perpValidation.js';
import Modal from '../Modal.jsx';
import './PerpCollateralModal.css';

/**
 * PerpCollateralModal - Deposit/withdraw collateral
 *
 * Follows the AddLiquidityModal pattern: two-tab modal with validation.
 */
function PerpCollateralModal({ market, position, wallet, onDeposit, onWithdraw, onClose }) {
    const [tab, setTab] = useState('deposit');
    const [amount, setAmount] = useState('');

    const collateral = position?.collateralQuote ?? 0;
    // Look up wallet balance using the market's quote asset (e.g. AGRS, ZDEX).
    const quoteAsset = market?.quoteAsset ?? '';
    const walletBalance = position?.quoteBalance ?? ((quoteAsset && wallet?.balance?.[quoteAsset]) ?? 0);

    const parsedAmount = useMemo(() => {
        const n = parseInt(amount, 10);
        return n > 0 ? n : 0;
    }, [amount]);

    const validation = useMemo(() => {
        if (!market || parsedAmount <= 0) {
            return { ok: false, error: null };
        }

        const state = {
            epochPhase: market.epochPhase,
            collateralQuote: toBigInt(collateral),
            positionBase: toBigInt(position?.positionBase ?? 0),
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
    }, [market, position, tab, parsedAmount, collateral]);

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
            setAmount(Math.floor(walletBalance).toString());
        } else {
            setAmount(collateral.toString());
        }
    }, [tab, walletBalance, collateral]);

    return (
        <Modal open onClose={onClose} title="Manage Collateral" size="md">
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
                            <span className="perp-collateral-balance">{formatQuote(collateral)}</span>
                        </div>
                        {tab === 'deposit' && (
                            <div className="perp-collateral-info-row">
                                <span>Wallet Balance</span>
                                <span className="perp-collateral-balance">{walletBalance.toLocaleString()} {quoteAsset || 'USD'}</span>
                            </div>
                        )}
                    </div>

                    {/* Amount Input */}
                    <div className="perp-collateral-input-group">
                        <div className="input-header">
                            <span className="input-label">Amount (quote units)</span>
                            <button type="button" className="input-balance" onClick={handleMax}>
                                MAX
                            </button>
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
                    {parsedAmount > 0 && (
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
                </div>

                <div className="modal-footer">
                    <button className="btn btn-secondary" onClick={onClose}>Cancel</button>
                    <button
                        className="btn btn-primary"
                        onClick={handleSubmit}
                        disabled={!wallet || !validation.ok}
                    >
                        {!wallet ? 'Connect wallet in header →'
                            : !amount ? 'Enter Amount'
                            : validation.error ? validation.error
                            : tab === 'deposit' ? 'Deposit' : 'Withdraw'}
                    </button>
                </div>
        </Modal>
    );
}

function formatQuote(value) {
    const num = Number(value);
    if (num >= 1_000_000) return '$' + (num / 1_000_000).toFixed(2) + 'M';
    if (num >= 1_000) return '$' + (num / 1_000).toFixed(2) + 'K';
    return '$' + num.toLocaleString(undefined, { maximumFractionDigits: 2 });
}

export default PerpCollateralModal;
