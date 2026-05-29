import { useState } from 'react';
import { usePerps } from '../../lib/PerpContext.jsx';
import './PerpInsuranceFundPanel.css';

/**
 * PerpInsuranceFundPanel - Collapsible panel showing insurance fund details
 *
 * Displays balance, fee income, claims paid for the selected market.
 * Includes a deposit action via PerpContext.
 */
function PerpInsuranceFundPanel({ market, wallet, writeEnabled, writeLockReason }) {
    const [collapsed, setCollapsed] = useState(false);
    const [depositAmount, setDepositAmount] = useState('');
    const [depositStatus, setDepositStatus] = useState('');
    const { depositInsurance } = usePerps();
    const walletConnected = !!wallet?.address;

    if (!market) return null;

    const balance = finiteNumberOrNull(market.insuranceBalance);
    const income = finiteNumberOrNull(market.feeIncome);
    const claims = finiteNumberOrNull(market.claimsPaid);
    const insuranceDepositSupported = market.kind === 'isolated_v2';
    const canDeposit = walletConnected
        && writeEnabled
        && insuranceDepositSupported
        && depositAmount
        && Number(depositAmount) > 0;

    return (
        <div className="perp-insurance-panel panel">
            <button
                className="perp-insurance-header"
                onClick={() => setCollapsed(c => !c)}
            >
                <span className="perp-insurance-title">Insurance Fund</span>
                <span className={`perp-insurance-toggle ${collapsed ? 'collapsed' : ''}`}>
                    &#x25BE;
                </span>
            </button>

            <div className={`perp-insurance-body ${collapsed ? 'perp-insurance-body--collapsed' : ''}`}>
                <div className="perp-insurance-stats">
                    <div className="perp-insurance-stat">
                        <span className="perp-insurance-stat-label">Balance</span>
                        <span className="perp-insurance-stat-value">
                            {formatDollarOrNA(balance)}
                        </span>
                    </div>
                    <div className="perp-insurance-stat">
                        <span className="perp-insurance-stat-label">Fee Income</span>
                        <span className="perp-insurance-stat-value perp-insurance-stat-value--positive">
                            {formatDollarOrNA(income)}
                        </span>
                    </div>
                    <div className="perp-insurance-stat">
                        <span className="perp-insurance-stat-label">Claims Paid</span>
                        <span className="perp-insurance-stat-value perp-insurance-stat-value--negative">
                            {formatDollarOrNA(claims)}
                        </span>
                    </div>
                </div>

                <div className="perp-insurance-deposit-row">
                    <input
                        type="number"
                        className="perp-insurance-deposit-input"
                        placeholder="Amount"
                        min="1"
                        value={depositAmount}
                        onChange={e => setDepositAmount(e.target.value)}
                    />
                    <button
                        className="btn btn-secondary perp-insurance-deposit-btn"
                        disabled={!canDeposit}
                        onClick={async () => {
                            const amt = Math.floor(Number(depositAmount));
                            if (amt > 0) {
                                setDepositStatus('Submitting insurance deposit...');
                                const result = await depositInsurance(market.id, amt);
                                if (result?.ok) {
                                    setDepositAmount('');
                                    setDepositStatus('Insurance deposit accepted');
                                } else {
                                    setDepositStatus(result?.error || 'Insurance deposit failed');
                                }
                            }
                        }}
                    >
                        Deposit
                    </button>
                </div>
                {!insuranceDepositSupported && (
                    <div className="perp-order-error">Insurance deposits are available for isolated perps markets.</div>
                )}
                {!writeEnabled && (
                    <div className="perp-order-error">{writeLockReason}</div>
                )}
                {depositStatus && (
                    <div className="perp-order-success">{depositStatus}</div>
                )}
            </div>
        </div>
    );
}

function finiteNumberOrNull(value) {
    if (value == null) return null; // Number(null) === 0 would mask "no data" as $0.00.
    const n = Number(value);
    return Number.isFinite(n) ? n : null;
}

function formatDollarOrNA(value) {
    if (value == null) return 'N/A';
    return `$${formatDollar(value)}`;
}

function formatDollar(value) {
    return value.toLocaleString(undefined, { minimumFractionDigits: 2, maximumFractionDigits: 2 });
}

export default PerpInsuranceFundPanel;
