import { useState } from 'react';
import { usePerps } from '../../lib/PerpContext.jsx';
import './PerpInsuranceFundPanel.css';

/**
 * PerpInsuranceFundPanel - Collapsible panel showing insurance fund details
 *
 * Displays balance, fee income, claims paid for the selected market.
 * Includes a deposit action via PerpContext.
 */
function PerpInsuranceFundPanel({ market, wallet }) {
    const [collapsed, setCollapsed] = useState(false);
    const [depositAmount, setDepositAmount] = useState('');
    const { depositInsurance } = usePerps();
    const walletConnected = !!wallet?.address;

    if (!market) return null;

    const balance = Number(market.insuranceBalance ?? 0);
    const income = Number(market.feeIncome ?? 0);
    const claims = Number(market.claimsPaid ?? 0);

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
                            ${formatDollar(balance)}
                        </span>
                    </div>
                    <div className="perp-insurance-stat">
                        <span className="perp-insurance-stat-label">Fee Income</span>
                        <span className="perp-insurance-stat-value perp-insurance-stat-value--positive">
                            ${formatDollar(income)}
                        </span>
                    </div>
                    <div className="perp-insurance-stat">
                        <span className="perp-insurance-stat-label">Claims Paid</span>
                        <span className="perp-insurance-stat-value perp-insurance-stat-value--negative">
                            ${formatDollar(claims)}
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
                        disabled={!walletConnected || !depositAmount || Number(depositAmount) <= 0}
                        onClick={() => {
                            const amt = Math.floor(Number(depositAmount));
                            if (amt > 0) {
                                depositInsurance(market.id, amt);
                                setDepositAmount('');
                            }
                        }}
                    >
                        Deposit
                    </button>
                </div>
            </div>
        </div>
    );
}

function formatDollar(value) {
    return value.toLocaleString(undefined, { minimumFractionDigits: 2, maximumFractionDigits: 2 });
}

export default PerpInsuranceFundPanel;
