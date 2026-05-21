import { useState } from 'react';
import './ZUSDWorkbench.css';
import {
  ZUSD_SUMMARY,
  ZUSD_OPERATIONS,
  DEMO_VAULTS,
  ZUSD_GUARDS,
  ZUSD_RISK_PARAMS,
} from '../lib/zusdData';
import { useDemoMode } from '../lib/DemoModeContext.jsx';
import ZUSDTauWalletSurface from './ZUSDTauWalletSurface.jsx';
import ZUSDMonetarySurface from './ZUSDMonetarySurface.jsx';

function MintPanel({ onClose }) {
  const [collateral, setCollateral] = useState('');
  const oraclePrice = ZUSD_SUMMARY.oraclePrice;
  const minCR = ZUSD_SUMMARY.minCollRatio / 100;
  const collAmt = parseFloat(collateral) || 0;
  const collValue = collAmt * oraclePrice;
  const maxMint = collValue > 0 ? Math.floor(collValue / minCR) : 0;
  const [mintAmt, setMintAmt] = useState('');
  const mint = parseFloat(mintAmt) || 0;
  const cr = mint > 0 ? ((collValue / mint) * 100).toFixed(1) : '\u2014';
  const fee = mint > 0 ? (mint * ZUSD_SUMMARY.baseRateBps / 10000).toFixed(2) : '0';
  const crNum = mint > 0 ? collValue / mint * 100 : Infinity;
  const crClass = crNum < 120 ? 'zusd-danger' : crNum < 150 ? 'zusd-warning' : 'zusd-healthy';

  return (
    <div className="zusd-action-panel panel animate-scale-in">
      <div className="zusd-action-header">
        <h3>Mint zUSD</h3>
        <button className="zusd-close" onClick={onClose}>&times;</button>
      </div>
      <div className="zusd-action-body">
        <label className="label">Collateral (AGRS)</label>
        <input
          className="input"
          type="number"
          placeholder="0.0"
          value={collateral}
          onChange={(e) => setCollateral(e.target.value)}
          min="0"
          step="any"
        />
        <div className="zusd-hint">Value: ${collValue.toLocaleString(undefined, { maximumFractionDigits: 2 })} at ${oraclePrice}/AGRS</div>

        <label className="label">zUSD to Mint</label>
        <input
          className="input"
          type="number"
          placeholder="0.0"
          value={mintAmt}
          onChange={(e) => setMintAmt(e.target.value)}
          min="0"
          max={maxMint}
          step="any"
        />
        <div className="zusd-hint">Max mintable: {maxMint.toLocaleString()} zUSD at {ZUSD_SUMMARY.minCollRatio}% CR</div>

        {mint > 0 && (
          <div className="zusd-preview animate-fade-in">
            <div className="zusd-preview-row">
              <span>Collateral Ratio</span>
              <span className={crClass}>{cr}%</span>
            </div>
            <div className="zusd-preview-row">
              <span>Borrow Fee</span>
              <span>{fee} zUSD ({ZUSD_SUMMARY.baseRateBps / 100}%)</span>
            </div>
            <div className="zusd-preview-row">
              <span>You Receive</span>
              <span>{(mint - parseFloat(fee)).toFixed(2)} zUSD</span>
            </div>
          </div>
        )}

        <button
          className="btn btn-primary btn-large zusd-submit"
          disabled={mint <= 0 || crNum < ZUSD_SUMMARY.minCollRatio}
        >
          {crNum < ZUSD_SUMMARY.minCollRatio ? `CR below ${ZUSD_SUMMARY.minCollRatio}%` : 'Mint zUSD'}
        </button>
      </div>
    </div>
  );
}

function StabilityPoolPanel({ onClose }) {
  const [amount, setAmount] = useState('');
  const amt = parseFloat(amount) || 0;
  const newPool = ZUSD_SUMMARY.stabilityPoolSize + amt;
  const share = amt > 0 ? ((amt / newPool) * 100).toFixed(2) : '0';

  return (
    <div className="zusd-action-panel panel animate-scale-in">
      <div className="zusd-action-header">
        <h3>Stability Pool Deposit</h3>
        <button className="zusd-close" onClick={onClose}>&times;</button>
      </div>
      <div className="zusd-action-body">
        <label className="label">zUSD to Deposit</label>
        <input
          className="input"
          type="number"
          placeholder="0.0"
          value={amount}
          onChange={(e) => setAmount(e.target.value)}
          min="0"
          step="any"
        />

        {amt > 0 && (
          <div className="zusd-preview animate-fade-in">
            <div className="zusd-preview-row">
              <span>Pool Size After</span>
              <span>{newPool.toLocaleString()} zUSD</span>
            </div>
            <div className="zusd-preview-row">
              <span>Your Share</span>
              <span>{share}%</span>
            </div>
            <div className="zusd-preview-row">
              <span>Earns</span>
              <span>Liquidation collateral at discount</span>
            </div>
          </div>
        )}

        <button className="btn btn-primary btn-large zusd-submit" disabled={amt <= 0}>
          Deposit to Stability Pool
        </button>
      </div>
    </div>
  );
}

function ZUSDWorkbench() {
  const { demoMode } = useDemoMode();
  const [activePanel, setActivePanel] = useState(null);

  if (!demoMode) {
    return (
      <section className="zusd-workbench">
        <ZUSDMonetarySurface />
        <ZUSDTauWalletSurface />
      </section>
    );
  }

  return (
    <section className="zusd-workbench">
      {/* Hero */}
      <div className="zusd-hero panel panel-glass animate-fade-in">
        <div>
          <p className="zusd-kicker">Collateralized stablecoin</p>
          <h1>zUSD</h1>
          <p className="zusd-subtitle">
            Borrow zUSD against AGRS collateral. Formally verified debt conservation,
            liquidation safety, and fee correctness via 7 Lean proofs.
          </p>
        </div>
        <div className="zusd-hero-meta">
          <span className="zusd-chip">CR {ZUSD_SUMMARY.globalCR.toFixed(1)}%</span>
          <span className="zusd-chip zusd-chip-accent">${(ZUSD_SUMMARY.totalDebt / 1e6).toFixed(2)}M minted</span>
        </div>
      </div>

      {/* Stats */}
      <div className="zusd-stats grid grid-4">
        <div className="stat panel animate-slide-up" style={{ animationDelay: '0ms' }}>
          <span className="stat-label">Total Debt</span>
          <span className="stat-value">{(ZUSD_SUMMARY.totalDebt / 1e6).toFixed(2)}M zUSD</span>
        </div>
        <div className="stat panel animate-slide-up" style={{ animationDelay: '50ms' }}>
          <span className="stat-label">Total Collateral</span>
          <span className="stat-value">${(ZUSD_SUMMARY.totalCollateral / 1e6).toFixed(2)}M</span>
        </div>
        <div className="stat panel animate-slide-up" style={{ animationDelay: '100ms' }}>
          <span className="stat-label">Stability Pool</span>
          <span className="stat-value">{(ZUSD_SUMMARY.stabilityPoolSize / 1e3).toFixed(0)}K zUSD</span>
        </div>
        <div className="stat panel animate-slide-up" style={{ animationDelay: '150ms' }}>
          <span className="stat-label">AGRS Price</span>
          <span className="stat-value">${ZUSD_SUMMARY.oraclePrice.toFixed(2)}</span>
        </div>
      </div>

      {/* Operations + Action Panel */}
      <div className="zusd-ops-row">
        <div className="panel zusd-section-card">
          <div className="zusd-section-header">
            <h2>Operations</h2>
            <span className="zusd-section-badge">What you can do</span>
          </div>
          <div className="zusd-ops-grid">
            {ZUSD_OPERATIONS.map((op) => (
              <button
                key={op.id}
                className={`zusd-op-card ${activePanel === op.id ? 'zusd-op-active' : ''}`}
                onClick={() => setActivePanel(activePanel === op.id ? null : op.id)}
                type="button"
              >
                <div className="zusd-op-label">{op.label}</div>
                <p className="zusd-op-desc">{op.description}</p>
                <span className="zusd-op-action">{op.action}</span>
              </button>
            ))}
          </div>
        </div>

        {activePanel === 'mint' && <MintPanel onClose={() => setActivePanel(null)} />}
        {activePanel === 'deposit_sp' && <StabilityPoolPanel onClose={() => setActivePanel(null)} />}
        {(activePanel === 'repay' || activePanel === 'redeem') && (
          <div className="zusd-action-panel panel animate-scale-in">
            <div className="zusd-action-header">
              <h3>{activePanel === 'repay' ? 'Repay Debt' : 'Redeem zUSD'}</h3>
              <button className="zusd-close" onClick={() => setActivePanel(null)}>&times;</button>
            </div>
            <div className="zusd-action-body">
              <label className="label">zUSD Amount</label>
              <input className="input" type="number" placeholder="0.0" min="0" step="any" />
              <div className="zusd-hint">
                {activePanel === 'repay'
                  ? 'Burns zUSD to reduce your vault debt and free collateral.'
                  : `Redeems 1 zUSD for $1 of AGRS at $${ZUSD_SUMMARY.oraclePrice}/AGRS.`}
              </div>
              <button className="btn btn-primary btn-large zusd-submit">
                {activePanel === 'repay' ? 'Repay' : 'Redeem'}
              </button>
            </div>
          </div>
        )}
      </div>

      {/* Vaults + Proofs */}
      <div className="zusd-grid">
        <div className="panel zusd-section-card">
          <div className="zusd-section-header">
            <h2>Active Vaults</h2>
            <span className="zusd-section-badge">{DEMO_VAULTS.length} vaults</span>
          </div>
          <div className="zusd-vault-table">
            <div className="zusd-vault-head">
              <span>Vault</span>
              <span>Collateral</span>
              <span>Debt</span>
              <span>CR</span>
              <span>Status</span>
            </div>
            {DEMO_VAULTS.map((vault) => (
              <div key={vault.id} className="zusd-vault-row">
                <span className="zusd-mono">{vault.owner}</span>
                <span>{vault.collateral.toLocaleString()} AGRS</span>
                <span>{vault.debt.toLocaleString()} zUSD</span>
                <span className={`zusd-cr zusd-cr-${vault.status}`}>{vault.cr.toFixed(1)}%</span>
                <span className={`zusd-vault-status zusd-vault-${vault.status}`}>{vault.status}</span>
              </div>
            ))}
          </div>
        </div>

        <div className="panel zusd-section-card">
          <div className="zusd-section-header">
            <h2>Formal Proofs</h2>
            <span className="zusd-section-badge">Lean 4</span>
          </div>
          <div className="zusd-proof-list">
            {ZUSD_GUARDS.map((guard) => (
              <article key={guard.id} className="zusd-proof-row">
                <div>
                  <div className="zusd-proof-title">{guard.label}</div>
                  <p className="zusd-proof-detail">{guard.detail}</p>
                  <span className="zusd-mono zusd-proof-file">{guard.proof}</span>
                </div>
                <span className={`zusd-status zusd-status-${guard.status}`}>{guard.status}</span>
              </article>
            ))}
          </div>
        </div>
      </div>

      {/* Risk Parameters */}
      <div className="panel zusd-section-card animate-fade-in">
        <div className="zusd-section-header">
          <h2>Risk Parameters</h2>
          <span className="zusd-section-badge">Protocol config</span>
        </div>
        <div className="zusd-risk-table">
          <div className="zusd-risk-head">
            <span>Parameter</span>
            <span>Value</span>
            <span>Note</span>
          </div>
          {ZUSD_RISK_PARAMS.map((row) => (
            <div key={row.param} className="zusd-risk-row">
              <span>{row.param}</span>
              <span className="zusd-mono">{row.value}</span>
              <span className="zusd-risk-note">{row.note}</span>
            </div>
          ))}
        </div>
      </div>
    </section>
  );
}

export default ZUSDWorkbench;
