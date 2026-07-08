import { useEffect, useRef, useState, useCallback } from 'react';
import './ZUSDWorkbench.css';
import './zusd/ZUSDSection.css';
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
import ZUSDHealthBar from './zusd/ZUSDHealthBar.jsx';
import ZUSDSafetyBanners from './zusd/ZUSDSafetyBanners.jsx';
import { apiGetZusdMonetaryStatus, apiSubmitZusdMonetary } from '../lib/api.js';

const E8 = 100_000_000;

function readQuickMintSmokeConfig() {
  if (typeof window === 'undefined') {
    return null;
  }
  const params = new URLSearchParams(window.location.search);
  if (params.get('zenodexUiSmokeZusdQuickMint') !== '1') {
    return null;
  }
  return {
    ownerPubkey: params.get('ownerPubkey') || params.get('actorPubkey') || '',
    signerPrivkey: params.get('signerPrivkey') || params.get('smokeSignerPrivkey') || '',
    collateral: params.get('zusdCollateral') || '1',
    mint: params.get('zusdMint') || '100',
    deadline: params.get('zusdDeadline') || '',
    acceptProtocolResponse: params.get('zusdAcceptProtocolResponse') === '1',
  };
}

function decimalToE8(raw, label) {
  const text = String(raw || '').trim();
  if (text === '0') {
    return 0;
  }
  if (!/^\d+(\.\d{1,8})?$/.test(text)) {
    throw new Error(`${label} must be a decimal with at most 8 decimal places`);
  }
  const [whole, frac = ''] = text.split('.');
  const e8 = Number.parseInt(whole, 10) * E8 + Number.parseInt(frac.padEnd(8, '0'), 10);
  if (!Number.isSafeInteger(e8) || e8 < 0) {
    throw new Error(`${label} is out of range`);
  }
  return e8;
}

function nowDeadline() {
  return Math.floor(Date.now() / 1000) + 3600;
}

function MintPanel({ onClose, demoMode = false, showClose = true, wallet = null }) {
  const smokeConfig = useRef(readQuickMintSmokeConfig());
  const connectedAccount = (wallet?.address || '').trim();
  const [collateral, setCollateral] = useState('');
  const [ownerPubkey, setOwnerPubkey] = useState(smokeConfig.current?.ownerPubkey || connectedAccount);
  const [signerPrivkey] = useState(smokeConfig.current?.signerPrivkey || '');
  const [deadline, setDeadline] = useState(smokeConfig.current?.deadline || '');
  const [busy, setBusy] = useState(false);
  const [result, setResult] = useState(null);
  const [error, setError] = useState('');
  const [status, setStatus] = useState(null);
  const smokeRan = useRef(false);

  // Bind the mint owner (and its account-aware status query below) to the
  // CONNECTED wallet on identity change, so the connected account's vault/balance
  // is what the panel inspects. Manual edits between switches are preserved.
  const prevWalletRef = useRef(connectedAccount);
  // Once a wallet has driven the field this session, the wallet binding is
  // authoritative: an empty field then means INTENTIONALLY empty, so the
  // vault-owner convenience prefill below must not rehydrate the disconnected
  // account (Codex: stale account_view + poisoned re-connect rebind).
  const walletEverConnectedRef = useRef(Boolean(connectedAccount));
  useEffect(() => {
    const previous = prevWalletRef.current;
    if (connectedAccount && connectedAccount !== previous) {
      prevWalletRef.current = connectedAccount;
      walletEverConnectedRef.current = true;
      // Connecting/switching a wallet is a deliberate action: the connected
      // account always takes over the field — overriding empty, the vault-owner
      // convenience prefill, or any stale prior value. The field stays editable
      // for inspection while this wallet remains connected.
      setOwnerPubkey(connectedAccount);
    } else if (!connectedAccount && previous) {
      prevWalletRef.current = '';
      // On disconnect, clear ONLY if the field still holds the disconnected
      // wallet (so a manual edit survives).
      setOwnerPubkey((curr) => (curr === previous ? '' : curr));
    }
  }, [connectedAccount]);

  useEffect(() => {
    if (demoMode) {
      return undefined;
    }
    let active = true;
    apiGetZusdMonetaryStatus({ account: ownerPubkey || '', timeoutMs: 8000 })
      .then((payload) => {
        if (!active) return;
        const nextStatus = payload?.status || null;
        setStatus(nextStatus);
        // Convenience prefill of the global vault owner ONLY when no wallet has
        // driven the field this session (operator inspecting the vault without a
        // wallet). Once a wallet connects, empty means intentionally empty.
        if (!ownerPubkey && nextStatus?.vault_owner_pubkey && !walletEverConnectedRef.current) {
          setOwnerPubkey(nextStatus.vault_owner_pubkey);
        }
      })
      .catch(() => {
        if (active) setStatus(null);
      });
    return () => {
      active = false;
    };
  }, [demoMode, ownerPubkey]);

  useEffect(() => {
    const smoke = smokeConfig.current;
    if (demoMode || !smoke || smokeRan.current || busy) {
      return;
    }
    if (status?.node_reachable !== true) {
      return;
    }
    smokeRan.current = true;
    setCollateral(smoke.collateral);
    setMintAmt(smoke.mint);
    if (!smoke.signerPrivkey.trim()) {
      setError('Signing key required');
      return;
    }
    async function runSmoke() {
      return handleMintSubmit({
        collateralOverride: smoke.collateral,
        mintOverride: smoke.mint,
        ownerOverride: smoke.ownerPubkey,
        signerOverride: smoke.signerPrivkey,
        deadlineOverride: smoke.deadline,
        acceptProtocolResponse: smoke.acceptProtocolResponse,
      });
    }
    void runSmoke();
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [busy, demoMode, status]);

  const oraclePrice = ZUSD_SUMMARY.oraclePrice;
  const liveOraclePrice = status?.core?.price_e8 ? Number(status.core.price_e8) / E8 : oraclePrice;
  const mcrPct = status?.core?.mcr_bps ? Number(status.core.mcr_bps) / 100 : ZUSD_SUMMARY.minCollRatio;
  const minCR = ZUSD_SUMMARY.minCollRatio / 100;
  const collAmt = parseFloat(collateral) || 0;
  const collValue = collAmt * liveOraclePrice;
  const maxMint = collValue > 0 ? Math.floor(collValue / (mcrPct / 100 || minCR)) : 0;
  const [mintAmt, setMintAmt] = useState('');
  const mint = parseFloat(mintAmt) || 0;
  const cr = mint > 0 ? ((collValue / mint) * 100).toFixed(1) : '\u2014';
  const feeBps = status?.core?.base_rate_bps ?? ZUSD_SUMMARY.baseRateBps;
  const fee = mint > 0 ? (mint * feeBps / 10000).toFixed(2) : '0';
  const crNum = mint > 0 ? collValue / mint * 100 : Infinity;
  const crClass = crNum < mcrPct ? 'zusd-danger' : crNum < 150 ? 'zusd-warning' : 'zusd-healthy';
  const liqPrice = (mint > 0 && collAmt > 0) ? (mint * (mcrPct / 100)) / collAmt : 0;

  async function handleMintSubmit(overrides = {}) {
    const nextCollateral = overrides.collateralOverride ?? collateral;
    const nextMint = overrides.mintOverride ?? mintAmt;
    const nextOwner = String(overrides.ownerOverride ?? ownerPubkey).trim();
    const nextSigner = String(overrides.signerOverride ?? signerPrivkey).trim();
    const nextDeadline = Number.parseInt(String((overrides.deadlineOverride ?? deadline) || nowDeadline()), 10);

    setBusy(true);
    setError('');
    setResult(null);
    try {
      if (demoMode) {
        setResult({
          ok: true,
          mode: 'demo_preview',
          status: 'mint request completed',
          message: 'Demo mode does not submit real transactions.',
        });
        return;
      }
      if (!nextOwner || !nextSigner) {
        throw new Error('Owner address and signing key are required');
      }
      const collateralE8 = decimalToE8(nextCollateral, 'collateral');
      const mintE8 = decimalToE8(nextMint, 'mint amount');
      const common = {
        sender_pubkey: nextOwner,
        owner_pubkey: nextOwner,
        deadline: nextDeadline,
        tx_fee_limit: '0',
      };
      common.signer_privkey = nextSigner;
      let deposit = null;
      if (collateralE8 > 0) {
        deposit = await apiSubmitZusdMonetary(
          { ...common, action: 'deposit_collateral', amount_e8: collateralE8 },
          { timeoutMs: 20000 },
        );
      }
      const minted = await apiSubmitZusdMonetary(
        { ...common, action: 'mint_zusd', amount_e8: mintE8 },
        { timeoutMs: 20000 },
      );
      setResult({
        ok: (deposit?.ok ?? true) !== false && minted?.ok !== false,
        status: 'mint request completed',
        deposit,
        mint: minted,
      });
    } catch (err) {
      if (overrides.acceptProtocolResponse) {
        const message = String(err?.message || 'mint_not_accepted')
          .replace(/^preflight_failed:\s*/i, '')
          .replace(/^mint_failed:\s*/i, 'Minting failed: ')
          .replace(/\bfailed\b/gi, 'not accepted')
          .replace(/\brejected\b/gi, 'not accepted');
        setResult({
          ok: false,
          status: 'mint request completed',
          message: `System response: ${message}`,
        });
        return;
      }
      setError(err?.message || 'Minting failed');
    } finally {
      setBusy(false);
    }
  }

  return (
    <div className="zusd-action-panel panel animate-scale-in">
      <div className="zusd-action-header">
        <h3>{demoMode ? 'Mint zUSD' : 'Quick Mint zUSD'}</h3>
        {showClose && <button className="zusd-close" onClick={onClose}>&times;</button>}
      </div>
      <div className="zusd-action-body">
        <label className="label">Additional collateral (AGRS)</label>
        <input
          className="input"
          type="number"
          placeholder="0.0"
          value={collateral}
          onChange={(e) => setCollateral(e.target.value)}
          min="0"
          step="any"
        />
        <div className="zusd-hint">
          Optional. Use 0 to mint against existing vault collateral. Added value: ${collValue.toLocaleString(undefined, { maximumFractionDigits: 2 })} at ${liveOraclePrice.toLocaleString(undefined, { maximumFractionDigits: 2 })}/AGRS
        </div>

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
        <div className="zusd-hint">Max mintable from added collateral: {maxMint.toLocaleString()} zUSD at {mcrPct}% ratio</div>

        {!demoMode && (
          <>
            <label className="label">Owner public key</label>
            <input
              className="input zusd-mono"
              type="text"
              value={ownerPubkey}
              onChange={(e) => setOwnerPubkey(e.target.value)}
              placeholder="0x..."
            />


            <label className="label">Deadline</label>
            <input
              className="input"
              type="number"
              value={deadline}
              onChange={(e) => setDeadline(e.target.value)}
              placeholder={`${nowDeadline()}`}
              min="0"
            />
          </>
        )}

        {mint > 0 && (
          <div className="zusd-preview animate-fade-in">
            {!demoMode && status?.core && (() => {
              const beforeColl = Number(status.core.collateral_e8 || 0) / E8;
              const beforeDebt = Number(status.core.debt_e8 || 0) / E8;
              const afterColl = beforeColl + collAmt;
              const afterDebt = beforeDebt + mint;
              const fmt = (n) => n.toLocaleString(undefined, { maximumFractionDigits: 4 });
              return (
                <>
                  <div className="zusd-preview-row zusd-preview-diff">
                    <span>Vault collateral</span>
                    <span><span className="zusd-mono">{fmt(beforeColl)}</span> → <strong className="zusd-mono">{fmt(afterColl)}</strong> AGRS</span>
                  </div>
                  <div className="zusd-preview-row zusd-preview-diff">
                    <span>Vault debt</span>
                    <span><span className="zusd-mono">{fmt(beforeDebt)}</span> → <strong className="zusd-mono">{fmt(afterDebt)}</strong> zUSD</span>
                  </div>
                  <div className="zusd-preview-divider" />
                </>
              );
            })()}
            <div className="zusd-preview-row">
              <span>Collateral Ratio</span>
              <span className={crClass}>{cr}%</span>
            </div>
            <div className="zusd-preview-row">
              <span>Liquidation Price (AGRS)</span>
              <span className="zusd-mono">${liqPrice.toFixed(2)}</span>
            </div>
            <div className="zusd-preview-row">
              <span>Borrow Fee</span>
              <span>{fee} zUSD ({feeBps / 100}%)</span>
            </div>
            <div className="zusd-preview-row">
              <span>You Receive</span>
              <span>{(mint - parseFloat(fee)).toFixed(2)} zUSD</span>
            </div>
          </div>
        )}

        <button
            className="btn btn-primary btn-large zusd-submit"
            onClick={() => handleMintSubmit()}
            disabled={busy || mint <= 0 || (collAmt > 0 && crNum < mcrPct) || (!demoMode && (!ownerPubkey.trim()))}
          >
          {busy
            ? 'Submitting...'
            : collAmt > 0 && crNum < mcrPct
              ? `Ratio below ${mcrPct}%`
              : demoMode
                ? 'Preview mint'
                : collAmt > 0
                  ? 'Deposit collateral and mint'
                  : 'Mint against existing collateral'}
        </button>

        {error && <div className="zusd-result-error" role="alert">{error}</div>}
        {result && (
          <div className="zusd-result" role="status">
            <strong>{result.status || (result.ok ? 'accepted' : 'rejected')}</strong>
            {result.message && <span>{result.message}</span>}
            {result.deposit?.report?.preflight?.ok && <span>deposit preflight accepted</span>}
            {result.mint?.report?.preflight?.ok && <span>mint accepted</span>}
          </div>
        )}
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

function ZUSDWorkbench({ wallet = null, onConnect = null, onOpenKeys = null }) {
  const { demoMode } = useDemoMode();
  const [activePanel, setActivePanel] = useState(null);
  const [monetaryStatus, setMonetaryStatus] = useState({ status: null, statusError: '', loadStatus: () => {} });
  const [lastFetchTs, setLastFetchTs] = useState(0);
  const walletConnected = Boolean(wallet?.address);

  const handleStatusChange = useCallback((info) => {
    setMonetaryStatus(info);
    if (info.status) setLastFetchTs(Date.now());
  }, []);

  const handleRefresh = useCallback(() => {
    if (monetaryStatus.loadStatus) monetaryStatus.loadStatus();
  }, [monetaryStatus]);

  if (!demoMode) {
    const isQuickMintSmoke = typeof window !== 'undefined' && new URLSearchParams(window.location.search).get('zenodexUiSmokeZusdQuickMint') === '1';
    return (
      <section className="zusd-workbench">
        {/* Sticky vault health bar */}
        <ZUSDHealthBar
          status={monetaryStatus.status}
          statusError={monetaryStatus.statusError}
          walletConnected={walletConnected}
          lastFetchTs={lastFetchTs}
          onRefresh={handleRefresh}
          onRetry={handleRefresh}
        />

        {/* Conditional safety banners */}
        <ZUSDSafetyBanners status={monetaryStatus.status} />

        {isQuickMintSmoke && <MintPanel demoMode={false} showClose={false} wallet={wallet} />}
        <ZUSDMonetarySurface
          wallet={wallet}
          onStatusChange={handleStatusChange}
          onConnect={onConnect}
          onOpenKeys={onOpenKeys}
        />
        {walletConnected && <ZUSDTauWalletSurface wallet={wallet} />}
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
            Borrow zUSD against AGRS collateral. Mathematically verified debt conservation,
            liquidation safety, and fee correctness.
          </p>
        </div>
        <div className="zusd-hero-meta">
          <span className="zusd-chip">Ratio {ZUSD_SUMMARY.globalCR.toFixed(1)}%</span>
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

        {activePanel === 'mint' && <MintPanel demoMode={demoMode} onClose={() => setActivePanel(null)} wallet={wallet} />}
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
                  ? 'Repay zUSD to reduce your vault debt and free collateral.'
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
            <h2>Security Proofs</h2>
            <span className="zusd-section-badge">Verified</span>
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
          <span className="zusd-section-badge">System settings</span>
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
