import { useEffect, useMemo, useState } from 'react';
import { apiGetZusdMonetaryStatus, apiPrepareZusdMonetary } from '../lib/api.js';
import InfoTip from './InfoTip.jsx';
import './ZUSDTauWalletSurface.css';

const E8 = 100_000_000;

const EMPTY_FORM = {
  action: 'mint_zusd',
  actor_pubkey: '',
  amount: '100',
  zk_proof_json: '',
  price_e8: String(100 * E8),
  delta: '1',
  deadline: '',
  tx_fee_limit: '0',
};

const ACTIONS = [
  ['deposit_collateral', 'Deposit Collateral'],
  ['withdraw_collateral', 'Withdraw Collateral'],
  ['mint_zusd', 'Mint zUSD'],
  ['repay_zusd', 'Repay zUSD'],
  ['deposit_sp', 'Deposit Stability Pool'],
  ['withdraw_sp', 'Withdraw Stability Pool'],
  ['redeem_zusd', 'Redeem zUSD'],
  ['claim_shutdown_collateral', 'Claim Shutdown Collateral'],
  ['claim_sp_shutdown_collateral', 'Claim SP Shutdown Collateral'],
  ['claim_sp_collateral', 'Claim SP Collateral'],
  ['stake_fee_shares', 'Stake Fee Shares'],
  ['activate_fee_stake', 'Activate Fee Stake'],
  ['claim_fee_rewards', 'Claim Fee Rewards'],
  ['unstake_fee_shares', 'Unstake Fee Shares'],
  ['liquidate', 'Liquidate Vault'],
  ['bootstrap_oracle', 'Bootstrap Oracle'],
  ['oracle_report', 'Oracle Report'],
  ['oracle_commit', 'Oracle Commit'],
  ['advance_epoch', 'Advance Epoch'],
];

function parsePositiveInt(raw) {
  const value = Number.parseInt(String(raw || '').trim(), 10);
  return Number.isFinite(value) && value > 0 ? value : null;
}

function parseJsonObject(raw, label) {
  const text = String(raw || '').trim();
  if (!text) return null;
  let value;
  try {
    value = JSON.parse(text);
  } catch {
    throw new Error(`${label} must be valid JSON`);
  }
  if (!value || typeof value !== 'object' || Array.isArray(value)) {
    throw new Error(`${label} must decode to an object`);
  }
  return value;
}

function compactId(value) {
  if (!value) return 'none';
  const text = String(value);
  if (text.length <= 18) return text;
  return `${text.slice(0, 10)}...${text.slice(-6)}`;
}

function formatE8(val) {
  if (val == null || val === '') return '0';
  return (Number(val) / E8).toLocaleString(undefined, {
    minimumFractionDigits: 2,
    maximumFractionDigits: 4,
  });
}

function formatAmount(value, digits = 4) {
  if (!Number.isFinite(value)) return '0';
  return value.toLocaleString(undefined, {
    minimumFractionDigits: value === 0 ? 0 : 2,
    maximumFractionDigits: digits,
  });
}

function formatCurrency(value) {
  if (!Number.isFinite(value)) return '$0.00';
  const digits = value >= 1000 ? 0 : 2;
  return value.toLocaleString(undefined, {
    style: 'currency',
    currency: 'USD',
    minimumFractionDigits: digits,
    maximumFractionDigits: digits,
  });
}

function formatRatio(value) {
  if (!Number.isFinite(value)) return 'No debt';
  if (value >= 10000) return `${formatAmount(value, 0)}%`;
  return `${value.toFixed(1)}%`;
}

function buildPayload(form) {
  const action = form.action;
  const actor = form.actor_pubkey.trim();
  const payload = { action };

  if (form.deadline.trim()) {
    payload.deadline = Number.parseInt(form.deadline.trim(), 10);
  }
  if (actor) {
    payload.sender_pubkey = actor;
  }
  if (String(form.tx_fee_limit || '').trim()) {
    payload.tx_fee_limit = String(form.tx_fee_limit).trim();
  }
  if (String(form.zk_proof_json || '').trim()) {
    payload.zk_proof = parseJsonObject(form.zk_proof_json, 'zk_proof_json');
  }

  if (['deposit_collateral', 'withdraw_collateral', 'mint_zusd', 'repay_zusd'].includes(action)) {
    payload.owner_pubkey = actor;
  }
  if (
    [
      'deposit_sp',
      'withdraw_sp',
      'redeem_zusd',
      'claim_sp_collateral',
      'claim_shutdown_collateral',
      'claim_sp_shutdown_collateral',
      'stake_fee_shares',
      'activate_fee_stake',
      'claim_fee_rewards',
      'unstake_fee_shares',
    ].includes(action)
  ) {
    payload.account_pubkey = actor;
  }
  if (['bootstrap_oracle', 'oracle_report', 'oracle_commit', 'liquidate', 'advance_epoch'].includes(action)) {
    payload.actor_pubkey = actor;
  }

  if (['bootstrap_oracle', 'oracle_report'].includes(action)) {
    payload.price_e8 = parsePositiveInt(form.price_e8) || 0;
  }
  if (action === 'advance_epoch') {
    payload.delta = parsePositiveInt(form.delta) || 0;
  }
  if (
    [
      'deposit_collateral',
      'withdraw_collateral',
      'mint_zusd',
      'repay_zusd',
      'deposit_sp',
      'withdraw_sp',
      'redeem_zusd',
      'claim_sp_collateral',
      'claim_shutdown_collateral',
      'claim_sp_shutdown_collateral',
    ].includes(action)
  ) {
    const explicitE8 = parsePositiveInt(form.amount_e8);
    if (explicitE8) {
      payload.amount_e8 = explicitE8;
    } else {
      payload.amount = parsePositiveInt(form.amount) || 0;
    }
  }
  if (['stake_fee_shares', 'unstake_fee_shares'].includes(action)) {
    payload.amount = parsePositiveInt(form.amount) || 0;
  }
  return payload;
}

// Machine-checked Lean 4 theorems backing the zUSD monetary surface. Every
// entry is a REAL, fully-proven file in lean-mathlib/Proofs/ (0 sorry/admit),
// verified by read-only inventory — the filename + headline theorem are exact.
// Rendered as honest evidence, not marketing: we cite the file and what it
// derives, and never claim more than the node enforces (see proof_profile).
const ZUSD_LEAN_PROOFS = [
  {
    title: 'Ceiling-Division Fee Safety',
    theorem: 'ceil_div_mul_ge',
    file: 'ZUSDCeilDivAlgebra.lean',
    desc: 'Borrow and redemption fees use ⌈n/d⌉ so collection always covers the exact amount — no rounding bypass.',
  },
  {
    title: 'Debt Conservation Homomorphism',
    theorem: 'conservation_homomorphism',
    file: 'ZUSDDebtHomomorphism.lean',
    desc: 'Net debt flow is additive (Δfree + Δsp = Δtotal) and forms an AddMonoidHom kernel — conservation composes.',
  },
  {
    title: 'Dual Conservation Independence',
    theorem: 'laws_independent',
    file: 'ZUSDDualConservation.lean',
    desc: 'Debt and collateral conservation are logically independent; both must be checked, neither implies the other.',
  },
  {
    title: 'MCR Headroom / TCR Safety',
    theorem: 'liq_improves_tcr_ratio',
    file: 'ZUSDMCRHeadroom.lean',
    desc: 'Given fixed collateral value and a strict debt reduction, the total collateral ratio strictly increases (cross-multiplication).',
  },
  {
    title: 'Stability-Pool Convexity',
    theorem: 'sp_ratio_convex_lower',
    file: 'ZUSDSPConvexity.lean',
    desc: 'Post-liquidation SP ratio is a convex combination of the old and vault ratios — bounded, predictable returns.',
  },
  {
    title: 'Collateral Flow Algebra',
    theorem: 'conservation_iff_balanced',
    file: 'ZUSDCollateralFlowAlgebra.lean',
    desc: 'Collateral obeys a 4-bucket Kirchhoff law: Δvault + Δsp + Δprotocol + Δexternal = 0. A closed system.',
  },
  {
    title: 'Fee Pipeline Correctness',
    theorem: 'higher_base_means_higher_redeem_fee',
    file: 'ZUSDFeePipeline.lean',
    desc: 'Fees flow through borrow, redeem and liquidation without leakage; base-rate coupling is monotone (H-RG-004).',
  },
];

function ZUSDMonetarySurface() {
  const [status, setStatus] = useState(null);
  const [statusError, setStatusError] = useState('');
  const [form, setForm] = useState(EMPTY_FORM);
  const [result, setResult] = useState(null);
  const [error, setError] = useState('');
  const [busy, setBusy] = useState(false);

  // Progressive Disclosure: Form tab navigation
  const [activeFormTab, setActiveFormTab] = useState('vault'); // 'vault', 'stability', 'system'

  // Vault Adjuster states
  const [collateralAdjust, setCollateralAdjust] = useState('');
  const [collAdjustMode, setCollAdjustMode] = useState('deposit'); // 'deposit', 'withdraw'
  const [borrowAdjust, setBorrowAdjust] = useState('');
  const [borrowAdjustMode, setBorrowAdjustMode] = useState('mint'); // 'mint', 'repay'

  // Stability Pool states
  const [spAdjust, setSpAdjust] = useState('');
  const [spAdjustMode, setSpAdjustMode] = useState('deposit'); // 'deposit', 'withdraw'

  const needsAmount = useMemo(
    () => [
      'deposit_collateral',
      'withdraw_collateral',
      'mint_zusd',
      'repay_zusd',
      'deposit_sp',
      'withdraw_sp',
      'redeem_zusd',
      'claim_sp_collateral',
      'claim_shutdown_collateral',
      'claim_sp_shutdown_collateral',
      'stake_fee_shares',
      'unstake_fee_shares',
    ].includes(form.action),
    [form.action],
  );
  const needsPrice = form.action === 'bootstrap_oracle' || form.action === 'oracle_report';
  const needsDelta = form.action === 'advance_epoch';

  async function loadStatus() {
    try {
      const payload = await apiGetZusdMonetaryStatus({ timeoutMs: 8000 });
      setStatus(payload?.status || null);
      setStatusError('');
      // Pre-fill actor pubkey if present in status
      if (payload?.status?.vault_owner_pubkey) {
        setForm((curr) => {
          if (!curr.actor_pubkey) {
            return { ...curr, actor_pubkey: payload.status.vault_owner_pubkey };
          }
          return curr;
        });
      }
    } catch (err) {
      setStatus(null);
      setStatusError(err?.message || 'status_unavailable');
    }
  }

  useEffect(() => {
    loadStatus();
  }, []);

  async function handlePrepare() {
    setBusy(true);
    setError('');
    try {
      const payload = await apiPrepareZusdMonetary(buildPayload(form), { timeoutMs: 15000 });
      setResult(payload);
    } catch (err) {
      setResult(null);
      setError(err?.message || 'prepare_failed');
    } finally {
      setBusy(false);
    }
  }

  const liveSummary = result?.transport || null;
  const proofProfile = result?.proof?.profile || null;
  const zkWrapper = result?.proof?.zk_wrapper || null;
  const artifactBinding = zkWrapper?.artifact_binding || null;
  const reportPromotionReady = result?.ok !== false && proofProfile?.promotion_ready === true;
  const latestReportBadge = result?.ok === false
    ? (result?.status || result?.error || 'rejected')
    : result?.report?.preflight?.ok
      ? 'preflight accepted'
      : 'deterministic';
  const liquidationFeeCompFixedE8 =
    status?.liquidation_fee_comp_fixed_collateral_e8 ?? status?.liquidation_gas_comp_fixed_collateral_e8 ?? 0;
  const liquidationFeeCompBps =
    status?.liquidation_fee_comp_bps ?? status?.liquidation_gas_comp_bps ?? 0;
  const branchTcrPct = status?.branch_tcr_bps == null ? null : Number(status.branch_tcr_bps) / 100;

  // NOTE: collateralAmt/debtAmt must be declared before `branchMode`, which
  // reads `debtAmt`. Declaring them after caused a render-time temporal-dead-zone
  // crash ("Cannot access 'debtAmt' before initialization") that the ErrorBoundary caught.
  const collateralSymbol = 'AGRS';
  const collateralAmt = Number(status?.core?.collateral_e8 ?? 0) / E8;
  const debtAmt = Number(status?.core?.debt_e8 ?? 0) / E8;

  const branchMode = status?.branch_mode || (debtAmt > 0 ? 'loading' : 'no_debt');
  const branchModeLabel = branchMode.replaceAll('_', ' ');

  const protocolRevenueZusd = Number(status?.core?.protocol_revenue_zusd_cum_e8 ?? 0) / E8;
  const protocolCollateralFees = Number(status?.core?.protocol_collateral_e8 ?? 0) / E8;
  const oraclePrice = status?.core?.price_e8 ? Number(status.core.price_e8) / E8 : 100;
  const collateralValue = collateralAmt * oraclePrice;
  const currentCR = debtAmt > 0 ? (collateralValue / debtAmt) * 100 : Infinity;
  const mcrPct = status?.core?.mcr_bps ? Number(status.core.mcr_bps) / 100 : 110;
  const ccrPct = status?.core?.ccr_bps ? Number(status.core.ccr_bps) / 100 : 150;
  const currentRiskClass = currentCR < mcrPct ? 'zusd-danger' : currentCR < ccrPct ? 'zusd-warning' : 'zusd-healthy';
  const currentRiskLabel = debtAmt <= 0 ? 'No debt' : currentCR < mcrPct ? 'Liquidation risk' : currentCR < ccrPct ? 'Low buffer' : 'Healthy';
  const liquidationPrice = debtAmt > 0 && collateralAmt > 0 ? (debtAmt * (mcrPct / 100)) / collateralAmt : 0;
  const collAdjustValue = Number.parseFloat(collateralAdjust) || 0;
  const debtAdjustValue = Number.parseFloat(borrowAdjust) || 0;
  const projectedCollateral = Math.max(
    0,
    collateralAmt + (collAdjustMode === 'deposit' ? collAdjustValue : -collAdjustValue),
  );
  const projectedDebt = Math.max(
    0,
    debtAmt + (borrowAdjustMode === 'mint' ? debtAdjustValue : -debtAdjustValue),
  );
  const projectedValue = projectedCollateral * oraclePrice;
  const projectedCR = projectedDebt > 0 ? (projectedValue / projectedDebt) * 100 : Infinity;
  const projectedRiskClass = projectedCR < mcrPct ? 'zusd-danger' : projectedCR < ccrPct ? 'zusd-warning' : 'zusd-healthy';
  const projectedLiqPrice = projectedDebt > 0 && projectedCollateral > 0
    ? (projectedDebt * (mcrPct / 100)) / projectedCollateral
    : 0;
  const maxMintAtMcr = Math.max(0, Math.floor((projectedValue / (mcrPct / 100)) - debtAmt));
  const maxMintAtTarget = Math.max(0, Math.floor((projectedValue / (ccrPct / 100)) - debtAmt));
  const networkLabel = status?.chain_id ? 'Zeno Network' : 'unknown';
  // ── Protocol stat tiles (live, node-reported) ──────────────────────────
  // `num` formats without a forced minimum-fraction (unlike formatAmount,
  // which pins min=2 and would throw RangeError when digits < 2).
  const c = status?.core || {};
  const spDebtZusd = Number(c.sp_debt_e8 ?? 0) / E8;
  const num = (v, d = 2) => (Number.isFinite(v) ? v.toLocaleString(undefined, { maximumFractionDigits: d }) : '—');
  const bps = (v, fallback = null) => (v == null ? fallback : Number(v) / 100);
  // Compact currency for headline tiles (exact value goes in the cell title).
  const usdCompact = (v) => {
    if (!Number.isFinite(v)) return '$0';
    const a = Math.abs(v);
    if (a >= 1e9) return `$${(v / 1e9).toFixed(1)}B`;
    if (a >= 1e6) return `$${(v / 1e6).toFixed(1)}M`;
    if (a >= 1e3) return `$${(v / 1e3).toFixed(1)}K`;
    return formatCurrency(v);
  };
  // Reveal tiny collateral instead of rounding it to "0 AGRS".
  const collateralUnits = collateralAmt > 0 && collateralAmt < 1 ? num(collateralAmt, 8) : num(collateralAmt, 2);
  const statTiles = [
    { label: 'Total debt', value: status ? num(debtAmt, 2) : '—', sub: 'zUSD' },
    { label: 'Collateral value', value: status ? usdCompact(collateralValue) : '—', title: status ? formatCurrency(collateralValue) : '', sub: `${collateralUnits} AGRS`, accent: 'cyan' },
    { label: 'Stability pool', value: status ? num(spDebtZusd, 2) : '—', sub: 'zUSD', accent: 'purple' },
    { label: 'AGRS price', value: status ? usdCompact(oraclePrice) : '—', title: status ? formatCurrency(oraclePrice) : '', sub: c.oracle_seen ? 'oracle live' : 'no oracle', accent: 'green' },
    { label: 'Protocol revenue', value: status ? num(protocolRevenueZusd, 2) : '—', sub: 'zUSD cumulative' },
  ];

  // ── Risk parameters (live, REAL — from status.core) ────────────────────
  const riskParams = [
    ['Minimum collateral ratio', mcrPct != null ? `${num(mcrPct, 1)}%` : '—', 'Below this, the vault is liquidatable'],
    ['Critical collateral ratio', ccrPct != null ? `${num(ccrPct, 1)}%` : '—', 'Below this, the branch enters recovery mode'],
    ['Borrow fee range', (c.borrow_fee_floor_bps != null) ? `${num(bps(c.borrow_fee_floor_bps), 2)}% – ${num(bps(c.borrow_fee_max_bps), 2)}%` : '—', 'Dynamic on the decaying base rate'],
    ['Redemption fee range', (c.redemption_fee_floor_bps != null) ? `${num(bps(c.redemption_fee_floor_bps), 2)}% – ${num(bps(c.redemption_fee_max_bps), 2)}%` : '—', 'Dynamic on the decaying base rate'],
    ['Min debt to open', (c.min_debt_open_e8 != null) ? `${num(Number(c.min_debt_open_e8) / E8, 0)} zUSD` : '—', 'Floor on new vault debt'],
    ['Max epoch redemption', (c.max_epoch_redemption_fraction_bps != null) ? `${num(bps(c.max_epoch_redemption_fraction_bps), 1)}%` : '—', 'Per-epoch redemption throttle'],
    ['Oracle staleness limit', (c.max_oracle_staleness_epochs != null) ? `${c.max_oracle_staleness_epochs} epochs` : '—', 'Fail-closed on a stale price'],
  ];

  // ── Runtime proof profile (live, node-reported claim scope) ────────────
  // Distinct from `proofProfile` above (which is the per-submit result's
  // profile); this is the node's STANDING claim scope from /status.
  const statusProofProfile = status?.proof_profile || null;
  const statusPromotionReady = statusProofProfile?.promotion_ready === true;

  return (
    <section className="zusd-wallet-surface">
      <div className="zusd-hero panel panel-glass animate-fade-in">
        <div>
          <p className="zusd-kicker">Collateralized stablecoin</p>
          <h1>zUSD Monetary Vault</h1>
          <p className="zusd-subtitle">
            Deposit AGRS collateral, mint zUSD debt, and manage your vault around collateral-ratio safety.
          </p>
        </div>
        <div className="zusd-hero-meta">
          <span className="zusd-chip">{collateralSymbol} collateral</span>
          {branchTcrPct != null && (
            <span className="zusd-chip mono">TCR {num(branchTcrPct, 1)}%</span>
          )}
          <span className="zusd-chip zusd-chip-accent">{status?.node_reachable ? 'Network connected' : 'Network unavailable'}</span>
        </div>
      </div>

      <div className="zusd-stat-tiles">
        {statTiles.map((t) => (
          <div className={`zusd-stat-tile${t.accent ? ` accent-${t.accent}` : ''}`} key={t.label}>
            <span className="zusd-stat-label">{t.label}</span>
            <span className="zusd-stat-value mono" title={t.title || undefined}>{t.value}</span>
            <span className="zusd-stat-sub">{t.sub}</span>
          </div>
        ))}
      </div>

      <div className="zusd-wallet-grid">
        <div className="panel zusd-wallet-card zusd-vault-overview">
          <div className="zusd-section-header">
            <h2>Your Vault</h2>
            <span className={`zusd-section-badge ${currentRiskClass}`}>{currentRiskLabel}</span>
          </div>

          <div className="zusd-vault-health">
            <span className="zusd-vault-health-label">Collateral ratio</span>
            <strong className={currentRiskClass}>{formatRatio(currentCR)}</strong>
            <div className="zusd-cr-gauge-bar" aria-label="Vault collateral-ratio buffer">
              <div
                className={`zusd-cr-gauge-fill ${currentCR < mcrPct ? 'fill-danger' : currentCR < ccrPct ? 'fill-warning' : 'fill-healthy'}`}
                style={{ width: `${Math.min(100, Number.isFinite(currentCR) ? (currentCR / 250) * 100 : 100)}%` }}
              />
            </div>
            <div className="zusd-vault-thresholds">
              <span>Liquidation {mcrPct}%</span>
              <span>Target {ccrPct}%+</span>
            </div>
          </div>

          <div className="zusd-vault-metrics">
            <div className="zusd-vault-metric">
              <span>{collateralSymbol} deposited</span>
              <strong>{formatE8(status?.core?.collateral_e8)}</strong>
              <small>{formatCurrency(collateralValue)} value</small>
            </div>
            <div className="zusd-vault-metric">
              <span>zUSD debt</span>
              <strong>{formatE8(status?.core?.debt_e8)}</strong>
              <small>Borrowed balance</small>
            </div>
            <div className="zusd-vault-metric">
              <span>Liquidation price</span>
              <strong>{liquidationPrice > 0 ? formatCurrency(liquidationPrice) : '-'}</strong>
              <small>Per {collateralSymbol}</small>
            </div>
            <div className="zusd-vault-metric">
              <span>Settlement mode</span>
              <strong>{branchModeLabel}</strong>
              <small>{branchTcrPct == null ? 'No active debt' : `${branchTcrPct.toFixed(2)}% branch CR`}</small>
            </div>
            <div className="zusd-vault-metric">
              <span>Stability pool</span>
              <strong>{formatE8(status?.core?.sp_debt_e8)}</strong>
              <small>{formatAmount(Number(status?.stability_pool_balance ?? 0), 4)} zUSD in escrow</small>
            </div>
          </div>

          <div className="zusd-wallet-meta zusd-vault-details">
            <div className="zusd-wallet-kv"><span>Vault Owner</span><span className="zusd-mono">{status?.vault_owner_pubkey || 'none'}</span></div>
            <div className="zusd-wallet-kv"><span>Network</span><span>{networkLabel}</span></div>
            <div className="zusd-wallet-kv"><span>zUSD Asset</span><span className="zusd-mono">{compactId(status?.asset_id || 'unavailable')}</span></div>
            <div className="zusd-wallet-kv"><span>Fee stake asset</span><span className="zusd-mono">{compactId(status?.fee_stake_asset_id || 'unavailable')}</span></div>
            <div className="zusd-wallet-kv">
              <span>Keeper compensation<InfoTip label="Keeper compensation">Liquidation trigger compensation from fixed collateral plus bps.</InfoTip></span>
              <span>{formatE8(liquidationFeeCompFixedE8)} {collateralSymbol} + {liquidationFeeCompBps} bps</span>
            </div>
            <div className="zusd-wallet-kv">
              <span>Borrowing fees<InfoTip label="Borrowing fees">Mint fees accrue to the protocol revenue reserve.</InfoTip></span>
              <span>{formatAmount(protocolRevenueZusd)} zUSD</span>
            </div>
            <div className="zusd-wallet-kv">
              <span>Redemption fees<InfoTip label="Redemption fees">Redemption fees accrue to the protocol collateral reserve.</InfoTip></span>
              <span>{formatAmount(protocolCollateralFees)} {collateralSymbol}</span>
            </div>
            <div className="zusd-wallet-kv">
              <span>Signing mode</span>
              <span>External signer required</span>
            </div>
            <div className="zusd-wallet-kv">
              <span>Shutdown settlement</span>
              <span>
                {status?.shutdown_claim_available || status?.sp_shutdown_claim_available ? 'available' : 'closed'}
              </span>
            </div>
          </div>

          {statusError ? <p className="zusd-wallet-error">Status error: {statusError}</p> : null}
          <button className="btn btn-secondary zusd-wallet-refresh" type="button" onClick={loadStatus}>
            Refresh status
          </button>
        </div>

        <div className="panel zusd-wallet-card zusd-vault-manager">
          <div className="zusd-section-header">
            <h2>Open or Adjust Vault</h2>
            <span className="zusd-section-badge">{collateralSymbol} to zUSD</span>
          </div>

          <div className="zusd-form-tabs">
            <button
              className={`zusd-form-tab-btn ${activeFormTab === 'vault' ? 'tab-active' : ''}`}
              onClick={() => setActiveFormTab('vault')}
              type="button"
            >
              Vault
            </button>
            <button
              className={`zusd-form-tab-btn ${activeFormTab === 'stability' ? 'tab-active' : ''}`}
              onClick={() => setActiveFormTab('stability')}
              type="button"
            >
              Stability Pool
            </button>
            <button
              className={`zusd-form-tab-btn ${activeFormTab === 'system' ? 'tab-active' : ''}`}
              onClick={() => {
                setActiveFormTab('system');
                setForm((c) => ({ ...c, action: 'mint_zusd' }));
              }}
              type="button"
            >
              Advanced
            </button>
          </div>

          <div className="zusd-wallet-form" style={{ marginTop: 'var(--space-md)' }}>
            {activeFormTab === 'vault' && (
              <div className="zusd-cdp-form">
                <div className="zusd-cdp-step">
                  <div className="zusd-cdp-step-head">
                    <span>1</span>
                    <div>
                      <strong>{collAdjustMode === 'deposit' ? 'Deposit AGRS collateral' : 'Withdraw AGRS collateral'}</strong>
                      <small>Collateral backs the zUSD debt in this vault.</small>
                    </div>
                  </div>
                  <div className="zusd-form-row">
                    <div className="input-group" style={{ flex: 1 }}>
                      <label className="label">{collateralSymbol} amount</label>
                      <input
                        className="input input-large"
                        type="number"
                        placeholder="0.0"
                        value={collateralAdjust}
                        onChange={(e) => setCollateralAdjust(e.target.value)}
                        min="0"
                        step="any"
                      />
                    </div>
                    <div className="input-group zusd-mode-field">
                      <label className="label">Action</label>
                      <select
                        className="input"
                        value={collAdjustMode}
                        onChange={(e) => setCollAdjustMode(e.target.value)}
                      >
                        <option value="deposit">Deposit</option>
                        <option value="withdraw">Withdraw</option>
                      </select>
                    </div>
                  </div>
                </div>

                <div className="zusd-cdp-step">
                  <div className="zusd-cdp-step-head">
                    <span>2</span>
                    <div>
                      <strong>{borrowAdjustMode === 'mint' ? 'Mint zUSD' : 'Repay zUSD'}</strong>
                      <small>Minting increases debt. Repayment burns zUSD and restores collateral headroom.</small>
                    </div>
                  </div>
                  <div className="zusd-form-row">
                    <div className="input-group" style={{ flex: 1 }}>
                      <label className="label">zUSD amount</label>
                      <input
                        className="input input-large"
                        type="number"
                        placeholder="0.0"
                        value={borrowAdjust}
                        onChange={(e) => setBorrowAdjust(e.target.value)}
                        min="0"
                        step="any"
                      />
                    </div>
                    <div className="input-group zusd-mode-field">
                      <label className="label">Action</label>
                      <select
                        className="input"
                        value={borrowAdjustMode}
                        onChange={(e) => setBorrowAdjustMode(e.target.value)}
                      >
                        <option value="mint">Mint</option>
                        <option value="repay">Repay</option>
                      </select>
                    </div>
                  </div>
                </div>

                <div className="zusd-preview zusd-vault-preview animate-fade-in">
                  <div className="zusd-preview-row">
                    <span>Vault collateral</span>
                    <span>
                      <span className="zusd-mono">{formatAmount(collateralAmt)}</span>
                      {' -> '}
                      <strong className="zusd-mono">{formatAmount(projectedCollateral)}</strong> {collateralSymbol}
                    </span>
                  </div>
                  <div className="zusd-preview-row">
                    <span>Vault debt</span>
                    <span>
                      <span className="zusd-mono">{formatAmount(debtAmt)}</span>
                      {' -> '}
                      <strong className="zusd-mono">{formatAmount(projectedDebt)}</strong> zUSD
                    </span>
                  </div>
                  <div className="zusd-preview-divider" />
                  <div className="zusd-preview-row">
                    <span>Collateral ratio after</span>
                    <span className={projectedRiskClass}>{formatRatio(projectedCR)}</span>
                  </div>
                  <div className="zusd-preview-row">
                    <span>Liquidation price after</span>
                    <span className="zusd-mono">{projectedLiqPrice > 0 ? formatCurrency(projectedLiqPrice) : '-'}</span>
                  </div>
                  <div className="zusd-preview-row">
                    <span>Mint capacity</span>
                    <span>{maxMintAtTarget.toLocaleString()} zUSD at {ccrPct}% target</span>
                  </div>
                  <div className="zusd-preview-row">
                    <span>Protocol maximum at MCR</span>
                    <span>{maxMintAtMcr.toLocaleString()} zUSD</span>
                  </div>
                </div>
              </div>
            )}

            {/* Stability Pool Tab */}
            {activeFormTab === 'stability' && (
              <>
                <div className="zusd-form-row">
                  <div className="input-group" style={{ flex: 1 }}>
                    <label className="label">Stability Pool Amount</label>
                    <input
                      className="input"
                      type="number"
                      placeholder="0.0"
                      value={spAdjust}
                      onChange={(e) => setSpAdjust(e.target.value)}
                      min="0"
                      step="any"
                    />
                  </div>
                  <div className="input-group" style={{ maxWidth: '140px' }}>
                    <label className="label">Action</label>
                    <select
                      className="input"
                      value={spAdjustMode}
                      onChange={(e) => setSpAdjustMode(e.target.value)}
                    >
                      <option value="deposit">Deposit zUSD</option>
                      <option value="withdraw">Withdraw zUSD</option>
                    </select>
                  </div>
                </div>
                <p className="zusd-wallet-placeholder">
                  Stability Pool writes are unavailable until the production external-signer envelope is integrated.
                </p>
              </>
            )}

            {/* System Ops Tab (Backwards-compatible Developer dropdown) */}
            {activeFormTab === 'system' && (
              <>
                <label className="label" htmlFor="zusd-monetary-action">Action</label>
                <select
                  id="zusd-monetary-action"
                  className="input"
                  value={form.action}
                  onChange={(event) => setForm((current) => ({ ...current, action: event.target.value }))}
                >
                  {ACTIONS.map(([value, label]) => (
                    <option key={value} value={value}>{label}</option>
                  ))}
                </select>

                {needsAmount ? (
                  <>
                    <label className="label" htmlFor="zusd-monetary-amount">Amount (whole units)</label>
                    <input
                      id="zusd-monetary-amount"
                      className="input"
                      type="number"
                      min="1"
                      step="1"
                      value={form.amount}
                      onChange={(event) => setForm((current) => ({ ...current, amount: event.target.value }))}
                    />
                  </>
                ) : null}

                {needsPrice ? (
                  <>
                    <label className="label" htmlFor="zusd-monetary-price">Price E8</label>
                    <input
                      id="zusd-monetary-price"
                      className="input"
                      type="number"
                      min="1"
                      step="1"
                      value={form.price_e8}
                      onChange={(event) => setForm((current) => ({ ...current, price_e8: event.target.value }))}
                    />
                  </>
                ) : null}

                {needsDelta ? (
                  <>
                    <label className="label" htmlFor="zusd-monetary-delta">Epoch Delta</label>
                    <input
                      id="zusd-monetary-delta"
                      className="input"
                      type="number"
                      min="1"
                      step="1"
                      value={form.delta}
                      onChange={(event) => setForm((current) => ({ ...current, delta: event.target.value }))}
                    />
                  </>
                ) : null}
              </>
            )}

            {/* Shared Transaction Settings fold */}
            <details className="zusd-advanced-options">
              <summary>Transaction signing</summary>
              <div className="zusd-wallet-form" style={{ marginTop: 'var(--space-md)' }}>
                <label className="label" htmlFor="zusd-monetary-actor">Actor Pubkey</label>
                <input
                  id="zusd-monetary-actor"
                  className="input"
                  value={form.actor_pubkey}
                  onChange={(event) => setForm((current) => ({ ...current, actor_pubkey: event.target.value }))}
                  placeholder="0x..."
                />

                <label className="label" htmlFor="zusd-monetary-deadline">Deadline Epoch Or Unix Time</label>
                <input
                  id="zusd-monetary-deadline"
                  className="input"
                  type="number"
                  min="1"
                  step="1"
                  value={form.deadline}
                  onChange={(event) => setForm((current) => ({ ...current, deadline: event.target.value }))}
                  placeholder="optional"
                />

                <label className="label" htmlFor="zusd-monetary-fee-limit">Tau Fee Limit (native units)</label>
                <input
                  id="zusd-monetary-fee-limit"
                  className="input"
                  type="number"
                  min="0"
                  step="1"
                  value={form.tx_fee_limit}
                  onChange={(event) => setForm((current) => ({ ...current, tx_fee_limit: event.target.value }))}
                />

              </div>
            </details>

            <p className="zusd-wallet-placeholder" role="status">
              Production profile is prepare-only. Submission is blocked until an external signer returns a verified signed envelope without exposing key material to the browser or API server.
            </p>
            <div className="zusd-wallet-actions">
              {activeFormTab === 'system' && (
                <button className="btn btn-secondary" type="button" onClick={handlePrepare} disabled={busy}>
                  {busy ? 'Preparing...' : 'Prepare unsigned request'}
                </button>
              )}
            </div>

            {error ? <p className="zusd-wallet-error">{error}</p> : null}
          </div>
        </div>
      </div>

      <div className="zusd-wallet-grid">
        <div className="panel zusd-wallet-card">
          <div className="zusd-section-header">
            <h2>Live Context</h2>
            <span className="zusd-section-badge">Auto-derived</span>
          </div>
          {liveSummary ? (
            <div className="zusd-wallet-meta">
              <div className="zusd-wallet-kv"><span>App Hash</span><span className="zusd-mono">{liveSummary.app_hash || 'none'}</span></div>
              <div className="zusd-wallet-kv"><span>Actor</span><span className="zusd-mono">{liveSummary.actor_pubkey}</span></div>
              <div className="zusd-wallet-kv"><span>AGRS Balance</span><span>{formatE8(liveSummary.native_balance_e8)} AGRS</span></div>
              <div className="zusd-wallet-kv"><span>Tau Fee Limit</span><span>{liveSummary.tx_fee_limit ?? '0'}</span></div>
              <div className="zusd-wallet-kv"><span>Fee Limit Covered</span><span>{liveSummary.fee_limit_native_balance_ok === null ? 'unknown' : liveSummary.fee_limit_native_balance_ok ? 'yes' : 'no'}</span></div>
              <div className="zusd-wallet-kv"><span>zUSD Balance</span><span>{formatAmount(Number(liveSummary.zusd_balance ?? 0), 4)} zUSD</span></div>
              <div className="zusd-wallet-kv"><span>Monetary Nonce</span><span>{liveSummary.last_used_nonce}</span></div>
              <div className="zusd-wallet-kv"><span>Tx Sequence</span><span>{liveSummary.tx_sequence_number}</span></div>
              <div className="zusd-wallet-kv"><span>Signing Mode</span><span>{liveSummary.signing_mode || 'prepare_only'}</span></div>
              {liveSummary.fee_limit_warning ? (
                <div className="zusd-wallet-kv"><span>Fee Warning</span><span>{liveSummary.fee_limit_warning}</span></div>
              ) : null}
            </div>
          ) : (
            <p className="zusd-wallet-placeholder">Submit a request to load the current network context.</p>
          )}
        </div>

        <div className="panel zusd-wallet-card">
          <div className="zusd-section-header">
            <h2>Proof Posture</h2>
            <span className="zusd-section-badge">{reportPromotionReady ? 'promotion ready' : 'bounded wrapper'}</span>
          </div>
          {proofProfile ? (
            <div className="zusd-wallet-meta">
              <div className="zusd-wallet-kv"><span>Proof profile</span><span className="zusd-mono">{proofProfile.profile_id || 'none'}</span></div>
              <div className="zusd-wallet-kv"><span>ZK proof verified</span><span>{zkWrapper?.zk_proof_verified ? 'yes' : 'no'}</span></div>
              <div className="zusd-wallet-kv"><span>ZK artifacts</span><span>{proofProfile?.artifact_binding_complete ? 'ready' : 'pending'}</span></div>
              <div className="zusd-wallet-kv"><span>Promotion ready</span><span>{reportPromotionReady ? 'yes' : 'no'}</span></div>
              <div className="zusd-wallet-kv"><span>Artifact binding</span><span className="zusd-mono">{compactId(artifactBinding?.binding_hash)}</span></div>
              <div className="zusd-wallet-kv"><span>Verifier command</span><span className="zusd-mono">{compactId(artifactBinding?.verifier_cmd_hash)}</span></div>
            </div>
          ) : (
            <p className="zusd-wallet-placeholder">No proof-wrapper receipt yet.</p>
          )}
        </div>

        <div className="panel zusd-wallet-card">
          <div className="zusd-section-header">
            <h2>Latest Report</h2>
            <span className="zusd-section-badge">{latestReportBadge}</span>
          </div>
          {result ? (
            <>
              {result.ok === false ? (
                <p className="zusd-wallet-error">
                  Submit rejected: {result.error || result.status || 'rejected'}
                </p>
              ) : null}
              <pre className="zusd-wallet-json">{JSON.stringify(result, null, 2)}</pre>
            </>
          ) : (
            <p className="zusd-wallet-placeholder">No monetary report yet.</p>
          )}
        </div>
      </div>

      <div className="zusd-assurance-grid">
        <div className="panel zusd-wallet-card zusd-risk-card">
          <div className="zusd-section-header">
            <h2>Risk parameters</h2>
            <span className="zusd-section-badge">live</span>
          </div>
          <table className="zusd-rp-table">
            <tbody>
              {riskParams.map(([name, value, note]) => (
                <tr key={name}>
                  <td className="zusd-rp-name">{name}</td>
                  <td className="zusd-rp-value mono">{value}</td>
                  <td className="zusd-rp-note">{note}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>

        <div className="panel zusd-wallet-card zusd-proofs-card">
          <div className="zusd-section-header">
            <h2>Formal proofs</h2>
            <span className="zusd-section-badge">Lean 4 · {ZUSD_LEAN_PROOFS.length} theorems</span>
          </div>

          {statusProofProfile && (
            <div className={`zusd-proof-profile ${statusPromotionReady ? 'is-ready' : 'is-advisory'}`}>
              <div className="zusd-proof-profile-head">
                <span className="zusd-proof-profile-dot" aria-hidden="true" />
                <span className="zusd-proof-profile-label">
                  {statusPromotionReady ? 'Promotion-ready proof profile' : 'Runtime claim scope (not production-final)'}
                </span>
              </div>
              <p className="zusd-proof-profile-detail">
                The node binds and replays the receipt, but does <strong>not</strong> claim ZK execution or production finality.
                {' '}ZK proof verified: <code>{String(statusProofProfile.zk_proof_verified)}</code>.
              </p>
              {Array.isArray(statusProofProfile.covered) && statusProofProfile.covered.length > 0 && (
                <ul className="zusd-proof-coverage">
                  {statusProofProfile.covered.map((item) => (
                    <li key={item} className="cov-on"><span className="zusd-cov-dot" aria-hidden="true" />{item.replaceAll('_', ' ')}</li>
                  ))}
                  {Array.isArray(statusProofProfile.not_covered) && statusProofProfile.not_covered.map((item) => (
                    <li key={item} className="cov-off"><span className="zusd-cov-dot" aria-hidden="true" />{item.replaceAll('_', ' ')}</li>
                  ))}
                </ul>
              )}
            </div>
          )}

          <p className="zusd-fp-caption">
            Machine-checked Lean 4 lemmas (model-level, proven offline) — distinct from the node&apos;s
            runtime claim scope above. The proofs hold for their models; they are not a claim that this
            live node enforces them.
          </p>
          <div className="zusd-fp-list">
            {ZUSD_LEAN_PROOFS.map((pf) => (
              <div className="zusd-fp-row" key={pf.file}>
                <div className="zusd-fp-row-top">
                  <span className="zusd-fp-name">{pf.title}</span>
                  <span className="zusd-fp-badge">Proved</span>
                </div>
                <p className="zusd-fp-desc">{pf.desc}</p>
                <code className="zusd-fp-file mono" title={`Theorem ${pf.theorem} in lean-mathlib/Proofs/${pf.file} (0 sorry)`}>
                  {pf.file} · {pf.theorem}
                </code>
              </div>
            ))}
          </div>
        </div>
      </div>
    </section>
  );
}

export default ZUSDMonetarySurface;
