import { useEffect, useMemo, useRef, useState } from 'react';
import { apiGetZusdMonetaryStatus, apiPrepareZusdMonetary, apiSubmitZusdMonetary } from '../lib/api.js';
import WalletConnect from './WalletConnect.jsx';
import WalletRecoveryPrompt from './WalletRecoveryPrompt.jsx';
import { formatZusdStatusIssue } from './zusd/statusCopy.js';
import './ZUSDTauWalletSurface.css';

const E8 = 100_000_000;

const EMPTY_FORM = {
  action: 'mint_zusd',
  actor_pubkey: '',
  signer_privkey: '',
  amount: '100',
  zk_proof_json: '',
  price_e8: String(100 * E8),
  delta: '1',
  deadline: '',
  tx_fee_limit: '0',
  signed_tau_tx_payload: '',
};

const ACTIONS = [
  ['deposit_collateral', 'Deposit Collateral'],
  ['withdraw_collateral', 'Withdraw Collateral'],
  ['mint_zusd', 'Mint zUSD'],
  ['repay_zusd', 'Repay zUSD'],
  ['deposit_sp', 'Deposit Stability Pool'],
  ['withdraw_sp', 'Withdraw Stability Pool'],
  ['redeem_zusd', 'Redeem zUSD'],
  ['claim_shutdown_collateral', 'Claim Emergency Collateral'],
  ['claim_sp_shutdown_collateral', 'Claim Pool Emergency Collateral'],
  ['claim_sp_collateral', 'Claim Pool Collateral'],
  ['stake_fee_shares', 'Stake Rewards'],
  ['activate_fee_stake', 'Activate Rewards'],
  ['claim_fee_rewards', 'Claim Fee Rewards'],
  ['unstake_fee_shares', 'Unstake Rewards'],
  ['liquidate', 'Liquidate Vault'],
  ['bootstrap_oracle', 'Initialize Price Feed'],
  ['oracle_report', 'Submit Price'],
  ['oracle_commit', 'Confirm Price'],
  ['advance_epoch', 'Advance Time Period'],
];

function readSmokeConfig() {
  if (typeof window === 'undefined') {
    return null;
  }
  const params = new URLSearchParams(window.location.search);
  if (params.get('zenodexUiSmokeZusdMonetary') !== '1') {
    return null;
  }
  return {
    action: params.get('zusdMonetaryAction') || 'mint_zusd',
    actor_pubkey: params.get('actorPubkey') || params.get('senderPubkey') || '',
    signer_privkey: params.get('signerPrivkey') || params.get('smokeSignerPrivkey') || '',
    amount: params.get('zusdAmount') || '100',
    amount_e8: params.get('zusdAmountE8') || '',
    zk_proof_json: params.get('zusdZkProofJson') || params.get('zkProofJson') || '',
    price_e8: params.get('zusdPriceE8') || String(100 * E8),
    delta: params.get('zusdDelta') || '1',
    deadline: params.get('zusdDeadline') || '',
    tx_fee_limit: params.get('zusdTxFeeLimit') || params.get('txFeeLimit') || '0',
    signed_tau_tx_payload:
      params.get('signedTauTxPayload') || params.get('signed_tau_tx_payload') || params.get('zusdSignedTauTxPayload') || '',
  };
}

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
  if (form.signer_privkey.trim()) {
    payload.signer_privkey = form.signer_privkey.trim();
  }
  if (String(form.tx_fee_limit || '').trim()) {
    payload.tx_fee_limit = String(form.tx_fee_limit).trim();
  }
  if (form.signed_tau_tx_payload.trim()) {
    payload.signed_tau_tx_payload = form.signed_tau_tx_payload.trim();
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

function ZUSDMonetarySurface({ wallet = null, onStatusChange = null, onConnect = null, onOpenKeys = null }) {
  const connectedAccount = (wallet?.address || '').trim();
  const [status, setStatus] = useState(null);
  const [statusError, setStatusError] = useState('');
  const [form, setForm] = useState(
    () => readSmokeConfig() || { ...EMPTY_FORM, actor_pubkey: connectedAccount },
  );
  const [, setResult] = useState(null);
  const [error, setError] = useState('');
  const [busy, setBusy] = useState(false);
  const smokeRan = useRef(false);

  // Expose status to parent for the sticky health bar
  const loadStatusRef = useRef(null);
  useEffect(() => {
    if (onStatusChange) {
      onStatusChange({ status, statusError, loadStatus: loadStatusRef.current });
    }
  }, [status, statusError, onStatusChange]);

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

  // Orchestrator states
  const [orchestrationStep, setOrchestrationStep] = useState(0);
  const [orchestrationMessage, setOrchestrationMessage] = useState('');

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
    loadStatusRef.current = loadStatus;
    try {
      const payload = await apiGetZusdMonetaryStatus({
        account: form.actor_pubkey.trim() || '',
        timeoutMs: 8000,
      });
      setStatus(payload?.status || null);
      setStatusError('');
      // Convenience prefill of the global vault owner ONLY when no wallet has
      // driven the field this session (operator inspecting the vault without a
      // wallet). Once a wallet connects, empty means intentionally empty — do not
      // rehydrate the disconnected account.
      if (payload?.status?.vault_owner_pubkey && !walletEverConnectedRef.current) {
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
    // Refetch account-aware status when the actor (connected account) changes
    // so balances/positions/collateral reflect THAT account.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [form.actor_pubkey]);

  // Bind the account-aware status query to the CONNECTED wallet: when the wallet
  // identity changes, set the actor field to it so balances/positions/collateral
  // reflect THAT account (fixes "50k shows in Pool but not zUSD"). Manual edits
  // between wallet switches are preserved — we only react to identity changes.
  const prevWalletRef = useRef(connectedAccount);
  // Once a wallet has driven the field this session, the wallet binding is
  // authoritative: an empty field means INTENTIONALLY empty, so the vault-owner
  // convenience prefill in loadStatus must not rehydrate the disconnected account.
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
      setForm((curr) => ({ ...curr, actor_pubkey: connectedAccount }));
    } else if (!connectedAccount && previous) {
      prevWalletRef.current = '';
      // On disconnect, clear ONLY if the field still holds the disconnected
      // wallet (so a manual edit survives).
      setForm((curr) =>
        curr.actor_pubkey === previous ? { ...curr, actor_pubkey: '' } : curr,
      );
    }
  }, [connectedAccount]);

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

  async function handleSubmit() {
    setBusy(true);
    setError('');
    try {
      const payload = await apiSubmitZusdMonetary(buildPayload(form), { timeoutMs: 20000 });
      setResult(payload);
      await loadStatus();
    } catch (err) {
      setResult(null);
      setError(err?.message || 'submit_failed');
    } finally {
      setBusy(false);
    }
  }

  // Sequential Orchestration for Vault Adjuster
  async function handleUnifiedAdjustment() {
    setBusy(true);
    setError('');
    setResult(null);
    setOrchestrationStep(1);
    setOrchestrationMessage('Validating settings...');

    try {
      const actor = form.actor_pubkey.trim();
      if (!actor) {
        throw new Error('Wallet public key is required. Open Transaction signing and set the actor key.');
      }

      const collVal = parseFloat(collateralAdjust) || 0;
      const borrowVal = parseFloat(borrowAdjust) || 0;

      if (collVal <= 0 && borrowVal <= 0) {
        throw new Error('Please specify a collateral or debt adjustment amount.');
      }

      const common = {
        actor_pubkey: form.actor_pubkey,
        signer_privkey: form.signer_privkey,
        deadline: form.deadline,
        tx_fee_limit: form.tx_fee_limit,
        signed_tau_tx_payload: form.signed_tau_tx_payload,
      };

      // Step 1: Collateral adjustment
      let depositRes = null;
      if (collVal > 0) {
        const collAction = collAdjustMode === 'deposit' ? 'deposit_collateral' : 'withdraw_collateral';
        const collActionLabel = collAdjustMode === 'deposit' ? 'Depositing collateral' : 'Withdrawing collateral';
        setOrchestrationMessage(`Step 1/2: Submitting ${collActionLabel} (${collVal} units)...`);

        const payload = buildPayload({
          ...common,
          action: collAction,
          amount: String(collVal),
        });

        depositRes = await apiSubmitZusdMonetary(payload, { timeoutMs: 20000 });
        if (!depositRes || !depositRes.ok) {
          throw new Error(depositRes?.error || depositRes?.status || `${collAction} failed`);
        }
        setResult(depositRes);
      }

      // Step 2: Debt adjustment
      if (borrowVal > 0) {
        if (collVal > 0) {
          setOrchestrationMessage('Synchronizing state with node...');
          await new Promise((resolve) => setTimeout(resolve, 1500));
          await loadStatus();
        }

        const debtAction = borrowAdjustMode === 'mint' ? 'mint_zusd' : 'repay_zusd';
        const debtActionLabel = borrowAdjustMode === 'mint' ? 'Minting zUSD' : 'Repaying zUSD';
        setOrchestrationStep(2);
        setOrchestrationMessage(`Step 2/2: Submitting ${debtActionLabel} (${borrowVal} units)...`);

        const payload = buildPayload({
          ...common,
          action: debtAction,
          amount: String(borrowVal),
        });

        const borrowRes = await apiSubmitZusdMonetary(payload, { timeoutMs: 20000 });
        if (!borrowRes || !borrowRes.ok) {
          throw new Error(borrowRes?.error || borrowRes?.status || `${debtAction} failed`);
        }
        setResult(borrowRes);
      }

      setOrchestrationMessage('Vault adjustment completed successfully!');
      setCollateralAdjust('');
      setBorrowAdjust('');
      await loadStatus();
    } catch (err) {
      setResult(null);
      setError(err?.message || 'Adjustment failed');
    } finally {
      setBusy(false);
      setOrchestrationStep(0);
    }
  }

  // Stability Pool submits
  async function handleStabilitySubmit() {
    setBusy(true);
    setError('');
    setResult(null);
    try {
      const actor = form.actor_pubkey.trim();
      if (!actor) {
        throw new Error('Wallet public key is required. Open Transaction signing and set the actor key.');
      }

      const spVal = parseFloat(spAdjust) || 0;
      if (spVal <= 0) {
        throw new Error('Please specify an amount.');
      }

      const spAction = spAdjustMode === 'deposit' ? 'deposit_sp' : 'withdraw_sp';
      const payload = buildPayload({
        ...form,
        action: spAction,
        amount: String(spVal),
      });

      const res = await apiSubmitZusdMonetary(payload, { timeoutMs: 20000 });
      setResult(res);
      setSpAdjust('');
      await loadStatus();
    } catch (err) {
      setError(err?.message || 'Stability pool transaction failed');
    } finally {
      setBusy(false);
    }
  }

  async function handleClaimSpRewards() {
    setBusy(true);
    setError('');
    setResult(null);
    try {
      const actor = form.actor_pubkey.trim();
      if (!actor) {
        throw new Error('Wallet public key is required. Open Transaction signing and set the actor key.');
      }

      const payload = buildPayload({
        ...form,
        action: 'claim_sp_collateral',
      });
      const res = await apiSubmitZusdMonetary(payload, { timeoutMs: 20000 });
      setResult(res);
      await loadStatus();
    } catch (err) {
      setError(err?.message || 'Claim rewards failed');
    } finally {
      setBusy(false);
    }
  }

  async function handleShutdownClaim(source) {
    setBusy(true);
    setError('');
    setResult(null);
    try {
      const actor = form.actor_pubkey.trim();
      if (!actor) {
        throw new Error('Wallet public key is required. Open Transaction signing and set the actor key.');
      }
      const amount = source === 'stability_pool' ? (Number.parseFloat(spAdjust) || 0) : (Number.parseFloat(borrowAdjust) || 0);
      if (amount <= 0) {
        throw new Error('Enter the zUSD amount for the shutdown claim.');
      }
      const payload = buildPayload({
        ...form,
        action: source === 'stability_pool' ? 'claim_sp_shutdown_collateral' : 'claim_shutdown_collateral',
        amount: String(amount),
      });
      const res = await apiSubmitZusdMonetary(payload, { timeoutMs: 20000 });
      setResult(res);
      if (source === 'stability_pool') {
        setSpAdjust('');
      } else {
        setBorrowAdjust('');
      }
      await loadStatus();
    } catch (err) {
      setError(err?.message || 'Shutdown claim failed');
    } finally {
      setBusy(false);
    }
  }

  useEffect(() => {
    const smoke = readSmokeConfig();
    if (!smoke || smokeRan.current || busy) {
      return;
    }
    if (status?.node_reachable !== true) {
      return;
    }
    smokeRan.current = true;
    async function runSmoke() {
      const nextSmoke = { ...smoke };
      setForm((current) => ({ ...current, ...nextSmoke }));
      if (!nextSmoke.signer_privkey.trim() && !nextSmoke.signed_tau_tx_payload.trim()) {
        throw new Error('Signing key or signed transaction required');
      }
      const payloadIn = buildPayload({ ...EMPTY_FORM, ...nextSmoke });
      return apiSubmitZusdMonetary(payloadIn, { timeoutMs: 20000 });
    }
    void runSmoke()
      .then((payload) => {
        setResult(payload);
        setError('');
      })
      .catch((err) => {
        setResult(null);
        setError(err?.message || 'submit_failed');
      });
  }, [busy, status]);

  const branchTcrPct = status?.branch_tcr_bps == null ? null : Number(status.branch_tcr_bps) / 100;
  const accountZusdBalance = status?.account_view ? Number(status.account_view.zusd_balance ?? 0) : null;
  const accountSpDeposit = status?.account_view ? Number(status.account_view.sp_deposit_e8 ?? 0) / E8 : null;
  const hasVaultStatus = status?.node_reachable === true && Boolean(status?.core);

  const collateralSymbol = 'AGRS';
  const collateralAmt = Number(status?.core?.collateral_e8 ?? 0) / E8;
  const debtAmt = Number(status?.core?.debt_e8 ?? 0) / E8;

  const protocolRevenueZusd = Number(status?.core?.protocol_revenue_zusd_cum_e8 ?? 0) / E8;
  const oraclePrice = status?.core?.price_e8 ? Number(status.core.price_e8) / E8 : 100;
  const collateralValue = collateralAmt * oraclePrice;
  const currentCR = debtAmt > 0 ? (collateralValue / debtAmt) * 100 : Infinity;
  const mcrPct = status?.core?.mcr_bps ? Number(status.core.mcr_bps) / 100 : 110;
  const ccrPct = status?.core?.ccr_bps ? Number(status.core.ccr_bps) / 100 : 150;
  const currentRiskClass = currentCR < mcrPct ? 'zusd-danger' : currentCR < ccrPct ? 'zusd-warning' : 'zusd-healthy';
  const currentRiskLabel = !hasVaultStatus
    ? 'Status needed'
    : debtAmt <= 0 ? 'No debt' : currentCR < mcrPct ? 'Liquidation risk' : currentCR < ccrPct ? 'Low buffer' : 'Healthy';
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
  const vaultSubmitLabel = collAdjustMode === 'deposit' && borrowAdjustMode === 'mint'
    ? 'Deposit AGRS and mint zUSD'
    : collAdjustMode === 'withdraw' && borrowAdjustMode === 'repay'
      ? 'Repay zUSD and withdraw AGRS'
      : 'Submit vault update';

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
  // Reveal tiny collateral instead of rounding to "0 AGRS" (the test fixture
  // holds 0.00001 AGRS, which must reconcile with its $ value).
  const collateralUnits = collateralAmt > 0 && collateralAmt < 1 ? num(collateralAmt, 8) : num(collateralAmt, 2);
  const statTiles = [
    { label: 'Total debt', value: num(debtAmt, 2), sub: 'zUSD' },
    { label: 'Collateral value', value: usdCompact(collateralValue), title: formatCurrency(collateralValue), sub: `${collateralUnits} AGRS`, accent: 'cyan' },
    { label: 'Stability pool', value: num(spDebtZusd, 2), sub: 'zUSD', accent: 'purple' },
    { label: 'AGRS price', value: usdCompact(oraclePrice), title: formatCurrency(oraclePrice), sub: c.oracle_seen ? 'price feed active' : 'awaiting price feed', accent: 'green' },
    { label: 'Protocol revenue', value: num(protocolRevenueZusd, 2), sub: 'zUSD cumulative' },
  ];

  // ── Risk parameters (live, REAL — from status.core) ────────────────────
  const riskParams = [
    ['Minimum collateral ratio', mcrPct != null ? `${num(mcrPct, 1)}%` : '—', 'Below this, the vault can be liquidated'],
    ['Critical collateral ratio', ccrPct != null ? `${num(ccrPct, 1)}%` : '—', 'Below this, the system enters recovery mode'],
    ['Borrow fee range', (c.borrow_fee_floor_bps != null) ? `${num(bps(c.borrow_fee_floor_bps), 2)}% – ${num(bps(c.borrow_fee_max_bps), 2)}%` : '—', 'Dynamic based on current activity'],
    ['Redemption fee range', (c.redemption_fee_floor_bps != null) ? `${num(bps(c.redemption_fee_floor_bps), 2)}% – ${num(bps(c.redemption_fee_max_bps), 2)}%` : '—', 'Dynamic based on current activity'],
    ['Min debt to open', (c.min_debt_open_e8 != null) ? `${num(Number(c.min_debt_open_e8) / E8, 0)} zUSD` : '—', 'Minimum amount to open a vault'],
    ['Max redemption per period', (c.max_epoch_redemption_fraction_bps != null) ? `${num(bps(c.max_epoch_redemption_fraction_bps), 1)}%` : '—', 'Limits redemptions per time period'],
    ['Price feed staleness limit', (c.max_oracle_staleness_epochs != null) ? `${c.max_oracle_staleness_epochs} periods` : '—', 'Rejects transactions if price is too old'],
  ];
  const localTestnetLabel = status?.node_reachable
    ? 'Local testnet connected'
    : 'Connect local node to manage your vault';
  const statusIssue = formatZusdStatusIssue(statusError);

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
        {connectedAccount && (
          <div className="zusd-hero-meta">
            {branchTcrPct != null && (
              <span className="zusd-chip mono">System ratio {num(branchTcrPct, 1)}%</span>
            )}
            <span className={`zusd-chip ${status?.node_reachable ? 'zusd-chip-accent' : ''}`}>{localTestnetLabel}</span>
          </div>
        )}
      </div>

      {connectedAccount && hasVaultStatus && (
        <div className="zusd-stat-tiles">
          {statTiles.map((t) => (
            <div className={`zusd-stat-tile${t.accent ? ` accent-${t.accent}` : ''}`} key={t.label}>
              <span className="zusd-stat-label">{t.label}</span>
              <span className="zusd-stat-value mono" title={t.title || undefined}>{t.value}</span>
              <span className="zusd-stat-sub">{t.sub}</span>
            </div>
          ))}
        </div>
      )}

      {connectedAccount && (
        <WalletRecoveryPrompt compact onOpenKeys={onOpenKeys} />
      )}

      {!connectedAccount ? (
        <div className="panel zusd-wallet-card zusd-empty-cta">
          <div className="zusd-empty-cta-body">
            <span className="zusd-empty-icon" aria-hidden="true">🔌</span>
            <h2>Connect your wallet</h2>
            <p>Connect to deposit collateral and start minting zUSD.</p>
            <ul className="zusd-empty-list">
              <li>Deposit AGRS as collateral</li>
              <li>Mint zUSD against your collateral</li>
              <li>Track your collateral ratio</li>
              <li>Transfer zUSD to other addresses</li>
            </ul>
            {onConnect ? (
              <WalletConnect wallet={wallet} onConnect={onConnect} />
            ) : (
              <p className="zusd-empty-hint">Use the Connect button in the header to get started.</p>
            )}
          </div>
        </div>
      ) : !hasVaultStatus ? (
        <div className="panel zusd-wallet-card zusd-status-empty" role="status" aria-busy={statusIssue ? undefined : 'true'}>
          <div className="zusd-status-empty-copy">
            <h2>{statusIssue ? 'Vault status needs local node' : 'Loading vault status'}</h2>
            <p>
              {statusIssue || 'Fetching vault balance, collateral ratio, and liquidation state.'}
            </p>
            <p>
              No vault balance, collateral ratio, or liquidation state is shown until status loads.
            </p>
          </div>
          {statusIssue ? (
            <button className="btn btn-secondary" type="button" onClick={loadStatus}>
              Retry status
            </button>
          ) : null}
        </div>
      ) : (
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
              <span>Your zUSD balance</span>
              <strong>{accountZusdBalance == null ? '-' : formatAmount(accountZusdBalance, 4)}</strong>
              <small>{accountSpDeposit == null ? 'Connected wallet balance pending' : `${formatAmount(accountSpDeposit, 4)} zUSD in stability pool`}</small>
            </div>
            <div className="zusd-vault-metric">
              <span>Liquidation price</span>
              <strong>{liquidationPrice > 0 ? formatCurrency(liquidationPrice) : '-'}</strong>
              <small>Per {collateralSymbol}</small>
            </div>
            <div className="zusd-vault-metric">
              <span>Stability pool</span>
              <strong>{formatE8(status?.core?.sp_debt_e8)}</strong>
              <small>{formatAmount(Number(status?.stability_pool_balance ?? 0), 4)} zUSD in escrow</small>
            </div>
          </div>

          {statusIssue ? (
            <div className="zusd-status-callout" role="status">
              <strong>Local testnet needs reconnecting</strong>
              <span>{statusIssue}</span>
              <button className="btn btn-secondary" type="button" onClick={loadStatus}>
                Retry status
              </button>
            </div>
          ) : null}
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
                    <span>System limit at minimum ratio</span>
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
                <button
                  className="btn btn-secondary w-100"
                  style={{ marginTop: 'var(--space-md)' }}
                  onClick={handleClaimSpRewards}
                  disabled={busy}
                  type="button"
                >
                  Claim Collateral Rewards
                </button>
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
                    <label className="label" htmlFor="zusd-monetary-price">Price (8 decimals)</label>
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
                    <label className="label" htmlFor="zusd-monetary-delta">Time Period Change</label>
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
                <label className="label" htmlFor="zusd-monetary-actor">Account Address</label>
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

                <label className="label" htmlFor="zusd-monetary-fee-limit">Maximum Fee (tokens)</label>
                <input
                  id="zusd-monetary-fee-limit"
                  className="input"
                  type="number"
                  min="0"
                  step="1"
                  value={form.tx_fee_limit}
                  onChange={(event) => setForm((current) => ({ ...current, tx_fee_limit: event.target.value }))}
                />


                <label className="label" htmlFor="zusd-monetary-signed-payload">Signed Transaction Data</label>
                <textarea
                  id="zusd-monetary-signed-payload"
                  className="input zusd-wallet-textarea"
                  rows={6}
                  value={form.signed_tau_tx_payload}
                  onChange={(event) => setForm((current) => ({ ...current, signed_tau_tx_payload: event.target.value }))}
                  placeholder='{"sender_pubkey":"...","signature":"..."}'
                />
              </div>
            </details>

            {/* Action buttons */}
            <div className="zusd-wallet-actions">
              {activeFormTab === 'vault' && (
                <>
                  <button
                    className="btn btn-primary w-100"
                    type="button"
                    onClick={handleUnifiedAdjustment}
                    disabled={busy || (collAdjustValue <= 0 && debtAdjustValue <= 0)}
                  >
                    {busy ? 'Processing...' : vaultSubmitLabel}
                  </button>
                  {status?.shutdown_claim_available ? (
                    <button
                      className="btn btn-secondary w-100"
                      type="button"
                      onClick={() => handleShutdownClaim('free')}
                      disabled={busy || debtAdjustValue <= 0}
                    >
                      Claim emergency collateral
                    </button>
                  ) : null}
                </>
              )}
              {activeFormTab === 'stability' && (
                <>
                  <button className="btn btn-primary w-100" type="button" onClick={handleStabilitySubmit} disabled={busy}>
                    {busy ? 'Processing...' : 'Submit Stability Pool'}
                  </button>
                  {status?.sp_shutdown_claim_available ? (
                    <button
                      className="btn btn-secondary w-100"
                      type="button"
                      onClick={() => handleShutdownClaim('stability_pool')}
                      disabled={busy || (Number.parseFloat(spAdjust) || 0) <= 0}
                    >
                      Claim shutdown pool share
                    </button>
                  ) : null}
                </>
              )}
              {activeFormTab === 'system' && (
                <>
                  <button className="btn btn-secondary" type="button" onClick={handlePrepare} disabled={busy}>
                    {busy ? 'Preparing...' : 'Prepare'}
                  </button>
                  <button className="btn btn-primary" type="button" onClick={handleSubmit} disabled={busy}>
                    {busy ? 'Submitting...' : 'Submit transaction'}
                  </button>
                </>
              )}
            </div>

            {/* Sequence Status messaging */}
            {orchestrationStep > 0 && (
              <div className="zusd-orchestrator-status">
                <span className="spinner-inline" />
                <span style={{ marginLeft: '8px' }}>{orchestrationMessage}</span>
              </div>
            )}

            {error ? <p className="zusd-wallet-error">{error}</p> : null}
          </div>
        </div>
      </div>
      )}

      {connectedAccount && hasVaultStatus && (
        <details className="zusd-risk-details">
          <summary>System risk settings</summary>
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
          </div>
        </details>
      )}
    </section>
  );
}

export default ZUSDMonetarySurface;
