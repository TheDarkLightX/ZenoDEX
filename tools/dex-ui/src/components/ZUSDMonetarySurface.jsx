import { useEffect, useMemo, useRef, useState } from 'react';
import { apiGetZusdMonetaryStatus, apiPrepareZusdMonetary, apiSubmitZusdMonetary } from '../lib/api.js';
import './ZUSDTauWalletSurface.css';

const E8 = 100_000_000;

const EMPTY_FORM = {
  action: 'mint_zusd',
  actor_pubkey: '',
  signer_privkey: '',
  amount: '100',
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
  ['claim_sp_collateral', 'Claim SP Collateral'],
  ['liquidate', 'Liquidate Vault'],
  ['bootstrap_oracle', 'Bootstrap Oracle'],
  ['oracle_report', 'Oracle Report'],
  ['oracle_commit', 'Oracle Commit'],
  ['advance_epoch', 'Advance Epoch'],
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
    signer_privkey: params.get('signerPrivkey') || '',
    amount: params.get('zusdAmount') || '100',
    amount_e8: params.get('zusdAmountE8') || '',
    price_e8: params.get('zusdPriceE8') || String(100 * E8),
    delta: params.get('zusdDelta') || '1',
    deadline: params.get('zusdDeadline') || '',
    tx_fee_limit: params.get('zusdTxFeeLimit') || params.get('txFeeLimit') || '0',
  };
}

function parsePositiveInt(raw) {
  const value = Number.parseInt(String(raw || '').trim(), 10);
  return Number.isFinite(value) && value > 0 ? value : null;
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

  if (['deposit_collateral', 'withdraw_collateral', 'mint_zusd', 'repay_zusd'].includes(action)) {
    payload.owner_pubkey = actor;
  }
  if (['deposit_sp', 'withdraw_sp', 'redeem_zusd', 'claim_sp_collateral'].includes(action)) {
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
    ].includes(action)
  ) {
    const explicitE8 = parsePositiveInt(form.amount_e8);
    if (explicitE8) {
      payload.amount_e8 = explicitE8;
    } else {
      payload.amount = parsePositiveInt(form.amount) || 0;
    }
  }
  return payload;
}

function ZUSDMonetarySurface() {
  const [status, setStatus] = useState(null);
  const [statusError, setStatusError] = useState('');
  const [form, setForm] = useState(() => readSmokeConfig() || EMPTY_FORM);
  const [result, setResult] = useState(null);
  const [error, setError] = useState('');
  const [busy, setBusy] = useState(false);
  const smokeRan = useRef(false);

  const needsAmount = useMemo(
    () => ['deposit_collateral', 'withdraw_collateral', 'mint_zusd', 'repay_zusd', 'deposit_sp', 'withdraw_sp', 'redeem_zusd', 'claim_sp_collateral'].includes(form.action),
    [form.action],
  );
  const needsPrice = form.action === 'bootstrap_oracle' || form.action === 'oracle_report';
  const needsDelta = form.action === 'advance_epoch';

  async function loadStatus() {
    try {
      const payload = await apiGetZusdMonetaryStatus({ timeoutMs: 8000 });
      setStatus(payload?.status || null);
      setStatusError('');
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

  async function handleSubmit() {
    setBusy(true);
    setError('');
    try {
      const payload = await apiSubmitZusdMonetary(buildPayload(form), { timeoutMs: 20000 });
      setResult(payload);
    } catch (err) {
      setResult(null);
      setError(err?.message || 'submit_failed');
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
    setForm((current) => ({ ...current, ...smoke }));
    void apiSubmitZusdMonetary(buildPayload({ ...EMPTY_FORM, ...smoke }), { timeoutMs: 20000 })
      .then((payload) => {
        setResult(payload);
        setError('');
      })
      .catch((err) => {
        setResult(null);
        setError(err?.message || 'submit_failed');
      });
  }, [busy, status]);

  const liveSummary = result?.transport || null;

  return (
    <section className="zusd-wallet-surface">
      <div className="zusd-hero panel panel-glass animate-fade-in">
        <div>
          <p className="zusd-kicker">Tau testnet monetary lane</p>
          <h1>zUSD Monetary Vault</h1>
          <p className="zusd-subtitle">
            Live stream-11 transactions for collateralized zUSD, stability-pool accounting, liquidation, and collateral claims.
          </p>
        </div>
        <div className="zusd-hero-meta">
          <span className="zusd-chip">Stream 11</span>
          <span className="zusd-chip zusd-chip-accent">{status?.node_reachable ? 'Tau node connected' : 'Tau node required'}</span>
        </div>
      </div>

      <div className="zusd-wallet-grid">
        <div className="panel zusd-wallet-card">
          <div className="zusd-section-header">
            <h2>Monetary State</h2>
            <span className="zusd-section-badge">App-state</span>
          </div>
          <div className="zusd-wallet-meta">
            <div className="zusd-wallet-kv"><span>Chain</span><span>{status?.chain_id || 'unknown'}</span></div>
            <div className="zusd-wallet-kv"><span>Asset ID</span><span className="zusd-mono">{status?.asset_id || 'unavailable'}</span></div>
            <div className="zusd-wallet-kv"><span>Vault Owner</span><span className="zusd-mono">{status?.vault_owner_pubkey || 'none'}</span></div>
            <div className="zusd-wallet-kv"><span>Collateral</span><span>{status?.core?.collateral_e8 ?? 0} E8</span></div>
            <div className="zusd-wallet-kv"><span>Debt</span><span>{status?.core?.debt_e8 ?? 0} E8</span></div>
            <div className="zusd-wallet-kv"><span>Stability Pool Debt</span><span>{status?.core?.sp_debt_e8 ?? 0} E8</span></div>
            <div className="zusd-wallet-kv"><span>SP Escrow</span><span>{status?.stability_pool_balance ?? 0} zUSD</span></div>
            <div className="zusd-wallet-kv"><span>Liquidation Comp Fixed</span><span>{status?.liquidation_gas_comp_fixed_collateral_e8 ?? 0} E8</span></div>
            <div className="zusd-wallet-kv"><span>Liquidation Comp Bps</span><span>{status?.liquidation_gas_comp_bps ?? 0}</span></div>
            <div className="zusd-wallet-kv"><span>Signing</span><span>{status?.allow_local_signing ? 'enabled' : 'prepare only'}</span></div>
          </div>
          {statusError ? <p className="zusd-wallet-error">Status error: {statusError}</p> : null}
          <button className="btn btn-secondary zusd-wallet-refresh" type="button" onClick={loadStatus}>
            Refresh status
          </button>
        </div>

        <div className="panel zusd-wallet-card">
          <div className="zusd-section-header">
            <h2>Prepare Or Submit</h2>
            <span className="zusd-section-badge">Stream 11</span>
          </div>
          <div className="zusd-wallet-form">
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

            <label className="label" htmlFor="zusd-monetary-actor">Actor Pubkey</label>
            <input
              id="zusd-monetary-actor"
              className="input"
              value={form.actor_pubkey}
              onChange={(event) => setForm((current) => ({ ...current, actor_pubkey: event.target.value }))}
              placeholder="0x..."
            />

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

            <label className="label" htmlFor="zusd-monetary-signer">Signer Privkey (local test only)</label>
            <input
              id="zusd-monetary-signer"
              className="input"
              value={form.signer_privkey}
              onChange={(event) => setForm((current) => ({ ...current, signer_privkey: event.target.value }))}
              placeholder="32-byte hex or integer"
            />

            <div className="zusd-wallet-actions">
              <button className="btn btn-secondary" type="button" onClick={handlePrepare} disabled={busy}>
                {busy ? 'Preparing...' : 'Prepare'}
              </button>
              <button className="btn btn-primary" type="button" onClick={handleSubmit} disabled={busy}>
                {busy ? 'Submitting...' : 'Submit to Tau node'}
              </button>
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
              <div className="zusd-wallet-kv"><span>Native Balance</span><span>{liveSummary.native_balance_e8 ?? 'unknown'} E8</span></div>
              <div className="zusd-wallet-kv"><span>Tau Fee Limit</span><span>{liveSummary.tx_fee_limit ?? '0'}</span></div>
              <div className="zusd-wallet-kv"><span>Fee Limit Covered</span><span>{liveSummary.fee_limit_native_balance_ok === null ? 'unknown' : liveSummary.fee_limit_native_balance_ok ? 'yes' : 'no'}</span></div>
              <div className="zusd-wallet-kv"><span>zUSD Balance</span><span>{liveSummary.zusd_balance}</span></div>
              <div className="zusd-wallet-kv"><span>Monetary Nonce</span><span>{liveSummary.last_used_nonce}</span></div>
              <div className="zusd-wallet-kv"><span>Tx Sequence</span><span>{liveSummary.tx_sequence_number}</span></div>
              {liveSummary.fee_limit_warning ? (
                <div className="zusd-wallet-kv"><span>Fee Warning</span><span>{liveSummary.fee_limit_warning}</span></div>
              ) : null}
            </div>
          ) : (
            <p className="zusd-wallet-placeholder">Prepare or submit a request to load the current Tau-node context.</p>
          )}
        </div>

        <div className="panel zusd-wallet-card">
          <div className="zusd-section-header">
            <h2>Latest Report</h2>
            <span className="zusd-section-badge">{result?.report?.preflight?.ok ? 'preflight accepted' : 'deterministic'}</span>
          </div>
          {result ? (
            <pre className="zusd-wallet-json">{JSON.stringify(result, null, 2)}</pre>
          ) : (
            <p className="zusd-wallet-placeholder">No monetary report yet.</p>
          )}
        </div>
      </div>
    </section>
  );
}

export default ZUSDMonetarySurface;
