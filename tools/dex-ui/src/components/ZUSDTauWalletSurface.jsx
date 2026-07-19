import { useEffect, useMemo, useState } from 'react';
import { apiGetZusdWalletStatus, apiPrepareZusdWallet } from '../lib/api.js';
import './ZUSDTauWalletSurface.css';

const EMPTY_FORM = {
  action: 'transfer',
  sender_pubkey: '',
  recipient_pubkey: '',
  operator_pubkey: '',
  amount: '100',
  deadline: '',
};

function buildPayload(form) {
  const payload = {
    action: form.action,
    amount: Number.parseInt(form.amount || '0', 10),
  };
  if (form.deadline.trim()) {
    payload.deadline = Number.parseInt(form.deadline.trim(), 10);
  }
  if (form.sender_pubkey.trim()) {
    payload.sender_pubkey = form.sender_pubkey.trim();
  }
  if (form.recipient_pubkey.trim()) {
    payload.recipient_pubkey = form.recipient_pubkey.trim();
  }
  if (form.operator_pubkey.trim()) {
    payload.operator_pubkey = form.operator_pubkey.trim();
  }
  return payload;
}

function ZUSDTauWalletSurface() {
  const [status, setStatus] = useState(null);
  const [statusError, setStatusError] = useState('');
  const [form, setForm] = useState(EMPTY_FORM);
  const [result, setResult] = useState(null);
  const [error, setError] = useState('');
  const [busy, setBusy] = useState(false);

  const isTransfer = form.action === 'transfer';
  const isMint = form.action === 'mint';
  const isBurn = form.action === 'burn';

  async function loadStatus() {
    try {
      const payload = await apiGetZusdWalletStatus({ timeoutMs: 8000 });
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

  const liveSummary = useMemo(() => {
    if (!result?.transport) return null;
    return result.transport;
  }, [result]);

  async function handlePrepare() {
    setBusy(true);
    setError('');
    try {
      const payload = await apiPrepareZusdWallet(buildPayload(form), { timeoutMs: 15000 });
      setResult(payload);
    } catch (err) {
      setResult(null);
      setError(err?.message || 'prepare_failed');
    } finally {
      setBusy(false);
    }
  }

  return (
    <section className="zusd-wallet-surface">
      <div className="zusd-hero panel panel-glass animate-fade-in">
        <div>
          <p className="zusd-kicker">zUSD account operations</p>
          <h1>zUSD Wallet</h1>
          <p className="zusd-subtitle">
            Review account balances and prepare unsigned zUSD wallet transactions for an external signer.
          </p>
        </div>
        <div className="zusd-hero-meta">
          <span className="zusd-chip">Live posture</span>
          <span className="zusd-chip zusd-chip-accent">{status?.node_reachable ? 'Network connected' : 'Network unavailable'}</span>
        </div>
      </div>

      <div className="zusd-wallet-grid">
        <div className="panel zusd-wallet-card">
          <div className="zusd-section-header">
            <h2>Wallet Status</h2>
            <span className="zusd-section-badge">Network-backed</span>
          </div>
          <div className="zusd-wallet-meta">
            <div className="zusd-wallet-kv"><span>Chain</span><span>{status?.chain_id || 'unknown'}</span></div>
            <div className="zusd-wallet-kv"><span>Asset ID</span><span className="zusd-mono">{status?.asset_id || 'unavailable'}</span></div>
            <div className="zusd-wallet-kv"><span>Endpoint</span><span>{status?.tau_host || 'network'}:{status?.tau_port || '-'}</span></div>
            <div className="zusd-wallet-kv"><span>Bridge</span><span>{status?.app_bridge_available ? 'available' : 'not detected'}</span></div>
            <div className="zusd-wallet-kv"><span>Signing</span><span>External signer required</span></div>
            <div className="zusd-wallet-kv"><span>Operator</span><span className="zusd-mono">{status?.token_operator_pubkey || 'not configured'}</span></div>
          </div>
          {statusError ? <p className="zusd-wallet-error">Status error: {statusError}</p> : null}
          {!statusError ? (
            <button className="btn btn-secondary zusd-wallet-refresh" type="button" onClick={loadStatus}>
              Refresh status
            </button>
          ) : null}
        </div>

        <div className="panel zusd-wallet-card">
          <div className="zusd-section-header">
            <h2>Prepare transfer</h2>
            <span className="zusd-section-badge">Unsigned request</span>
          </div>
          <div className="zusd-wallet-form">
            <label className="label" htmlFor="zusd-action">Action</label>
            <select
              id="zusd-action"
              className="input"
              value={form.action}
              onChange={(event) => setForm((current) => ({ ...current, action: event.target.value }))}
            >
              <option value="transfer">Transfer</option>
              <option value="mint">Mint</option>
              <option value="burn">Burn</option>
            </select>

            {(isTransfer || isBurn) ? (
              <>
                <label className="label" htmlFor="zusd-sender">Sender Pubkey</label>
                <input
                  id="zusd-sender"
                  className="input"
                  value={form.sender_pubkey}
                  onChange={(event) => setForm((current) => ({ ...current, sender_pubkey: event.target.value }))}
                  placeholder="0x..."
                />
              </>
            ) : null}

            {(isTransfer || isMint) ? (
              <>
                <label className="label" htmlFor="zusd-recipient">Recipient Pubkey</label>
                <input
                  id="zusd-recipient"
                  className="input"
                  value={form.recipient_pubkey}
                  onChange={(event) => setForm((current) => ({ ...current, recipient_pubkey: event.target.value }))}
                  placeholder="0x..."
                />
              </>
            ) : null}

            {isMint ? (
              <>
                <label className="label" htmlFor="zusd-operator">Operator Pubkey</label>
                <input
                  id="zusd-operator"
                  className="input"
                  value={form.operator_pubkey}
                  onChange={(event) => setForm((current) => ({ ...current, operator_pubkey: event.target.value }))}
                  placeholder="0x..."
                />
              </>
            ) : null}

            <label className="label" htmlFor="zusd-amount">Amount</label>
            <input
              id="zusd-amount"
              className="input"
              type="number"
              min="1"
              step="1"
              value={form.amount}
              onChange={(event) => setForm((current) => ({ ...current, amount: event.target.value }))}
            />

            <label className="label" htmlFor="zusd-deadline">Deadline Epoch Or Unix Time</label>
            <input
              id="zusd-deadline"
              className="input"
              type="number"
              min="1"
              step="1"
              value={form.deadline}
              onChange={(event) => setForm((current) => ({ ...current, deadline: event.target.value }))}
              placeholder="optional"
            />

            <p className="zusd-wallet-placeholder" role="status">
              Submission is blocked until the production external-signer envelope is integrated. Private key material is never accepted by this UI.
            </p>
            <div className="zusd-wallet-actions">
              <button className="btn btn-secondary" type="button" onClick={handlePrepare} disabled={busy}>
                {busy ? 'Preparing...' : 'Prepare unsigned request'}
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
              <div className="zusd-wallet-kv"><span>Sender Balance</span><span>{liveSummary.sender_balance_before}</span></div>
              <div className="zusd-wallet-kv"><span>Recipient Balance</span><span>{liveSummary.recipient_balance_before}</span></div>
              <div className="zusd-wallet-kv"><span>Total Supply</span><span>{liveSummary.total_supply_before}</span></div>
              <div className="zusd-wallet-kv"><span>Token Nonce</span><span>{liveSummary.last_used_nonce}</span></div>
              <div className="zusd-wallet-kv"><span>Tx Sequence</span><span>{liveSummary.tx_sequence_number}</span></div>
            </div>
          ) : (
            <p className="zusd-wallet-placeholder">Prepare a request to load the current network context.</p>
          )}
        </div>

        <div className="panel zusd-wallet-card">
          <div className="zusd-section-header">
            <h2>Latest Report</h2>
            <span className="zusd-section-badge">Deterministic</span>
          </div>
          {result ? (
            <pre className="zusd-wallet-json">{JSON.stringify(result, null, 2)}</pre>
          ) : (
            <p className="zusd-wallet-placeholder">No transport report yet.</p>
          )}
        </div>
      </div>
    </section>
  );
}

export default ZUSDTauWalletSurface;
