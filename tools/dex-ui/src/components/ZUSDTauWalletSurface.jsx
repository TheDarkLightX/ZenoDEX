import { useEffect, useRef, useState } from 'react';
import { apiGetZusdWalletStatus, apiPrepareZusdWallet, apiSubmitZusdWallet } from '../lib/api.js';
import './ZUSDTauWalletSurface.css';

const EMPTY_FORM = {
  action: 'transfer',
  sender_pubkey: '',
  recipient_pubkey: '',
  operator_pubkey: '',
  signer_privkey: '',
  amount: '100',
  deadline: '',
};

function readSmokeConfig() {
  if (typeof window === 'undefined') {
    return null;
  }
  const params = new URLSearchParams(window.location.search);
  if (params.get('zenodexUiSmokeZusd') !== '1') {
    return null;
  }
  return {
    action: params.get('zusdAction') || 'transfer',
    sender_pubkey: params.get('senderPubkey') || '',
    recipient_pubkey: params.get('recipientPubkey') || '',
    operator_pubkey: params.get('operatorPubkey') || '',
    signer_privkey: params.get('signerPrivkey') || params.get('smokeSignerPrivkey') || '',
    amount: params.get('zusdAmount') || '100',
    deadline: params.get('zusdDeadline') || '',
  };
}

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
  if (form.signer_privkey.trim()) {
    payload.signer_privkey = form.signer_privkey.trim();
  }
  return payload;
}

function ZUSDTauWalletSurface({ wallet = null }) {
  const connectedAccount = (wallet?.address || '').trim();
  const [status, setStatus] = useState(null);
  const [statusError, setStatusError] = useState('');
  const [form, setForm] = useState(
    () => readSmokeConfig() || { ...EMPTY_FORM, sender_pubkey: connectedAccount },
  );
  const [, setResult] = useState(null);
  const [error, setError] = useState('');
  const [busy, setBusy] = useState(false);
  const smokeRan = useRef(false);

  async function loadStatus() {
    try {
      const payload = await apiGetZusdWalletStatus({
        account: form.sender_pubkey.trim() || '',
        timeoutMs: 8000,
      });
      setStatus(payload?.status || null);
      setStatusError('');
    } catch (err) {
      setStatus(null);
      setStatusError(err?.message === 'not_found' ? 'wallet service unavailable' : (err?.message || 'status_unavailable'));
    }
  }

  useEffect(() => {
    loadStatus();
    // Refetch account-aware status when the sender (connected account) changes
    // so the holder's token balance reflects THAT account.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [form.sender_pubkey]);

  // Bind the account-aware status query to the CONNECTED wallet: when the wallet
  // identity changes, set the sender field to it so the holder's token balance
  // reflects THAT account (fixes "50k shows in Pool but not zUSD"). Manual edits
  // between wallet switches are preserved — we only react to identity changes.
  const prevWalletRef = useRef(connectedAccount);
  useEffect(() => {
    const previous = prevWalletRef.current;
    if (connectedAccount && connectedAccount !== previous) {
      prevWalletRef.current = connectedAccount;
      // Connecting/switching a wallet is a deliberate action: the connected
      // account always takes over the field — overriding empty or any stale
      // prior value. The field stays editable for inspection while connected.
      setForm((curr) => ({ ...curr, sender_pubkey: connectedAccount }));
    } else if (!connectedAccount && previous) {
      prevWalletRef.current = '';
      // On disconnect, clear ONLY if the field still holds the disconnected
      // wallet (so a manual edit survives).
      setForm((curr) =>
        curr.sender_pubkey === previous ? { ...curr, sender_pubkey: '' } : curr,
      );
    }
  }, [connectedAccount]);

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

  async function handleSubmit() {
    setBusy(true);
    setError('');
    try {
      const payload = await apiSubmitZusdWallet(buildPayload(form), { timeoutMs: 20000 });
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
    async function runSmoke() {
      const nextSmoke = { ...smoke };
      setForm(nextSmoke);
      if (!nextSmoke.signer_privkey.trim() && !String(nextSmoke.signed_tau_tx_payload || '').trim()) {
        throw new Error('smoke signer credential or signed payload required');
      }
      return apiSubmitZusdWallet(buildPayload(nextSmoke), { timeoutMs: 20000 });
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

  const accountTokenBalance = status?.account_view ? Number(status.account_view.balance ?? 0) : null;

  return (
    <section className="zusd-wallet-surface">
      <div className="zusd-section-header">
        <h2>Transfer zUSD</h2>
        <span className="zusd-section-badge">{status?.node_reachable ? 'Connected' : 'Not connected'}</span>
      </div>

      <div className="zusd-wallet-grid">
        <div className="panel zusd-wallet-card">
          <div className="zusd-wallet-meta">
            <div className="zusd-wallet-kv"><span>Network</span><span>{status?.chain_id || 'unknown'}</span></div>
            <div className="zusd-wallet-kv"><span>Your zUSD balance</span><span>{accountTokenBalance == null ? 'unknown' : accountTokenBalance.toLocaleString()}</span></div>
            <div className="zusd-wallet-kv"><span>Signing</span><span>{status?.allow_local_signing ? 'Local signature' : 'Wallet signature'}</span></div>
          </div>
          <details className="zusd-advanced-options">
            <summary>Protocol details</summary>
            <div className="zusd-wallet-meta" style={{ marginTop: 'var(--space-md)' }}>
              <div className="zusd-wallet-kv"><span>Asset ID</span><span className="zusd-mono">{status?.asset_id || 'unavailable'}</span></div>
              <div className="zusd-wallet-kv"><span>Endpoint</span><span>{status?.tau_host || 'network'}:{status?.tau_port || '-'}</span></div>
              <div className="zusd-wallet-kv"><span>Bridge</span><span>{status?.app_bridge_available ? 'available' : 'not detected'}</span></div>
              <div className="zusd-wallet-kv"><span>Operator</span><span className="zusd-mono">{status?.token_operator_pubkey || 'not configured'}</span></div>
            </div>
          </details>
          {statusError ? <p className="zusd-wallet-error">Status error: {statusError}</p> : null}
        </div>

        <div className="panel zusd-wallet-card">
          <div className="zusd-section-header">
            <h2>Submit transfer</h2>
            <span className="zusd-section-badge">Wallet transaction</span>
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
            </select>

            <label className="label" htmlFor="zusd-sender">Sender address</label>
            <input
              id="zusd-sender"
              className="input"
              value={form.sender_pubkey}
              onChange={(event) => setForm((current) => ({ ...current, sender_pubkey: event.target.value }))}
              placeholder="0x..."
            />

            <label className="label" htmlFor="zusd-recipient">Recipient address</label>
            <input
              id="zusd-recipient"
              className="input"
              value={form.recipient_pubkey}
              onChange={(event) => setForm((current) => ({ ...current, recipient_pubkey: event.target.value }))}
              placeholder="0x..."
            />

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

            <label className="label" htmlFor="zusd-deadline">Deadline (time limit)</label>
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

            <details className="zusd-advanced-options">
              <summary>Advanced (signing key)</summary>
              <div className="zusd-wallet-form" style={{ marginTop: 'var(--space-md)' }}>
                <label className="label" htmlFor="zusd-signer">Signing key</label>
                <input
                  id="zusd-signer"
                  className="input"
                  value={form.signer_privkey}
                  onChange={(event) => setForm((current) => ({ ...current, signer_privkey: event.target.value }))}
                  placeholder="private key"
                />
              </div>
            </details>

            <div className="zusd-wallet-actions">
              <button className="btn btn-secondary" type="button" onClick={handlePrepare} disabled={busy}>
                {busy ? 'Preparing...' : 'Prepare'}
              </button>
              <button className="btn btn-primary" type="button" onClick={handleSubmit} disabled={busy}>
                {busy ? 'Submitting...' : 'Submit transaction'}
              </button>
            </div>
            {error ? <p className="zusd-wallet-error">{error}</p> : null}
            <p className="zusd-wallet-hint">Need to mint zUSD? Use the Vault Manager above to deposit collateral and mint.</p>
          </div>
        </div>
      </div>
    </section>
  );
}

export default ZUSDTauWalletSurface;
