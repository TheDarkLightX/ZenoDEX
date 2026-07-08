// Copyright DarkLightX/Dana Edwards
// System status bar — chain state, sync freshness, data-flow notice

import { useEffect, useState } from 'react';

const STALE_THRESHOLD_MS = 5 * 60 * 1000; // 5 minutes

export default function ProofsStatusBar({ onRefresh }) {
  const [status, setStatus] = useState({ state: 'loading', chainId: '', height: null, syncedAt: null });
  const [now, setNow] = useState(Date.now());

  useEffect(() => {
    const interval = setInterval(() => setNow(Date.now()), 5000);
    return () => clearInterval(interval);
  }, []);

  async function fetchStatus() {
    setStatus((s) => ({ ...s, state: s.state === 'offline' ? 'loading' : s.state }));
    try {
      const res = await fetch('/api/dex/proof_mining_status', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          claim: { body: {} },
          chain_balances: {},
          app_state_json: '{}',
          tx_sender_pubkey: '0x' + '00'.repeat(48),
          expected_proposal_hash: '',
        }),
      });
      if (!res.ok) throw new Error(`HTTP ${res.status}`);
      const data = await res.json();
      const chainId = data?.chain_id || data?.status?.chain_id || 'unknown';
      const height = data?.height ?? data?.status?.height ?? null;
      setStatus({ state: 'online', chainId, height, syncedAt: Date.now() });
    } catch {
      setStatus((s) => ({
        ...s,
        state: 'offline',
        chainId: s.chainId || 'unknown',
        height: s.height,
        syncedAt: s.syncedAt,
      }));
    }
  }

  useEffect(() => {
    void fetchStatus();
  }, []);

  const ageMs = status.syncedAt ? now - status.syncedAt : null;
  const isStale = status.state === 'online' && ageMs !== null && ageMs > STALE_THRESHOLD_MS;
  const isOffline = status.state === 'offline';
  const isLoading = status.state === 'loading';

  const dotCls = isOffline ? 'offline' : isStale ? 'stale' : 'online';
  const ageLabel = ageMs !== null
    ? ageMs < 60000 ? `${Math.round(ageMs / 1000)}s ago`
    : ageMs < 3600000 ? `${Math.round(ageMs / 60000)}m ago`
    : `${Math.round(ageMs / 3600000)}h ago`
    : '—';

  return (
    <div className="proofs-system-bar" role="status" aria-live="polite">
      <div className="proofs-system-row">
        <span className={`proofs-system-dot ${dotCls}`} aria-hidden="true"></span>
        <span className="proofs-system-meta">
          {isLoading ? 'Connecting…' : isOffline ? 'Service offline' : 'Service online'}
          {!isOffline && !isLoading && status.chainId !== 'unknown' && ` | Network ${status.chainId}`}
          {!isOffline && !isLoading && status.height != null && ` | Block number ${status.height}`}
          {!isOffline && !isLoading && ` | Updated ${ageLabel}`}
        </span>
        <button className="proofs-system-refresh" type="button" onClick={() => { void fetchStatus(); onRefresh?.(); }} aria-label="Refresh system status">
          ↻
        </button>
      </div>
      {isStale && (
        <div className="proofs-system-stale-warning">
          ⚠ Data is outdated: last synced {ageLabel}.<br />
          Cannot verify checkpoint against current data.
        </div>
      )}
      {isOffline && (
        <div className="proofs-system-offline-warning">
          Cannot validate or verify against current data.
        </div>
      )}
      <div className="proofs-data-notice">
        <strong>Data:</strong> Validation checks your local data. Pasted data stays in this browser.
        Submit sends the payment to your service. Never paste private keys or seed phrases.
      </div>
      <div className="proofs-specs-row">
        <a className="proofs-spec-link" href="#spec-proof_mining_manager_v1" onClick={(e) => e.preventDefault()}>Payment system v1 ↗</a>
        <a className="proofs-spec-link" href="#spec-browser_checkpoint_bundle_v0" onClick={(e) => e.preventDefault()}>Checkpoint system v0 ↗</a>
      </div>
    </div>
  );
}
