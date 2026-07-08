// Copyright DarkLightX/Dana Edwards
// Verify checkpoint tab — full vs structural verification modes

import { useState } from 'react';
import { verifyBrowserCheckpointBundleV0 } from '../../sdk/zenoProofClient.js';

function formatJson(value) {
  return JSON.stringify(value, null, 2);
}

function parseJson(text, name) {
  try {
    return JSON.parse(String(text || '').trim() || '{}');
  } catch (err) {
    throw new Error(`${name}: ${err?.message || 'invalid_json'}`);
  }
}

function checkBlsSupport() {
  if (typeof window === 'undefined') return false;
  return !!(window.crypto && window.crypto.subtle && typeof window.crypto.subtle.digest === 'function');
}

function GapCard({ gap }) {
  const parts = String(gap).split(/[:—-]/).map((s) => s.trim()).filter(Boolean);
  const title = parts[0] || gap;
  const cause = parts[1] || '';
  return (
    <div className="proofs-gap-card">
      <div className="proofs-gap-title">✕ {title}</div>
      {cause && <div className="proofs-gap-cause">Cause: {cause}</div>}
      <div className="proofs-gap-action">Action: Ask peer for newer bundle or verify archived state</div>
    </div>
  );
}

export default function VerifyCheckpointTab({ systemStatus }) {
  const [bundleText, setBundleText] = useState('');
  const [mode, setMode] = useState('full');
  const [result, setResult] = useState({ state: 'idle', data: null, error: '' });
  const [blsSupported] = useState(() => checkBlsSupport());

  const report = result.data;
  const isStale = systemStatus === 'stale';
  const isOffline = systemStatus === 'offline';

  function handleClear() {
    setBundleText('');
    setResult({ state: 'idle', data: null, error: '' });
  }

  async function handleVerify() {
    setResult({ state: 'checking', data: null, error: '' });
    try {
      const bundle = parseJson(bundleText, 'checkpoint_bundle');
      const report = await verifyBrowserCheckpointBundleV0(bundle, {
        requireIndependentBls: mode === 'full',
      });
      setResult({ state: 'done', data: report, error: '' });
    } catch (err) {
      setResult({ state: 'error', data: null, error: err?.message || 'bundle_verify_failed' });
    }
  }

  const resultCls = report?.ok
    ? mode === 'full' ? 'verified' : 'partial'
    : result.state === 'done' ? 'rejected' : '';

  return (
    <div className="proofs-tab-panel" role="tabpanel" aria-label="Verify checkpoint">
      <p className="proofs-tab-goal">Check if this checkpoint matches your data.</p>

      <div className="proofs-step-section">
        <p className="proofs-step-label">Data used for comparison</p>
        <div className="proofs-system-row" style={{ fontSize: '0.78em', opacity: 0.7 }}>
          <span className={`proofs-system-dot ${systemStatus === 'offline' ? 'offline' : isStale ? 'stale' : 'online'}`} aria-hidden="true"></span>
          <span>
            {isOffline ? 'Service offline' : 'Service'}
            {!isOffline && ' | Recently updated'}
          </span>
        </div>
        {isStale && (
          <div className="proofs-system-stale-warning" style={{ marginTop: '6px' }}>
            ⚠ Data is outdated. Cannot verify checkpoint against current data.
            <br />
            <button className="btn btn-ghost btn-sm" type="button" onClick={handleVerify} style={{ marginTop: '4px' }}>Check data format only</button>
          </div>
        )}
      </div>

      <div className="proofs-step-section">
        <p className="proofs-step-label">Checkpoint data</p>
        <div className="proofs-json-input">
          <textarea
            className="proofs-json-textarea"
            value={bundleText}
            onChange={(e) => { setBundleText(e.target.value); setResult({ state: 'idle', data: null, error: '' }); }}
            placeholder="Paste checkpoint bundle JSON"
            spellCheck="false"
            aria-label="Checkpoint data"
          />
          {bundleText && (
            <button className="proofs-json-clear" type="button" onClick={handleClear} aria-label="Clear input">×</button>
          )}
        </div>
      </div>

      <div className="proofs-verify-mode">
        <p className="proofs-step-label">Check type</p>
        <label className="proofs-radio-row">
          <input type="radio" name="verify-mode" value="full" checked={mode === 'full'} onChange={() => setMode('full')} disabled={!blsSupported} />
          <div>
            <div className="proofs-radio-label">Complete check{!blsSupported && ' (unavailable)'}</div>
            <div className="proofs-radio-desc">Data format, signatures, and comparison check</div>
          </div>
        </label>
        <label className="proofs-radio-row">
          <input type="radio" name="verify-mode" value="structural" checked={mode === 'structural'} onChange={() => setMode('structural')} />
          <div>
            <div className="proofs-radio-label">Format check only</div>
            <div className="proofs-radio-desc">Checks data format only. Does not verify authenticity.</div>
          </div>
        </label>
        {!blsSupported && (
          <div className="proofs-banner proofs-banner-warning" style={{ marginTop: '6px' }}>
            Browser does not support signature verification. Complete check is unavailable — only format checks can be performed.
          </div>
        )}
      </div>

      <div className="proofs-actions">
        <button className="btn btn-secondary btn-sm" type="button" onClick={handleClear}>Clear</button>
        <button className="btn btn-primary proofs-primary-btn" type="button" onClick={handleVerify} disabled={!bundleText || isOffline}>
          {result.state === 'checking' ? 'Verifying…' : 'Verify checkpoint'}
        </button>
      </div>

      {result.error && (
        <div className="proofs-banner proofs-banner-error" role="alert">
          Error: {result.error}
        </div>
      )}

      {result.state === 'done' && report && (
        <div className={`proofs-verify-result ${resultCls}`} role="region" aria-label="Verification result">
          {report.ok && mode === 'full' && (
            <>
              <div className="proofs-verify-result-status">✓ Verified against your data</div>
              <div className="proofs-submit-result-meta">
                {report.height != null && `Block number ${report.height}`}
                {report.chain_id && ` | Network ${report.chain_id}`}
              </div>
            </>
          )}
          {report.ok && mode === 'structural' && (
            <>
              <div className="proofs-verify-result-status">◐ Format is correct, signature not checked</div>
              <div className="proofs-check-action">Action: Run full verification before accepting this checkpoint.</div>
            </>
          )}
          {!report.ok && (
            <>
              <div className="proofs-verify-result-status">✕ Check failed</div>
              {Array.isArray(report.gaps) && report.gaps.length > 0 ? (
                report.gaps.map((gap, i) => <GapCard key={i} gap={gap} />)
              ) : (
                <div className="proofs-check-action">No specific gaps reported. Check raw report for details.</div>
              )}
            </>
          )}
          <div className="proofs-submit-result-actions">
            <button className="btn btn-ghost btn-sm" type="button" onClick={() => navigator.clipboard.writeText(formatJson(report))}>Copy diagnostic</button>
            <button className="btn btn-ghost btn-sm" type="button" onClick={() => { const blob = new Blob([formatJson(report)], { type: 'application/json' }); const url = URL.createObjectURL(blob); const a = document.createElement('a'); a.href = url; a.download = 'verification-report.json'; a.click(); URL.revokeObjectURL(url); }}>Download report</button>
          </div>
        </div>
      )}

      {result.state === 'idle' && (
        <div className="proofs-verify-result">
          <div className="proofs-check-label" style={{ opacity: 0.4 }}>Not checked yet</div>
        </div>
      )}

      <details className="proofs-advanced">
        <summary>Raw verification report</summary>
        <div className="proofs-advanced-body">
          {report ? (
            <pre className="proofs-api-code-block">{formatJson(report)}</pre>
          ) : (
            <p className="proofs-tab-hint">Verify a bundle to see the raw report.</p>
          )}
        </div>
      </details>
    </div>
  );
}
