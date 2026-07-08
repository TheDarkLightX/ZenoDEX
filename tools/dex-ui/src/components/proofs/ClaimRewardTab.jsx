// Copyright DarkLightX/Dana Edwards
// Claim reward tab — validate payout package → submit when ready

import { useEffect, useState } from 'react';
import {
  apiCheckProofMiningStatus,
  apiSubmitLedgerTransaction,
} from '../../lib/api.js';

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

function compactHash(hash) {
  if (!hash || typeof hash !== 'string') return '—';
  if (hash.length <= 16) return hash;
  return `${hash.slice(0, 10)}…${hash.slice(-8)}`;
}

function detectPackageFields(jsonText) {
  if (!jsonText || jsonText.trim() === '{}' || jsonText.trim() === '') return null;
  try {
    const parsed = JSON.parse(jsonText);
    const tx = parsed.tx || parsed;
    const sender = tx.tx_sender_pubkey || parsed.tx_sender_pubkey || '';
    const operations = tx.operations || parsed.operations || {};
    const hasRewardStream = Object.values(operations).some(
      (op) => op?.module === 'ZenoProofMining' || op?.action === 'submit_proof'
    );
    const claim = tx.operations?.['10']?.claim || parsed.claim;
    const chainId = parsed.chain_id || tx.chain_id || claim?.body?.chain_id || '';
    const height = parsed.height ?? tx.height ?? claim?.body?.epoch ?? null;
    const isWrongArtifactType = !tx.operations && !parsed.claim && !parsed.tx;
    return { sender: compactHash(sender), chainId, hasRewardStream, height, isWrongArtifactType };
  } catch {
    return null;
  }
}

const MAX_JSON_SIZE = 512 * 1024; // 512KB warning threshold

function isLikelyWrongArtifact(parsed) {
  const tx = parsed.tx || parsed;
  const hasOps = tx.operations && typeof tx.operations === 'object';
  const hasClaim = parsed.claim || tx.operations?.['10']?.claim;
  const hasProofContext = parsed.proof_mining_context;
  const hasBalances = parsed.chain_balances;
  // If it looks like a checkpoint bundle, not a payout package
  const isCheckpoint = parsed.schema?.includes('checkpoint') || parsed.header?.chain_id;
  return !hasOps && !hasClaim && (isCheckpoint || (!hasProofContext && !hasBalances));
}

function submitTxAccepted(result) {
  if (!result || typeof result !== 'object') return false;
  if (result.tx_accepted === true) return true;
  if (result.receipt && typeof result.receipt === 'object') return result.receipt.accepted === true;
  return result.ok === true && result.status === 'accepted';
}

function getTxId(result) {
  if (!result) return '';
  return result.tx_id || result.receipt?.tx_id || result.tx_hash || '';
}

function getIncludedHeight(result) {
  if (!result) return null;
  return result.height ?? result.receipt?.height ?? result.included_at_height ?? null;
}

function ReadinessCheck({ label, passed, pending, action }) {
  const icon = pending ? '○' : passed ? '✓' : '✕';
  const cls = pending ? 'proofs-check-pending' : passed ? 'proofs-check-pass' : 'proofs-check-fail';
  return (
    <div className="proofs-check-row">
      <span className={`proofs-check-icon ${cls}`} aria-hidden="true">{icon}</span>
      <div className="proofs-check-label">
        {label}
        {!passed && !pending && action && <div className="proofs-check-action">→ {action}</div>}
      </div>
    </div>
  );
}

export default function ClaimRewardTab({ systemStatus }) {
  const [packageText, setPackageText] = useState('');
  const [validation, setValidation] = useState({ state: 'idle', data: null, error: '', validatedAt: null });
  const [submit, setSubmit] = useState({ state: 'idle', data: null, error: '' });
  const [now, setNow] = useState(() => Date.now());

  useEffect(() => {
    const interval = setInterval(() => setNow(Date.now()), 5000);
    return () => clearInterval(interval);
  }, []);

  const detected = detectPackageFields(packageText);
  const status = validation.data;
  const checks = status?.checks || {};
  const allChecksPass = validation.state === 'done' && status && Object.values(checks).every(Boolean);
  const systemOffline = systemStatus === 'offline';

  // Validate-to-submit gap protection: if validation is older than 60s, warn
  const validationAgeMs = validation.validatedAt ? now - validation.validatedAt : null;
  const validationStale = validation.state === 'done' && validationAgeMs !== null && validationAgeMs > 60_000;

  // Wrong artifact type detection
  const wrongArtifact = detected?.isWrongArtifactType;

  // Large JSON warning
  const jsonTooLarge = packageText.length > MAX_JSON_SIZE;

  function handleClear() {
    setPackageText('');
    setValidation({ state: 'idle', data: null, error: '' });
    setSubmit({ state: 'idle', data: null, error: '' });
  }

  async function handleValidate() {
    setValidation({ state: 'checking', data: null, error: '', validatedAt: null });
    try {
      const parsed = parseJson(packageText, 'payout_package');
      if (isLikelyWrongArtifact(parsed)) {
        setValidation({ state: 'error', data: null, error: 'This looks like a different data type (e.g. checkpoint data), not a payout package. Expected a transaction with operations containing a ZenoProofMining submit_proof action.', validatedAt: null });
        return;
      }
      const tx = parsed.tx || parsed;
      const claim = tx.operations?.['10']?.claim || parsed.claim || {};
      const sender = tx.tx_sender_pubkey || parsed.tx_sender_pubkey || '';
      const chainBalances = parsed.chain_balances || {};
      const appStateJson = parsed.app_state_json || '{}';
      const expectedProposalHash = claim?.body?.proposal_hash || '';
      const result = await apiCheckProofMiningStatus({
        claim,
        chain_balances: chainBalances,
        app_state_json: appStateJson,
        tx_sender_pubkey: sender,
        expected_proposal_hash: expectedProposalHash,
      }, { timeoutMs: 15000 });
      setValidation({ state: 'done', data: result?.status || result, error: '', validatedAt: Date.now() });
    } catch (err) {
      setValidation({ state: 'error', data: null, error: err?.message || 'validation_failed', validatedAt: null });
    }
  }

  async function handleSubmit() {
    setSubmit({ state: 'submitting', data: null, error: '' });
    try {
      const payload = parseJson(packageText, 'payout_transaction');
      const txPayload = payload.tx ? payload : { tx: payload };
      const result = await apiSubmitLedgerTransaction(txPayload, { timeoutMs: 20000 });
      setSubmit({ state: 'done', data: result, error: '' });
    } catch (err) {
      setSubmit({ state: 'error', data: null, error: err?.message || 'submit_failed' });
    }
  }

  const submitDisabled = !allChecksPass || systemOffline || validationStale || wrongArtifact;
  const submitReason = systemOffline
    ? 'Service offline'
    : wrongArtifact
    ? 'Wrong file type — paste payment data, not checkpoint data'
    : validationStale
    ? 'Check is outdated — re-check to confirm current status'
    : !allChecksPass
    ? 'Fix the issues above first'
    : '';

  const submitResult = submit.data;
  const submitAccepted = submitTxAccepted(submitResult);
  const submitRejected = submit.state === 'done' && !submitAccepted;
  const submitUnknown = submit.state === 'error' && /timeout|network|fetch/i.test(submit.error);

  return (
    <div className="proofs-tab-panel" role="tabpanel" aria-label="Claim reward">
      <p className="proofs-tab-goal">Check your payment, then submit.</p>

      <div className="proofs-step-section">
        <p className="proofs-step-label">Step 1 — Add payout package</p>
        <p className="proofs-source-guidance">
          Need: Payment transaction data.
        </p>

        <div className="proofs-json-input">
          <textarea
            className="proofs-json-textarea"
            value={packageText}
            onChange={(e) => { setPackageText(e.target.value); setValidation({ state: 'idle', data: null, error: '' }); }}
            placeholder="Paste payout package JSON"
            spellCheck="false"
            aria-label="Payment data"
          />
          {packageText && (
            <button className="proofs-json-clear" type="button" onClick={handleClear} aria-label="Clear input">×</button>
          )}
        </div>

        {detected && (
          <div className="proofs-detected">
            <div className="proofs-detected-row">
              <span className="proofs-detected-label">Sender:</span>
              <span className="proofs-detected-value">{detected.sender}</span>
            </div>
            <div className="proofs-detected-row">
              <span className="proofs-detected-label">Chain:</span>
              <span className="proofs-detected-value">{detected.chainId || '—'}</span>
            </div>
            <div className="proofs-detected-row">
              <span className="proofs-detected-label">Reward stream:</span>
              <span className="proofs-detected-value">{detected.hasRewardStream ? 'present' : 'missing'}</span>
            </div>
            <div className="proofs-detected-row">
              <span className="proofs-detected-label">Package block number:</span>
              <span className="proofs-detected-value">{detected.height ?? '—'}</span>
            </div>
          </div>
        )}

        <div className="proofs-actions">
          <button className="btn btn-secondary btn-sm" type="button" onClick={handleClear}>Clear</button>
          <button className="btn btn-primary proofs-primary-btn" type="button" onClick={handleValidate} disabled={!packageText || systemOffline}>
            {validation.state === 'checking' ? 'Validating…' : 'Validate transaction'}
          </button>
        </div>

        {validation.error && (
          <div className="proofs-banner proofs-banner-error" role="alert">
            Validation error: {validation.error}
          </div>
        )}

        {jsonTooLarge && (
          <div className="proofs-banner proofs-banner-warning">
            Large input ({Math.round(packageText.length / 1024)}KB). Parsing may be slow.
          </div>
        )}

        {wrongArtifact && !validation.error && (
          <div className="proofs-banner proofs-banner-warning">
            This doesn't look like a payout package. Expected a transaction with a ZenoProofMining submit_proof action.
          </div>
        )}

        {validationStale && (
          <div className="proofs-banner proofs-banner-warning">
            Validation is stale (checked {Math.round(validationAgeMs / 1000)}s ago). Chain state may have changed — re-validate before submitting.
          </div>
        )}

        {validation.state === 'done' && status && (
          <div className="proofs-readiness" role="region" aria-label="Validation readiness">
            <p className="proofs-readiness-title">Readiness</p>
            <ReadinessCheck label="JSON parses" passed={true} />
            <ReadinessCheck label="Chain matches local API" passed={checks.chain_ok !== false} pending={checks.chain_ok === undefined} />
            <ReadinessCheck label="Reward stream present" passed={checks.reward_stream_ok !== false} pending={checks.reward_stream_ok === undefined} />
            <ReadinessCheck label="Verification context matches app state" passed={Boolean(checks.proof_ok)} pending={checks.proof_ok === undefined} action="Hash mismatch. Re-generate verification context from same batch." />
            <ReadinessCheck label="Sender matches payout transaction" passed={Boolean(checks.binding_ok)} pending={checks.binding_ok === undefined} action="Sender in transaction doesn't match claim sender." />
            <ReadinessCheck label="Nonce is fresh" passed={Boolean(checks.nonce_ok)} pending={checks.nonce_ok === undefined} action="Nonce already used. Generate a new claim." />
            <ReadinessCheck label="Claim not already claimed" passed={Boolean(checks.unclaimed_ok)} pending={checks.unclaimed_ok === undefined} action="This reward has already been claimed." />
          </div>
        )}
      </div>

      <div className="proofs-submit-section">
        <p className="proofs-step-label">Step 2 — Review and submit</p>
        <p className="proofs-destination">
          Destination: Service{detected?.chainId ? ` | Chain ${detected.chainId}` : ''}{systemStatus === 'online' ? ' | Ready' : ''}
        </p>
        <button
          className={`btn ${submitDisabled ? 'btn-disabled' : 'btn-primary'} proofs-submit-btn`}
          type="button"
          onClick={handleSubmit}
          disabled={submitDisabled || submit.state === 'submitting'}
        >
          {submit.state === 'submitting' ? 'Submitting…' : submitDisabled ? '🔒 Submit payout' : 'Submit payout'}
        </button>
        {submitDisabled && <div className="proofs-submit-disabled-reason">{submitReason}</div>}

        {submitAccepted && (
          <div className="proofs-submit-result accepted" role="alert">
            <div className="proofs-submit-result-status">✓ Accepted by local API</div>
            <div className="proofs-submit-result-meta">
              Payment ID: {compactHash(getTxId(submitResult))}
              {getIncludedHeight(submitResult) != null && `    Included at block number: ${getIncludedHeight(submitResult)}`}
            </div>
            <div className="proofs-submit-result-actions">
              <button className="btn btn-ghost btn-sm" type="button" onClick={() => navigator.clipboard.writeText(getTxId(submitResult))}>Copy payment ID</button>
              <button className="btn btn-ghost btn-sm" type="button" onClick={() => { const blob = new Blob([formatJson(submitResult)], { type: 'application/json' }); const url = URL.createObjectURL(blob); const a = document.createElement('a'); a.href = url; a.download = 'payout-receipt.json'; a.click(); URL.revokeObjectURL(url); }}>Download receipt</button>
            </div>
          </div>
        )}
        {submitRejected && (
          <div className="proofs-submit-result rejected" role="alert">
            <div className="proofs-submit-result-status">✕ Rejected: {submit.error || submitResult?.error || 'unknown'}</div>
            <div className="proofs-submit-result-actions">
              <button className="btn btn-ghost btn-sm" type="button" onClick={handleSubmit}>Retry</button>
              <button className="btn btn-ghost btn-sm" type="button" onClick={() => navigator.clipboard.writeText(formatJson(submitResult))}>Copy diagnostic</button>
            </div>
          </div>
        )}
        {submitUnknown && (
          <div className="proofs-submit-result unknown" role="alert">
            <div className="proofs-submit-result-status">⚠ Submission status unknown</div>
            <div className="proofs-check-action">Network timeout. Check by payment ID or retry safely.</div>
            <div className="proofs-submit-result-actions">
              <button className="btn btn-ghost btn-sm" type="button" onClick={handleSubmit}>Retry</button>
            </div>
          </div>
        )}
      </div>

      <details className="proofs-advanced">
        <summary>Advanced: Build payout package from separate data</summary>
        <div className="proofs-advanced-body">
          <BuildFromArtifacts onPackageBuilt={(pkg) => { setPackageText(formatJson(pkg)); setValidation({ state: 'idle', data: null, error: '', validatedAt: null }); setSubmit({ state: 'idle', data: null, error: '' }); }} />
        </div>
      </details>

      <details className="proofs-advanced">
        <summary>Raw API request and response</summary>
        <div className="proofs-advanced-body">
          {validation.state === 'done' && status ? (
            <pre className="proofs-api-code-block">{formatJson(status)}</pre>
          ) : (
            <p className="proofs-tab-hint">Validate a transaction to see the raw API response.</p>
          )}
        </div>
      </details>
    </div>
  );
}

function BuildFromArtifacts({ onPackageBuilt }) {
  const [claimText, setClaimText] = useState('');
  const [contextText, setContextText] = useState('');
  const [balancesText, setBalancesText] = useState('');
  const [appStateText, setAppStateText] = useState('');
  const [sender, setSender] = useState('');

  function detectArtifact(text, fields) {
    if (!text || text.trim() === '{}') return null;
    try {
      const parsed = JSON.parse(text);
      const result = {};
      for (const [label, path] of fields) {
        const val = path.split('.').reduce((obj, key) => obj?.[key], parsed);
        if (val != null) result[label] = typeof val === 'string' && val.length > 20 ? `${val.slice(0, 10)}…${val.slice(-8)}` : val;
      }
      return Object.keys(result).length > 0 ? result : null;
    } catch {
      return null;
    }
  }

  const claimDetected = detectArtifact(claimText, [['epoch', 'body.epoch'], ['reward', 'body.reward_amount'], ['proposal', 'body.proposal_hash']]);
  const contextDetected = detectArtifact(contextText, [['chain', 'chain_id'], ['batch', 'batch_hash']]);
  const balancesDetected = detectArtifact(balancesText, []);

  function handleUsePackage() {
    try {
      const claim = JSON.parse(claimText || '{}');
      const context = JSON.parse(contextText || '{}');
      const balances = JSON.parse(balancesText || '{}');
      const appState = appStateText || '{}';
      const txSender = sender || claim?.body?.sender || '0x' + '11'.repeat(48);
      const pkg = {
        tx: {
          tx_id: `proof-mining-${Date.now().toString(36)}`,
          tx_sender_pubkey: txSender,
          block_timestamp: Math.floor(Date.now() / 1000),
          operations: {
            '10': {
              module: 'ZenoProofMining',
              action: 'submit_proof',
              claim,
              recipient_pubkey: txSender,
            },
          },
        },
        proof_mining_context: context,
        chain_balances: balances,
        app_state_json: appState,
      };
      onPackageBuilt(pkg);
    } catch {
      // Error shown via parse state
    }
  }

  return (
    <div>
      <div className="proofs-artifact-field">
        <div className="proofs-artifact-label">Claim data</div>
        <textarea className="proofs-json-textarea" value={claimText} onChange={(e) => setClaimText(e.target.value)} placeholder="Paste claim JSON" spellCheck="false" />
        {claimDetected && <div className="proofs-artifact-detected">Detected: {Object.entries(claimDetected).map(([k, v]) => `${k}: ${v}`).join(', ')}</div>}
      </div>
      <div className="proofs-artifact-field">
        <div className="proofs-artifact-label">Proof-mining context</div>
        <textarea className="proofs-json-textarea" value={contextText} onChange={(e) => setContextText(e.target.value)} placeholder="Paste context JSON" spellCheck="false" />
        {contextDetected && <div className="proofs-artifact-detected">Detected: {Object.entries(contextDetected).map(([k, v]) => `${k}: ${v}`).join(', ')}</div>}
      </div>
      <div className="proofs-artifact-field">
        <div className="proofs-artifact-label">Account balances</div>
        <textarea className="proofs-json-textarea" value={balancesText} onChange={(e) => setBalancesText(e.target.value)} placeholder="Paste balances JSON" spellCheck="false" />
        {balancesDetected && <div className="proofs-artifact-detected">Detected: {Object.entries(balancesDetected).map(([k, v]) => `${k}: ${v}`).join(', ')}</div>}
      </div>
      <div className="proofs-artifact-field">
        <div className="proofs-artifact-label">Application state</div>
        <textarea className="proofs-json-textarea" value={appStateText} onChange={(e) => setAppStateText(e.target.value)} placeholder="Paste app state JSON" spellCheck="false" />
      </div>
      <div className="proofs-artifact-field">
        <div className="proofs-artifact-label">Sender address (override — forces re-validation)</div>
        <input className="proofs-json-textarea" style={{ minHeight: 'auto', height: '37px' }} value={sender} onChange={(e) => setSender(e.target.value)} placeholder="0x...  (leave empty to derive from claim)" />
      </div>
      <div className="proofs-artifact-field">
        <div className="proofs-artifact-label">Generated package preview:</div>
        <pre className="proofs-api-code-block">{claimText ? '{ tx: { operations: { 10: { ... } }, ... } }' : 'Fill in data above'}</pre>
      </div>
      <button className="btn btn-secondary btn-sm" type="button" onClick={handleUsePackage}>Use generated package</button>
    </div>
  );
}
