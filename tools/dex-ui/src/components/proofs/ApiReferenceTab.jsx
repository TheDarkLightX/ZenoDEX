// Copyright DarkLightX/Dana Edwards
// API reference tab — endpoint docs, request/response shapes, errors, try-it

import { useState } from 'react';
import { apiCheckProofMiningStatus, apiSubmitLedgerTransaction } from '../../lib/api.js';

function formatJson(value) {
  return JSON.stringify(value, null, 2);
}

const ENDPOINTS = [
  {
    id: 'claim-validation',
    label: 'Claim validation',
    method: 'POST',
    route: '/api/dex/proof_mining_status',
    description: 'Validates a proof-mining claim against local chain state. Secure: never confirms payment over unencrypted connection.',
    requestShape: {
      claim: { body: { epoch: 0, reward_amount: 0, proposal_hash: '0x...', sender: '0x...' } },
      chain_balances: { '0x...': 0 },
      app_state_json: 'string',
      tx_sender_pubkey: '0x...',
      expected_proposal_hash: '0x...',
    },
    responseShape: {
      enabled: true,
      claimable: false,
      checks: { proof_ok: true, binding_ok: false, nonce_ok: true, unclaimed_ok: true },
    },
    errors: [
      { code: '400', name: 'Invalid data format', desc: 'Malformed JSON in request body' },
      { code: '409', name: 'Network mismatch', desc: 'Chain ID in request does not match API' },
      { code: '422', name: 'Verification context mismatch', desc: 'Proof context hash doesn\'t match app state' },
      { code: '503', name: 'Service unavailable', desc: 'Service is offline or unreachable' },
    ],
    tryItApi: (body) => apiCheckProofMiningStatus(body, { timeoutMs: 15000 }),
  },
  {
    id: 'payout-submit',
    label: 'Payout submit',
    method: 'POST',
    route: '/tx',
    description: 'Sends payment to the network. Only works when connected to a running network.',
    requestShape: {
      tx: {
        tx_id: 'proof-mining-...',
        tx_sender_pubkey: '0x...',
        block_timestamp: 0,
        operations: { '10': { module: 'ZenoProofMining', action: 'submit_proof', claim: {}, recipient_pubkey: '0x...' } },
      },
    },
    responseShape: {
      tx_accepted: true,
      height: 43,
      tx_id: '0x...',
    },
    errors: [
      { code: '400', name: 'Invalid data format', desc: 'Malformed JSON in request body' },
      { code: '422', name: 'Invalid payment', desc: 'Claim is malformed or missing required fields' },
      { code: '409', name: 'Already paid', desc: 'This reward has already been claimed' },
      { code: '503', name: 'Network unavailable', desc: 'Ledger node is offline or unreachable' },
    ],
    tryItApi: (body) => apiSubmitLedgerTransaction(body, { timeoutMs: 20000 }),
  },
  {
    id: 'checkpoint-verify',
    label: 'Checkpoint verify',
    method: 'Browser',
    route: 'verifyBrowserCheckpointBundleV0()',
    description: 'Verifies checkpoint data in your browser. Works offline — checks data format and signatures.',
    requestShape: {
      bundle: { header: { height: 0, chain_id: '...' }, block_hash: '0x...', signatures: [] },
      options: { requireIndependentBls: true },
    },
    responseShape: {
      ok: true,
      height: 42,
      chain_id: 'zeno-ledger-localtest-v0',
      gaps: [],
    },
    errors: [
      { code: '—', name: 'hash_mismatch', desc: 'Block hash doesn\'t match header' },
      { code: '—', name: 'header_replay_failed', desc: 'Header doesn\'t chain to previous' },
      { code: '—', name: 'bls_quorum_failed', desc: 'Insufficient BLS signatures' },
      { code: '—', name: 'stale_bundle', desc: 'Bundle height is older than local chain' },
    ],
    tryItApi: null,
  },
];

const SUB_TABS = ['Request', 'Response', 'Errors', 'Try it'];

export default function ApiReferenceTab() {
  const [endpointId, setEndpointId] = useState(ENDPOINTS[0].id);
  const [subTab, setSubTab] = useState('Request');
  const [tryItText, setTryItText] = useState('');
  const [tryItResult, setTryItResult] = useState({ state: 'idle', data: null, error: '' });

  const endpoint = ENDPOINTS.find((e) => e.id === endpointId);

  function handleEndpointChange(newId) {
    setEndpointId(newId);
    setSubTab('Request');
    setTryItText(formatJson(endpoint.requestShape));
    setTryItResult({ state: 'idle', data: null, error: '' });
  }

  async function handleTryIt() {
    if (!endpoint.tryItApi) return;
    setTryItResult({ state: 'checking', data: null, error: '' });
    try {
      const body = JSON.parse(tryItText || '{}');
      const result = await endpoint.tryItApi(body);
      setTryItResult({ state: 'done', data: result, error: '' });
    } catch (err) {
      setTryItResult({ state: 'error', data: null, error: err?.message || 'request_failed' });
    }
  }

  function handleCopyCurl() {
    const curl = `curl -X ${endpoint.method} ${endpoint.route} \\\n  -H "Content-Type: application/json" \\\n  -d '${JSON.stringify(endpoint.requestShape)}'`;
    navigator.clipboard.writeText(curl);
  }

  return (
    <div className="proofs-tab-panel" role="tabpanel" aria-label="API reference">
      <p className="proofs-tab-goal">View data formats and test the service.</p>

      <div className="proofs-api-endpoint-bar">
        {ENDPOINTS.map((ep) => (
          <button
            key={ep.id}
            className={`proofs-api-endpoint-tab ${endpointId === ep.id ? 'active' : ''}`}
            type="button"
            onClick={() => handleEndpointChange(ep.id)}
          >
            {ep.label}
          </button>
        ))}
      </div>

      <div className="proofs-api-route">{endpoint.method} {endpoint.route}</div>
      <div className="proofs-api-sends-to">Sends to: your local service</div>
      <div className="proofs-api-actions">
        <button className="btn btn-ghost btn-sm" type="button" onClick={handleCopyCurl}>Copy command</button>
        <button className="btn btn-ghost btn-sm" type="button" onClick={() => { const blob = new Blob([formatJson(endpoint.requestShape)], { type: 'application/json' }); const url = URL.createObjectURL(blob); const a = document.createElement('a'); a.href = url; a.download = `${endpoint.id}-schema.json`; a.click(); URL.revokeObjectURL(url); }}>Download format guide</button>
        <a className="btn btn-ghost btn-sm" href={`#spec-${endpoint.id}`} onClick={(e) => e.preventDefault()}>View documentation ↗</a>
      </div>

      <p className="proofs-tab-hint">{endpoint.description}</p>

      <div className="proofs-api-subtabs">
        {SUB_TABS.map((st) => (
          <button
            key={st}
            className={`proofs-api-subtab ${subTab === st ? 'active' : ''}`}
            type="button"
            onClick={() => setSubTab(st)}
          >
            {st}
          </button>
        ))}
      </div>

      {subTab === 'Request' && (
        <pre className="proofs-api-code-block">{formatJson(endpoint.requestShape)}</pre>
      )}

      {subTab === 'Response' && (
        <pre className="proofs-api-code-block">{formatJson(endpoint.responseShape)}</pre>
      )}

      {subTab === 'Errors' && (
        <div className="proofs-error-table">
          {endpoint.errors.map((err) => (
            <div key={err.name} className="proofs-error-row">
              <span className="proofs-error-code">{err.code}</span>
              <span className="proofs-error-name">{err.name}</span>
              <span className="proofs-error-desc">{err.desc}</span>
            </div>
          ))}
        </div>
      )}

      {subTab === 'Try it' && (
        <div>
          {endpoint.tryItApi ? (
            <>
              <p className="proofs-tab-hint">Paste data (example shown). Sends to your service.</p>
              <textarea
                className="proofs-json-textarea"
                value={tryItText || formatJson(endpoint.requestShape)}
                onChange={(e) => setTryItText(e.target.value)}
                spellCheck="false"
                aria-label="API try-it request JSON"
              />
              <button className="btn btn-primary btn-sm" type="button" onClick={handleTryIt} disabled={tryItResult.state === 'checking'}>
                {tryItResult.state === 'checking' ? 'Sending…' : 'Send to service'}
              </button>
              {tryItResult.error && (
                <div className="proofs-banner proofs-banner-error" style={{ marginTop: '8px' }}>
                  Error: {tryItResult.error}
                </div>
              )}
              {tryItResult.data && (
                <>
                  <p className="proofs-step-label" style={{ marginTop: '12px' }}>Response:</p>
                  <pre className="proofs-api-code-block">{formatJson(tryItResult.data)}</pre>
                </>
              )}
            </>
          ) : (
            <p className="proofs-tab-hint">
              This endpoint runs in the browser, not via HTTP. Use the "Verify checkpoint" tab to test it.
            </p>
          )}
        </div>
      )}

      <details className="proofs-advanced">
        <summary>Version compatibility matrix</summary>
        <div className="proofs-advanced-body">
          <pre className="proofs-api-code-block">{`proof_mining_manager_v1  →  /api/dex/proof_mining_status
browser_checkpoint_bundle_v0  →  verifyBrowserCheckpointBundleV0()
ledger_tx_v0  →  /tx`}</pre>
        </div>
      </details>
    </div>
  );
}
