// Copyright DarkLightX/Dana Edwards
// Developer tab — API reference, try-it, catalogs (templates, proofs, guards)

import { useState } from 'react';
import {
  apiPrepareAutotraderLive,
  apiSubmitAutotraderLive,
  apiPreflightAutotraderSupervisor,
  apiExecuteAutotraderSupervisor,
} from '../../lib/api.js';
import { STRATEGY_TEMPLATES, FORMAL_PROOFS, TAU_POLICY_GUARDS } from '../../lib/strategyData.js';

function formatJson(value) {
  return JSON.stringify(value, null, 2);
}

const ENDPOINTS = [
  {
    id: 'prepare',
    label: 'Prepare',
    method: 'POST',
    path: '/api/strategy/autotrader/prepare',
    description: 'Validate strategy config and build a prepared report.',
    requestExample: {
      acknowledge_experimental_live_risk: true,
      signer_privkey: 7,
      chain_id: 'tau-local',
      tx_sequence_number: 9,
      tx_expiration_time: 999,
      policy: {
        strategy_id: 'dca.live.ui',
        template: 'dca',
        asset_universe: ['tASSET0', 'tZENO'],
        allowed_actions: ['PLACE_SWAP_EXACT_IN'],
      },
    },
    errors: [
      { code: '400', name: 'invalid_config', desc: 'Strategy config is malformed' },
      { code: '422', name: 'guard_failed', desc: 'One or more safety checks failed' },
      { code: '503', name: 'api_unavailable', desc: 'Autotrader API is offline' },
    ],
    apiFn: apiPrepareAutotraderLive,
  },
  {
    id: 'submit',
    label: 'Submit',
    method: 'POST',
    path: '/api/strategy/autotrader/submit',
    description: 'Submit a prepared strategy for execution.',
    requestExample: {
      acknowledge_experimental_live_risk: true,
      signer_privkey: 7,
      chain_id: 'tau-local',
      execution_id: 'strategy-ui-exec-1',
      signed_tau_tx_payload: '...',
    },
    errors: [
      { code: '400', name: 'invalid_payload', desc: 'Signed payload is malformed' },
      { code: '409', name: 'already_running', desc: 'A strategy with this config is active' },
      { code: '422', name: 'guard_failed', desc: 'Safety checks failed at submit time' },
    ],
    apiFn: apiSubmitAutotraderLive,
  },
  {
    id: 'preflight',
    label: 'Supervisor preflight',
    method: 'POST',
    path: '/api/strategy/autotrader/supervisor/preflight',
    description: 'Run a read-only readiness probe (no chain state mutated).',
    requestExample: {
      acknowledge_experimental_live_risk: true,
      signer_privkey: 7,
      chain_id: 'tau-local',
      execution_id: 'strategy-ui-supervisor-1',
    },
    errors: [
      { code: '403', name: 'supervisor_disabled', desc: 'Supervisor gate is off' },
      { code: '422', name: 'supervisor_profile_not_ready', desc: 'Supervisor profile missing or incomplete' },
    ],
    apiFn: apiPreflightAutotraderSupervisor,
  },
  {
    id: 'execute',
    label: 'Supervisor execute',
    method: 'POST',
    path: '/api/strategy/autotrader/supervisor/execute',
    description: 'Execute one supervised tick (real transactions on local-testnet).',
    requestExample: {
      acknowledge_experimental_live_risk: true,
      signer_privkey: 7,
      chain_id: 'tau-local',
      execution_id: 'strategy-ui-supervisor-1',
      signed_tau_tx_payload: '...',
    },
    errors: [
      { code: '403', name: 'supervisor_disabled', desc: 'Supervisor gate is off' },
      { code: '409', name: 'already_running', desc: 'A tick is already in progress' },
      { code: '429', name: 'rate_limited', desc: 'Max runs per process exceeded' },
    ],
    apiFn: apiExecuteAutotraderSupervisor,
  },
];

export default function DeveloperTab() {
  const [activeEndpoint, setActiveEndpoint] = useState('prepare');
  const [subTab, setSubTab] = useState('request');
  const [tryItText, setTryItText] = useState('');
  const [tryItResult, setTryItResult] = useState(null);
  const [tryItError, setTryItError] = useState('');
  const [tryItBusy, setTryItBusy] = useState(false);

  const endpoint = ENDPOINTS.find((e) => e.id === activeEndpoint);

  async function handleTryIt() {
    setTryItBusy(true);
    setTryItError('');
    setTryItResult(null);
    try {
      const body = JSON.parse(tryItText || '{}');
      const result = await endpoint.apiFn(body, { timeoutMs: 20000 });
      setTryItResult(result);
    } catch (err) {
      setTryItError(err?.message || 'request_failed');
    } finally {
      setTryItBusy(false);
    }
  }

  return (
    <div className="strategy-tab-panel" role="tabpanel" aria-label="Developer">
      <p className="strategy-tab-goal">Test API calls, inspect raw payloads, and explore safety specs.</p>

      <div className="strategy-banner strategy-banner-warning">
        ⚠ Sandbox: local-testnet only. Cannot submit live transactions.
      </div>

      <div className="strategy-step-section">
        <p className="strategy-step-label">Endpoint</p>
        <div className="strategy-api-endpoint-bar">
          {ENDPOINTS.map((ep) => (
            <button
              key={ep.id}
              className={`strategy-api-endpoint-tab ${activeEndpoint === ep.id ? 'active' : ''}`}
              type="button"
              onClick={() => { setActiveEndpoint(ep.id); setSubTab('request'); setTryItText(formatJson(ep.requestExample)); setTryItResult(null); setTryItError(''); }}
            >
              {ep.label}
            </button>
          ))}
        </div>

        <div className="strategy-api-route">{endpoint.method} {endpoint.path}</div>
        <div className="strategy-api-meta">
          Env: local-testnet | Auth: test-key
          {' | '}{endpoint.description}
        </div>
        <div className="strategy-actions">
          <button
            className="btn btn-ghost btn-sm"
            type="button"
            onClick={() => navigator.clipboard.writeText(`curl -X ${endpoint.method} http://localhost:18080${endpoint.path} -H 'Content-Type: application/json' -d '${JSON.stringify(endpoint.requestExample)}'`)}
          >
            Copy curl
          </button>
        </div>

        <div className="strategy-api-subtabs">
          <button className={`strategy-api-subtab ${subTab === 'request' ? 'active' : ''}`} type="button" onClick={() => setSubTab('request')}>Request</button>
          <button className={`strategy-api-subtab ${subTab === 'errors' ? 'active' : ''}`} type="button" onClick={() => setSubTab('errors')}>Errors</button>
          <button className={`strategy-api-subtab ${subTab === 'try' ? 'active' : ''}`} type="button" onClick={() => setSubTab('try')}>Try it</button>
        </div>

        {subTab === 'request' && (
          <pre className="strategy-api-code-block">{formatJson(endpoint.requestExample)}</pre>
        )}

        {subTab === 'errors' && (
          <div className="strategy-error-table">
            {endpoint.errors.map((err) => (
              <div key={err.name} className="strategy-error-row">
                <span className="strategy-error-code">{err.code}</span>
                <span className="strategy-error-name">{err.name}</span>
                <span className="strategy-error-desc">{err.desc}</span>
              </div>
            ))}
          </div>
        )}

        {subTab === 'try' && (
          <div>
            <p className="strategy-tab-hint">Paste request JSON (example pre-filled):</p>
            <textarea
              className="strategy-json-textarea"
              value={tryItText}
              onChange={(e) => setTryItText(e.target.value)}
              spellCheck="false"
              style={{ minHeight: '120px' }}
            />
            <div className="strategy-actions">
              <button
                className="btn btn-primary btn-sm strategy-primary-btn"
                type="button"
                onClick={handleTryIt}
                disabled={tryItBusy || !tryItText}
              >
                {tryItBusy ? 'Sending…' : 'Send to local API'}
              </button>
            </div>
            {tryItError && (
              <div className="strategy-banner strategy-banner-error">Error: {tryItError}</div>
            )}
            {tryItResult && (
              <div>
                <p className="strategy-step-label">Response</p>
                <pre className="strategy-api-code-block">{formatJson(tryItResult)}</pre>
              </div>
            )}
          </div>
        )}
      </div>

      <details className="strategy-advanced">
        <summary>Strategy templates catalog</summary>
        <div className="strategy-advanced-body">
          {STRATEGY_TEMPLATES.map((tmpl) => (
            <div key={tmpl.id} className="strategy-row">
              <div className="strategy-row-title">{tmpl.label}</div>
              <div className="strategy-row-meta">{tmpl.description}</div>
              <div className="strategy-row-meta">Actions: {tmpl.allowedActions.join(', ')}</div>
            </div>
          ))}
        </div>
      </details>

      <details className="strategy-advanced">
        <summary>Safety check sequence (10-stage pipeline)</summary>
        <div className="strategy-advanced-body">
          <div className="strategy-safety-list">
            {TAU_POLICY_GUARDS.map((guard, idx) => (
              <div key={guard.id} className="strategy-check-row">
                <span className="strategy-check-icon" aria-hidden="true">{idx + 1}.</span>
                <span className="strategy-check-label">
                  {guard.label}
                  <div className="strategy-row-meta">{guard.detail}</div>
                  <div className="strategy-api-meta">{guard.spec}</div>
                </span>
                <span className="strategy-check-pass">✓ {guard.status}</span>
              </div>
            ))}
          </div>
        </div>
      </details>

      <details className="strategy-advanced">
        <summary>Formal proofs (Lean 4)</summary>
        <div className="strategy-advanced-body">
          {FORMAL_PROOFS.map((proof) => (
            <div key={proof.id} className="strategy-check-row">
              <span className="strategy-check-label">
                {proof.label}
                <div className="strategy-api-meta">{proof.file}</div>
              </span>
              <span className="strategy-check-pass">✓ {proof.status}</span>
            </div>
          ))}
        </div>
      </details>

      <details className="strategy-advanced">
        <summary>Raw tx payload editor</summary>
        <div className="strategy-advanced-body">
          <p className="strategy-tab-hint">Paste or edit a raw signed tx payload for debugging.</p>
          <textarea className="strategy-json-textarea" placeholder='{"signed_payload":"…","signature":"…"}' spellCheck="false" />
        </div>
      </details>
    </div>
  );
}
