import { useEffect, useState } from 'react';
import './StrategyWorkbench.css';
import { useDemoMode } from '../lib/DemoModeContext.jsx';
import {
  apiGetAutotraderStatus,
  apiPrepareAutotraderLive,
} from '../lib/api.js';
import {
  STRATEGY_TEMPLATES,
  TAU_POLICY_GUARDS,
  DEMO_STRATEGIES,
  FORMAL_PROOFS,
} from '../lib/strategyData';

function isAutoTraderSmokeEnabled() {
  if (typeof window === 'undefined') {
    return false;
  }
  return new URLSearchParams(window.location.search).get('zenodexUiSmokeStrategyLive') === '1';
}

function StrategyCard({ strategy }) {
  const [expanded, setExpanded] = useState(false);
  const template = STRATEGY_TEMPLATES.find((t) => t.id === strategy.template);
  const statusClass = strategy.status === 'active' ? 'strat-status-active' : 'strat-status-paused';
  const pct = strategy.guardsTotal > 0
    ? Math.round((strategy.guardsPassed / strategy.guardsTotal) * 100)
    : 0;

  return (
    <article className="panel strat-card animate-slide-up">
      <div className="strat-card-top">
        <div className="strat-card-identity">
          <span className={`strat-status ${statusClass}`}>{strategy.status}</span>
          <h3 className="strat-card-title">{strategy.strategyId}</h3>
          <span className="strat-card-template">{template?.label || strategy.template}</span>
        </div>
        <div className="strat-card-pair">
          <span className="strat-token">{strategy.assetIn}</span>
          <span className="strat-arrow">&rarr;</span>
          <span className="strat-token">{strategy.assetOut}</span>
        </div>
      </div>

      <div className="strat-card-stats">
        <div className="stat">
          <span className="stat-label">Guards</span>
          <span className="stat-value">{strategy.guardsPassed}/{strategy.guardsTotal}</span>
        </div>
        <div className="stat">
          <span className="stat-label">Guard Coverage</span>
          <div className="strat-progress-bar">
            <div
              className="strat-progress-fill"
              style={{ width: `${pct}%`, background: pct === 100 ? 'var(--accent-green)' : 'var(--accent-orange)' }}
            />
          </div>
        </div>
        <div className="stat">
          <span className="stat-label">Backend</span>
          <span className="stat-value strat-mono">{strategy.policyBackend}</span>
        </div>
        <div className="stat">
          <span className="stat-label">Executions</span>
          <span className="stat-value">{strategy.executionHistory.length}</span>
        </div>
      </div>

      <button
        className="btn btn-secondary strat-expand-btn"
        onClick={() => setExpanded(!expanded)}
        type="button"
      >
        {expanded ? 'Hide Details' : 'Show Details'}
      </button>

      {expanded && (
        <div className="strat-details animate-fade-in">
          <div className="strat-detail-grid">
            <div className="strat-detail-section">
              <h4>Notional Caps</h4>
              <div className="strat-kv-list">
                <div className="strat-kv"><span>Per Order</span><span>{strategy.notionalCaps.perOrder.toLocaleString()}</span></div>
                <div className="strat-kv"><span>Per Window</span><span>{strategy.notionalCaps.perWindow.toLocaleString()}</span></div>
                <div className="strat-kv"><span>Lifetime</span><span>{strategy.notionalCaps.lifetime.toLocaleString()}</span></div>
              </div>
            </div>
            <div className="strat-detail-section">
              <h4>Risk Limits</h4>
              <div className="strat-kv-list">
                <div className="strat-kv"><span>Max Slippage</span><span>{strategy.riskLimits.maxSlippageBps} bps</span></div>
                <div className="strat-kv"><span>Oracle Staleness</span><span>{strategy.riskLimits.maxOracleStale} epochs</span></div>
                <div className="strat-kv"><span>Quote Receipts</span><span>{strategy.riskLimits.requireQuoteReceipts ? 'required' : 'optional'}</span></div>
              </div>
            </div>
            <div className="strat-detail-section">
              <h4>Window</h4>
              <div className="strat-kv-list">
                <div className="strat-kv"><span>From Epoch</span><span>{strategy.window.from}</span></div>
                <div className="strat-kv"><span>Until Epoch</span><span>{strategy.window.until}</span></div>
                <div className="strat-kv"><span>Min Spacing</span><span>{strategy.window.spacing} epochs</span></div>
              </div>
            </div>
            <div className="strat-detail-section">
              <h4>Controls</h4>
              <div className="strat-kv-list">
                <div className="strat-kv"><span>Kill Switch</span><span className={strategy.controls.killSwitch ? 'strat-green' : 'strat-red'}>{strategy.controls.killSwitch ? 'enabled' : 'disabled'}</span></div>
                <div className="strat-kv"><span>Max Live Orders</span><span>{strategy.controls.maxLiveOrders}</span></div>
              </div>
            </div>
          </div>

          {strategy.executionHistory.length > 0 && (
            <div className="strat-exec-history">
              <h4>Execution History</h4>
              <div className="strat-exec-table">
                <div className="strat-exec-head">
                  <span>Epoch</span>
                  <span>Action</span>
                  <span>Amount</span>
                  <span>Status</span>
                </div>
                {strategy.executionHistory.map((exec, idx) => (
                  <div key={idx} className="strat-exec-row">
                    <span className="strat-mono">{exec.epoch}</span>
                    <span>{exec.action}</span>
                    <span>{exec.amount.toLocaleString()}</span>
                    <span className={`strat-exec-status strat-exec-${exec.status}`}>{exec.status}</span>
                  </div>
                ))}
              </div>
            </div>
          )}

          {strategy.lastDecision.epoch > 0 && (
            <div className="strat-last-decision">
              <h4>Last Decision</h4>
              <div className="strat-kv-list">
                <div className="strat-kv"><span>Epoch</span><span>{strategy.lastDecision.epoch}</span></div>
                <div className="strat-kv"><span>Candidate</span><span className="strat-mono">{strategy.lastDecision.candidate}</span></div>
                <div className="strat-kv"><span>Admissible</span><span className={strategy.lastDecision.admissible ? 'strat-green' : 'strat-red'}>{strategy.lastDecision.admissible ? 'yes' : 'no'}</span></div>
                <div className="strat-kv"><span>Model</span><span className="strat-mono">{strategy.decisionModel}</span></div>
              </div>
            </div>
          )}
        </div>
      )}
    </article>
  );
}

function AutoTraderLivePrepareSurface({ demoMode }) {
  const smokeEnabled = isAutoTraderSmokeEnabled();
  const [status, setStatus] = useState(null);
  const [acknowledged, setAcknowledged] = useState(smokeEnabled);
  const [result, setResult] = useState(null);
  const [error, setError] = useState('');
  const [busy, setBusy] = useState(false);

  const report = result?.report || null;
  const decisionTag = report?.decision?.tag || 'pending';
  const liveAdmission = report?.live_admission?.ok === true ? 'accepted' : 'pending';
  const submitBundle = report?.submit_bundle?.ok === true ? 'ready' : 'pending';
  const operations = report?.operations && typeof report.operations === 'object' ? report.operations : {};
  const operationCount = Object.values(operations).reduce((total, values) => (
    Array.isArray(values) ? total + values.length : total
  ), 0);
  const nonClaims = result?.not_claimed || status?.not_claimed || [];

  async function refreshStatus() {
    try {
      const payload = await apiGetAutotraderStatus();
      setStatus(payload?.status || null);
    } catch (err) {
      setError(err?.message || 'status_unavailable');
    }
  }

  async function prepareLiveStrategy() {
    setBusy(true);
    setError('');
    try {
      const payload = await apiPrepareAutotraderLive({
        acknowledge_experimental_live_risk: acknowledged,
        signer_privkey: 7,
        chain_id: 'tau-local',
        tx_sequence_number: 9,
        tx_expiration_time: 999,
      });
      setResult(payload);
    } catch (err) {
      setResult(null);
      setError(err?.message || 'prepare_failed');
    } finally {
      setBusy(false);
    }
  }

  useEffect(() => {
    refreshStatus();
  }, []);

  useEffect(() => {
    if (!demoMode && smokeEnabled) {
      prepareLiveStrategy();
    }
    // The smoke path intentionally runs once from the URL trigger.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [demoMode, smokeEnabled]);

  return (
    <div className="panel strat-section-card strat-live-panel animate-fade-in" aria-label="AutoTrader live prepare">
      <div className="strat-section-header">
        <div>
          <h2>AutoTrader Live Prepare</h2>
          <p className="strat-live-copy">
            Receipt-backed prepare builds signed operations after policy, guard, nonce, and tx-envelope checks.
          </p>
        </div>
        <span className="strat-section-badge">{status?.mode || 'receipt-backed prepare'}</span>
      </div>

      <div className="strat-live-grid">
        <div className="strat-live-metric">
          <span>API</span>
          <strong>{status?.enabled ? 'mounted' : 'checking'}</strong>
        </div>
        <div className="strat-live-metric">
          <span>Decision</span>
          <strong>{decisionTag}</strong>
        </div>
        <div className="strat-live-metric">
          <span>Live admission</span>
          <strong>{liveAdmission}</strong>
        </div>
        <div className="strat-live-metric">
          <span>Submit bundle</span>
          <strong>{submitBundle}</strong>
        </div>
        <div className="strat-live-metric">
          <span>Operations</span>
          <strong>{operationCount}</strong>
        </div>
        <div className="strat-live-metric">
          <span>Chain</span>
          <strong>{report?.signing?.chain_id || status?.chain_id || 'tau-local'}</strong>
        </div>
      </div>

      <label className="strat-live-ack">
        <input
          type="checkbox"
          checked={acknowledged}
          onChange={(event) => setAcknowledged(event.target.checked)}
          disabled={busy || demoMode}
        />
        <span>Acknowledge experimental live risk for local receipt preparation</span>
      </label>

      <div className="strat-live-actions">
        <button
          className="btn btn-primary"
          type="button"
          onClick={prepareLiveStrategy}
          disabled={busy || demoMode || !acknowledged}
        >
          {busy ? 'Preparing...' : 'Prepare Live Strategy'}
        </button>
        <button className="btn btn-secondary" type="button" onClick={refreshStatus} disabled={busy}>
          Refresh Status
        </button>
      </div>

      {error && (
        <div className="strat-live-error" role="alert">
          {error}
        </div>
      )}

      {result && (
        <div className="strat-live-result" aria-label="AutoTrader prepare result">
          <div className="strat-kv"><span>Status</span><span>{result.status}</span></div>
          <div className="strat-kv"><span>Signer</span><span className="strat-mono">{report?.signing?.signer_pubkey}</span></div>
          <div className="strat-kv"><span>Intent count</span><span>{report?.decision?.intents?.length || 0}</span></div>
          <div className="strat-kv"><span>Risk acknowledgement</span><span>{report?.risk_disclosure?.user_acknowledged ? 'recorded' : 'missing'}</span></div>
          {report?.tau_tx_payload && (
            <div className="strat-live-code strat-mono">
              {JSON.stringify({ action: 'SWAP_EXACT_IN', decision: decisionTag, operations: operationCount })}
            </div>
          )}
        </div>
      )}

      {nonClaims.length > 0 && (
        <div className="strat-live-nonclaims">
          {nonClaims.map((item) => (
            <span key={item} className="strat-action-chip">{item}</span>
          ))}
        </div>
      )}
    </div>
  );
}

function StrategyWorkbench() {
  const { demoMode } = useDemoMode();
  const postureLabel = demoMode ? 'Demo workbench' : 'Live prepare mounted';
  const subtitle = demoMode
    ? 'Inspect strategy templates, guard catalogs, and proof inventory with static reference data. This tab does not submit live strategies or show receipt-backed execution.'
    : 'Prepare receipt-backed AutoTrader operations locally after explicit risk acknowledgement. Unattended execution and production chain submission remain outside the mounted claim.';

  return (
    <section className="strat-workbench">
      {/* Hero */}
      <div className="strat-hero panel panel-glass animate-fade-in">
        <div>
          <p className="strat-kicker">Policy-constrained automation</p>
          <h1>AutoTrader Strategies</h1>
          <p className="strat-subtitle">{subtitle}</p>
        </div>
        <div className="strat-hero-meta">
          <span className="strat-chip">{postureLabel}</span>
          <span className="strat-chip">{DEMO_STRATEGIES.length} strategies</span>
          <span className="strat-chip strat-chip-accent">{TAU_POLICY_GUARDS.length} guards</span>
        </div>
      </div>

      <AutoTraderLivePrepareSurface demoMode={demoMode} />

      {/* Strategy Templates */}
      <div className="strat-grid">
        <div className="panel strat-section-card">
          <div className="strat-section-header">
            <h2>Strategy Templates</h2>
            <span className="strat-section-badge">Available types</span>
          </div>
          <div className="strat-template-grid">
            {STRATEGY_TEMPLATES.map((tmpl) => (
              <div key={tmpl.id} className="strat-template-card">
                <div className="strat-template-label">{tmpl.label}</div>
                <p className="strat-template-desc">{tmpl.description}</p>
                <div className="strat-template-meta">
                  {tmpl.allowedActions.map((action) => (
                    <span key={action} className="strat-action-chip">{action}</span>
                  ))}
                </div>
              </div>
            ))}
          </div>
        </div>

        <div className="panel strat-section-card">
          <div className="strat-section-header">
            <h2>Formal Proofs</h2>
            <span className="strat-section-badge">Lean 4</span>
          </div>
          <div className="strat-proof-list">
            {FORMAL_PROOFS.map((proof) => (
              <article key={proof.id} className="strat-proof-row">
                <div>
                  <div className="strat-proof-title">{proof.label}</div>
                  <span className="strat-mono strat-proof-file">{proof.file}</span>
                </div>
                <span className="strat-status strat-status-proved">{proof.status}</span>
              </article>
            ))}
          </div>
        </div>
      </div>

      {/* Tau Policy Guard Pipeline */}
      <div className="panel strat-section-card animate-fade-in">
        <div className="strat-section-header">
          <h2>Tau Policy Guard Pipeline</h2>
          <span className="strat-section-badge">10-stage verification</span>
        </div>
        <div className="strat-guard-pipeline">
          {TAU_POLICY_GUARDS.map((guard, idx) => (
            <div key={guard.id} className="strat-guard-step">
              <div className="strat-guard-index">{idx + 1}</div>
              <div className="strat-guard-body">
                <div className="strat-guard-label">{guard.label}</div>
                <p className="strat-guard-detail">{guard.detail}</p>
                <span className="strat-mono strat-guard-spec">{guard.spec}</span>
              </div>
              <span className={`strat-status strat-status-${guard.status}`}>{guard.status}</span>
            </div>
          ))}
        </div>
      </div>

      {/* Active Strategies */}
      <div className="strat-section-header strat-standalone-header">
        <h2>Active Strategies</h2>
        <span className="strat-section-badge">{demoMode ? 'Demo data' : 'Reference data'}</span>
      </div>
      {DEMO_STRATEGIES.map((strategy) => (
        <StrategyCard key={strategy.strategyId} strategy={strategy} />
      ))}
    </section>
  );
}

export default StrategyWorkbench;
