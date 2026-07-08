// Copyright DarkLightX/Dana Edwards
// Safety tab — safety checks, dry run, incident history, pause controls

import { useEffect, useState } from 'react';
import {
  apiGetAutotraderStatus,
  apiPreflightAutotraderSupervisor,
  apiExecuteAutotraderSupervisor,
} from '../../lib/api.js';
import { TAU_POLICY_GUARDS } from '../../lib/strategyData.js';

const SUPERVISOR_EXECUTION_ID = 'strategy-ui-supervisor-1';
const FIXTURE_SIGNER_OWNER = '0xadc3b042bd6a603ea4cd32a99456be0c1da7851138793d786186515acf5a258bd017e89502a441302f2ec110a8c96f5d';

function formatJson(value) {
  return JSON.stringify(value, null, 2);
}

function CheckRow({ index, label, passed, pending }) {
  const icon = pending ? '○' : passed ? '✓' : '✕';
  const cls = pending ? 'strategy-check-pending' : passed ? 'strategy-check-pass' : 'strategy-check-fail';
  return (
    <div className="strategy-check-row">
      <span className="strategy-check-icon" aria-hidden="true">{index}.</span>
      <span className={`strategy-check-icon ${cls}`} aria-hidden="true">{icon}</span>
      <span className="strategy-check-label">{label}</span>
    </div>
  );
}

export default function SafetyTab({ systemStatus, signedPayload, onPauseAll, onResumeAll }) {
  const [status, setStatus] = useState(null);
  const [preflight, setPreflight] = useState(null);
  const [executeResult, setExecuteResult] = useState(null);
  const [busy, setBusy] = useState(false);
  const [error, setError] = useState('');
  const [showConfirm, setShowConfirm] = useState(false);
  const [checkedAt, setCheckedAt] = useState(null);
  const [now, setNow] = useState(() => Date.now());

  useEffect(() => {
    let cancelled = false;
    async function fetchStatus() {
      try {
        const payload = await apiGetAutotraderStatus({ timeoutMs: 5000 });
        if (!cancelled) setStatus(payload?.status || null);
      } catch {
        // offline handled by status bar
      }
    }
    fetchStatus();
    const interval = setInterval(fetchStatus, 15000);
    return () => { cancelled = true; clearInterval(interval); };
  }, []);

  useEffect(() => {
    const interval = setInterval(() => setNow(Date.now()), 5000);
    return () => clearInterval(interval);
  }, []);

  const supervisorEnabled = status?.supervisor_enabled === true;
  const supervisorStatus = status?.supervisor || null;
  const supervisorReady = supervisorStatus?.supervisor_ready === true;
  const supervisorGaps = Array.isArray(supervisorStatus?.readiness_gaps) ? supervisorStatus.readiness_gaps : [];
  const preflightOk = preflight?.ok === true;
  const hasSignedPayload = signedPayload && signedPayload.trim().length > 0;
  const executeReady = supervisorEnabled && supervisorReady && preflightOk && hasSignedPayload;
  const systemOffline = systemStatus === 'offline';

  const checkAgeMs = checkedAt ? now - checkedAt : null;
  const checkStale = checkAgeMs !== null && checkAgeMs > 60_000;

  function supervisorBody() {
    return {
      acknowledge_experimental_live_risk: true,
      signer_privkey: 7,
      chain_id: 'tau-local',
      execution_id: SUPERVISOR_EXECUTION_ID,
      ...(hasSignedPayload ? { signed_tau_tx_payload: signedPayload.trim() } : {}),
    };
  }

  async function handleDryRun() {
    setBusy('preflight');
    setError('');
    setExecuteResult(null);
    try {
      const payload = await apiPreflightAutotraderSupervisor(supervisorBody(), { timeoutMs: 20000 });
      setPreflight(payload);
      setCheckedAt(Date.now());
      if (payload?.ok !== true) setError(payload?.error || 'dry_run_failed');
    } catch (err) {
      setPreflight({ ok: false, error: err?.message });
      setError(err?.message || 'dry_run_failed');
    } finally {
      setBusy(false);
    }
  }

  async function handleExecute() {
    setShowConfirm(false);
    setBusy('execute');
    setError('');
    try {
      const payload = await apiExecuteAutotraderSupervisor(supervisorBody(), { timeoutMs: 20000 });
      setExecuteResult(payload);
      if (payload?.ok !== true) setError(payload?.error || 'execute_failed');
    } catch (err) {
      setExecuteResult({ ok: false, error: err?.message });
      setError(err?.message || 'execute_failed');
    } finally {
      setBusy(false);
    }
  }

  // Incident history from supervisor results and preflight failures
  const incidents = [];
  if (preflight?.ok === false) {
    incidents.push({ epoch: '—', strategy: 'supervisor', reason: `Dry run failed: ${preflight.error || 'unknown'}` });
  }
  if (executeResult?.ok === false) {
    incidents.push({ epoch: '—', strategy: 'supervisor', reason: `Execute failed: ${executeResult.error || 'unknown'}` });
  }

  return (
    <div className="strategy-tab-panel" role="tabpanel" aria-label="Safety">
      <p className="strategy-tab-goal">Monitor safety checks and control running automation.</p>

      <div className="strategy-step-section">
        <p className="strategy-step-label">Automation status</p>
        <div className="strategy-row-meta">
          ● {supervisorEnabled ? 'Enabled' : 'Disabled'}
          {' | Supervisor: '}{!supervisorEnabled ? 'gated off' : supervisorReady ? 'ready' : 'blocked'}
          {checkedAt && ` | Last dry run: ${Math.round((now - checkedAt) / 1000)}s ago`}
        </div>
        <div className="strategy-row-actions">
          <button className="btn btn-secondary btn-sm" type="button" onClick={onPauseAll} disabled={systemOffline}>
            ⏸ Pause all
          </button>
          <button className="btn btn-secondary btn-sm" type="button" onClick={onResumeAll} disabled={systemOffline}>
            Resume all
          </button>
        </div>
      </div>

      <div className="strategy-step-section">
        <p className="strategy-step-label">
          Safety checks {checkedAt && `(${Math.round((now - checkedAt) / 1000)}s ago)`}
        </p>
        <div className="strategy-safety-list">
          {TAU_POLICY_GUARDS.map((guard, idx) => (
            <CheckRow
              key={guard.id}
              index={idx + 1}
              label={guard.label}
              passed={preflightOk}
              pending={!preflight}
            />
          ))}
        </div>
        {checkStale && (
          <div className="strategy-banner strategy-banner-warning">
            Dry run is stale. Re-run before executing.
          </div>
        )}
      </div>

      <div className="strategy-step-section">
        <p className="strategy-step-label">Strategy limits</p>
        <div className="strategy-row-meta">
          Max actions/tick: {supervisorStatus?.max_actions_per_tick ?? '—'}
          {' | Max runs/process: '}{supervisorStatus?.max_runs_per_process ?? '—'}
          {' | Stage: '}{supervisorStatus?.stage ?? '—'}
        </div>
      </div>

      {supervisorGaps.length > 0 && (
        <div className="strategy-banner strategy-banner-warning">
          Supervisor readiness gaps:
          <ul>
            {supervisorGaps.map((gap, i) => <li key={i}>{gap}</li>)}
          </ul>
        </div>
      )}

      <div className="strategy-step-section">
        <p className="strategy-step-label">Dry run</p>
        <div className="strategy-row-meta">
          Status: {preflight ? (preflightOk ? 'passed' : 'failed') : 'not run'}
        </div>
        <div className="strategy-actions">
          <button
            className="btn btn-primary strategy-primary-btn"
            type="button"
            onClick={handleDryRun}
            disabled={busy || !supervisorEnabled || !supervisorReady || systemOffline}
          >
            {busy === 'preflight' ? 'Running…' : 'Run dry run'}
          </button>
        </div>

        {preflightOk && (
          <div className="strategy-banner strategy-banner-success">
            ✓ Dry run passed — checks are current
          </div>
        )}
        {preflight && !preflightOk && (
          <div className="strategy-banner strategy-banner-error">
            ✕ Dry run failed: {preflight.error || 'unknown'}
            <div className="strategy-row-actions">
              <button className="btn btn-ghost btn-sm" type="button" onClick={handleDryRun}>Retry</button>
              <button className="btn btn-ghost btn-sm" type="button" onClick={() => navigator.clipboard.writeText(formatJson(preflight))}>Copy diagnostic</button>
            </div>
          </div>
        )}
      </div>

      {preflightOk && (
        <div className="strategy-step-section">
          <p className="strategy-step-label">Run automation</p>
          {!showConfirm ? (
            <button
              className="btn btn-secondary btn-sm"
              type="button"
              onClick={() => setShowConfirm(true)}
              disabled={busy || !executeReady || systemOffline}
            >
              Run automation now
            </button>
          ) : (
            <div className="strategy-confirm-dialog">
              <div className="strategy-confirm-title">⚠ This will execute real transactions on local-testnet.</div>
              <div className="strategy-confirm-detail">Strategy: supervisor tick via {SUPERVISOR_EXECUTION_ID}</div>
              <div className="strategy-confirm-actions">
                <button className="btn btn-ghost btn-sm" type="button" onClick={() => setShowConfirm(false)}>Cancel</button>
                <button className="btn btn-primary btn-sm" type="button" onClick={handleExecute} disabled={busy}>
                  {busy === 'execute' ? 'Executing…' : 'Confirm and execute'}
                </button>
              </div>
            </div>
          )}

          {executeResult?.ok === true && (
            <div className="strategy-banner strategy-banner-success">
              ✓ Executed — runs remaining: {executeResult.execution?.remaining_runs_in_process ?? '—'}
            </div>
          )}
          {executeResult?.ok === false && (
            <div className="strategy-banner strategy-banner-error">
              ✕ Execute failed: {executeResult.error || 'unknown'}
            </div>
          )}
        </div>
      )}

      <div className="strategy-step-section">
        <p className="strategy-step-label">Incident history</p>
        {incidents.length > 0 ? (
          incidents.map((inc, i) => (
            <div key={i} className="strategy-incident-row">
              Epoch {inc.epoch} | {inc.strategy} | {inc.reason}
            </div>
          ))
        ) : (
          <div className="strategy-incident-empty">No incidents recorded.</div>
        )}
      </div>

      {error && (
        <div className="strategy-banner strategy-banner-error" role="alert">
          {error}
        </div>
      )}

      <details className="strategy-advanced">
        <summary>Raw supervisor report</summary>
        <div className="strategy-advanced-body">
          {executeResult || preflight ? (
            <pre className="strategy-api-code-block">{formatJson(executeResult || preflight)}</pre>
          ) : (
            <p className="strategy-tab-hint">Run a dry run or execute to see the raw report.</p>
          )}
        </div>
      </details>
    </div>
  );
}
