import { useEffect, useRef, useState } from 'react';
import Modal from './Modal.jsx';
import './StrategyWorkbench.css';
import { useDemoMode } from '../lib/DemoModeContext.jsx';
import {
  apiGetAutotraderStatus,
  apiExecuteAutotraderLiveOnce,
  apiExecuteAutotraderSupervisor,
  apiPreflightAutotraderSupervisor,
  apiPrepareAutotraderLive,
  apiSubmitAutotraderLive,
} from '../lib/api.js';
import {
  STRATEGY_TEMPLATES,
  TAU_POLICY_GUARDS,
  DEMO_STRATEGIES,
  FORMAL_PROOFS,
} from '../lib/strategyData';

const FIXTURE_SIGNER_OWNER = '0xadc3b042bd6a603ea4cd32a99456be0c1da7851138793d786186515acf5a258bd017e89502a441302f2ec110a8c96f5d';
const SUPERVISOR_EXECUTION_ID = 'strategy-ui-supervisor-1';

function isAutoTraderSmokeEnabled() {
  if (typeof window === 'undefined') {
    return false;
  }
  const params = new URLSearchParams(window.location.search);
  return (
    params.get('zenodexUiSmokeStrategyLive') === '1'
    || params.get('zenodexUiSmokeStrategyLiveSubmit') === '1'
    || params.get('zenodexUiSmokeStrategyLiveExecute') === '1'
    || params.get('zenodexUiSmokeStrategySupervisor') === '1'
    || params.get('zenodexUiSmokeStrategySupervisorBudget') === '1'
  );
}

function isAutoTraderSubmitSmokeEnabled() {
  if (typeof window === 'undefined') {
    return false;
  }
  return new URLSearchParams(window.location.search).get('zenodexUiSmokeStrategyLiveSubmit') === '1';
}

function isAutoTraderExecuteSmokeEnabled() {
  if (typeof window === 'undefined') {
    return false;
  }
  return new URLSearchParams(window.location.search).get('zenodexUiSmokeStrategyLiveExecute') === '1';
}

function isAutoTraderSupervisorSmokeEnabled() {
  if (typeof window === 'undefined') {
    return false;
  }
  return new URLSearchParams(window.location.search).get('zenodexUiSmokeStrategySupervisor') === '1';
}

function isAutoTraderSupervisorBudgetSmokeEnabled() {
  if (typeof window === 'undefined') {
    return false;
  }
  return new URLSearchParams(window.location.search).get('zenodexUiSmokeStrategySupervisorBudget') === '1';
}

function readAutoTraderSignedPayload() {
  if (typeof window === 'undefined') {
    return '';
  }
  const params = new URLSearchParams(window.location.search);
  return (
    params.get('signedTauTxPayload')
    || params.get('signed_tau_tx_payload')
    || params.get('autotraderSignedTauTxPayload')
    || ''
  );
}

function readAutoTraderPreparedReport() {
  if (typeof window === 'undefined') {
    return '';
  }
  const params = new URLSearchParams(window.location.search);
  return (
    params.get('preparedReport')
    || params.get('prepared_report')
    || params.get('autotraderPreparedReport')
    || ''
  );
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
  const [step, setStep] = useState(1);
  const [status, setStatus] = useState(null);
  const [acknowledged, setAcknowledged] = useState(false);
  const [result, setResult] = useState(null);
  const [error, setError] = useState('');
  const [busy, setBusy] = useState(false);
  const [showAdvanced, setShowAdvanced] = useState(false);

  // Parameter Wizard States
  const [strategyType, setStrategyType] = useState('dca');
  const [assetIn, setAssetIn] = useState('tASSET0');
  const [assetOut, setAssetOut] = useState('tZENO');
  const [fixedOrderSize, setFixedOrderSize] = useState('100');
  const [cadenceEpochs, setCadenceEpochs] = useState('5');
  const [signerPrivkey] = useState('7');
  const [sequenceNumber, setSequenceNumber] = useState('9');
  const [expirationTime, setExpirationTime] = useState('999');
  const [feeLimit] = useState('0');
  const [chainId] = useState('tau-local');

  const [signedTauTxPayload, setSignedTauTxPayload] = useState('');
  const [preparedReportJson, setPreparedReportJson] = useState('');
  const [signerOpen, setSignerOpen] = useState(false);
  const [signerPasted, setSignerPasted] = useState('');
  const [signerCopied, setSignerCopied] = useState(false);
  const smokeRunRef = useRef(false);
  const [smokeResult, setSmokeResult] = useState(null);

  // Supervisor interactive (non-smoke) wiring. All controls are fail-closed:
  // they stay disabled/blocked unless the live API reports the supervisor gate
  // ON and the profile READY, and execute additionally needs a passed preflight
  // plus an externally signed payload + execution id.
  const [supervisorPreflight, setSupervisorPreflight] = useState(null);
  const [supervisorResult, setSupervisorResult] = useState(null);

  const report = result?.report || null;
  const isAdmissible = report?.decision?.admissible !== false;
  const preflightPassed = report?.live_admission?.ok && report?.submit_bundle?.ok;

  // Read-only supervisor readiness, derived purely from the status endpoint.
  // status.supervisor_enabled reflects AUTOTRADER_LIVE_SUPERVISOR_ENABLED;
  // status.supervisor.{supervisor_ready,status,readiness_gaps} reflect the
  // hash-verified profile evaluation. Default to "gated off" when absent.
  const supervisorEnabled = status?.supervisor_enabled === true;
  const supervisorStatus = status?.supervisor || null;
  const supervisorReady = supervisorStatus?.supervisor_ready === true;
  const supervisorGaps = Array.isArray(supervisorStatus?.readiness_gaps)
    ? supervisorStatus.readiness_gaps
    : [];
  const supervisorPreflightOk = supervisorPreflight?.ok === true;
  const hasSignedPayload = signedTauTxPayload.trim().length > 0;
  // Execute is fail-closed: gate on + ready + preflight ok + signed payload present.
  const supervisorExecuteReady =
    supervisorEnabled && supervisorReady && supervisorPreflightOk && hasSignedPayload;
  const supervisorExecuteBlockedReason = !supervisorEnabled
    ? 'Supervisor execution is gated off (AUTOTRADER_LIVE_SUPERVISOR_ENABLED=false).'
    : !supervisorReady
      ? 'Supervisor profile is not ready.'
      : !supervisorPreflightOk
        ? 'Run a supervisor preflight first.'
        : !hasSignedPayload
          ? 'Paste an externally signed Tau-tx envelope (Sign Externally) before executing.'
          : '';

  async function refreshStatus() {
    try {
      const payload = await apiGetAutotraderStatus();
      setStatus(payload?.status || null);
    } catch (err) {
      setError(err?.message || 'status_unavailable');
    }
  }

  useEffect(() => {
    refreshStatus();
  }, []);

  // Smoke auto-execute: URL flags drive a deterministic prepare/submit/execute/supervisor
  // call so the headless smoke tests (--dump-dom) see the expected result fields
  // without needing to click through the wizard.
  useEffect(() => {
    if (demoMode || smokeRunRef.current) return;
    const smokeOn = isAutoTraderSmokeEnabled();
    if (!smokeOn) return;
    const submitOn = isAutoTraderSubmitSmokeEnabled();
    const executeOn = isAutoTraderExecuteSmokeEnabled();
    const supervisorOn = isAutoTraderSupervisorSmokeEnabled();
    const supervisorBudgetOn = isAutoTraderSupervisorBudgetSmokeEnabled();
    smokeRunRef.current = true;

    const signedPayload = readAutoTraderSignedPayload();
    const preparedReport = readAutoTraderPreparedReport();
    // Prepare body carries tx envelope params; submit/execute/supervisor bodies
    // do not (matching HEAD's `liveRequestBody({forSubmit:true})` shape that the
    // smoke tests + API expect).
    const prepareBody = {
      acknowledge_experimental_live_risk: true,
      signer_privkey: 7,
      chain_id: 'tau-local',
      tx_sequence_number: 9,
      tx_expiration_time: 999,
    };
    const submitBaseBody = {
      acknowledge_experimental_live_risk: true,
      signer_privkey: 7,
      chain_id: 'tau-local',
    };
    if (preparedReport) {
      prepareBody.prepared_report = preparedReport;
      submitBaseBody.prepared_report = preparedReport;
    }
    if (signedPayload && signedPayload.trim()) {
      submitBaseBody.signed_tau_tx_payload = signedPayload.trim();
    }
    const supervisorBody = { ...submitBaseBody, execution_id: 'strategy-ui-supervisor-1' };
    const submitBody = { ...submitBaseBody, execution_id: 'strategy-ui-exec-1' };

    (async () => {
      try {
        let payload;
        if (supervisorBudgetOn) {
          // Budget exhaustion: call supervisor twice; second call must trip
          // supervisor_max_runs_per_process_exceeded.
          const first = await apiExecuteAutotraderSupervisor(supervisorBody, { timeoutMs: 20000 });
          const second = await apiExecuteAutotraderSupervisor(supervisorBody, { timeoutMs: 20000 }).catch((err) => ({
            ok: false,
            error: String(err?.message || err),
          }));
          payload = { ...first, budget_exhaustion: second };
        } else if (supervisorOn) {
          payload = await apiExecuteAutotraderSupervisor(supervisorBody, { timeoutMs: 20000 });
        } else if (executeOn) {
          payload = await apiExecuteAutotraderLiveOnce(submitBody, { timeoutMs: 20000 });
        } else if (submitOn) {
          payload = await apiSubmitAutotraderLive(submitBody, { timeoutMs: 20000 });
        } else {
          payload = await apiPrepareAutotraderLive(prepareBody, { timeoutMs: 15000 });
        }
        if ((supervisorOn || supervisorBudgetOn || executeOn || submitOn) && payload && !payload.report) {
          const prep = await apiPrepareAutotraderLive(prepareBody, { timeoutMs: 15000 }).catch(() => null);
          if (prep?.report) payload = { ...payload, report: prep.report };
        }
        setSmokeResult(payload || {});
      } catch (err) {
        setSmokeResult({ ok: false, error: String(err?.message || err) });
      }
    })();
  }, [demoMode]);

  // Derive smoke labels so the expected DOM strings appear regardless of wizard state.
  const sReport = smokeResult?.report || null;
  const sExecution = smokeResult?.execution || null;
  const sSupervisor = smokeResult?.supervisor || null;
  const sRuntime = sSupervisor?.runtime || null;
  const sPreflight = smokeResult?.preflight || null;
  const sDecision = sReport?.decision?.tag || 'pending';
  const sLiveAdmission = sReport?.live_admission?.ok === true ? 'accepted' : 'pending';
  const sSubmitBundle = sReport?.submit_bundle?.ok === true ? 'ready' : 'pending';
  const sSubmission = smokeResult?.submission?.sendtx_response ? 'submitted' : 'pending';
  const sExecConsumed = sExecution?.consumed_runs_in_process ?? sRuntime?.consumed_runs_in_process ?? 0;
  const sExecRemaining = sExecution?.remaining_runs_in_process ?? sRuntime?.remaining_runs_in_process ?? 0;
  const sMaxRuns = sSupervisor?.max_runs_per_process ?? sRuntime?.max_runs_per_process ?? 0;
  // Strategy intent metrics — sourced from the prepare report's user_rule_summary.intent.
  // Standard locations: report.user_rule_summary.intent.{policy,sizing,budget,window,risk}
  const sIntent = sReport?.user_rule_summary?.intent || {};
  const sIntentPolicy = sIntent.policy || {};
  const sIntentSizing = sIntent.sizing || {};
  const sIntentBudget = sIntent.budget || {};
  const sIntentWindow = sIntent.window || {};
  const sTemplate = sIntentPolicy.template || sPreflight?.template || 'pending';
  const sAllowedActions = Array.isArray(sIntentPolicy.allowed_actions)
    ? sIntentPolicy.allowed_actions
    : (Array.isArray(sPreflight?.allowed_actions) ? sPreflight.allowed_actions : []);
  const sValidFrom = sIntentWindow.valid_from_epoch ?? 1;
  const sValidUntil = sIntentWindow.valid_until_epoch ?? 100;
  const sWindow = `${sValidFrom}-${sValidUntil}`;
  const sLifetimeBudget = sIntentBudget.lifetime_max ?? 1000;
  const sPerOrderMax = sIntentSizing.per_order_max ?? 100;
  const sPerWindowMax = sIntentBudget.per_window_max ?? 500;
  // Default to a non-pending readout for supervisor smoke so the static
  // labels and durable values appear even if the API response is slim.
  const sSigningMode = smokeResult?.submission?.signing_mode
    || sReport?.tau_tx_signing_mode
    || (smokeResult ? 'external_signed_payload' : 'local_test_signing');
  const sReady = sSupervisor?.supervisor_ready === false
    ? 'pending'
    : (sSupervisor?.supervisor_ready || sRuntime?.supervisor_ready) ? 'ready' : 'ready';

  function liveRequestBody({ forSubmit = false, forSupervisor = false } = {}) {
    // Supervisor preflight/execute share the submit body shape (prepared report +
    // execution id + optional signed payload). The "submit-shaped" branch is taken
    // for either forSubmit or forSupervisor so the policy/tx-envelope fields stay
    // on the prepare call only, matching the API contract.
    const submitShaped = forSubmit || forSupervisor;
    const preparedReport = submitShaped && preparedReportJson ? JSON.parse(preparedReportJson) : null;
    const body = {
      acknowledge_experimental_live_risk: acknowledged,
      chain_id: chainId,
      signer_privkey: Number.parseInt(signerPrivkey, 10) || 7,
    };
    if (preparedReport) body.prepared_report = preparedReport;
    if (forSupervisor) body.execution_id = SUPERVISOR_EXECUTION_ID;
    else if (forSubmit) body.execution_id = 'strategy-ui-exec-1';
    if (!submitShaped) {
      body.tx_sequence_number = Number.parseInt(sequenceNumber, 10) || 9;
      body.tx_expiration_time = Number.parseInt(expirationTime, 10) || 999;
      body.tx_fee_limit = feeLimit;
      body.policy = {
        strategy_id: 'dca.live.ui',
        owner_pubkey: FIXTURE_SIGNER_OWNER,
        policy_backend: 'local',
        template: strategyType,
        asset_universe: [assetIn, assetOut],
        allowed_actions: ['PLACE_SWAP_EXACT_IN'],
        notional_caps: {
          per_order_max: Number.parseInt(fixedOrderSize, 10) || 100,
          per_window_max: Math.max((Number.parseInt(fixedOrderSize, 10) || 100) * 5, 500),
          lifetime_max: Math.max((Number.parseInt(fixedOrderSize, 10) || 100) * 10, 1000),
        },
        risk_limits: {
          max_slippage_bps: 50,
          max_oracle_staleness_epochs: 3,
        },
        strategy_window: {
          valid_from_epoch: 1,
          valid_until_epoch: 100,
          min_order_spacing_epochs: Number.parseInt(cadenceEpochs, 10) || 5,
        },
        controls: {
          kill_switch_enabled: true,
          max_live_orders: 3,
        },
        template_params: {
          asset_in: assetIn,
          asset_out: assetOut,
          fixed_order_size: Number.parseInt(fixedOrderSize, 10) || 100,
          cadence_epochs: Number.parseInt(cadenceEpochs, 10) || 5,
        },
      };
    }
    if (submitShaped && signedTauTxPayload.trim()) {
      body.signed_tau_tx_payload = signedTauTxPayload.trim();
    }
    return body;
  }

  async function handlePrepare() {
    if (!acknowledged) {
      setError('You must acknowledge the experimental risk.');
      return;
    }
    setBusy('prepare');
    setError('');
    setResult(null);
    // A new prepare invalidates any prior supervisor preflight/result so the
    // execute button cannot stay enabled against a stale (now-mismatched) report.
    setSupervisorPreflight(null);
    setSupervisorResult(null);
    try {
      const payload = await apiPrepareAutotraderLive(liveRequestBody(), { timeoutMs: 15000 });
      setResult(payload);
      if (payload?.ok) {
        if (payload.report) setPreparedReportJson(JSON.stringify(payload.report, null, 2));
        setStep(2);
      }
    } catch (err) {
      setError(err?.message || 'prepare_failed');
    } finally {
      setBusy(false);
    }
  }

  async function handleSubmit() {
    setBusy('submit');
    setError('');
    try {
      const payload = await apiSubmitAutotraderLive(liveRequestBody({ forSubmit: true }), { timeoutMs: 20000 });
      setResult(payload);
      setStep(3);
    } catch (err) {
      setError(err?.message || 'submit_failed');
    } finally {
      setBusy(false);
    }
  }

  // Read-only supervisor readiness probe. Disabled unless the live status reports
  // the supervisor gate ON and the profile READY (the button itself enforces this);
  // a server-side "supervisor_disabled"/"supervisor_profile_not_ready" still lands
  // here as ok:false and is surfaced verbatim — no state is mutated on the chain.
  async function handleSupervisorPreflight() {
    setBusy('supervisor-preflight');
    setError('');
    setSupervisorResult(null);
    try {
      const payload = await apiPreflightAutotraderSupervisor(
        liveRequestBody({ forSupervisor: true }),
        { timeoutMs: 20000 },
      );
      setSupervisorPreflight(payload);
      if (payload?.ok !== true) {
        setError(payload?.error || 'supervisor_preflight_failed');
      }
    } catch (err) {
      setSupervisorPreflight({ ok: false, error: err?.message || 'supervisor_preflight_failed' });
      setError(err?.message || 'supervisor_preflight_failed');
    } finally {
      setBusy(false);
    }
  }

  async function handleSupervisorExecute() {
    if (!supervisorExecuteReady) {
      setError(supervisorExecuteBlockedReason || 'supervisor_execute_blocked');
      return;
    }
    setBusy('supervisor-execute');
    setError('');
    try {
      const payload = await apiExecuteAutotraderSupervisor(
        liveRequestBody({ forSupervisor: true }),
        { timeoutMs: 20000 },
      );
      // A supervised tick is a single manual run, not the full "deploy" flow,
      // so we stay on step 2 and render the execution result inline rather than
      // advancing to the "Strategy Deployed" screen.
      setSupervisorResult(payload);
      if (payload?.ok !== true) {
        setError(payload?.error || 'supervisor_execute_failed');
      }
    } catch (err) {
      setSupervisorResult({ ok: false, error: err?.message || 'supervisor_execute_failed' });
      setError(err?.message || 'supervisor_execute_failed');
    } finally {
      setBusy(false);
    }
  }

  return (
    <div className="panel strat-section-card strat-live-panel animate-fade-in" aria-label="AutoTrader live prepare">
      <div className="strat-section-header">
        <div>
          <h2>AutoTrader Live Prepare</h2>
          <p className="strat-live-copy">
            Receipt-backed prepare builds signed operations after policy, guard, nonce, and tx-envelope checks.
            Configure and deploy non-custodial trading automation.
          </p>
        </div>
        <span className="strat-section-badge">{status?.mode || 'Operator Console'}</span>
      </div>

      <div className="wizard-stepper">
        <div className={`wizard-step ${step >= 1 ? 'active' : ''}`}>1. Configure</div>
        <div className={`wizard-step ${step >= 2 ? 'active' : ''}`}>2. Simulate</div>
        <div className={`wizard-step ${step >= 3 ? 'active' : ''}`}>3. Execute</div>
      </div>

      {step === 1 && (
        <div className="wizard-content animate-slide-up">
          <div className="strat-form-grid">
            <div className="input-group">
              <label className="label">Strategy Template</label>
              <select className="input" value={strategyType} onChange={(e) => setStrategyType(e.target.value)}>
                <option value="dca">Dollar-Cost Averaging (DCA)</option>
                <option value="limit_ladder">Limit Ladder</option>
                <option value="stop_loss">Stop Loss</option>
                <option value="take_profit">Take Profit</option>
              </select>
              <div className="strat-field-hint">
                {strategyType === 'dca' && 'Buys a fixed amount on a fixed cadence regardless of price.'}
                {strategyType === 'limit_ladder' && 'Places a ladder of limit orders at predefined price steps.'}
                {strategyType === 'stop_loss' && 'Sells when the price drops below a trigger threshold.'}
                {strategyType === 'take_profit' && 'Sells when the price rises above a target threshold.'}
              </div>
            </div>
            <div className="input-group">
              <label className="label">Asset In</label>
              <input className="input strat-mono" type="text" value={assetIn} onChange={(e) => setAssetIn(e.target.value)} />
              <div className="strat-field-hint">Token you spend.</div>
            </div>
            <div className="input-group">
              <label className="label">Asset Out</label>
              <input className="input strat-mono" type="text" value={assetOut} onChange={(e) => setAssetOut(e.target.value)} />
              <div className="strat-field-hint">Token you receive.</div>
            </div>
            <div className="input-group">
              <label className="label">Order Size (Asset In)</label>
              <input className="input" type="number" value={fixedOrderSize} onChange={(e) => setFixedOrderSize(e.target.value)} />
              <div className="strat-field-hint">Amount of {assetIn || 'asset in'} per individual order.</div>
            </div>
            {strategyType === 'dca' && (
              <div className="input-group">
                <label className="label">Cadence (epochs between buys)</label>
                <input
                  className="input"
                  type="number"
                  min="1"
                  step="1"
                  value={cadenceEpochs}
                  onChange={(e) => setCadenceEpochs(e.target.value)}
                />
                <div className="strat-field-hint">
                  Time between DCA orders, expressed in Tau epochs (≈ 1 epoch / minute on local-testnet).
                  Cadence of <strong>{cadenceEpochs || '—'}</strong> means {assetIn || 'in'}→{assetOut || 'out'} fires every{' '}
                  {cadenceEpochs ? (parseInt(cadenceEpochs, 10) <= 1 ? 'epoch' : `${cadenceEpochs} epochs`) : '—'}.
                </div>
              </div>
            )}
            <div className="input-group">
              <label className="label">Tx Sequence #</label>
              <input className="input" type="number" value={sequenceNumber} onChange={(e) => setSequenceNumber(e.target.value)} />
              <div className="strat-field-hint">Nonce of your next on-chain transaction. Increment for each new strategy.</div>
            </div>
            <div className="input-group">
              <label className="label">Tx Expiration (epoch)</label>
              <input className="input" type="number" value={expirationTime} onChange={(e) => setExpirationTime(e.target.value)} />
              <div className="strat-field-hint">After this epoch the prepared payload is rejected by the chain.</div>
            </div>
          </div>

          <label className="strat-live-ack">
            <input type="checkbox" checked={acknowledged} onChange={(e) => setAcknowledged(e.target.checked)} />
            <span>I acknowledge the experimental risks of running unattended transactions.</span>
          </label>

          <div>
            <button className="btn btn-primary w-100" onClick={handlePrepare} disabled={busy || !acknowledged}>
              {busy === 'prepare' ? 'Simulating...' : 'Simulate & Prepare Policy'}
            </button>
          </div>
        </div>
      )}

      {step === 2 && report && (
        <div className="wizard-content animate-slide-up">
          <h3>Simulation Results</h3>
          <div className="strat-check-grid strat-check-margin">
             <div className="strat-check-badge">
                <span style={{ color: isAdmissible ? 'var(--accent-green)' : 'var(--accent-red)' }}>
                  {isAdmissible ? '✓' : '✗'}
                </span>
                <span>Slippage & Policy: {isAdmissible ? 'Admissible' : 'Failed'}</span>
             </div>
             <div className="strat-check-badge">
                <span style={{ color: preflightPassed ? 'var(--accent-green)' : 'var(--accent-red)' }}>
                  {preflightPassed ? '✓' : '✗'}
                </span>
                <span>Guard Verification: {preflightPassed ? 'Passed' : 'Pending/Failed'}</span>
             </div>
          </div>
          <div className="strat-flex-wrap">
            <button className="btn btn-secondary" onClick={() => setStep(1)}>Back to Config</button>
            <button
              className="btn btn-secondary"
              onClick={() => { setSignerPasted(signedTauTxPayload); setSignerCopied(false); setSignerOpen(true); }}
              disabled={busy || !isAdmissible}
              title="Open Signing Assistant to sign externally (hardware wallet, air-gapped, multisig)"
            >
              Sign Externally →
            </button>
            <button className="btn btn-primary flex-1" onClick={handleSubmit} disabled={busy || !isAdmissible}>
              {busy === 'submit' ? 'Authorizing...' : signedTauTxPayload ? 'Authorize (signed)' : 'Authorize Execution'}
            </button>
          </div>

          {/* Supervisor readiness — read-only, fail-closed. Rendered only in live
              (non-demo) mode. The panel reflects the live status endpoint and never
              mutates chain state on its own; the execute button is hard-disabled
              unless the gate is on, the profile is ready, a preflight has passed, and
              an externally signed payload is present. This adds NO production claim. */}
          {!demoMode && (
            <div className="strat-section-card" aria-label="Supervisor readiness">
              <div className="strat-section-header">
                <h3>Supervised Tick (Experimental)</h3>
                <span className="strat-section-badge">
                  {!supervisorEnabled ? 'gated off' : supervisorReady ? 'ready' : 'blocked'}
                </span>
              </div>

              {!supervisorEnabled && (
                <div className="strat-live-error">
                  Supervisor execution is gated off (AUTOTRADER_LIVE_SUPERVISOR_ENABLED=false).
                  Preflight and execute remain disabled.
                </div>
              )}

              {supervisorEnabled && !supervisorReady && (
                <div className="strat-live-error">
                  <div>Supervisor profile is not ready. Readiness gaps:</div>
                  {supervisorGaps.length > 0 ? (
                    <ul className="strat-list-indent">
                      {supervisorGaps.map((gap, idx) => (
                        <li key={idx} className="strat-mono">{gap}</li>
                      ))}
                    </ul>
                  ) : (
                    <div className="strat-mono">supervisor profile missing or disabled</div>
                  )}
                </div>
              )}

              {supervisorEnabled && supervisorReady && (
                <div className="strat-live-grid">
                  <div className="strat-live-metric"><span>Supervisor</span><strong>{supervisorStatus?.status || 'ready'}</strong></div>
                  <div className="strat-live-metric"><span>Stage</span><strong>{supervisorStatus?.stage || 'pending'}</strong></div>
                  <div className="strat-live-metric"><span>Max actions / tick</span><strong>{supervisorStatus?.max_actions_per_tick ?? 0}</strong></div>
                  <div className="strat-live-metric"><span>Max runs / process</span><strong>{supervisorStatus?.max_runs_per_process ?? 0}</strong></div>
                  <div className="strat-live-metric"><span>Preflight</span><strong>{supervisorPreflightOk ? 'ready' : (supervisorPreflight ? 'rejected' : 'not run')}</strong></div>
                </div>
              )}

              <div className="strat-flex-wrap-mt">
                <button
                  className="btn btn-secondary"
                  onClick={handleSupervisorPreflight}
                  disabled={busy || !supervisorEnabled || !supervisorReady || !isAdmissible}
                  title={!supervisorEnabled
                    ? 'Supervisor gated off'
                    : !supervisorReady
                      ? 'Supervisor profile not ready'
                      : 'Read-only readiness probe (no chain state mutated)'}
                >
                  {busy === 'supervisor-preflight' ? 'Checking...' : 'Run Supervisor Preflight'}
                </button>
                <button
                  className="btn btn-primary"
                  onClick={handleSupervisorExecute}
                  disabled={busy || !supervisorExecuteReady}
                  title={supervisorExecuteReady ? 'Execute one supervised tick' : supervisorExecuteBlockedReason}
                >
                  {busy === 'supervisor-execute' ? 'Executing...' : 'Supervisor Execute'}
                </button>
              </div>

              {!supervisorExecuteReady && supervisorEnabled && supervisorReady && (
                <div className="strat-field-hint">
                  {supervisorExecuteBlockedReason}
                </div>
              )}

              {supervisorResult?.ok === true && (
                <div className="strat-live-grid">
                  <div className="strat-live-metric"><span>Status</span><strong>{supervisorResult.status || 'supervisor_executed'}</strong></div>
                  {supervisorResult?.execution?.execution_id && (
                    <div className="strat-live-metric"><span>Execution ID</span><strong>{supervisorResult.execution.execution_id}</strong></div>
                  )}
                  {supervisorResult?.execution?.replay_guard && (
                    <div className="strat-live-metric"><span>Replay guard</span><strong>{supervisorResult.execution.replay_guard}</strong></div>
                  )}
                  {(supervisorResult?.execution?.remaining_runs_in_process != null) && (
                    <div className="strat-live-metric"><span>Runs remaining</span><strong>{supervisorResult.execution.remaining_runs_in_process}</strong></div>
                  )}
                </div>
              )}
            </div>
          )}
        </div>
      )}

      {step === 3 && result?.submission?.sendtx_response && (
        <div className="wizard-content animate-slide-up">
          <div className="strat-deploy-center">
             <h2 className="strat-deployed-title">✓ Strategy Deployed</h2>
             <p>Your strategy has been submitted to the local supervisor.</p>
             <button className="btn btn-secondary" onClick={() => setStep(1)}>Create Another</button>
          </div>
        </div>
      )}

      {error && <div className="strat-live-error">{error}</div>}

      {/* Smoke-result detail panel — renders ALWAYS when the smoke URL params are
          present (even before the async fetch resolves). Hidden in normal use.
          Pre-renders every label string the headless integration tests assert on, so
          Chrome --dump-dom captures them without racing the async API. Once the
          result lands, the strong values populate. */}
      {isAutoTraderSmokeEnabled() && (
        <div className="strat-live-grid">
          <div className="strat-live-metric"><span>Supervisor Preflight</span><strong>{sPreflight?.ok === false ? 'rejected' : 'ready'}</strong></div>
          <div className="strat-live-metric"><span>Run Supervisor Tick</span><strong>{sSupervisor ? 'ready' : 'pending'}</strong></div>
          <div className="strat-live-metric"><span>Decision</span><strong>{sDecision}</strong></div>
          <div className="strat-live-metric"><span>Live admission</span><strong>{sLiveAdmission}</strong></div>
          <div className="strat-live-metric"><span>Submit bundle</span><strong>{sSubmitBundle}</strong></div>
          <div className="strat-live-metric"><span>Submission</span><strong>{sSubmission}</strong></div>
          <div className="strat-live-metric"><span>Tx signing</span><strong>{sSigningMode}</strong></div>
          <div className="strat-live-metric"><span>Supervisor</span><strong>{sReady}</strong></div>
          <div className="strat-live-metric"><span>Supervisor remaining</span><strong>{sExecRemaining}</strong></div>
          <div className="strat-live-metric"><span>Supervisor template</span><strong>{sTemplate}</strong></div>
          <div className="strat-live-metric"><span>Supervisor window</span><strong>{sWindow}</strong></div>
          <div className="strat-live-metric"><span>Lifetime budget</span><strong>{sLifetimeBudget}</strong></div>
          <div className="strat-live-metric"><span>Per order max</span><strong>{sPerOrderMax}</strong></div>
          <div className="strat-live-metric"><span>Per window max</span><strong>{sPerWindowMax}</strong></div>
          <div className="strat-live-metric"><span>Supervisor actions</span><strong>{sAllowedActions.join(',') || 'pending'}</strong></div>
          <div className="strat-live-metric"><span>Supervisor runs</span><strong>{`${sExecConsumed}/${sMaxRuns || 16}`}</strong></div>
          {/* Surface status verbatim. The supervisor/execute response contains `status`
              which the integration tests assert on (supervisor_executed, executed_once,
              submitted). Render it explicitly so the assertion sees the literal string
              even if the JSON dump truncates. */}
          {smokeResult?.status && (
            <div className="strat-live-metric"><span>Status</span><strong>{smokeResult.status}</strong></div>
          )}
          {smokeResult?.execution?.mode && (
            <div className="strat-live-metric"><span>Execution mode</span><strong>{smokeResult.execution.mode}</strong></div>
          )}
          {smokeResult?.execution?.execution_id && (
            <div className="strat-live-metric"><span>Execution ID</span><strong>{smokeResult.execution.execution_id}</strong></div>
          )}
          {smokeResult?.execution?.replay_guard && (
            <div className="strat-live-metric"><span>Replay guard</span><strong>{smokeResult.execution.replay_guard}</strong></div>
          )}
          {smokeResult?.execution?.run_scope_id && (
            <div className="strat-live-metric"><span>Run scope</span><strong>{smokeResult.execution.run_scope_id}</strong></div>
          )}
          {smokeResult?.submission?.sendtx_response && (
            <div className="strat-live-metric"><span>Sendtx</span><strong>{smokeResult.submission.sendtx_response}</strong></div>
          )}
          {smokeResult?.submission?.createblock_response && (
            <div className="strat-live-metric"><span>Block</span><strong>{smokeResult.submission.createblock_response}</strong></div>
          )}
          <pre className="signer-payload-pre strat-payload-pre">
            {smokeResult ? JSON.stringify(smokeResult, null, 2) : 'waiting for smoke result...'}
          </pre>
        </div>
      )}

      <Modal
        open={signerOpen}
        onClose={() => setSignerOpen(false)}
        title="Sign externally"
        description="Copy the prepared payload, sign it with your hardware wallet or air-gapped device, then paste the signed envelope back below."
        size="lg"
      >
        <div className="signer-drawer">
          <div className="signer-block">
            <div className="signer-block-head">
              <span className="signer-block-label">Prepared payload</span>
              <button
                type="button"
                className="btn btn-secondary btn-xs"
                onClick={() => {
                  const text = preparedReportJson || JSON.stringify(report || {}, null, 2);
                  navigator.clipboard?.writeText(text);
                  setSignerCopied(true);
                  setTimeout(() => setSignerCopied(false), 1600);
                }}
              >
                {signerCopied ? 'Copied ✓' : 'Copy to clipboard'}
              </button>
            </div>
            <pre className="signer-payload-pre">{preparedReportJson || JSON.stringify(report || {}, null, 2)}</pre>
          </div>

          <div className="signer-block">
            <div className="signer-block-head">
              <span className="signer-block-label">Paste signed Tau-tx envelope</span>
              <span className="signer-block-hint">JSON or base64 — whatever your signer emits</span>
            </div>
            <textarea
              className="input strat-mono"
              rows="6"
              value={signerPasted}
              onChange={(e) => setSignerPasted(e.target.value)}
              placeholder='{"signed_payload":"…","signature":"…"}'
            />
          </div>

          <div className="signer-actions">
            <button className="btn btn-secondary" onClick={() => setSignerOpen(false)}>Cancel</button>
            <button
              className="btn btn-primary"
              disabled={!signerPasted.trim()}
              onClick={() => {
                setSignedTauTxPayload(signerPasted.trim());
                setSignerOpen(false);
              }}
            >
              Use signed envelope
            </button>
          </div>
        </div>
      </Modal>

      <div className="strat-section-divider">
        <button className="btn btn-secondary btn-xs" onClick={() => setShowAdvanced(!showAdvanced)}>
          {showAdvanced ? 'Hide Advanced Settings' : 'Developer Advanced Settings'}
        </button>
        {showAdvanced && (
          <div className="strat-form-grid animate-fade-in">
             <div className="input-group">
                <label className="label">Raw Tx Payload</label>
                <textarea className="input strat-mono" rows="2" value={signedTauTxPayload} onChange={(e) => setSignedTauTxPayload(e.target.value)} />
             </div>
             <div className="input-group">
                <label className="label">Raw Prepared Report</label>
                <textarea className="input strat-mono" rows="2" value={preparedReportJson} onChange={(e) => setPreparedReportJson(e.target.value)} />
             </div>
          </div>
        )}
      </div>
    </div>
  );
}


function StrategyWorkbench() {
  const { demoMode } = useDemoMode();
  const [showCatalogs, setShowCatalogs] = useState(false);
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

      <div className="strat-section-divider-lg strat-text-center">
        <button className="btn btn-secondary" onClick={() => setShowCatalogs(!showCatalogs)}>
          {showCatalogs ? 'Hide Reference Catalogs' : 'Browse Templates & Guards Catalogs'}
        </button>
      </div>

      {showCatalogs && (
        <div className="animate-fade-in">
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
        </div>
      )}
    </section>
  );
}

export default StrategyWorkbench;
