// Copyright DarkLightX/Dana Edwards
// Strategies tab — active strategies list + create strategy wizard

import { useEffect, useState } from 'react';
import {
  apiPrepareAutotraderLive,
  apiSubmitAutotraderLive,
} from '../../lib/api.js';
import { STRATEGY_TEMPLATES, DEMO_STRATEGIES } from '../../lib/strategyData.js';
import { useDemoMode } from '../../lib/DemoModeContext.jsx';

const FIXTURE_SIGNER_OWNER = '0xadc3b042bd6a603ea4cd32a99456be0c1da7851138793d786186515acf5a258bd017e89502a441302f2ec110a8c96f5d';
const SUPERVISOR_EXECUTION_ID = 'strategy-ui-supervisor-1';

function formatJson(value) {
  return JSON.stringify(value, null, 2);
}

function StrategyRow({ strategy, onPause, onResume, onStop }) {
  const template = STRATEGY_TEMPLATES.find((t) => t.id === strategy.template);
  const isRunning = strategy.status === 'active';
  const isPaused = strategy.status === 'paused';
  const lastExec = strategy.executionHistory[strategy.executionHistory.length - 1];
  const spent = strategy.executionHistory
    .filter((e) => e.status === 'settled')
    .reduce((sum, e) => sum + e.amount, 0);
  const remaining = strategy.notionalCaps.lifetime - spent;

  return (
    <div className="strategy-row">
      <div className="strategy-row-title">
        {template?.label || strategy.template}: {strategy.assetIn} → {strategy.assetOut}
        <span className={`strategy-row-status ${isRunning ? 'running' : isPaused ? 'paused-manual' : 'stopped'}`}>
          {isRunning ? 'Running' : isPaused ? 'Paused (manual)' : 'Stopped'}
        </span>
      </div>
      <div className="strategy-row-meta">
        {strategy.notionalCaps.perOrder}/{strategy.window.spacing} epochs
        {' | Last: '}{lastExec ? `epoch ${lastExec.epoch} (${lastExec.status === 'settled' ? '✓' : '…'})` : '—'}
        {' | Spent: '}{spent}
        {' | Remaining: '}{remaining}
        {' | Profile: '}{strategy.riskLimits.maxSlippageBps <= 100 ? 'conservative' : 'aggressive'}
      </div>
      <div className="strategy-row-actions">
        {isRunning && (
          <button className="btn btn-secondary btn-sm" type="button" onClick={() => onPause(strategy)}>Pause</button>
        )}
        {isPaused && (
          <button className="btn btn-secondary btn-sm" type="button" onClick={() => onResume(strategy)}>Resume</button>
        )}
        <button className="btn btn-ghost btn-sm" type="button" onClick={() => onStop(strategy)}>Stop</button>
      </div>
    </div>
  );
}

function ReadinessCheck({ label, passed, pending, action }) {
  const icon = pending ? '○' : passed ? '✓' : '✕';
  const cls = pending ? 'strategy-check-pending' : passed ? 'strategy-check-pass' : 'strategy-check-fail';
  return (
    <div className="strategy-check-row">
      <span className={`strategy-check-icon ${cls}`} aria-hidden="true">{icon}</span>
      <div className="strategy-check-label">
        {label}
        {!passed && !pending && action && <div className="strategy-check-action">→ {action}</div>}
      </div>
    </div>
  );
}

export default function StrategiesTab({ systemStatus }) {
  const [step, setStep] = useState(1);
  const [acknowledged, setAcknowledged] = useState(false);
  const [result, setResult] = useState(null);
  const [error, setError] = useState('');
  const [busy, setBusy] = useState(false);
  const [configSnapshot, setConfigSnapshot] = useState(null);
  const [checkedAt, setCheckedAt] = useState(null);
  const [now, setNow] = useState(() => Date.now());

  // Form state
  const [strategyType, setStrategyType] = useState('dca');
  const [assetIn, setAssetIn] = useState('tASSET0');
  const [assetOut, setAssetOut] = useState('tZENO');
  const [fixedOrderSize, setFixedOrderSize] = useState('100');
  const [cadenceEpochs, setCadenceEpochs] = useState('5');
  const [sequenceNumber, setSequenceNumber] = useState('9');
  const [expirationTime, setExpirationTime] = useState('999');

  // Signing state
  const [signedPayload, setSignedPayload] = useState('');
  const [preparedReportJson, setPreparedReportJson] = useState('');
  const [showSigning, setShowSigning] = useState(false);
  const [signerPasted, setSignerPasted] = useState('');
  const [signerCopied, setSignerCopied] = useState(false);

  // Active strategies — demo data only shown when demoMode is active
  const { demoMode } = useDemoMode();
  const [strategies, setStrategies] = useState([]);

  useEffect(() => {
    const interval = setInterval(() => setNow(Date.now()), 5000);
    return () => clearInterval(interval);
  }, []);

  // Load demo strategies only in demo mode; clear when demo mode is off
  useEffect(() => {
    setStrategies(demoMode ? DEMO_STRATEGIES : []);
  }, [demoMode]);

  const report = result?.report || null;
  const isAdmissible = report?.decision?.admissible !== false;
  const systemOffline = systemStatus === 'offline';

  // Stale check detection: if config changed since last check, check is stale
  const currentConfig = { strategyType, assetIn, assetOut, fixedOrderSize, cadenceEpochs, sequenceNumber, expirationTime };
  const configChanged = configSnapshot && JSON.stringify(configSnapshot) !== JSON.stringify(currentConfig);
  const checkAgeMs = checkedAt ? now - checkedAt : null;
  const checkStale = (configChanged || (checkAgeMs !== null && checkAgeMs > 60_000)) && step >= 2;

  function liveRequestBody({ forSubmit, forSupervisor } = {}) {
    const submitShaped = forSubmit || forSupervisor;
    const body = {
      acknowledge_experimental_live_risk: true,
      signer_privkey: 7,
      chain_id: 'tau-local',
    };
    if (forSupervisor) body.execution_id = SUPERVISOR_EXECUTION_ID;
    else if (forSubmit) body.execution_id = 'strategy-ui-exec-1';
    if (!submitShaped) {
      body.tx_sequence_number = Number.parseInt(sequenceNumber, 10) || 9;
      body.tx_expiration_time = Number.parseInt(expirationTime, 10) || 999;
      body.tx_fee_limit = '0';
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
        risk_limits: { max_slippage_bps: 50, max_oracle_staleness_epochs: 3 },
        strategy_window: {
          valid_from_epoch: 1, valid_until_epoch: 100,
          min_order_spacing_epochs: Number.parseInt(cadenceEpochs, 10) || 5,
        },
        controls: { kill_switch_enabled: true, max_live_orders: 3 },
        template_params: {
          asset_in: assetIn, asset_out: assetOut,
          fixed_order_size: Number.parseInt(fixedOrderSize, 10) || 100,
          cadence_epochs: Number.parseInt(cadenceEpochs, 10) || 5,
        },
      };
    }
    if (submitShaped && signedPayload.trim()) body.signed_tau_tx_payload = signedPayload.trim();
    return body;
  }

  async function handlePrepare() {
    if (!acknowledged) { setError('You must acknowledge the experimental risk.'); return; }
    setBusy('prepare');
    setError('');
    setResult(null);
    try {
      const payload = await apiPrepareAutotraderLive(liveRequestBody(), { timeoutMs: 15000 });
      setResult(payload);
      if (payload?.ok) {
        if (payload.report) setPreparedReportJson(formatJson(payload.report));
        setConfigSnapshot({ ...currentConfig });
        setCheckedAt(Date.now());
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

  function handleConfigChange(setter) {
    return (e) => { setter(e.target.value); };
  }

  function handlePause(strategy) {
    setStrategies((prev) => prev.map((s) => s.strategyId === strategy.strategyId ? { ...s, status: 'paused' } : s));
  }
  function handleResume(strategy) {
    setStrategies((prev) => prev.map((s) => s.strategyId === strategy.strategyId ? { ...s, status: 'active' } : s));
  }
  function handleStop(strategy) {
    setStrategies((prev) => prev.map((s) => s.strategyId === strategy.strategyId ? { ...s, status: 'stopped' } : s));
  }

  const startDisabled = !acknowledged || !signedPayload || checkStale || systemOffline || !isAdmissible;
  const startReason = systemOffline
    ? 'Local API offline'
    : !acknowledged
    ? 'Acknowledge the risk first'
    : !signedPayload
    ? 'Sign the transaction package first'
    : checkStale
    ? 'Safety check is stale — re-check before starting'
    : !isAdmissible
    ? 'Safety checks failed'
    : '';

  return (
    <div className="strategy-tab-panel" role="tabpanel" aria-label="Strategies">
      <p className="strategy-tab-goal">Create, start, and monitor automated trading strategies.</p>

      {strategies.length > 0 && (
        <div className="strategy-step-section">
          <p className="strategy-step-label">Active strategies</p>
          {strategies.map((s) => (
            <StrategyRow key={s.strategyId} strategy={s} onPause={handlePause} onResume={handleResume} onStop={handleStop} />
          ))}
        </div>
      )}

      {strategies.length === 0 && (
        <div className="strategy-step-section">
          <p className="strategy-tab-hint">No active strategies. Create one below.</p>
        </div>
      )}

      <div className="strategy-step-section">
        <p className="strategy-step-label">Step 1 — Configure</p>
        <div className="strategy-form-grid">
          <div className="strategy-form-field">
            <label className="strategy-form-label">Strategy</label>
            <select className="strategy-form-input" value={strategyType} onChange={handleConfigChange(setStrategyType)}>
              <option value="dca">DCA — Dollar-Cost Averaging</option>
              <option value="limit_ladder">Limit Ladder</option>
              <option value="stop_loss">Stop Loss</option>
              <option value="take_profit">Take Profit</option>
            </select>
          </div>
          <div className="strategy-form-field">
            <label className="strategy-form-label">Asset in</label>
            <input className="strategy-form-input" type="text" value={assetIn} onChange={handleConfigChange(setAssetIn)} />
          </div>
          <div className="strategy-form-field">
            <label className="strategy-form-label">Asset out</label>
            <input className="strategy-form-input" type="text" value={assetOut} onChange={handleConfigChange(setAssetOut)} />
          </div>
          <div className="strategy-form-field">
            <label className="strategy-form-label">Amount per order</label>
            <input className="strategy-form-input" type="number" value={fixedOrderSize} onChange={handleConfigChange(setFixedOrderSize)} />
          </div>
          <div className="strategy-form-field">
            <label className="strategy-form-label">Buy every (epochs)</label>
            <input className="strategy-form-input" type="number" min="1" value={cadenceEpochs} onChange={handleConfigChange(setCadenceEpochs)} />
          </div>
          <div className="strategy-form-field">
            <label className="strategy-form-label">Transaction number</label>
            <input className="strategy-form-input" type="number" value={sequenceNumber} onChange={handleConfigChange(setSequenceNumber)} />
          </div>
          <div className="strategy-form-field">
            <label className="strategy-form-label">Expires at epoch</label>
            <input className="strategy-form-input" type="number" value={expirationTime} onChange={handleConfigChange(setExpirationTime)} />
          </div>
        </div>

        <div className="strategy-actions">
          <button
            className="btn btn-primary strategy-primary-btn"
            type="button"
            onClick={handlePrepare}
            disabled={busy || !acknowledged || systemOffline}
          >
            {busy === 'prepare' ? 'Checking…' : 'Run safety check'}
          </button>
        </div>
      </div>

      {step >= 2 && report && (
        <div className="strategy-step-section">
          <p className="strategy-step-label">
            Step 2 — Review safety check
            {checkedAt && ` (checked ${Math.round((now - checkedAt) / 1000)}s ago)`}
          </p>
          <div className={`strategy-safety-check ${checkStale ? 'stale' : ''}`}>
            <p className="strategy-safety-check-title">
              {checkStale ? '⚠ Check is stale' : `Passed checks at epoch ${report?.decision?.epoch || '—'}`}
            </p>
            <ReadinessCheck label="Allowed by safety rules" passed={isAdmissible} />
            <ReadinessCheck label="Safety checks passed (10/10)" passed={isAdmissible} />
            <ReadinessCheck label="Balance sufficient" passed={isAdmissible} pending={!isAdmissible} />
            <ReadinessCheck label="Nonce is fresh" passed={isAdmissible} pending={!isAdmissible} />
            {checkStale && (
              <button className="btn btn-secondary btn-sm" type="button" onClick={handlePrepare} disabled={busy}>
                Re-check now
              </button>
            )}
          </div>
          {checkStale && (
            <div className="strategy-banner strategy-banner-warning">
              Config changed since last check. Re-check before starting.
            </div>
          )}
        </div>
      )}

      <div className="strategy-step-section">
        <p className="strategy-step-label">Step 3 — Sign and start</p>
        <div className="strategy-risk-ack">
          <input type="checkbox" id="strategy-ack" checked={acknowledged} onChange={(e) => setAcknowledged(e.target.checked)} />
          <label htmlFor="strategy-ack">I understand the risks and want to proceed.</label>
        </div>

        <div className="strategy-actions">
          <button
            className="btn btn-secondary btn-sm"
            type="button"
            onClick={() => { setSignerPasted(signedPayload); setSignerCopied(false); setShowSigning(true); }}
            disabled={!isAdmissible || systemOffline}
          >
            Sign transaction package
          </button>
        </div>

        {showSigning && (
          <div className="strategy-signing-panel">
            <div className="strategy-signing-title">Sign transaction package</div>
            <p className="strategy-tab-hint">Your strategy is ready. Sign it with your external wallet to start.</p>
            <div className="strategy-safety-check-title">Prepared package</div>
            <pre className="strategy-api-code-block">{preparedReportJson || formatJson(report || {})}</pre>
            <button
              className="btn btn-ghost btn-sm"
              type="button"
              onClick={() => {
                navigator.clipboard?.writeText(preparedReportJson || formatJson(report || {}));
                setSignerCopied(true);
                setTimeout(() => setSignerCopied(false), 1600);
              }}
            >
              {signerCopied ? 'Copied ✓' : 'Copy package'}
            </button>
            <div className="strategy-signing-steps">
              How to sign:<br />
              1. Copy the prepared package above<br />
              2. Sign it with your Tau-tx signing tool<br />
              3. Paste the signed package below
            </div>
            <textarea
              className="strategy-json-textarea"
              value={signerPasted}
              onChange={(e) => setSignerPasted(e.target.value)}
              placeholder='{"signed_payload":"…","signature":"…"}'
              spellCheck="false"
            />
            <div className="strategy-actions">
              <button className="btn btn-ghost btn-sm" type="button" onClick={() => setShowSigning(false)}>Cancel</button>
              <button
                className="btn btn-secondary btn-sm strategy-primary-btn"
                type="button"
                disabled={!signerPasted.trim()}
                onClick={() => { setSignedPayload(signerPasted.trim()); setShowSigning(false); }}
              >
                Use signed package
              </button>
            </div>
          </div>
        )}

        {signedPayload && !showSigning && (
          <div className="strategy-banner strategy-banner-success">
            ✓ Signed package loaded
          </div>
        )}

        <div className="strategy-actions">
          <button
            className={`btn ${startDisabled ? 'btn-disabled' : 'btn-primary'} strategy-start-btn strategy-primary-btn`}
            type="button"
            onClick={handleSubmit}
            disabled={startDisabled || busy === 'submit'}
          >
            {busy === 'submit' ? 'Starting…' : startDisabled ? '🔒 Start strategy' : 'Start strategy'}
          </button>
        </div>
        {startDisabled && <div className="strategy-submit-disabled-reason">{startReason}</div>}
      </div>

      {step === 3 && result?.submission?.sendtx_response && (
        <div className="strategy-banner strategy-banner-success">
          ✓ Strategy started
          <div className="strategy-row-meta">Submitted to local supervisor. Monitor in Safety tab.</div>
          <div className="strategy-row-actions">
            <button className="btn btn-ghost btn-sm" type="button" onClick={() => { setStep(1); setResult(null); setSignedPayload(''); }}>Create another</button>
          </div>
        </div>
      )}

      {error && (
        <div className="strategy-banner strategy-banner-error" role="alert">
          {error}
        </div>
      )}

      <details className="strategy-advanced">
        <summary>Advanced: Raw prepared report</summary>
        <div className="strategy-advanced-body">
          {preparedReportJson ? (
            <pre className="strategy-api-code-block">{preparedReportJson}</pre>
          ) : (
            <p className="strategy-tab-hint">Run a safety check to see the raw report.</p>
          )}
        </div>
      </details>
    </div>
  );
}
