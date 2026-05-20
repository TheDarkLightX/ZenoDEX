import { useState } from 'react';
import './StrategyWorkbench.css';
import {
  STRATEGY_TEMPLATES,
  TAU_POLICY_GUARDS,
  DEMO_STRATEGIES,
  FORMAL_PROOFS,
} from '../lib/strategyData';

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

function StrategyWorkbench() {
  return (
    <section className="strat-workbench">
      {/* Hero */}
      <div className="strat-hero panel panel-glass animate-fade-in">
        <div>
          <p className="strat-kicker">Policy-constrained automation</p>
          <h1>AutoTrader Strategies</h1>
          <p className="strat-subtitle">
            Configure automated trading strategies with Tau-verified policy guards.
            Every decision is bound by a 10-guard pipeline before intent emission.
          </p>
        </div>
        <div className="strat-hero-meta">
          <span className="strat-chip">{DEMO_STRATEGIES.length} strategies</span>
          <span className="strat-chip strat-chip-accent">{TAU_POLICY_GUARDS.length} guards</span>
        </div>
      </div>

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
        <span className="strat-section-badge">Demo data</span>
      </div>
      {DEMO_STRATEGIES.map((strategy) => (
        <StrategyCard key={strategy.strategyId} strategy={strategy} />
      ))}
    </section>
  );
}

export default StrategyWorkbench;
