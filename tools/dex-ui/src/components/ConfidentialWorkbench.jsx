import { useEffect, useState } from 'react';
import './ConfidentialWorkbench.css';
import { CONFIDENTIAL_SURFACE } from '../lib/confidentialData';
import { apiGetConfidentialStatus } from '../lib/api';
import { useDemoMode } from '../lib/DemoModeContext.jsx';

function ConfidentialWorkbench() {
  const { demoMode } = useDemoMode();
  const [liveStatus, setLiveStatus] = useState(null);
  const [liveError, setLiveError] = useState('');

  useEffect(() => {
    if (demoMode) {
      setLiveStatus(null);
      setLiveError('');
      return undefined;
    }
    let active = true;
    (async () => {
      try {
        const payload = await apiGetConfidentialStatus({ timeoutMs: 5000 });
        if (!active) return;
        setLiveStatus(payload?.status || null);
        setLiveError('');
      } catch (err) {
        if (!active) return;
        setLiveStatus(null);
        setLiveError(err?.message || 'status_unavailable');
      }
    })();
    return () => {
      active = false;
    };
  }, [demoMode]);

  const stageLabel = String(liveStatus?.stage || CONFIDENTIAL_SURFACE.summary.stage || 'beta').toUpperCase();
  const subtitle = String(liveStatus?.user_summary || CONFIDENTIAL_SURFACE.summary.subtitle);
  const operatorContact = String(liveStatus?.operator_contact || 'not_configured');
  const measurementCount = Number.isFinite(liveStatus?.approved_measurements_count)
    ? liveStatus.approved_measurements_count
    : 0;
  const betaReady = liveStatus?.beta_ready === true;
  const readinessGaps = Array.isArray(liveStatus?.readiness_gaps) ? liveStatus.readiness_gaps : [];

  return (
    <section className="confidential-workbench">
      <div className="confidential-hero panel panel-glass animate-fade-in">
        <div>
          <p className="confidential-kicker">TEE-first product surface</p>
          <h1>{CONFIDENTIAL_SURFACE.summary.title}</h1>
          <p className="confidential-subtitle">{subtitle}</p>
        </div>
        <div className="confidential-hero-meta">
          <span className="confidential-chip">Verified {CONFIDENTIAL_SURFACE.summary.verifiedAt}</span>
          <span className="confidential-chip confidential-chip-accent">{stageLabel}</span>
        </div>
      </div>

      <div className="confidential-grid">
        <div className="panel confidential-card">
          <div className="confidential-card-header">
            <h2>Beta Status</h2>
            <span className="confidential-section-badge">Operator posture</span>
          </div>
          <div className="confidential-check-list">
            <article className="confidential-check-row">
              <div>
                <div className="confidential-check-title">Main-Branch Readiness</div>
                <p className="confidential-check-detail">
                  {betaReady
                    ? 'Ready for main as an opt-in beta feature, not as the default swap path.'
                    : 'Not yet ready for main as a beta feature.'}
                </p>
              </div>
              <div className="confidential-check-meta">
                <span className={`confidential-status ${betaReady ? 'confidential-status-verified' : ''}`}>
                  {betaReady ? 'beta-ready' : 'incomplete'}
                </span>
              </div>
            </article>
            <article className="confidential-check-row">
              <div>
                <div className="confidential-check-title">Approved Measurements</div>
                <p className="confidential-check-detail">
                  {measurementCount > 0
                    ? `${measurementCount} measurement(s) are configured for live TEE providers.`
                    : 'No live TEE measurement allowlist is configured in this environment.'}
                </p>
              </div>
              <div className="confidential-check-meta">
                <span className="confidential-proof">{measurementCount}</span>
              </div>
            </article>
            <article className="confidential-check-row">
              <div>
                <div className="confidential-check-title">Operator Contact</div>
                <p className="confidential-check-detail">
                  {demoMode
                    ? 'Demo mode is on, so live operator status is hidden.'
                    : liveError
                      ? `Live status unavailable: ${liveError}`
                      : `Current support contact: ${operatorContact}`}
                </p>
              </div>
              <div className="confidential-check-meta">
                <span className="confidential-proof">/api/confidential/status</span>
              </div>
            </article>
          </div>
          {readinessGaps.length > 0 ? (
            <div className="confidential-card-footer">
              <div className="confidential-check-title">What still needs to be configured</div>
              <ul className="confidential-bullet-list">
                {readinessGaps.map((item) => (
                  <li key={item}>{item}</li>
                ))}
              </ul>
            </div>
          ) : null}
        </div>

        <div className="panel confidential-card">
          <div className="confidential-card-header">
            <h2>Formal Surface</h2>
            <span className="confidential-section-badge">Proof-backed</span>
          </div>
          <div className="confidential-check-list">
            {CONFIDENTIAL_SURFACE.checks.map((check) => (
              <article key={check.id} className="confidential-check-row">
                <div>
                  <div className="confidential-check-title">{check.label}</div>
                  <p className="confidential-check-detail">{check.detail}</p>
                </div>
                <div className="confidential-check-meta">
                  <span className={`confidential-status confidential-status-${check.status}`}>{check.status}</span>
                  <span className="confidential-proof">{check.proof}</span>
                </div>
              </article>
            ))}
          </div>
        </div>

        <div className="panel confidential-card">
          <div className="confidential-card-header">
            <h2>Sealed-Bid Flow</h2>
            <span className="confidential-section-badge">UX-critical</span>
          </div>
          <div className="confidential-phase-list">
            {CONFIDENTIAL_SURFACE.phases.map((phase, idx) => (
              <div key={phase.id} className="confidential-phase-row">
                <div className="confidential-phase-index">{idx + 1}</div>
                <div>
                  <div className="confidential-phase-title">{phase.title}</div>
                  <p className="confidential-phase-detail">{phase.detail}</p>
                </div>
              </div>
            ))}
          </div>
        </div>
      </div>

      <div className="confidential-grid">
        <div className="panel confidential-card">
          <div className="confidential-card-header">
            <h2>Use Cases</h2>
            <span className="confidential-section-badge">Where it fits</span>
          </div>
          <ul className="confidential-bullet-list">
            {CONFIDENTIAL_SURFACE.useCases.map((item) => (
              <li key={item}>{item}</li>
            ))}
          </ul>
        </div>

        <div className="panel confidential-card">
          <div className="confidential-card-header">
            <h2>User Benefits</h2>
            <span className="confidential-section-badge">Why it matters</span>
          </div>
          <ul className="confidential-bullet-list">
            {CONFIDENTIAL_SURFACE.userBenefits.map((item) => (
              <li key={item}>{item}</li>
            ))}
          </ul>
        </div>
      </div>

      <div className="confidential-grid">
        <div className="panel confidential-card">
          <div className="confidential-card-header">
            <h2>Not the Default For</h2>
            <span className="confidential-section-badge">When to skip it</span>
          </div>
          <ul className="confidential-bullet-list">
            {CONFIDENTIAL_SURFACE.notDefaultFor.map((item) => (
              <li key={item}>{item}</li>
            ))}
          </ul>
        </div>

        <div className="panel confidential-card">
          <div className="confidential-card-header">
            <h2>Disaster Catalog</h2>
            <span className="confidential-section-badge">Terminal hazards</span>
          </div>
          <div className="confidential-disaster-table">
            <div className="confidential-disaster-head">
              <span>State</span>
              <span>Kernel</span>
              <span>Discharge</span>
            </div>
            {CONFIDENTIAL_SURFACE.disasterCatalog.map((row) => (
              <div key={row.disasterId} className="confidential-disaster-row">
                <span className="confidential-mono">{row.disasterId}</span>
                <span>{row.model}</span>
                <span className="confidential-discharge">
                  {row.dischargeAction}
                  <span className="confidential-disaster-status">{row.status}</span>
                </span>
              </div>
            ))}
          </div>
        </div>
      </div>
    </section>
  );
}

export default ConfidentialWorkbench;
