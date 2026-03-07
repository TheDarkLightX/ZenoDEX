import './ConfidentialWorkbench.css';
import { CONFIDENTIAL_SURFACE } from '../lib/confidentialData';

function ConfidentialWorkbench() {
  return (
    <section className="confidential-workbench">
      <div className="confidential-hero panel panel-glass animate-fade-in">
        <div>
          <p className="confidential-kicker">TEE-first product surface</p>
          <h1>{CONFIDENTIAL_SURFACE.summary.title}</h1>
          <p className="confidential-subtitle">{CONFIDENTIAL_SURFACE.summary.subtitle}</p>
        </div>
        <div className="confidential-hero-meta">
          <span className="confidential-chip">Verified {CONFIDENTIAL_SURFACE.summary.verifiedAt}</span>
          <span className="confidential-chip confidential-chip-accent">Experimental Lane</span>
        </div>
      </div>

      <div className="confidential-grid">
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
