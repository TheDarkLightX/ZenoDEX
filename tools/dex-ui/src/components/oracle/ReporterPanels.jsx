// Copyright DarkLightX/Dana Edwards
// Oracle reporter onboarding and reporter health panels.
import { useEffect, useRef, useState } from 'react';
import { zenoOracleApiUrl, compactId, randomSmokeHex } from '../../lib/oracleUtils.js';

function ReporterOnboardingPanel({ selectedFeed }) {
  const [status, setStatus] = useState('Ready');
  const [sourceId, setSourceId] = useState('source:manual');
  const reporterSmokeRan = useRef(false);

  // Step locking state
  // 0: Create Identity, 1: Register+Bond, 2: Submit Reports
  const [currentStepIndex, setCurrentStepIndex] = useState(0);

  // Price formatting state
  const [displayPrice, setDisplayPrice] = useState('1.50');

  // Calculate e8 equivalent automatically
  const priceE8 = Math.floor(parseFloat(displayPrice || 0) * 100000000);

  const steps = [
    { id: 'identity', label: 'Create account', status: currentStepIndex > 0 ? 'completed' : 'available' },
    { id: 'register_bond', label: 'Register & deposit', status: currentStepIndex > 1 ? 'completed' : (currentStepIndex === 1 ? 'available' : 'locked') },
    { id: 'submit', label: 'Submit price reports', status: currentStepIndex === 2 ? 'available' : 'locked' },
  ];

  async function post(path, payload) {
    const response = await fetch(zenoOracleApiUrl(path), {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(payload),
    });
    const body = await response.json();
    if (!response.ok || body.ok === false) {
      throw new Error(body.error || `HTTP ${response.status}`);
    }
    return body;
  }

  async function createIdentity() {
    setStatus('Creating identity...');
    try {
      const payload = await post('/api/oracle/identity/create', { force: true });
      setStatus(`Identity ${compactId(payload.reporter_id)} created`);
      setCurrentStepIndex(1); // unlock next step
    } catch (error) {
      setStatus(String(error.message || error));
    }
  }

  async function registerAndBond() {
    setStatus('Registering reporter...');
    try {
      await post('/api/oracle/reporter/register', {
        query_id: selectedFeed.queryId,
        required_bond_e8: 100000000,
        force: true,
      });
      await post('/api/oracle/reporter/bond', { amount_e8: 100000000 });
      setStatus(`Bonded for ${selectedFeed.feed}`);
      setCurrentStepIndex(2); // unlock next step
    } catch (error) {
      setStatus(String(error.message || error));
    }
  }

  async function registerSourceForSelectedFeed() {
    const source = sourceId.trim();
    if (!source) {
      throw new Error('source_id_required');
    }
    await post('/api/oracle/source/register', {
      source_id: source,
      source_kind: 'manual',
      control_group_id: `${source}:control`,
      venue_id: `${source}:venue`,
      data_family_id: 'price:manual-spot',
      transport_id: `${source}:ui`,
      asset_class: 'crypto',
      query_id: selectedFeed.queryId,
      assurance_class: 'S3',
      force: true,
    });
  }

  async function submitReport() {
    setStatus('Submitting report...');
    try {
      await registerSourceForSelectedFeed();
      const payload = await post('/api/oracle/report/submit', {
        query_id: selectedFeed.queryId,
        price_e8: priceE8,
        source_observed_epoch: Math.max(1, Math.floor(Date.now() / 1000)),
        source_id: sourceId,
      });
      setStatus(`Source registered; report ${compactId(payload.report_id)} submitted successfully`);
    } catch (error) {
      setStatus(String(error.message || error));
    }
  }

  useEffect(() => {
    if (typeof window === 'undefined') {
      return;
    }
    const params = new URLSearchParams(window.location.search);
    if (params.get('zenodexUiSmokeOracleReporterOnboarding') !== '1' || reporterSmokeRan.current) {
      return;
    }
    if (!selectedFeed?.queryId || selectedFeed.queryId === 'placeholder') {
      return;
    }
    reporterSmokeRan.current = true;
    async function runSmoke() {
      const runHex = randomSmokeHex(8);
      setSourceId(`source:ui-reporter:${runHex}`);
      setStatus('Reporter onboarding smoke running...');
      await post('/api/oracle/identity/create', { force: true });
      await post('/api/oracle/reporter/register', {
        query_id: selectedFeed.queryId,
        required_bond_e8: 100000000,
        force: true,
      });
      await post('/api/oracle/reporter/bond', { amount_e8: 100000000 });
      await post('/api/oracle/source/register', {
        source_id: `source:ui-reporter:${runHex}`,
        source_kind: 'manual',
        control_group_id: `control:ui-reporter:${runHex}`,
        venue_id: `venue:ui-reporter:${runHex}`,
        data_family_id: 'price:manual-spot',
        transport_id: `ui:manual:${runHex}`,
        asset_class: 'crypto',
        query_id: selectedFeed.queryId,
        assurance_class: 'S3',
        force: true,
      });
      const payload = await post('/api/oracle/report/submit', {
        query_id: selectedFeed.queryId,
        price_e8: priceE8,
        source_observed_epoch: 12,
        source_id: `source:ui-reporter:${runHex}`,
      });
      setCurrentStepIndex(2);
      setStatus(`Reporter onboarding smoke submitted ${compactId(payload.report_id)}`);
    }
    void runSmoke().catch((error) => {
      setStatus(`Reporter onboarding smoke failed ${error?.message || 'unknown'}`);
    });
  }, [selectedFeed?.queryId, priceE8]);

  return (
    <section className="panel zor-panel animate-fade-in">
      <div className="zor-section-header">
        <div>
          <h2>Add Reporter</h2>
          <p>Complete the steps in order to start submitting oracle reports.</p>
        </div>
        <span className="zor-subtle-chip">Service</span>
      </div>

      <div className="zor-step-list" style={{ marginBottom: 'var(--space-lg)' }}>
        {steps.map((step, index) => (
          <div key={step.id} className="zor-step-row" style={{ opacity: index > currentStepIndex ? 0.5 : 1 }}>
            <span className="zor-step-index" style={{ background: index < currentStepIndex ? 'var(--accent-green)' : (index === currentStepIndex ? 'var(--accent-cyan)' : 'var(--border-primary)') }}>
              {index < currentStepIndex ? '✓' : index + 1}
            </span>
            <strong>{step.label}</strong>
            <small style={{ color: index === currentStepIndex ? 'var(--accent-cyan)' : 'inherit' }}>{step.status}</small>
          </div>
        ))}
      </div>

      <div className="zor-button-row" style={{ borderBottom: '1px solid var(--border-primary)', paddingBottom: 'var(--space-lg)', marginBottom: 'var(--space-lg)' }}>
        <button
          className="btn btn-secondary"
          type="button"
          onClick={createIdentity}
          disabled={currentStepIndex !== 0}
        >
          {currentStepIndex > 0 ? 'Identity Created ✓' : '1. Create Identity'}
        </button>
        <button
          className="btn btn-primary"
          type="button"
          onClick={registerAndBond}
          disabled={currentStepIndex !== 1}
        >
          {currentStepIndex > 1 ? 'Registered & Bonded ✓' : '2. Register + Bond'}
        </button>
      </div>

      <div className="zor-report-submit-grid" style={{ opacity: currentStepIndex === 2 ? 1 : 0.4, pointerEvents: currentStepIndex === 2 ? 'auto' : 'none' }}>
        <label>
          <span className="label">Data source name</span>
          <input
            className="input"
            value={sourceId}
            onChange={(event) => setSourceId(event.target.value)}
            disabled={currentStepIndex !== 2}
          />
        </label>
        <label>
          <span className="label">Current price</span>
          <input
            className="input"
            inputMode="decimal"
            value={displayPrice}
            onChange={(event) => setDisplayPrice(event.target.value)}
            disabled={currentStepIndex !== 2}
            placeholder="1.50"
          />
          <small style={{ display: 'block', marginTop: '4px', color: 'var(--text-muted)' }}>
            Converted to smallest unit: <span className="strat-mono">{priceE8}</span>
          </small>
        </label>
        <button
          className="btn btn-primary"
          type="button"
          onClick={submitReport}
          disabled={currentStepIndex !== 2 || priceE8 <= 0}
        >
          3. Submit Report
        </button>
      </div>

      {status !== 'Ready' && (
        <div style={{ marginTop: 'var(--space-md)', padding: 'var(--space-sm)', background: 'var(--background-subtle)', borderRadius: 'var(--radius-sm)', textAlign: 'center' }}>
          <span className="zor-action-state">{status}</span>
        </div>
      )}
    </section>
  );
}

function ReporterPanel({ reporters }) {
  return (
    <section className="panel zor-panel">
      <div className="zor-section-header">
        <div>
          <h2>Reporter Health</h2>
          <p>Bond, liveness, and control-group state for active reporters.</p>
        </div>
        <span className="zor-subtle-chip">{reporters.length} sampled</span>
      </div>
      <div className="zor-reporter-table">
        <div className="zor-reporter-head">
          <span>Reporter</span>
          <span>Bond</span>
          <span>Accepted</span>
          <span>Missed</span>
          <span>Status</span>
        </div>
        {reporters.map((reporter) => (
          <div key={reporter.id} className="zor-reporter-row">
            <span>
              <strong>{reporter.id}</strong>
              <small>{reporter.controlGroup}</small>
            </span>
            <span>{reporter.bond ?? <span className="zor-muted">no bond</span>}</span>
            <span>{reporter.accepted}</span>
            <span>{reporter.missed}</span>
            <span className={`zor-status zor-reporter-${reporter.status}`}>{reporter.status}</span>
          </div>
        ))}
      </div>
    </section>
  );
}

export {
  ReporterOnboardingPanel,
  ReporterPanel,
};
