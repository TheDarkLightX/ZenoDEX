import { useEffect, useRef, useState } from 'react';
import './ConfidentialWorkbench.css';
import { CONFIDENTIAL_SURFACE } from '../lib/confidentialData';
import {
  apiAdmitConfidentialAttestation,
  apiExecuteConfidentialAttestation,
  apiGetConfidentialStatus,
} from '../lib/api';
import { useDemoMode } from '../lib/DemoModeContext.jsx';

const SMOKE_NITRO_PCR0 = 'a'.repeat(96);
const SMOKE_NITRO_PCR8 = 'b'.repeat(96);
const SMOKE_POLICY_DIGEST = `0x${'d'.repeat(64)}`;

function confidentialAttestationSmokeEnabled() {
  if (typeof window === 'undefined') return false;
  return new URLSearchParams(window.location.search).get('zenodexUiSmokeConfidentialVerify') === '1';
}

function buildAttestationRequest({ requestId = 'req-ui' } = {}) {
  return {
    attestation_payload: {
      provider: 'nitro',
      nonce: 'ui-smoke',
      summary: {
        pcrs: {
          0: SMOKE_NITRO_PCR0,
          8: SMOKE_NITRO_PCR8,
        },
      },
    },
    extension_id: 'route-premium-v1',
    provider_id: 'provider-1',
    request_id: requestId,
    policy_version: 'tee-policy-v1',
    do_execute: 1,
    policy_ok: 1,
    nonce_unused: 1,
    output_bound_ok: 1,
    current_epoch: 10,
    max_attestation_age: 2,
    fee_charged: 7,
    receipt_fee: 7,
    credit_before: 40,
    credit_after: 33,
    provider_balance_before: 9,
    provider_balance_after: 16,
    expected_policy_digest: SMOKE_POLICY_DIGEST,
  };
}

function buildRuntimeExecutionRequest({ requestId = 'req-ui', executionId = 'exec-ui' } = {}) {
  return {
    ...buildAttestationRequest({ requestId }),
    execution_id: executionId,
    execution_kind: 'private_route_quote',
    result_code: 'bounded_route_selected',
  };
}

function ConfidentialWorkbench() {
  const { demoMode } = useDemoMode();
  const smokeRan = useRef(false);
  const [liveStatus, setLiveStatus] = useState(null);
  const [liveError, setLiveError] = useState('');
  const [attestationStatus, setAttestationStatus] = useState('');
  const [attestationResult, setAttestationResult] = useState(null);
  const [attestationError, setAttestationError] = useState('');
  const [runtimeStatus, setRuntimeStatus] = useState('');
  const [runtimeResult, setRuntimeResult] = useState(null);
  const [runtimeError, setRuntimeError] = useState('');

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

  async function runAttestationVerify() {
    setAttestationStatus('attestation admission running');
    setAttestationError('');
    setAttestationResult(null);
    try {
      const requestId = confidentialAttestationSmokeEnabled() ? 'req-ui' : `req-ui-${Date.now()}`;
      const payload = await apiAdmitConfidentialAttestation(
        buildAttestationRequest({ requestId }),
        { timeoutMs: 10000 },
      );
      setAttestationResult(payload || null);
      setAttestationStatus(payload?.ok ? 'attestation accepted' : 'attestation rejected');
    } catch (err) {
      setAttestationResult(null);
      setAttestationStatus('attestation rejected');
      setAttestationError(err?.message || 'verification_failed');
    }
  }

  async function runRuntimeExecute() {
    setRuntimeStatus('runtime execution running');
    setRuntimeError('');
    setRuntimeResult(null);
    try {
      const requestId = confidentialAttestationSmokeEnabled() ? 'req-ui-runtime' : `req-ui-runtime-${Date.now()}`;
      const executionId = confidentialAttestationSmokeEnabled() ? 'exec-ui' : `exec-ui-${Date.now()}`;
      const payload = await apiExecuteConfidentialAttestation(
        buildRuntimeExecutionRequest({ requestId, executionId }),
        { timeoutMs: 10000 },
      );
      setAttestationResult(payload || null);
      setAttestationStatus(payload?.ok ? 'attestation accepted' : 'attestation rejected');
      setAttestationError('');
      setRuntimeResult(payload?.runtime_receipt || null);
      setRuntimeStatus(payload?.ok ? 'runtime receipt ready' : 'runtime receipt rejected');
    } catch (err) {
      setRuntimeResult(null);
      setRuntimeStatus('runtime receipt rejected');
      setRuntimeError(err?.message || 'runtime_execution_failed');
    }
  }

  useEffect(() => {
    if (demoMode || !confidentialAttestationSmokeEnabled() || smokeRan.current) {
      return;
    }
    smokeRan.current = true;
    void runRuntimeExecute();
  }, [demoMode]);

  const stageLabel = String(liveStatus?.stage || CONFIDENTIAL_SURFACE.summary.stage || 'beta').toUpperCase();
  const subtitle = String(liveStatus?.user_summary || CONFIDENTIAL_SURFACE.summary.subtitle);
  const operatorContact = String(liveStatus?.operator_contact || 'not_configured');
  const measurementCount = Number.isFinite(liveStatus?.approved_measurements_count)
    ? liveStatus.approved_measurements_count
    : 0;
  const betaReady = liveStatus?.beta_ready === true;
  const readinessGaps = Array.isArray(liveStatus?.readiness_gaps) ? liveStatus.readiness_gaps : [];
  const claimScope = String(liveStatus?.claim_scope || CONFIDENTIAL_SURFACE.summary.claimScope);
  const nonClaims = Array.isArray(liveStatus?.non_claims) && liveStatus.non_claims.length > 0
    ? liveStatus.non_claims
    : [CONFIDENTIAL_SURFACE.summary.nonClaim];
  const statusHash = String(liveStatus?.status_hash || '');
  const allowlistHash = String(liveStatus?.approved_measurements_hash || '');
  const verifierBindingHash = String(
    runtimeResult?.body?.external_verifier_binding_hash
    || attestationResult?.external_verifier_binding_hash
    || liveStatus?.external_verifier_binding_hash
    || ''
  );
  const receiptHash = String(attestationResult?.receipt_hash || '');
  const measurement = String(attestationResult?.measurement || attestationResult?.measurement_provider || '');
  const executionAdmitted = attestationResult?.execution_admitted === true;
  const runtimeReceiptHash = String(runtimeResult?.receipt_hash || '');
  const runtimeBody = runtimeResult?.body || {};
  const runtimeEffectDigest = String(runtimeBody?.public_effect_digest || '');
  const runtimeRedacted = runtimeBody?.result_redacted === true;

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
            <article className="confidential-check-row">
              <div>
                <div className="confidential-check-title">Attestation Receipt</div>
                <p className="confidential-check-detail">
                  {attestationStatus || 'No live attestation receipt has been accepted in this session.'}
                </p>
              </div>
              <div className="confidential-check-meta">
                <button
                  className="confidential-action-button"
                  type="button"
                  onClick={runAttestationVerify}
                  disabled={demoMode || attestationStatus === 'attestation admission running'}
                >
                  Admit Attestation
                </button>
                <span className="confidential-proof">/api/confidential/attestation/admit</span>
              </div>
            </article>
            <article className="confidential-check-row">
              <div>
                <div className="confidential-check-title">Runtime Receipt</div>
                <p className="confidential-check-detail">
                  {runtimeStatus || 'No bounded confidential runtime receipt has been produced in this session.'}
                </p>
              </div>
              <div className="confidential-check-meta">
                <button
                  className="confidential-action-button"
                  type="button"
                  onClick={runRuntimeExecute}
                  disabled={demoMode || runtimeStatus === 'runtime execution running'}
                >
                  Execute Runtime
                </button>
                <span className="confidential-proof">/api/confidential/attestation/execute</span>
              </div>
            </article>
          </div>
          {attestationResult || attestationError || runtimeResult || runtimeError ? (
            <div className="confidential-attestation-result">
              {attestationResult ? (
                <>
                  <span>receipt {receiptHash || 'missing'}</span>
                  <span>measurement {measurement.startsWith('nitro:') ? 'nitro' : measurement || 'unknown'}</span>
                  <span>{executionAdmitted ? 'execution admitted' : 'execution withheld'}</span>
                  <span>{attestationResult?.request_consumed ? 'request consumed' : 'request unconsumed'}</span>
                </>
              ) : (
                <span>attestation error {attestationError}</span>
              )}
              {runtimeResult ? (
                <>
                  <span>runtime receipt {runtimeReceiptHash || 'missing'}</span>
                  <span>{runtimeRedacted ? 'result redacted' : 'result exposed'}</span>
                  <span>effect digest {runtimeEffectDigest || 'missing'}</span>
                  <span>status hash {statusHash || runtimeBody?.operator_status_hash || 'missing'}</span>
                  <span>allowlist hash {allowlistHash || runtimeBody?.approved_measurements_hash || 'missing'}</span>
                  <span>verifier binding {verifierBindingHash || 'missing'}</span>
                </>
              ) : runtimeError ? (
                <span>runtime error {runtimeError}</span>
              ) : null}
            </div>
          ) : null}
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
            <h2>Assurance Surface</h2>
            <span className="confidential-section-badge">Bounded evidence</span>
          </div>
          <div className="confidential-claim-scope">
            <div>
              <div className="confidential-check-title">Confidentiality Claim Scope</div>
              <p className="confidential-check-detail">{claimScope}</p>
            </div>
            <ul className="confidential-bullet-list">
              {nonClaims.map((item) => (
                <li key={item}>{item}</li>
              ))}
            </ul>
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
