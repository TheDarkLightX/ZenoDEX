import { useEffect, useRef, useState } from 'react';
import './ConfidentialWorkbench.css';
import { CONFIDENTIAL_SURFACE } from '../lib/confidentialData';
import {
  apiAdmitConfidentialAttestation,
  apiCommitConfidentialSealedBid,
  apiExecuteConfidentialAttestation,
  apiGetConfidentialStatus,
  apiGetConfidentialSealedBidStatus,
  apiOpenRevealConfidentialSealedBid,
  apiResetConfidentialSealedBid,
  apiRevealConfidentialSealedBid,
  apiSettleConfidentialSealedBid,
  getRuntimeConfig,
} from '../lib/api';
import { useDemoMode } from '../lib/DemoModeContext.jsx';

const DEFAULT_SMOKE_NITRO_PCR0 = '0123456789abcdef'.repeat(6);
const DEFAULT_SMOKE_NITRO_PCR8 = 'fedcba9876543210'.repeat(6);
const DEFAULT_SMOKE_POLICY_DIGEST = `0x${'d'.repeat(64)}`;

function isHex(value, length) {
  return typeof value === 'string' && new RegExp(`^[0-9a-fA-F]{${length}}$`).test(value.trim());
}

function confidentialSmokeFixture() {
  const raw = getRuntimeConfig()?.localTestnetConfidentialFixture || {};
  const nitroPcr0 = isHex(raw.nitroPcr0, 96)
    ? raw.nitroPcr0.trim().toLowerCase()
    : DEFAULT_SMOKE_NITRO_PCR0;
  const nitroPcr8 = isHex(raw.nitroPcr8, 96)
    ? raw.nitroPcr8.trim().toLowerCase()
    : DEFAULT_SMOKE_NITRO_PCR8;
  const rawPolicy = typeof raw.policyDigest === 'string' ? raw.policyDigest.trim().toLowerCase() : '';
  const policyDigest = /^0x[0-9a-f]{64}$/.test(rawPolicy) ? rawPolicy : DEFAULT_SMOKE_POLICY_DIGEST;
  return { nitroPcr0, nitroPcr8, policyDigest };
}

function randomSmokeHex(bytes = 8) {
  const buffer = new Uint8Array(bytes);
  if (typeof crypto !== 'undefined' && crypto.getRandomValues) {
    crypto.getRandomValues(buffer);
  } else {
    for (let i = 0; i < buffer.length; i += 1) {
      buffer[i] = Math.floor(Math.random() * 256);
    }
  }
  return Array.from(buffer, (byte) => byte.toString(16).padStart(2, '0')).join('');
}

function confidentialAttestationSmokeEnabled() {
  if (typeof window === 'undefined') return false;
  const params = new URLSearchParams(window.location.search);
  return (
    params.get('zenodexUiSmokeConfidentialVerify') === '1'
    || params.get('zenodexUiSmokeConfidentialReplay') === '1'
  );
}

function confidentialRuntimeReplaySmokeEnabled() {
  if (typeof window === 'undefined') return false;
  return new URLSearchParams(window.location.search).get('zenodexUiSmokeConfidentialReplay') === '1';
}

function confidentialSealedBidSmokeEnabled() {
  if (typeof window === 'undefined') return false;
  return new URLSearchParams(window.location.search).get('zenodexUiSmokeSealedBid') === '1';
}

function canonicalJson(value) {
  if (Array.isArray(value)) {
    return `[${value.map(item => canonicalJson(item)).join(',')}]`;
  }
  if (value && typeof value === 'object') {
    return `{${Object.keys(value).sort().map(key => `${JSON.stringify(key)}:${canonicalJson(value[key])}`).join(',')}}`;
  }
  return JSON.stringify(value);
}

async function sha256Hex(text) {
  if (typeof crypto === 'undefined' || !crypto.subtle) {
    throw new Error('web_crypto_unavailable');
  }
  const digest = await crypto.subtle.digest('SHA-256', new TextEncoder().encode(text));
  return `0x${Array.from(new Uint8Array(digest), byte => byte.toString(16).padStart(2, '0')).join('')}`;
}

async function sealedBidCommitment({ quantity, limitPrice, nonce }) {
  const body = {
    schema: 'zenodex/sealed_bid_reveal/v1',
    quantity: Number(quantity),
    limit_price: Number(limitPrice),
    nonce: String(nonce),
  };
  return sha256Hex(`zenodex:zenodex.sealed_bid_reveal/v1:v1\u0000${canonicalJson(body)}`);
}

function buildAttestationRequest({ requestId = 'req-ui' } = {}) {
  const fixture = confidentialSmokeFixture();
  return {
    attestation_payload: {
      provider: 'nitro',
      nonce: 'ui-smoke',
      summary: { pcrs: { 0: fixture.nitroPcr0, 8: fixture.nitroPcr8 } },
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
    expected_policy_digest: fixture.policyDigest,
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

// --- Small display helpers -------------------------------------------------

function truncHash(value, head = 8, tail = 6) {
  if (!value) return '';
  const s = String(value);
  if (s.length <= head + tail + 1) return s;
  return `${s.slice(0, head)}…${s.slice(-tail)}`;
}

function CopyHash({ value, label }) {
  const [copied, setCopied] = useState(false);
  if (!value) return <span className="cwb-empty">not yet produced</span>;
  return (
    <button
      type="button"
      className="cwb-hash"
      title={`Copy ${label || 'value'}`}
      onClick={async () => {
        try {
          await navigator.clipboard.writeText(value);
          setCopied(true);
          setTimeout(() => setCopied(false), 1200);
        } catch {
          // Clipboard may be unavailable; fail silently rather than throw.
        }
      }}
    >
      <span className="cwb-hash-mono">{truncHash(value)}</span>
      <span className="cwb-hash-copy">{copied ? 'copied' : 'copy'}</span>
    </button>
  );
}

function StatusDot({ tone, label }) {
  // tone: 'ok' | 'warn' | 'err' | 'idle'
  return (
    <span className={`cwb-status cwb-status-${tone}`} role="status">
      <span className="cwb-status-dot" aria-hidden="true" />
      {label}
    </span>
  );
}

// --- Component -------------------------------------------------------------

function ConfidentialWorkbench() {
  const { demoMode } = useDemoMode();
  const smokeRan = useRef(false);
  const sealedBidSmokeRan = useRef(false);
  const smokeIdSuffix = useRef(null);

  const [liveState, setLiveState] = useState({ status: 'idle', data: null, error: '' });
  const [attestationState, setAttestationState] = useState({ status: 'idle', result: null, error: '' });
  const [runtimeState, setRuntimeState] = useState({ status: 'idle', result: null, error: '' });
  const [sealedBidState, setSealedBidState] = useState({ status: 'idle', result: null, error: '' });
  const [sealedBidForm, setSealedBidForm] = useState({
    unitsForSale: 5,
    aliceQuantity: 4,
    aliceLimitPrice: 105,
    bobQuantity: 3,
    bobLimitPrice: 103,
  });

  function smokeId(prefix) {
    if (!smokeIdSuffix.current) {
      smokeIdSuffix.current = randomSmokeHex(8);
    }
    return `${prefix}-${smokeIdSuffix.current}`;
  }

  useEffect(() => {
    if (demoMode) {
      setLiveState({ status: 'idle', data: null, error: '' });
      return undefined;
    }
    let active = true;
    (async () => {
      setLiveState(s => ({ ...s, status: 'loading' }));
      try {
        const payload = await apiGetConfidentialStatus({ timeoutMs: 5000 });
        if (!active) return;
        setLiveState({ status: 'success', data: payload?.status || null, error: '' });
      } catch (err) {
        if (!active) return;
        setLiveState({ status: 'error', data: null, error: err?.message || 'status_unavailable' });
      }
    })();
    return () => {
      active = false;
    };
  }, [demoMode]);

  async function runAttestationVerify() {
    setAttestationState({ status: 'running', result: null, error: '' });
    try {
      const requestId = confidentialAttestationSmokeEnabled() ? smokeId('req-ui') : `req-ui-${Date.now()}`;
      const payload = await apiAdmitConfidentialAttestation(
        buildAttestationRequest({ requestId }),
        { timeoutMs: 10000 },
      );
      setAttestationState({
        status: payload?.ok ? 'accepted' : 'rejected',
        result: payload || null,
        error: '',
      });
    } catch (err) {
      setAttestationState({
        status: 'rejected',
        result: null,
        error: err?.message || 'verification_failed',
      });
    }
  }

  async function runRuntimeExecute({
    preserveResultOnError = false,
    requestIdOverride = null,
    executionIdOverride = null,
  } = {}) {
    setRuntimeState(s => ({ ...s, status: 'running', error: '', result: preserveResultOnError ? s.result : null }));
    try {
      const requestId = requestIdOverride
        || (confidentialAttestationSmokeEnabled() ? smokeId('req-ui-runtime') : `req-ui-runtime-${Date.now()}`);
      const executionId = executionIdOverride
        || (confidentialAttestationSmokeEnabled() ? smokeId('exec-ui') : `exec-ui-${Date.now()}`);
      const payload = await apiExecuteConfidentialAttestation(
        buildRuntimeExecutionRequest({ requestId, executionId }),
        { timeoutMs: 10000 },
      );
      setAttestationState({
        status: payload?.ok ? 'accepted' : 'rejected',
        result: payload || null,
        error: '',
      });
      setRuntimeState({
        status: payload?.ok ? 'ready' : 'rejected',
        result: payload?.runtime_receipt || null,
        error: '',
      });
      return payload;
    } catch (err) {
      setRuntimeState(s => ({
        status: 'rejected',
        result: preserveResultOnError ? s.result : null,
        error: err?.message || 'runtime_execution_failed',
      }));
      throw err;
    }
  }

  function updateSealedBidForm(name, value) {
    const numeric = Number(value);
    setSealedBidForm(current => ({
      ...current,
      [name]: Number.isFinite(numeric) ? Math.trunc(numeric) : current[name],
    }));
  }

  async function runSealedBidFlow() {
    setSealedBidState({ status: 'running', result: null, error: '' });
    try {
      const batchId = confidentialSealedBidSmokeEnabled()
        ? smokeId('ui-sealed-bid')
        : `ui-sealed-bid-${Date.now()}`;
      const unitsForSale = Math.max(0, Math.trunc(Number(sealedBidForm.unitsForSale)));
      const aliceQuantity = Math.max(1, Math.trunc(Number(sealedBidForm.aliceQuantity)));
      const aliceLimitPrice = Math.max(1, Math.trunc(Number(sealedBidForm.aliceLimitPrice)));
      const bobQuantity = Math.max(1, Math.trunc(Number(sealedBidForm.bobQuantity)));
      const bobLimitPrice = Math.max(1, Math.trunc(Number(sealedBidForm.bobLimitPrice)));
      const aliceNonce = `alice-${randomSmokeHex(16)}`;
      const bobNonce = `bob-${randomSmokeHex(16)}`;
      const aliceCommitment = await sealedBidCommitment({
        quantity: aliceQuantity,
        limitPrice: aliceLimitPrice,
        nonce: aliceNonce,
      });
      const bobCommitment = await sealedBidCommitment({
        quantity: bobQuantity,
        limitPrice: bobLimitPrice,
        nonce: bobNonce,
      });

      const reset = await apiResetConfidentialSealedBid({
        batch_id: batchId,
        units_for_sale: unitsForSale,
        bond_amount: 7,
      }, { timeoutMs: 10000 });
      const aliceCommit = await apiCommitConfidentialSealedBid({
        batch_id: batchId,
        bidder_id: 'alice',
        commitment: aliceCommitment,
        bond_amount: 7,
      }, { timeoutMs: 10000 });
      const bobCommit = await apiCommitConfidentialSealedBid({
        batch_id: batchId,
        bidder_id: 'bob',
        commitment: bobCommitment,
        bond_amount: 7,
      }, { timeoutMs: 10000 });
      const openReveal = await apiOpenRevealConfidentialSealedBid({
        batch_id: batchId,
      }, { timeoutMs: 10000 });
      const aliceReveal = await apiRevealConfidentialSealedBid({
        batch_id: batchId,
        bidder_id: 'alice',
        quantity: aliceQuantity,
        limit_price: aliceLimitPrice,
        nonce: aliceNonce,
      }, { timeoutMs: 10000 });
      const statusBeforeSettle = await apiGetConfidentialSealedBidStatus({ timeoutMs: 10000 });
      const assetSettlementAvailable = statusBeforeSettle?.status?.asset_settlement_available === true;
      const settleBody = {
        batch_id: batchId,
      };
      if (assetSettlementAvailable) {
        settleBody.asset_settlement = {
          mode: 'local_ledger_fixture',
          fund_local_fixture: true,
        };
      }
      const settled = await apiSettleConfidentialSealedBid(settleBody, { timeoutMs: 10000 });
      const status = await apiGetConfidentialSealedBidStatus({ timeoutMs: 10000 });

      const result = {
        batchId,
        commitments: {
          alice: aliceCommitment,
          bob: bobCommitment,
        },
        reset,
        aliceCommit,
        bobCommit,
        openReveal,
        aliceReveal,
        statusBeforeSettle,
        settled,
        status,
      };
      setSealedBidState({ status: 'settled', result, error: '' });
      return result;
    } catch (err) {
      setSealedBidState({
        status: 'rejected',
        result: null,
        error: err?.message || 'sealed_bid_flow_failed',
      });
      throw err;
    }
  }

  useEffect(() => {
    if (demoMode || !confidentialAttestationSmokeEnabled() || smokeRan.current) return;
    smokeRan.current = true;
    async function runSmoke() {
      if (confidentialRuntimeReplaySmokeEnabled()) {
        const replayRequestId = smokeId('req-ui-runtime-replay');
        const replayExecutionId = smokeId('exec-ui-replay');
        await runRuntimeExecute({
          preserveResultOnError: false,
          requestIdOverride: replayRequestId,
          executionIdOverride: replayExecutionId,
        });
        await runRuntimeExecute({
          preserveResultOnError: true,
          requestIdOverride: replayRequestId,
          executionIdOverride: replayExecutionId,
        });
        return;
      }
      await runRuntimeExecute();
    }
    void runSmoke().catch(() => {});
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [demoMode]);

  useEffect(() => {
    if (demoMode || !confidentialSealedBidSmokeEnabled() || sealedBidSmokeRan.current) return;
    sealedBidSmokeRan.current = true;
    void runSealedBidFlow().catch(() => {});
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [demoMode]);

  // --- Derived display values ---------------------------------------------
  const liveStatus = liveState.data;
  const liveError = liveState.error;
  const runtimeConfig = getRuntimeConfig();
  const localTestnet = String(runtimeConfig?.deployment || '').toLowerCase() === 'local-testnet';

  const stage = String(liveStatus?.stage || CONFIDENTIAL_SURFACE.summary.stage || 'beta');
  const subtitle = String(liveStatus?.user_summary || CONFIDENTIAL_SURFACE.summary.subtitle);
  const operatorContact = String(liveStatus?.operator_contact || 'not_configured');
  const measurementCount = Number.isFinite(liveStatus?.approved_measurements_count)
    ? liveStatus.approved_measurements_count
    : 0;
  const betaReady = liveStatus?.beta_ready === true;
  const readinessGaps = Array.isArray(liveStatus?.readiness_gaps) ? liveStatus.readiness_gaps : [];
  const localBetaWired = localTestnet
    && liveStatus?.tee_enabled === true
    && liveStatus?.sealed_bid_enabled === true
    && measurementCount > 0;
  const claimScope = String(liveStatus?.claim_scope || CONFIDENTIAL_SURFACE.summary.claimScope);
  const nonClaims = Array.isArray(liveStatus?.non_claims) && liveStatus.non_claims.length > 0
    ? liveStatus.non_claims
    : [CONFIDENTIAL_SURFACE.summary.nonClaim];
  // Live capability gates — the node reports these disabled in this environment,
  // so the action CTAs must not invite an action the node will refuse. Demo mode
  // keeps the illustrative flow enabled.
  const teeReady = liveStatus?.tee_enabled === true;
  const sealedReady = liveStatus?.sealed_bid_enabled === true;
  const attestDisabledReason = !demoMode && !teeReady ? 'TEE attestation is disabled on this node' : null;
  const sealedDisabledReason = !demoMode && !sealedReady ? 'Sealed-bid auctions are disabled on this node' : null;
  // Prefer live arrays over static copy (mirrors the claim_scope/non_claims pattern).
  const liveUseCases = Array.isArray(liveStatus?.use_cases) && liveStatus.use_cases.length
    ? liveStatus.use_cases : CONFIDENTIAL_SURFACE.useCases;
  const liveNotDefaultFor = Array.isArray(liveStatus?.not_default_for) && liveStatus.not_default_for.length
    ? liveStatus.not_default_for : CONFIDENTIAL_SURFACE.notDefaultFor;
  const statusHash = String(liveStatus?.status_hash || '');
  const allowlistHash = String(liveStatus?.approved_measurements_hash || '');

  const attestationResult = attestationState.result;
  const runtimeResult = runtimeState.result;
  const sealedBidResult = sealedBidState.result;

  const verifierBindingHash = String(
    runtimeResult?.body?.external_verifier_binding_hash
    || attestationResult?.external_verifier_binding_hash
    || liveStatus?.external_verifier_binding_hash
    || ''
  );
  const receiptHash = String(attestationResult?.receipt_hash || '');
  const measurement = String(attestationResult?.measurement || attestationResult?.measurement_provider || '');
  const executionAdmitted = attestationResult?.execution_admitted === true;
  // Attestation mode: real vs smoke. The v2 verifier exposes
  // production_security_claim, attestation_source, certificate_hash, and is_smoke
  // in the result. When these fields are absent (legacy verifier), we infer
  // smoke mode from the known smoke PCR pattern.
  const attestationSource = String(
    attestationResult?.attestation_source
    || attestationResult?.result?.attestation_source
    || ''
  );
  const productionSecurityClaim = attestationResult?.production_security_claim === true
    || attestationResult?.result?.production_security_claim === true;
  const attestationCertHash = String(
    attestationResult?.certificate_hash
    || attestationResult?.result?.certificate_hash
    || ''
  );
  const isSmokeAttestation = attestationSource === 'smoke'
    || attestationResult?.is_smoke === true
    || (!attestationSource && measurement.includes('0123456789abcdef'));
  const attestationModeLabel = productionSecurityClaim
    ? 'Production-verified (real TEE attestation)'
    : isSmokeAttestation
      ? 'Smoke fixture (local-testnet only)'
      : attestationSource
        ? `Verified via ${attestationSource}`
        : 'Verification mode unknown';
  const runtimeReceiptHash = String(runtimeResult?.receipt_hash || '');
  const runtimeBody = runtimeResult?.body || {};
  const runtimeEffectDigest = String(runtimeBody?.public_effect_digest || '');
  const runtimeRedacted = runtimeBody?.result_redacted === true;
  const sealedSettlement = sealedBidResult?.settled?.settlement || {};
  const sealedBondOutcome = sealedBidResult?.settled?.bond_outcome || {};
  const sealedBatch = sealedBidResult?.settled?.batch || {};
  const sealedAliceReceiptHash = String(sealedBidResult?.aliceCommit?.receipt_hash || '');
  const sealedAliceCommitment = String(sealedBidResult?.commitments?.alice || '');
  const sealedBobCommitment = String(sealedBidResult?.commitments?.bob || '');

  // Headline status: one pill the user can read in 2 seconds.
  let headlineTone = 'idle';
  let headlineLabel = 'Status unknown';
  if (demoMode) {
    headlineTone = 'idle';
    headlineLabel = 'Demo mode — live status hidden';
  } else if (liveError) {
    headlineTone = 'err';
    headlineLabel = 'Live status unavailable';
  } else if (betaReady) {
    headlineTone = 'ok';
    headlineLabel = 'Beta-ready';
  } else if (localBetaWired) {
    headlineTone = 'warn';
    headlineLabel = readinessGaps.length > 0
      ? `Local beta wired, production gaps (${readinessGaps.length})`
      : 'Local beta wired';
  } else if (liveStatus) {
    headlineTone = 'warn';
    headlineLabel = readinessGaps.length > 0
      ? `Configuration incomplete (${readinessGaps.length})`
      : 'Configuration incomplete';
  }

  function attestationActionLabel() {
    if (attestDisabledReason) return 'Disabled on this node';
    if (attestationState.status === 'running') return 'Verifying…';
    if (attestationState.status === 'accepted') return 'Verify another';
    return 'Verify TEE attestation';
  }

  function runtimeActionLabel() {
    if (attestDisabledReason) return 'Disabled on this node';
    if (runtimeState.status === 'running') return 'Running…';
    if (runtimeState.status === 'ready') return 'Run another';
    return 'Run confidential execution';
  }

  function sealedBidActionLabel() {
    if (sealedDisabledReason) return 'Disabled on this node';
    if (sealedBidState.status === 'running') return 'Running…';
    if (sealedBidState.status === 'settled') return 'Run another auction';
    return 'Run commit/reveal auction';
  }

  return (
    <section className="confidential-workbench">
      {/* ─── Hero: what is this, is it healthy, can I use it? ───────── */}
      <header className="cwb-hero panel animate-fade-in">
        <div className="cwb-hero-main">
          <p className="cwb-kicker">CONFIDENTIAL TRADING</p>
          <h1 className="cwb-title">Hide large orders inside a trusted enclave</h1>
          <p className="cwb-lede">
            {subtitle}
          </p>
        </div>
        <div className="cwb-hero-side">
          <StatusDot tone={headlineTone} label={headlineLabel} />
          <span className="cwb-stage">stage · {stage}</span>
        </div>
      </header>

      {/* ─── Readiness checklist: surfaced (not buried in an accordion) so the
              "Configuration incomplete (N)" status in the hero is immediately
              actionable — the operator sees exactly what is not yet configured. */}
      {readinessGaps.length > 0 && (
        <section
          className="cwb-readiness-card panel animate-fade-in"
          aria-label="Configuration readiness"
        >
          <div className="cwb-readiness-card-head">
            <span className="cwb-readiness-count" aria-hidden="true">{readinessGaps.length}</span>
            <div>
              <h2 className="cwb-readiness-card-title">
                Not yet configured for confidential trading
              </h2>
              <p className="cwb-readiness-card-sub">
                {readinessGaps.length} item{readinessGaps.length === 1 ? '' : 's'} must be set on
                this node before the flows below are production-ready.
              </p>
            </div>
          </div>
          <ul className="cwb-readiness-card-list">
            {readinessGaps.map((item) => (
              <li key={item} className="cwb-readiness-card-item">
                <span className="cwb-readiness-card-dot" aria-hidden="true" />
                <span>{item}</span>
              </li>
            ))}
          </ul>
        </section>
      )}

      {/* ─── Primary actions: each card drives one live API path ───────── */}
      <div className="cwb-actions">
        <article className="cwb-action panel">
          <div className="cwb-action-head">
            <h2 className="cwb-action-title">1 · Verify a TEE attestation</h2>
            <p className="cwb-action-lede">
              Confirm an enclave is genuine and matches an approved measurement.
              Returns a signed attestation receipt.
            </p>
          </div>

          <button
            className="btn btn-primary btn-large cwb-action-cta"
            type="button"
            onClick={runAttestationVerify}
            disabled={demoMode || attestationState.status === 'running' || Boolean(attestDisabledReason)}
            title={attestDisabledReason || undefined}
          >
            {attestationActionLabel()}
          </button>
          {attestDisabledReason && (
            <p className="cwb-action-note">{attestDisabledReason}. The spec path is verified, but execution is gated off in this environment.</p>
          )}

          {(attestationState.result || attestationState.error) && (
            <div className="cwb-result animate-fade-in">
              <header className="cwb-result-head">
                <StatusDot
                  tone={attestationState.status === 'accepted' ? 'ok' : 'err'}
                  label={attestationState.status === 'accepted'
                    ? (executionAdmitted ? 'Accepted — execution admitted' : 'Accepted — execution withheld')
                    : 'Rejected'}
                />
              </header>
              {attestationState.error && (
                <p className="cwb-result-error">{attestationState.error}</p>
              )}
              {attestationState.result && (
                <dl className="cwb-result-list">
                  <div><dt>Receipt</dt><dd><CopyHash value={receiptHash} label="receipt hash" /></dd></div>
                  <div>
                    <dt>Measurement</dt>
                    <dd>{measurement.startsWith('nitro:') ? 'AWS Nitro' : (measurement.startsWith('sgx:') ? 'Intel SGX' : (measurement || <span className="cwb-empty">unknown</span>))}</dd>
                  </div>
                  <div>
                    <dt>Attestation mode</dt>
                    <dd>
                      <span className={`cwb-attestation-mode ${productionSecurityClaim ? 'cwb-attestation-real' : isSmokeAttestation ? 'cwb-attestation-smoke' : ''}`}>
                        {attestationModeLabel}
                      </span>
                    </dd>
                  </div>
                  {attestationCertHash && (
                    <div><dt>Cert hash</dt><dd><CopyHash value={attestationCertHash} label="certificate hash" /></dd></div>
                  )}
                  <div>
                    <dt>Request</dt>
                    <dd>{attestationState.result?.request_consumed ? 'consumed' : 'unconsumed'}</dd>
                  </div>
                </dl>
              )}
            </div>
          )}
        </article>

        <article className="cwb-action panel">
          <div className="cwb-action-head">
            <h2 className="cwb-action-title">2 · Run a confidential execution</h2>
            <p className="cwb-action-lede">
              Run an admitted confidential order request. The runtime produces a
              public proof digest and a redacted receipt without exposing order size
              or direction.
            </p>
          </div>

          <button
            className="btn btn-primary btn-large cwb-action-cta"
            type="button"
            onClick={runRuntimeExecute}
            disabled={demoMode || runtimeState.status === 'running' || Boolean(attestDisabledReason)}
            title={attestDisabledReason || undefined}
          >
            {runtimeActionLabel()}
          </button>
          {attestDisabledReason && (
            <p className="cwb-action-note">Confidential execution requires the TEE runtime, which is disabled on this node.</p>
          )}

          {(runtimeState.result || runtimeState.error) && (
            <div className="cwb-result animate-fade-in">
              <header className="cwb-result-head">
                <StatusDot
                  tone={runtimeState.status === 'ready' ? 'ok' : 'err'}
                  label={runtimeState.status === 'ready'
                    ? (runtimeRedacted ? 'Ready — result redacted' : 'Ready — result exposed')
                    : 'Rejected'}
                />
              </header>
              {runtimeState.error && (
                <p className="cwb-result-error">{runtimeState.error}</p>
              )}
              {runtimeState.result && (
                <dl className="cwb-result-list">
                  <div><dt>Runtime receipt</dt><dd><CopyHash value={runtimeReceiptHash} label="runtime receipt" /></dd></div>
                  <div><dt>Public effect digest</dt><dd><CopyHash value={runtimeEffectDigest} label="effect digest" /></dd></div>
                  <div><dt>Operator status hash</dt><dd><CopyHash value={statusHash || runtimeBody?.operator_status_hash} label="status hash" /></dd></div>
                  <div><dt>Allowlist hash</dt><dd><CopyHash value={allowlistHash || runtimeBody?.approved_measurements_hash} label="allowlist hash" /></dd></div>
                  <div><dt>Verifier binding</dt><dd><CopyHash value={verifierBindingHash} label="verifier binding" /></dd></div>
                </dl>
              )}
            </div>
          )}
        </article>

        <article className="cwb-action panel">
          <div className="cwb-action-head">
            <h2 className="cwb-action-title">3 · Run sealed-bid auction</h2>
            <p className="cwb-action-lede">
              Commitments are computed in the browser. The commit request sends only
              bidder identity, commitment, and bond; quantity, price, and nonce are
              sent only during reveal. When FHE is provisioned, bids are compared
              homomorphically without individual decryption.
            </p>
          </div>

          <div className="cwb-form-grid" aria-label="Sealed-bid auction inputs">
            <label>
              <span>Units</span>
              <input
                type="number"
                min="0"
                max="65535"
                value={sealedBidForm.unitsForSale}
                onChange={(event) => updateSealedBidForm('unitsForSale', event.target.value)}
              />
            </label>
            <label>
              <span>Alice qty</span>
              <input
                type="number"
                min="1"
                max="65535"
                value={sealedBidForm.aliceQuantity}
                onChange={(event) => updateSealedBidForm('aliceQuantity', event.target.value)}
              />
            </label>
            <label>
              <span>Alice price</span>
              <input
                type="number"
                min="1"
                max="65535"
                value={sealedBidForm.aliceLimitPrice}
                onChange={(event) => updateSealedBidForm('aliceLimitPrice', event.target.value)}
              />
            </label>
            <label>
              <span>Bob qty</span>
              <input
                type="number"
                min="1"
                max="65535"
                value={sealedBidForm.bobQuantity}
                onChange={(event) => updateSealedBidForm('bobQuantity', event.target.value)}
              />
            </label>
            <label>
              <span>Bob price</span>
              <input
                type="number"
                min="1"
                max="65535"
                value={sealedBidForm.bobLimitPrice}
                onChange={(event) => updateSealedBidForm('bobLimitPrice', event.target.value)}
              />
            </label>
          </div>

          <button
            className="btn btn-primary btn-large cwb-action-cta"
            type="button"
            onClick={runSealedBidFlow}
            disabled={demoMode || sealedBidState.status === 'running' || Boolean(sealedDisabledReason)}
            title={sealedDisabledReason || undefined}
          >
            {sealedBidActionLabel()}
          </button>
          {sealedDisabledReason && (
            <p className="cwb-action-note">{sealedDisabledReason}. The commit/reveal spec is verified, but the auction path is gated off here.</p>
          )}

          {(sealedBidState.result || sealedBidState.error) && (
            <div className="cwb-result animate-fade-in">
              <header className="cwb-result-head">
                <StatusDot
                  tone={sealedBidState.status === 'settled' ? 'ok' : 'err'}
                  label={sealedBidState.status === 'settled'
                    ? 'Sealed-bid flow settled'
                    : 'Sealed-bid flow rejected'}
                />
              </header>
              {sealedBidState.error && (
                <p className="cwb-result-error">{sealedBidState.error}</p>
              )}
              {sealedBidState.result && (
                <dl className="cwb-result-list">
                  <div><dt>Batch</dt><dd>{sealedBidResult.batchId}</dd></div>
                  <div><dt>Phase</dt><dd>{sealedBatch.phase || 'unknown'}</dd></div>
                  <div><dt>Alice commit</dt><dd><CopyHash value={sealedAliceCommitment} label="Alice commitment" /></dd></div>
                  <div><dt>Bob commit</dt><dd><CopyHash value={sealedBobCommitment} label="Bob commitment" /></dd></div>
                  <div><dt>Alice receipt</dt><dd><CopyHash value={sealedAliceReceiptHash} label="Alice commit receipt" /></dd></div>
                  <div><dt>Clearing price</dt><dd>{Number(sealedSettlement.clearing_price || 0).toLocaleString()}</dd></div>
                  <div><dt>Filled units</dt><dd>{Number(sealedSettlement.total_filled || 0).toLocaleString()}</dd></div>
                  <div><dt>Slashed bond</dt><dd>{Number(sealedBondOutcome.total_slashed || 0).toLocaleString()}</dd></div>
                  <div><dt>Asset settlement</dt><dd>{sealedBidResult.settled?.asset_settlement_executed ? 'executed' : 'external adapter required'}</dd></div>
                </dl>
              )}
            </div>
          )}
        </article>
      </div>

      {/* ─── Operator details: collapsed by default ─────────────────── */}
      <details className="cwb-disclosure panel">
        <summary className="cwb-disclosure-summary">
          <span>Operator details</span>
          <span className="cwb-disclosure-hint">
            Approved measurements · operator contact · status &amp; allowlist hashes
          </span>
        </summary>
        <div className="cwb-disclosure-body">
          <dl className="cwb-detail-grid">
            <div>
              <dt>Approved measurements</dt>
              <dd>{measurementCount.toLocaleString()}</dd>
            </div>
            <div>
              <dt>Operator contact</dt>
              <dd>{demoMode ? 'hidden in demo mode' : operatorContact}</dd>
            </div>
            <div>
              <dt>Status hash</dt>
              <dd><CopyHash value={statusHash} label="status hash" /></dd>
            </div>
            <div>
              <dt>Allowlist hash</dt>
              <dd><CopyHash value={allowlistHash} label="allowlist hash" /></dd>
            </div>
          </dl>
        </div>
      </details>

      {/* ─── How it works: 4-phase sealed-bid flow ──────────────────── */}
      <details className="cwb-disclosure panel">
        <summary className="cwb-disclosure-summary">
          <span>How sealed-bid auctions work</span>
          <span className="cwb-disclosure-hint">4 phases · commit → reveal → clearing → complete</span>
        </summary>
        <div className="cwb-disclosure-body">
          <ol className="cwb-phase-list">
            {CONFIDENTIAL_SURFACE.phases.map((phase, idx) => (
              <li key={phase.id} className="cwb-phase">
                <span className="cwb-phase-num">{idx + 1}</span>
                <div>
                  <div className="cwb-phase-title">{phase.title}</div>
                  <p className="cwb-phase-detail">{phase.detail}</p>
                </div>
              </li>
            ))}
          </ol>
        </div>
      </details>

      {/* ─── Assurance scope: bounded evidence checks ───────────────── */}
      <details className="cwb-disclosure panel">
        <summary className="cwb-disclosure-summary">
          <span>Assurance scope &amp; bounded evidence</span>
          <span className="cwb-disclosure-hint">
            What we claim · what we explicitly do not claim · evidence checks
          </span>
        </summary>
        <div className="cwb-disclosure-body">
          <p className="cwb-claim-scope">{claimScope}</p>
          <h3 className="cwb-disclosure-subhead">Explicit non-claims</h3>
          <ul className="cwb-bullet-list">
            {nonClaims.map((item) => <li key={item}>{item}</li>)}
          </ul>
          <h3 className="cwb-disclosure-subhead">Evidence checks</h3>
          <div className="cwb-check-list">
            {CONFIDENTIAL_SURFACE.checks.map((check) => (
              <article key={check.id} className="cwb-check">
                <div>
                  <div className="cwb-check-title">{check.label}</div>
                  <p className="cwb-check-detail">{check.detail}</p>
                </div>
                <div className="cwb-check-meta">
                  <span className={`cwb-status cwb-status-${check.status === 'verified' ? 'ok' : check.status === 'pending' ? 'warn' : 'err'}`}>
                    <span className="cwb-status-dot" aria-hidden="true" />
                    {check.status}
                  </span>
                  <span className="cwb-check-proof">{check.proof}</span>
                </div>
              </article>
            ))}
          </div>
        </div>
      </details>

      {/* ─── Where it fits / where to skip / disaster catalog ────────── */}
      <details className="cwb-disclosure panel">
        <summary className="cwb-disclosure-summary">
          <span>When to use confidential trading</span>
          <span className="cwb-disclosure-hint">
            Use cases · benefits · when to skip it · terminal hazards
          </span>
        </summary>
        <div className="cwb-disclosure-body cwb-disclosure-grid">
          <div>
            <h3 className="cwb-disclosure-subhead">Use cases</h3>
            <ul className="cwb-bullet-list">
              {liveUseCases.map((item) => <li key={item}>{item}</li>)}
            </ul>
          </div>
          <div>
            <h3 className="cwb-disclosure-subhead">User benefits</h3>
            <ul className="cwb-bullet-list">
              {CONFIDENTIAL_SURFACE.userBenefits.map((item) => <li key={item}>{item}</li>)}
            </ul>
          </div>
          <div>
            <h3 className="cwb-disclosure-subhead">Not the default for</h3>
            <ul className="cwb-bullet-list">
              {liveNotDefaultFor.map((item) => <li key={item}>{item}</li>)}
            </ul>
          </div>
          <div>
            <h3 className="cwb-disclosure-subhead">Terminal hazards</h3>
            <table className="cwb-disaster-table">
              <thead>
                <tr><th scope="col">State</th><th scope="col">Kernel</th><th scope="col">Discharge</th></tr>
              </thead>
              <tbody>
                {CONFIDENTIAL_SURFACE.disasterCatalog.map((row) => (
                  <tr key={row.disasterId}>
                    <td className="mono">{row.disasterId}</td>
                    <td>{row.model}</td>
                    <td>{row.dischargeAction} <span className="cwb-mini-chip">{row.status}</span></td>
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
        </div>
      </details>
    </section>
  );
}

export default ConfidentialWorkbench;
