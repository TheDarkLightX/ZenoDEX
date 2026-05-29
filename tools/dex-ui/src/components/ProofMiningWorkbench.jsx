import { useEffect, useRef, useState } from 'react';
import './ProofMiningWorkbench.css';
import VerifiedBySpec from './VerifiedBySpec.jsx';
import {
  apiBuildProofMiningPayoutTemplate,
  apiCheckProofMiningStatus,
  apiGetTokenomicsStatus,
  apiSubmitLedgerTransaction,
  getRuntimeConfig,
} from '../lib/api';
import { buildAndSignCreatePoolIntent } from '../sdk/dexIntentSigner.js';
import { browserKeyGenerationAllowed, connectPreferredWallet } from '../sdk/walletSignerPolicy.js';
import {
  BROWSER_CHECKPOINT_BUNDLE_SCHEMA_V0,
  hashV0,
  stableStringify,
  verifyBrowserCheckpointBundleV0,
} from '../sdk/zenoProofClient';

const DEFAULT_SENDER = `0x${'11'.repeat(48)}`;
const DEFAULT_REWARD_POOL = `0x${'99'.repeat(48)}`;
const DEFAULT_PRE_STATE = `0x${'01'.repeat(32)}`;
const DEFAULT_BATCH = `0x${'02'.repeat(32)}`;
const DEFAULT_DEX_AFTER = `0x${'03'.repeat(32)}`;

function formatJson(value) {
  return JSON.stringify(value, null, 2);
}

function parseJson(text, name) {
  try {
    return JSON.parse(String(text || '').trim() || '{}');
  } catch (err) {
    throw new Error(`${name}: ${err?.message || 'invalid_json'}`);
  }
}

function encodeText(text) {
  return new TextEncoder().encode(text);
}

function concatBytes(parts) {
  const total = parts.reduce((sum, part) => sum + part.length, 0);
  const out = new Uint8Array(total);
  let offset = 0;
  for (const part of parts) {
    out.set(part, offset);
    offset += part.length;
  }
  return out;
}

async function sha256Hex(bytes) {
  if (typeof crypto === 'undefined' || !crypto.subtle) {
    throw new Error('browser crypto.subtle is unavailable');
  }
  const digest = await crypto.subtle.digest('SHA-256', bytes);
  return `0x${Array.from(new Uint8Array(digest), byte => byte.toString(16).padStart(2, '0')).join('')}`;
}

async function canonicalDomainHash(label, value) {
  const prefix = encodeText(`zenodex:${label}:v1\0`);
  return sha256Hex(concatBytes([prefix, encodeText(stableStringify(value))]));
}

function rewardForEpoch(baseReward, epoch) {
  const shifted = Number(baseReward) >> Number(epoch);
  return shifted > 0 ? shifted : 1;
}

function root(byte) {
  return `0x${String(byte).repeat(64)}`;
}

function normalizeHexPubkey(value) {
  const text = String(value || '').trim().toLowerCase();
  return /^0x[0-9a-f]{96}$/.test(text) ? text : '';
}

function parseNonnegativeInteger(value) {
  const num = Number(value);
  return Number.isSafeInteger(num) && num >= 0 ? num : null;
}

async function resolveDemoRewardPool() {
  try {
    const data = await apiGetTokenomicsStatus({ timeoutMs: 5_000 });
    const status = data?.status || {};
    const activePoolId = status.active_participant_reward_pool_id || 'active_participant_rewards_pool';
    const activePool = Array.isArray(status.allocation_rows)
      ? status.allocation_rows.find((row) => row?.id === activePoolId)
      : null;
    const rewardPool = normalizeHexPubkey(activePool?.recipient_pubkey);
    const balance = parseNonnegativeInteger(activePool?.current_balance);
    if (rewardPool && balance != null) {
      return { rewardPool, rewardPoolBefore: balance };
    }
  } catch {
    // The workbench still supports offline sample construction.
  }
  return { rewardPool: DEFAULT_REWARD_POOL, rewardPoolBefore: 20 };
}

async function buildDemoBrowserCheckpointBundle({ height = 2, chainId = 'zeno-ledger-localtest-v0' } = {}) {
  const registry = {
    schema: 'zenodex/zeno_ledger/signer_registry/v0',
    registry_id: 'browser-debug-registry',
    payload_kind: 'checkpoint',
    threshold: 2,
    signers: [],
    registry_hash: root('a'),
  };
  const signatureSetRoot = await hashV0('light_client_signature_set_root_v0', {
    registry_hash: registry.registry_hash,
    payload_kind: 'checkpoint',
    threshold: registry.threshold,
  });
  const headerChain = [];
  let prevHeaderHash = root('0');
  for (let currentHeight = 1; currentHeight <= height; currentHeight += 1) {
    const headerRoots = {
      post_state_root: root('3'),
      evidence_root: root('5'),
      config_digest: root('7'),
      module_versions_digest: root('d'),
    };
    const header = {
      schema: 'zenodex/zeno_ledger/header/v0',
      chain_id: chainId,
      height: currentHeight,
      time_ms: 1_779_710_000_000 + currentHeight,
      prev_header_hash: prevHeaderHash,
      sequencer_set_hash: root('9'),
      ingress_root: root('4'),
      tx_root: root('f'),
      pre_state_root: root('e'),
      post_state_root: headerRoots.post_state_root,
      app_hash: await hashV0('app_hash_v0', {
        chain_id: chainId,
        height: currentHeight,
        ...headerRoots,
      }),
      evidence_root: headerRoots.evidence_root,
      body_root: root('6'),
      data_availability_root: root('a'),
      proof_journal_hash: root('8'),
      config_digest: headerRoots.config_digest,
      module_versions_digest: headerRoots.module_versions_digest,
      signature_set_root: signatureSetRoot,
    };
    headerChain.push(header);
    prevHeaderHash = await hashV0('header_v0', header);
  }
  const targetHeader = headerChain[headerChain.length - 1];
  const checkpoint = {
    schema: 'zenodex/zeno_ledger/checkpoint/v0',
    chain_id: chainId,
    height,
    header_hash: await hashV0('header_v0', targetHeader),
    app_hash: targetHeader.app_hash,
    post_state_root: targetHeader.post_state_root,
    ingress_root: targetHeader.ingress_root,
    evidence_root: targetHeader.evidence_root,
    body_root: targetHeader.body_root,
    config_digest: targetHeader.config_digest,
    proof_journal_hash: targetHeader.proof_journal_hash,
    sequencer_set_hash: targetHeader.sequencer_set_hash,
    signature_set_root: signatureSetRoot,
    signature_set: [],
  };
  const checkpointHash = await hashV0('light_client_checkpoint_v0', checkpoint);
  const rangeSummary = {
    ok: true,
    checked_heights: headerChain.map((header) => header.height),
    last_header_hash: checkpoint.header_hash,
    from_height: 1,
    to_height: height,
    trusted_prev_header_hash: root('0'),
  };
  const body = {
    schema: BROWSER_CHECKPOINT_BUNDLE_SCHEMA_V0,
    chain_id: chainId,
    from_height: 1,
    to_height: height,
    trusted_prev_header_hash: root('0'),
    header_chain: headerChain,
    target_header: targetHeader,
    target_checkpoint: checkpoint,
    signer_registry: registry,
    signature_envelopes: [
      { signer_id: 'a', key_id: 'a', envelope_hash: root('b') },
      { signer_id: 'b', key_id: 'b', envelope_hash: root('c') },
    ],
    verification_summary: {
      schema: 'zenodex.zeno_sdk.browser_checkpoint_verification_summary.v0',
      builder_id: 'browser-debug',
      python_range_replay_verified: true,
      python_bls_quorum_verified: true,
      browser_range_replay_verified: false,
      browser_range_replay_available: true,
      browser_bls_quorum_verified: false,
      browser_bls_quorum_available: false,
      checkpoint_hash: checkpointHash,
      target_header_hash: checkpoint.header_hash,
      expected_signature_set_root: signatureSetRoot,
      registry_hash: registry.registry_hash,
      quorum_report_hash: root('d'),
      accepted_weight: 2,
      threshold: 2,
      range_summary: rangeSummary,
      range_summary_hash: await hashV0('browser_checkpoint_range_summary_v0', rangeSummary),
    },
    capabilities: {
      python_range_replay_verified: true,
      python_bls_quorum_verified: true,
      browser_shape_and_hash_verified: true,
      browser_range_replay_verified: false,
      browser_range_replay_available: true,
      browser_bls_quorum_verified: false,
    },
    non_claims: [
      'browser package v0 does not replay full ledger state transitions',
    ],
  };
  return {
    ...body,
    bundle_hash: await hashV0('browser_checkpoint_bundle_v0', body),
  };
}

async function buildDemoProofMiningRequest() {
  const chainId = 'tau-testnet-alpha';
  const baseReward = 8;
  const epoch = 1;
  const { rewardPool, rewardPoolBefore } = await resolveDemoRewardPool();
  const rewardAmount = rewardForEpoch(baseReward, epoch);
  const rewardPoolAfter = rewardPoolBefore - rewardAmount;
  const appState = {
    schema: 'zenodex/tau_app_state/v1',
    proof_mining: {
      schema: 'zenodex/proof_mining_runtime_state/v1',
      reward_pool_pubkey: rewardPool,
      epoch,
      base_reward: baseReward,
      initial_pool: rewardPoolBefore,
      reward_pool_balance: rewardPoolBefore,
      total_paid: 0,
      claimed_slots: [],
    },
  };
  const proof = {
    pre_state_commitment: DEFAULT_PRE_STATE,
    batch_commitment: DEFAULT_BATCH,
    verifier: 'browser-debug-dummy',
  };
  const witnessHash = await canonicalDomainHash('dex_proof_payload', proof);
  const proposalBinding = {
    mode: 'explicit_v1',
    chain_id: chainId,
    prev_state_hash: DEFAULT_PRE_STATE,
    batch_hash: DEFAULT_BATCH,
    witness_hash: witnessHash,
    dex_hash_after: DEFAULT_DEX_AFTER,
  };
  const proposalHash = await canonicalDomainHash('proof_mining_proposal', proposalBinding);
  const flags = {
    proof_ok: 1,
    binding_ok: 1,
    policy_ok: 1,
    nonce_ok: 1,
    unclaimed_ok: 1,
  };
  const body = {
    schema: 'zenodex/permissionless_solver_proof_mining_claim/v1',
    round_id: 'browser-debug-round',
    job_digest: 'browser-debug-job',
    proposal_hash: proposalHash,
    proposal_binding: proposalBinding,
    winner: {
      miner_id: DEFAULT_SENDER,
      witness_sha256: witnessHash,
      improvement_u64: 5,
    },
    bounded_model: {
      proposal_slot: 0,
      prover_id: 1,
      base_reward: baseReward,
      epoch,
      reward_amount: rewardAmount,
      reward_kind: 'TreasuryTransfer',
    },
    budget: {
      reward_pool_before: rewardPoolBefore,
      reward_pool_after: rewardPoolAfter,
    },
    verification_flags: flags,
    tau_inputs: {
      i1: baseReward,
      i2: epoch,
      i3: rewardAmount,
      i4: rewardPoolBefore,
      i5: flags.proof_ok,
      i6: flags.binding_ok,
      i7: flags.policy_ok,
      i8: flags.nonce_ok,
      i9: flags.unclaimed_ok,
    },
    conditions: {
      round_ok: true,
      positive_improvement: true,
      budget_ok: true,
      tau_gate_expected_ok: true,
    },
  };
  const claim = {
    body,
    claim_hash: await canonicalDomainHash('permissionless_solver_proof_mining_claim', body),
  };
  const proofMiningContext = {
    chain_id: chainId,
    prev_state_hash: DEFAULT_PRE_STATE,
    batch_hash: DEFAULT_BATCH,
    witness_hash: witnessHash,
    dex_hash_after: DEFAULT_DEX_AFTER,
    proposal_hash: proposalHash,
    proof_scheme: 'dummy',
  };
  return {
    app_state_json: formatJson(appState),
    chain_balances: {
      [rewardPool]: rewardPoolBefore,
      [DEFAULT_SENDER]: 0,
    },
    claim,
    proof_mining_context: proofMiningContext,
    tx_sender_pubkey: DEFAULT_SENDER,
    expected_proposal_hash: proposalHash,
  };
}

function buildProofMiningSubmitTemplate(request) {
  const txId = `proof-mining-submit-${Date.now().toString(36)}`;
  return {
    tx: {
      tx_id: txId,
      tx_sender_pubkey: request.tx_sender_pubkey,
      block_timestamp: Math.floor(Date.now() / 1000),
      operations: {
        '10': {
          module: 'ZenoProofMining',
          action: 'submit_proof',
          claim: request.claim,
          recipient_pubkey: request.tx_sender_pubkey,
        },
      },
    },
  };
}

async function connectProofMiningSigningWallet(chainId) {
  const runtimeConfig = getRuntimeConfig();
  return connectPreferredWallet({
    chainId,
    globalObject: typeof window === 'undefined' ? globalThis : window,
    runtimeConfig,
    allowBrowserFallback: browserKeyGenerationAllowed({
      locationSearch: typeof window === 'undefined' ? '' : window.location.search,
      runtimeConfig,
      env: import.meta.env,
    }),
  });
}

function dexIntentSignerForWallet(wallet) {
  return wallet?.signDexIntentForEngine || wallet?.signDexIntent || null;
}

async function buildLiveProofMiningPayoutTemplate() {
  const chainId = 'zeno-ledger-localtest-v0';
  const wallet = await connectProofMiningSigningWallet(chainId);
  const { rewardPool } = await resolveDemoRewardPool();
  const seed = `${Date.now().toString(36)}-${Math.random().toString(36).slice(2)}`;
  const rawAsset0 = await hashV0('proof_mining_demo_asset0_v0', { seed });
  const rawAsset1 = await hashV0('proof_mining_demo_asset1_v0', { seed });
  const [asset0, asset1] = [rawAsset0, rawAsset1].sort();
  const createdAt = Math.floor(Date.now() / 1000);
  const signed = await buildAndSignCreatePoolIntent({
    chainId,
    privkey: wallet.privkey,
    signDexIntent: dexIntentSignerForWallet(wallet),
    payload: {
      senderPubkey: wallet.address,
      asset0,
      asset1,
      amount0: 2_000,
      amount1: 3_000,
      feeBps: 30,
      nonce: 1,
      createdAt,
      deadline: 1_999_999_999,
    },
  });
  const response = await apiBuildProofMiningPayoutTemplate({
    chain_id: chainId,
    tx_sender_pubkey: wallet.address,
    signed_intent: signed,
    faucet_mint: [
      { pubkey: wallet.address, asset: asset0, amount: 10_000 },
      { pubkey: wallet.address, asset: asset1, amount: 10_000 },
    ],
    base_reward: 8,
    epoch: 1,
    proposal_slot: 0,
    prover_id: 1,
    reward_pool_pubkey: rewardPool,
  }, { timeoutMs: 20_000 });
  return {
    ...response.status_request,
    tx: response.tx,
    wallet,
    reward_pool_pubkey: response.reward_pool_pubkey,
    reward_asset_id: response.reward_asset_id,
    reward_pool_before: response.reward_pool_before,
  };
}

function submitTxAccepted(result) {
  if (!result || typeof result !== 'object') return false;
  if (result.tx_accepted === true) return true;
  if (result.receipt && typeof result.receipt === 'object') {
    return result.receipt.accepted === true;
  }
  return result.ok === true && result.status === 'accepted';
}

function proofMiningSmokeEnabled() {
  if (typeof window === 'undefined') return false;
  return new URLSearchParams(window.location.search).get('zenodexUiSmokeProofMining') === '1';
}

function StatusPill({ ok, label }) {
  const tone = ok ? 'ok' : 'bad';
  return <span className={`pmw-pill pmw-pill-${tone}`}>{label}</span>;
}

function CheckGrid({ checks }) {
  if (!checks || typeof checks !== 'object') {
    return <p className="pmw-muted">No check bits returned.</p>;
  }
  return (
    <div className="pmw-check-grid">
      {Object.entries(checks).map(([name, value]) => (
        <div key={name} className="pmw-check-row">
          <span>{name}</span>
          <StatusPill ok={Boolean(value)} label={value ? 'pass' : 'fail'} />
        </div>
      ))}
    </div>
  );
}

function ProofMiningWorkbench() {
  const smokeRan = useRef(false);
  const [claimText, setClaimText] = useState('{}');
  const [contextText, setContextText] = useState('{}');
  const [balancesText, setBalancesText] = useState('{}');
  const [appStateText, setAppStateText] = useState('');
  const [sender, setSender] = useState(DEFAULT_SENDER);
  const [proofStatus, setProofStatus] = useState({ state: 'idle', data: null, error: '' });
  const [submitTxText, setSubmitTxText] = useState('{}');
  const [submitStatus, setSubmitStatus] = useState({ state: 'idle', data: null, error: '' });
  const [smokeMessage, setSmokeMessage] = useState('');

  const [bundleText, setBundleText] = useState('');
  const [requireBls, setRequireBls] = useState(false);
  const [bundleStatus, setBundleStatus] = useState({ state: 'idle', data: null, error: '' });

  async function loadDemoClaim() {
    setProofStatus({ state: 'loading_sample', data: null, error: '' });
    try {
      const request = await buildLiveProofMiningPayoutTemplate();
      setClaimText(formatJson(request.claim));
      setContextText(formatJson(request.proof_mining_context));
      setBalancesText(formatJson(request.chain_balances));
      setAppStateText(request.app_state_json);
      setSender(request.tx_sender_pubkey);
      setSubmitTxText(formatJson({ tx: request.tx }));
      setProofStatus({ state: 'sample_loaded', data: null, error: '' });
    } catch (err) {
      try {
        const request = await buildDemoProofMiningRequest();
        setClaimText(formatJson(request.claim));
        setContextText(formatJson(request.proof_mining_context));
        setBalancesText(formatJson(request.chain_balances));
        setAppStateText(request.app_state_json);
        setSender(request.tx_sender_pubkey);
        setSubmitTxText(formatJson(buildProofMiningSubmitTemplate(request)));
        setProofStatus({ state: 'sample_loaded', data: null, error: err?.message || 'live_template_unavailable' });
      } catch (fallbackErr) {
        setProofStatus({ state: 'error', data: null, error: fallbackErr?.message || err?.message || 'sample_build_failed' });
      }
    }
  }

  async function runProofMiningSmoke() {
    setSmokeMessage('');
    setProofStatus({ state: 'checking', data: null, error: '' });
    setBundleStatus({ state: 'checking', data: null, error: '' });
    const request = await buildLiveProofMiningPayoutTemplate();
    setClaimText(formatJson(request.claim));
    setContextText(formatJson(request.proof_mining_context));
    setBalancesText(formatJson(request.chain_balances));
    setAppStateText(request.app_state_json);
    setSender(request.tx_sender_pubkey);
    setSubmitTxText(formatJson({ tx: request.tx }));
    const result = await apiCheckProofMiningStatus(request, { timeoutMs: 15_000 });
    setProofStatus({ state: 'done', data: result?.status || null, error: '' });
    const bundle = await buildDemoBrowserCheckpointBundle();
    setBundleText(formatJson(bundle));
    const report = await verifyBrowserCheckpointBundleV0(bundle, { requireIndependentBls: false });
    setBundleStatus({ state: 'done', data: report, error: '' });
    setSmokeMessage('Proof mining smoke complete');
  }

  async function checkClaimability() {
    setProofStatus({ state: 'checking', data: null, error: '' });
    try {
      const request = {
        app_state_json: appStateText,
        chain_balances: parseJson(balancesText, 'chain_balances'),
        claim: parseJson(claimText, 'claim'),
        proof_mining_context: parseJson(contextText, 'proof_mining_context'),
        tx_sender_pubkey: String(sender || '').trim(),
      };
      request.expected_proposal_hash = String(request.claim?.body?.proposal_hash || '');
      const result = await apiCheckProofMiningStatus(request, { timeoutMs: 15_000 });
      setProofStatus({ state: 'done', data: result?.status || null, error: '' });
    } catch (err) {
      setProofStatus({ state: 'error', data: null, error: err?.message || 'proof_mining_status_failed' });
    }
  }

  async function submitPayoutTransaction() {
    setSubmitStatus({ state: 'submitting', data: null, error: '' });
    try {
      const payload = parseJson(submitTxText, 'payout_transaction');
      const result = await apiSubmitLedgerTransaction(payload, { timeoutMs: 20_000 });
      setSubmitStatus({ state: 'done', data: result, error: '' });
    } catch (err) {
      setSubmitStatus({ state: 'error', data: null, error: err?.message || 'proof_mining_submit_failed' });
    }
  }

  async function verifyCheckpointBundle() {
    setBundleStatus({ state: 'checking', data: null, error: '' });
    try {
      const bundle = parseJson(bundleText, 'checkpoint_bundle');
      const report = await verifyBrowserCheckpointBundleV0(bundle, { requireIndependentBls: requireBls });
      setBundleStatus({ state: 'done', data: report, error: '' });
    } catch (err) {
      setBundleStatus({ state: 'error', data: null, error: err?.message || 'bundle_verify_failed' });
    }
  }

  useEffect(() => {
    if (!proofMiningSmokeEnabled() || smokeRan.current) return;
    smokeRan.current = true;
    const timer = setTimeout(() => {
      void runProofMiningSmoke().catch((err) => {
        setProofStatus({ state: 'error', data: null, error: err?.message || 'proof_mining_smoke_failed' });
        setSmokeMessage('Proof mining smoke failed');
      });
    }, 0);
    return () => clearTimeout(timer);
  }, []);

  const status = proofStatus.data;
  const report = bundleStatus.data;

  return (
    <section className="proof-mining-workbench">
      <div className="pmw-header">
        <div>
          <p className="pmw-kicker">Proof operations</p>
          <h1>Proof mining and browser verification</h1>
          <p>
            Verify checkpoint bundles in the browser and preflight proof-mining claims
            against the live local API before submitting a payout transaction.
          </p>
        </div>
        <div className="pmw-specs">
          <VerifiedBySpec spec="proof_mining_manager_v1" kind="esso" />
          <VerifiedBySpec spec="browser_checkpoint_bundle_v0" kind="tau" />
        </div>
      </div>

      <div className="pmw-layout">
        <section className="pmw-panel">
          <div className="pmw-panel-head">
            <div>
              <h2>Proof-mining claimability</h2>
              <p>Build a local sample or paste a real claim, context, and balance snapshot.</p>
            </div>
            <button type="button" className="btn-secondary" onClick={loadDemoClaim}>
              Load sample
            </button>
          </div>

          <div className="pmw-form-grid">
            <label>
              <span>Claim artifact</span>
              <textarea value={claimText} onChange={(event) => setClaimText(event.target.value)} spellCheck="false" />
            </label>
            <label>
              <span>Verified proof-mining context</span>
              <textarea value={contextText} onChange={(event) => setContextText(event.target.value)} spellCheck="false" />
            </label>
            <label>
              <span>Chain balances</span>
              <textarea value={balancesText} onChange={(event) => setBalancesText(event.target.value)} spellCheck="false" />
            </label>
            <label>
              <span>App state JSON</span>
              <textarea value={appStateText} onChange={(event) => setAppStateText(event.target.value)} spellCheck="false" />
            </label>
          </div>

          <div className="pmw-inline-fields">
            <label>
              <span>Sender pubkey</span>
              <input value={sender} onChange={(event) => setSender(event.target.value)} />
            </label>
          </div>

          <button type="button" className="btn-primary pmw-primary" onClick={checkClaimability}>
            Check claimability
          </button>

          {proofStatus.error && <p className="pmw-error">{proofStatus.error}</p>}
          {smokeMessage && <p className="pmw-note">{smokeMessage}</p>}
          {proofStatus.state === 'sample_loaded' && (
            <p className="pmw-note">
              Sample loaded from the live tokenomics reward pool when available.
            </p>
          )}
          {status && (
            <div className="pmw-result">
              <div className="pmw-result-head">
                <StatusPill ok={Boolean(status.enabled)} label={status.enabled ? 'enabled' : 'disabled'} />
                <StatusPill ok={Boolean(status.claimable)} label={status.claimable ? 'claimable' : 'blocked'} />
                {status.error && <span className="pmw-result-error">{status.error}</span>}
              </div>
              <CheckGrid checks={status.checks} />
              <details>
                <summary>Raw status</summary>
                <pre>{formatJson(status)}</pre>
              </details>
            </div>
          )}

          <div className="pmw-submit-box">
            <div>
              <h3>Submit payout transaction</h3>
              <p>
                Paste the full ledger transaction that produced the verified DEX proof context and includes
                stream 10. A standalone claim is expected to be rejected by the runtime.
              </p>
            </div>
            <label className="pmw-bundle-field">
              <span>Ledger transaction JSON</span>
              <textarea value={submitTxText} onChange={(event) => setSubmitTxText(event.target.value)} spellCheck="false" />
            </label>
            <button type="button" className="btn-primary pmw-primary" onClick={submitPayoutTransaction}>
              Submit payout transaction
            </button>
            {submitStatus.error && <p className="pmw-error">{submitStatus.error}</p>}
            {submitStatus.data && (
              <div className="pmw-result">
                <div className="pmw-result-head">
                  <StatusPill
                    ok={submitTxAccepted(submitStatus.data)}
                    label={submitTxAccepted(submitStatus.data) ? 'accepted' : 'rejected'}
                  />
                  {submitStatus.data.height != null && <span className="pmw-muted">height {submitStatus.data.height}</span>}
                </div>
                <details>
                  <summary>Raw submit result</summary>
                  <pre>{formatJson(submitStatus.data)}</pre>
                </details>
              </div>
            )}
          </div>
        </section>

        <section className="pmw-panel">
          <div className="pmw-panel-head">
            <div>
              <h2>Browser checkpoint verification</h2>
              <p>Paste a browser checkpoint bundle and verify hash binding, header replay, and optional BLS quorum.</p>
            </div>
          </div>
          <label className="pmw-bundle-field">
            <span>Checkpoint bundle JSON</span>
            <textarea value={bundleText} onChange={(event) => setBundleText(event.target.value)} spellCheck="false" />
          </label>
          <label className="pmw-toggle">
            <input
              type="checkbox"
              checked={requireBls}
              onChange={(event) => setRequireBls(event.target.checked)}
            />
            Require independent browser BLS verification
          </label>
          <button type="button" className="btn-primary pmw-primary" onClick={verifyCheckpointBundle}>
            Verify bundle
          </button>
          {bundleStatus.error && <p className="pmw-error">{bundleStatus.error}</p>}
          {report && (
            <div className="pmw-result">
              <div className="pmw-result-head">
                <StatusPill ok={Boolean(report.ok)} label={report.ok ? 'verified' : 'rejected'} />
                {report.height != null && <span className="pmw-muted">height {report.height}</span>}
                {report.chain_id && <span className="pmw-muted">{report.chain_id}</span>}
              </div>
              {Array.isArray(report.gaps) && report.gaps.length > 0 && (
                <ul className="pmw-gap-list">
                  {report.gaps.map((gap) => <li key={gap}>{gap}</li>)}
                </ul>
              )}
              <details>
                <summary>Raw verification report</summary>
                <pre>{formatJson(report)}</pre>
              </details>
            </div>
          )}
        </section>
      </div>
    </section>
  );
}

export default ProofMiningWorkbench;
