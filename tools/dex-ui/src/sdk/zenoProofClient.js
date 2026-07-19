export const BROWSER_CHECKPOINT_BUNDLE_SCHEMA_V0 = 'zenodex.zeno_sdk.browser_checkpoint_bundle.v0';
export const BROWSER_WALLET_SYNC_STATE_SCHEMA_V0 = 'zenodex.zeno_sdk.wallet_sync_state.v0';
export const BROWSER_CHECKPOINT_VERIFICATION_SUMMARY_SCHEMA_V0 =
  'zenodex.zeno_sdk.browser_checkpoint_verification_summary.v0';
export const ZK_PROOF_STATUS_SUMMARY_SCHEMA_V0 = 'zenodex.zeno_sdk.zk_proof_status_summary.v0';

const ROOT_RE = /^0x[0-9a-f]{64}$/;
const HASH_RE = /^(?:0x|sha256:)[0-9a-f]{64}$/;
const MAX_SIGNATURE_ENVELOPES = 64;
const MAX_HEADER_CHAIN_HEADERS = 4096;
const textEncoder = new TextEncoder();
const ZK_MODES = new Set(['auto-strict', 'strict', 'open']);
const ZK_EFFECTIVE_MODES = new Set(['strict', 'open']);
const PROOF_VERIFIER_KINDS = new Set(['disabled', 'subprocess', 'misconfigured']);
const HEADER_SCHEMA_V0 = 'zenodex/zeno_ledger/header/v0';
const CHECKPOINT_SCHEMA_V0 = 'zenodex/zeno_ledger/checkpoint/v0';
const BUNDLE_KEYS_V0 = [
  'schema',
  'chain_id',
  'from_height',
  'to_height',
  'trusted_prev_header_hash',
  'header_chain',
  'target_header',
  'target_checkpoint',
  'signer_registry',
  'signature_envelopes',
  'verification_summary',
  'capabilities',
  'non_claims',
  'bundle_hash',
];
const VERIFICATION_SUMMARY_KEYS_V0 = [
  'schema',
  'builder_id',
  'python_range_replay_verified',
  'python_bls_quorum_verified',
  'browser_range_replay_verified',
  'browser_range_replay_available',
  'browser_bls_quorum_verified',
  'browser_bls_quorum_available',
  'checkpoint_hash',
  'target_header_hash',
  'expected_signature_set_root',
  'registry_hash',
  'quorum_report_hash',
  'accepted_weight',
  'threshold',
  'range_summary',
  'range_summary_hash',
];
const CAPABILITY_KEYS_V0 = [
  'python_range_replay_verified',
  'python_bls_quorum_verified',
  'browser_shape_and_hash_verified',
  'browser_range_replay_verified',
  'browser_range_replay_available',
  'browser_bls_quorum_verified',
];
const RANGE_SUMMARY_KEYS_V0 = [
  'ok',
  'checked_heights',
  'last_header_hash',
  'from_height',
  'to_height',
  'trusted_prev_header_hash',
];
const WALLET_SYNC_STATE_KEYS_V0 = [
  'schema',
  'surface',
  'chain_id',
  'height',
  'app_hash',
  'target_header_hash',
  'checkpoint_hash',
  'signer_registry_hash',
  'trust_model',
  'bundle_hash',
  'updated_at_ms',
  'state_hash',
];
const HEADER_ROOT_FIELDS_V0 = [
  'prev_header_hash',
  'sequencer_set_hash',
  'ingress_root',
  'tx_root',
  'pre_state_root',
  'post_state_root',
  'app_hash',
  'evidence_root',
  'body_root',
  'data_availability_root',
  'proof_journal_hash',
  'config_digest',
  'module_versions_digest',
  'signature_set_root',
];

function isRecord(value) {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}

function requireRecord(value, name) {
  if (!isRecord(value)) {
    throw new Error(`${name} must be an object`);
  }
  return value;
}

function requireRoot(value, name) {
  if (typeof value !== 'string' || !ROOT_RE.test(value)) {
    throw new Error(`${name} must be a canonical 32-byte root`);
  }
  return value;
}

function requireNonnegativeInt(value, name) {
  if (!Number.isSafeInteger(value) || value < 0) {
    throw new Error(`${name} must be a non-negative safe integer`);
  }
  return value;
}

function assertNoSurrogates(text) {
  for (let i = 0; i < text.length; i += 1) {
    const code = text.charCodeAt(i);
    if (code >= 0xd800 && code <= 0xdfff) {
      throw new Error('surrogate code points are not allowed in canonical encoding');
    }
  }
}

export function stableStringify(value) {
  if (value === null) return 'null';
  if (value === true) return 'true';
  if (value === false) return 'false';
  if (typeof value === 'string') {
    assertNoSurrogates(value);
    return JSON.stringify(value);
  }
  if (typeof value === 'number') {
    if (!Number.isSafeInteger(value)) {
      throw new Error('only safe integers are allowed in canonical encoding');
    }
    return String(value);
  }
  if (Array.isArray(value)) {
    return `[${value.map((item) => stableStringify(item)).join(',')}]`;
  }
  if (isRecord(value)) {
    return `{${Object.keys(value).sort().map((key) => {
      assertNoSurrogates(key);
      return `${JSON.stringify(key)}:${stableStringify(value[key])}`;
    }).join(',')}}`;
  }
  throw new Error(`unsupported canonical encoding type: ${typeof value}`);
}

function encodeUvarint(value) {
  let n = requireNonnegativeInt(value, 'uvarint');
  const out = [];
  while (true) {
    const byte = n & 0x7f;
    n = Math.floor(n / 128);
    if (n) {
      out.push(byte | 0x80);
    } else {
      out.push(byte);
      break;
    }
  }
  return Uint8Array.from(out);
}

function concatBytes(parts) {
  const total = parts.reduce((acc, part) => acc + part.length, 0);
  const out = new Uint8Array(total);
  let offset = 0;
  for (const part of parts) {
    out.set(part, offset);
    offset += part.length;
  }
  return out;
}

function encodeBytes(bytes) {
  return concatBytes([encodeUvarint(bytes.length), bytes]);
}

async function sha256Hex(bytes) {
  const webCrypto = globalThis.crypto?.subtle;
  if (webCrypto) {
    const digest = await webCrypto.digest('SHA-256', bytes);
    return `0x${Array.from(new Uint8Array(digest), (b) => b.toString(16).padStart(2, '0')).join('')}`;
  }
  const { createHash } = await import('node:crypto');
  return `0x${createHash('sha256').update(bytes).digest('hex')}`;
}

export async function hashV0(domain, value) {
  if (typeof domain !== 'string' || !/^[A-Za-z0-9_.:/-]+$/.test(domain)) {
    throw new Error('domain contains unsupported characters');
  }
  const prefix = textEncoder.encode(`zenodex:zeno_ledger_${domain}:v1\0`);
  const payload = value instanceof Uint8Array
    ? value
    : textEncoder.encode(stableStringify(value));
  return sha256Hex(concatBytes([prefix, encodeBytes(payload)]));
}

function bodyWithoutHash(obj, hashKey) {
  const body = {};
  for (const key of Object.keys(obj)) {
    if (key !== hashKey) {
      body[key] = obj[key];
    }
  }
  return body;
}

function exactKeys(obj, keys, name) {
  const actual = Object.keys(obj).sort();
  const expected = [...keys].sort();
  if (actual.length !== expected.length || actual.some((key, index) => key !== expected[index])) {
    throw new Error(`${name} keys mismatch`);
  }
}

function requireNonEmptyString(value, name) {
  if (typeof value !== 'string' || value === '') {
    throw new Error(`${name} must be non-empty`);
  }
  return value;
}

function optionalStringOrNull(value, name) {
  if (value === null || value === undefined) return null;
  if (typeof value !== 'string') {
    throw new Error(`${name} must be a string or null`);
  }
  return value;
}

function parseProofArtifactHashes(value, gaps, name = 'proof_artifact_hashes') {
  if (value === undefined || value === null) return {};
  if (!isRecord(value)) {
    gaps.push(`${name} must be an object`);
    return {};
  }
  const out = {};
  for (const [key, item] of Object.entries(value)) {
    if (typeof key !== 'string' || key === '') {
      gaps.push(`${name} keys must be non-empty strings`);
      continue;
    }
    if (typeof item !== 'string' || !HASH_RE.test(item)) {
      gaps.push(`${name}.${key} must be a 32-byte 0x or sha256 hash`);
      continue;
    }
    out[key] = item;
  }
  return out;
}

export function parseZkProofStatusV0(input, options = {}) {
  const gaps = [];
  try {
    const obj = requireRecord(input, 'proof status');
    const opts = options === undefined || options === null
      ? {}
      : requireRecord(options, 'proof status options');
    const requested = obj.zk_mode_requested ?? obj.mode_requested ?? 'open';
    const effective = obj.zk_mode_effective ?? obj.mode_effective ?? requested;
    if (typeof requested !== 'string' || !ZK_MODES.has(requested)) {
      gaps.push('zk_mode_requested is invalid');
    }
    if (typeof effective !== 'string' || !ZK_EFFECTIVE_MODES.has(effective)) {
      gaps.push('zk_mode_effective is invalid');
    }
    const zkRequired = obj.zk_required === true || obj.required === true;
    const verifierKind = obj.proof_verifier_kind ?? obj.verifier_kind ?? 'disabled';
    if (typeof verifierKind !== 'string' || !PROOF_VERIFIER_KINDS.has(verifierKind)) {
      gaps.push('proof_verifier_kind is invalid');
    }
    const proofArtifactHashes = parseProofArtifactHashes(obj.proof_artifact_hashes, gaps);
    const expectedProofArtifactHashes = parseProofArtifactHashes(
      opts.expectedProofArtifactHashes ?? opts.expected_proof_artifact_hashes,
      gaps,
      'expected_proof_artifact_hashes',
    );
    const fallbackReason = optionalStringOrNull(obj.zk_fallback_reason ?? obj.fallback_reason ?? null, 'zk_fallback_reason');
    const productionSecurityClaim = obj.production_security_claim === true;
    const custodyMode = typeof obj.custody_mode === 'string' ? obj.custody_mode : '';
    const fixtureBacked = obj.fixture_backed === true
      || custodyMode.includes('fixture');
    const fallback = requested === 'auto-strict' && effective === 'open' && Boolean(fallbackReason);
    let proofMode = 'open';
    if (fallback) {
      proofMode = 'fallback';
    } else if (fixtureBacked) {
      proofMode = 'fixture';
    } else if (effective === 'strict') {
      proofMode = 'strict';
    }

    if (effective === 'strict' && zkRequired !== true) {
      gaps.push('strict zk mode requires zk_required=true');
    }
    if (fallback) {
      gaps.push('auto-strict fallback is not an acceptable proof status');
    }
    if (effective === 'strict' && verifierKind !== 'subprocess') {
      gaps.push('strict zk mode requires a configured subprocess verifier');
    }
    if (effective === 'strict') {
      if (!proofArtifactHashes.verifier) gaps.push('strict zk mode requires proof verifier artifact hash');
      if (!proofArtifactHashes.circuit) gaps.push('strict zk mode requires proof circuit artifact hash');
    }
    for (const [key, expected] of Object.entries(expectedProofArtifactHashes)) {
      if (!proofArtifactHashes[key]) {
        gaps.push(`expected proof artifact hash missing:${key}`);
      } else if (proofArtifactHashes[key] !== expected) {
        gaps.push(`proof artifact hash mismatch:${key}`);
      }
    }
    if (productionSecurityClaim && proofMode !== 'strict') {
      gaps.push('production_security_claim requires strict non-fixture zk mode');
    }
    if (productionSecurityClaim) {
      gaps.push('production_security_claim is self-reported and cannot be promoted by this parser');
    }

    return {
      schema: ZK_PROOF_STATUS_SUMMARY_SCHEMA_V0,
      ok: gaps.length === 0,
      status: gaps.length === 0 ? 'accepted' : 'blocked',
      proof_mode: proofMode,
      zk_mode_requested: typeof requested === 'string' ? requested : null,
      zk_mode_effective: typeof effective === 'string' ? effective : null,
      zk_required: zkRequired,
      proof_verifier_kind: typeof verifierKind === 'string' ? verifierKind : null,
      proof_artifact_hashes: proofArtifactHashes,
      expected_proof_artifact_hashes: expectedProofArtifactHashes,
      artifact_pinning_verified: (
        Object.keys(expectedProofArtifactHashes).length > 0
        && Object.entries(expectedProofArtifactHashes).every(([key, expected]) => proofArtifactHashes[key] === expected)
      ),
      fallback,
      fallback_reason: fallbackReason,
      fixture_backed: fixtureBacked,
      production_security_claim: productionSecurityClaim,
      can_make_production_security_claim: false,
      gaps,
    };
  } catch (err) {
    return {
      schema: ZK_PROOF_STATUS_SUMMARY_SCHEMA_V0,
      ok: false,
      status: 'blocked',
      proof_mode: 'rejected',
      zk_required: false,
      proof_artifact_hashes: {},
      expected_proof_artifact_hashes: {},
      artifact_pinning_verified: false,
      fallback: false,
      fallback_reason: null,
      fixture_backed: false,
      production_security_claim: false,
      can_make_production_security_claim: false,
      gaps: [err?.message || 'proof status rejected'],
    };
  }
}

function validateHeaderShape(header, name = 'header') {
  requireRecord(header, name);
  exactKeys(header, ['schema', 'chain_id', 'height', 'time_ms', ...HEADER_ROOT_FIELDS_V0], name);
  if (header.schema !== HEADER_SCHEMA_V0) {
    throw new Error(`${name} schema mismatch`);
  }
  requireNonEmptyString(header.chain_id, `${name} chain_id`);
  requireNonnegativeInt(header.height, `${name} height`);
  requireNonnegativeInt(header.time_ms, `${name} time_ms`);
  for (const key of HEADER_ROOT_FIELDS_V0) {
    requireRoot(header[key], `${name} ${key}`);
  }
}

async function canonicalHeaderHashV0(header) {
  validateHeaderShape(header);
  const appHash = await hashV0('app_hash_v0', {
    chain_id: header.chain_id,
    height: header.height,
    post_state_root: header.post_state_root,
    evidence_root: header.evidence_root,
    config_digest: header.config_digest,
    module_versions_digest: header.module_versions_digest,
  });
  if (header.app_hash !== appHash) {
    throw new Error('header app_hash mismatch');
  }
  return hashV0('header_v0', header);
}

function validateCheckpointShape(checkpoint) {
  requireRecord(checkpoint, 'target_checkpoint');
  exactKeys(checkpoint, [
    'schema',
    'chain_id',
    'height',
    'header_hash',
    'app_hash',
    'post_state_root',
    'ingress_root',
    'evidence_root',
    'body_root',
    'config_digest',
    'proof_journal_hash',
    'sequencer_set_hash',
    'signature_set_root',
    'signature_set',
  ], 'target checkpoint');
  if (checkpoint.schema !== CHECKPOINT_SCHEMA_V0) {
    throw new Error('target checkpoint schema mismatch');
  }
  if (typeof checkpoint.chain_id !== 'string' || !checkpoint.chain_id) {
    throw new Error('target checkpoint chain_id must be non-empty');
  }
  requireNonnegativeInt(checkpoint.height, 'target checkpoint height');
  for (const key of [
    'header_hash',
    'app_hash',
    'post_state_root',
    'ingress_root',
    'evidence_root',
    'body_root',
    'config_digest',
    'proof_journal_hash',
    'sequencer_set_hash',
    'signature_set_root',
  ]) {
    requireRoot(checkpoint[key], `target checkpoint ${key}`);
  }
  if (!Array.isArray(checkpoint.signature_set) || checkpoint.signature_set.length !== 0) {
    throw new Error('target checkpoint signature_set must be empty');
  }
}

async function validateCheckpointHeaderBinding(checkpoint, header) {
  validateCheckpointShape(checkpoint);
  validateHeaderShape(header, 'target_header');
  if (checkpoint.chain_id !== header.chain_id) {
    throw new Error('checkpoint/header chain_id mismatch');
  }
  if (checkpoint.height !== header.height) {
    throw new Error('checkpoint/header height mismatch');
  }
  const headerHash = await canonicalHeaderHashV0(header);
  if (checkpoint.header_hash !== headerHash) {
    throw new Error('checkpoint/header hash mismatch');
  }
  for (const key of [
    'app_hash',
    'post_state_root',
    'ingress_root',
    'evidence_root',
    'body_root',
    'config_digest',
    'proof_journal_hash',
    'sequencer_set_hash',
    'signature_set_root',
  ]) {
    if (checkpoint[key] !== header[key]) {
      throw new Error(`checkpoint/header ${key} mismatch`);
    }
  }
  return headerHash;
}

async function replayHeaderChainV0({
  headerChain,
  trustedPrevHeaderHash,
  fromHeight,
  toHeight,
}) {
  if (
    !Array.isArray(headerChain)
    || headerChain.length === 0
    || headerChain.length > MAX_HEADER_CHAIN_HEADERS
  ) {
    throw new Error('header_chain length rejected');
  }
  if (headerChain.length !== toHeight - fromHeight + 1) {
    throw new Error('header_chain length must match height range');
  }

  let prevHash = trustedPrevHeaderHash;
  let chainId = null;
  const checkedHeights = [];
  for (let index = 0; index < headerChain.length; index += 1) {
    const header = requireRecord(headerChain[index], `header_chain[${index}]`);
    validateHeaderShape(header, `header_chain[${index}]`);
    const expectedHeight = fromHeight + index;
    if (header.height !== expectedHeight) {
      throw new Error('header_chain must be ordered by consecutive height');
    }
    if (chainId === null) {
      chainId = header.chain_id;
    } else if (header.chain_id !== chainId) {
      throw new Error('headers must share one chain_id');
    }
    if (header.prev_header_hash !== prevHash) {
      throw new Error(index === 0 ? 'first header prev_header_hash mismatch' : 'header prev_header_hash does not match previous header hash');
    }
    checkedHeights.push(header.height);
    prevHash = await canonicalHeaderHashV0(header);
  }
  return {
    ok: true,
    chainId,
    checkedHeights,
    lastHeaderHash: prevHash,
    tipHeader: headerChain[headerChain.length - 1],
  };
}

function requireRangeSummary(summary) {
  const rangeSummary = requireRecord(summary.range_summary, 'verification summary range_summary');
  exactKeys(rangeSummary, RANGE_SUMMARY_KEYS_V0, 'verification summary range_summary');
  if (rangeSummary.ok !== true) {
    throw new Error('verification summary range_summary must be accepted');
  }
  if (!Array.isArray(rangeSummary.checked_heights)) {
    throw new Error('verification summary range_summary checked_heights must be an array');
  }
  return rangeSummary;
}

export async function verifyBrowserCheckpointBundleV0(bundle, options = {}) {
  const gaps = [];
  const trustBuilderBls = options.trustBuilderBls === true;
  const requireIndependentBls = options.requireIndependentBls === undefined
    ? !trustBuilderBls
    : Boolean(options.requireIndependentBls);
  try {
    if (!requireIndependentBls && !trustBuilderBls) {
      throw new Error('trustBuilderBls=true is required when independent BLS verification is disabled');
    }
    // The bundle can be internally consistent while still pointing at an
    // attacker-selected history. Browser callers must pin the roots they trust.
    const expectedTrustedPrevHeaderHash = requireRoot(
      options.expectedTrustedPrevHeaderHash,
      'expectedTrustedPrevHeaderHash',
    );
    const expectedSignerRegistryHash = requireRoot(
      options.expectedSignerRegistryHash,
      'expectedSignerRegistryHash',
    );
    requireRecord(bundle, 'bundle');
    exactKeys(bundle, BUNDLE_KEYS_V0, 'bundle');
    if (bundle.schema !== BROWSER_CHECKPOINT_BUNDLE_SCHEMA_V0) {
      throw new Error('bundle schema mismatch');
    }
    requireRoot(bundle.bundle_hash, 'bundle_hash');
    const computedBundleHash = await hashV0('browser_checkpoint_bundle_v0', bodyWithoutHash(bundle, 'bundle_hash'));
    if (computedBundleHash !== bundle.bundle_hash) {
      throw new Error('bundle_hash mismatch');
    }

    const checkpoint = requireRecord(bundle.target_checkpoint, 'target_checkpoint');
    const targetHeader = requireRecord(bundle.target_header, 'target_header');
    const summary = requireRecord(bundle.verification_summary, 'verification_summary');
    const registry = requireRecord(bundle.signer_registry, 'signer_registry');
    const capabilities = requireRecord(bundle.capabilities, 'capabilities');
    exactKeys(summary, VERIFICATION_SUMMARY_KEYS_V0, 'verification summary');
    exactKeys(capabilities, CAPABILITY_KEYS_V0, 'capabilities');
    const targetHeaderHash = await validateCheckpointHeaderBinding(checkpoint, targetHeader);
    if (
      !Array.isArray(bundle.signature_envelopes)
      || bundle.signature_envelopes.length === 0
      || bundle.signature_envelopes.length > MAX_SIGNATURE_ENVELOPES
    ) {
      throw new Error('signature_envelopes length rejected');
    }
    const fromHeight = requireNonnegativeInt(bundle.from_height, 'from_height');
    const toHeight = requireNonnegativeInt(bundle.to_height, 'to_height');
    if (fromHeight > toHeight) {
      throw new Error('from_height must be <= to_height');
    }
    if (bundle.chain_id !== checkpoint.chain_id) {
      throw new Error('bundle chain_id mismatch');
    }
    if (toHeight !== checkpoint.height) {
      throw new Error('bundle to_height mismatch');
    }
    const trustedPrevHeaderHash = requireRoot(bundle.trusted_prev_header_hash, 'trusted_prev_header_hash');
    if (trustedPrevHeaderHash !== expectedTrustedPrevHeaderHash) {
      throw new Error('trusted_prev_header_hash trust anchor mismatch');
    }

    if (summary.schema !== BROWSER_CHECKPOINT_VERIFICATION_SUMMARY_SCHEMA_V0) {
      throw new Error('verification summary schema mismatch');
    }
    const checkpointHash = await hashV0('light_client_checkpoint_v0', checkpoint);
    if (summary.checkpoint_hash !== checkpointHash) {
      throw new Error('verification summary checkpoint_hash mismatch');
    }
    if (summary.target_header_hash !== checkpoint.header_hash || summary.target_header_hash !== targetHeaderHash) {
      throw new Error('verification summary target_header_hash mismatch');
    }
    if (summary.python_range_replay_verified !== true || capabilities.python_range_replay_verified !== true) {
      throw new Error('builder range replay verification is required');
    }
    if (capabilities.browser_shape_and_hash_verified !== true) {
      throw new Error('browser shape/hash capability is required');
    }
    if (
      summary.browser_range_replay_available !== true
      || capabilities.browser_range_replay_available !== true
      || summary.browser_range_replay_verified !== false
      || capabilities.browser_range_replay_verified !== false
    ) {
      throw new Error('browser range replay capability flags mismatch');
    }
    if (
      summary.browser_bls_quorum_available !== false
      || summary.browser_bls_quorum_verified !== false
      || capabilities.browser_bls_quorum_verified !== false
    ) {
      throw new Error('browser BLS capability flags mismatch');
    }
    const rangeReplay = await replayHeaderChainV0({
      headerChain: bundle.header_chain,
      trustedPrevHeaderHash,
      fromHeight,
      toHeight,
    });
    if (rangeReplay.chainId !== bundle.chain_id) {
      throw new Error('header_chain chain_id mismatch');
    }
    if (rangeReplay.lastHeaderHash !== checkpoint.header_hash) {
      throw new Error('header_chain tip hash mismatch');
    }
    if (stableStringify(rangeReplay.tipHeader) !== stableStringify(targetHeader)) {
      throw new Error('header_chain tip must equal target_header');
    }
    const rangeSummary = requireRangeSummary(summary);
    requireRoot(summary.range_summary_hash, 'verification summary range_summary_hash');
    const rangeSummaryHash = await hashV0('browser_checkpoint_range_summary_v0', rangeSummary);
    if (rangeSummaryHash !== summary.range_summary_hash) {
      throw new Error('verification summary range_summary_hash mismatch');
    }
    if (
      rangeSummary.from_height !== bundle.from_height
      || rangeSummary.to_height !== bundle.to_height
      || rangeSummary.trusted_prev_header_hash !== trustedPrevHeaderHash
      || rangeSummary.last_header_hash !== rangeReplay.lastHeaderHash
      || stableStringify(rangeSummary.checked_heights) !== stableStringify(rangeReplay.checkedHeights)
    ) {
      throw new Error('verification summary range_summary mismatch');
    }
    // Builder-trust mode skips cryptographic signature verification only. It
    // still binds the registry contents to the caller-pinned registry hash.
    const { validateSignerRegistryV0 } = await import('./zenoBlsVerifier.js');
    const signerRegistry = await validateSignerRegistryV0(registry);
    requireRoot(signerRegistry.registry_hash, 'signer registry hash');
    if (signerRegistry.registry_hash !== expectedSignerRegistryHash) {
      throw new Error('signer registry trust anchor mismatch');
    }
    requireNonnegativeInt(signerRegistry.threshold, 'signer registry threshold');
    const signatureSetRoot = await hashV0('light_client_signature_set_root_v0', {
      registry_hash: signerRegistry.registry_hash,
      payload_kind: 'checkpoint',
      threshold: signerRegistry.threshold,
    });
    if (checkpoint.signature_set_root !== signatureSetRoot) {
      throw new Error('checkpoint signature_set_root mismatch');
    }
    if (summary.expected_signature_set_root !== signatureSetRoot) {
      throw new Error('verification summary signature_set_root mismatch');
    }
    if (summary.registry_hash !== signerRegistry.registry_hash) {
      throw new Error('verification summary registry_hash mismatch');
    }
    requireRoot(summary.quorum_report_hash, 'verification summary quorum_report_hash');
    const acceptedWeight = requireNonnegativeInt(summary.accepted_weight, 'verification summary accepted_weight');
    const threshold = requireNonnegativeInt(summary.threshold, 'verification summary threshold');
    if (threshold <= 0 || acceptedWeight <= 0 || threshold !== signerRegistry.threshold || acceptedWeight < threshold) {
      throw new Error('verification summary threshold mismatch');
    }
    if (summary.python_bls_quorum_verified !== true || capabilities.python_bls_quorum_verified !== true) {
      throw new Error('builder BLS quorum verification is required');
    }
    let browserBlsVerified = false;
    let browserBlsAcceptedWeight = null;
    const trustModel = requireIndependentBls ? 'independent_bls' : 'builder_bls_claim';
    if (requireIndependentBls) {
      // Lazy-import the BLS verifier so consumers who don't need it pay
      // zero cost in load time + bundle size.
      const { verifyBlsQuorumV0 } = await import('./zenoBlsVerifier.js');
      const result = await verifyBlsQuorumV0(bundle, { expectedPayloadHash: checkpointHash });
      if (!result.ok) {
        throw new Error(`independent BLS verification failed: ${result.error}`);
      }
      if (result.payloadHash !== checkpointHash) {
        throw new Error('independent BLS verification payload hash mismatch');
      }
      if (result.quorumReportHash !== summary.quorum_report_hash) {
        throw new Error('independent BLS verification quorum report hash mismatch');
      }
      if (result.acceptedWeight !== acceptedWeight) {
        throw new Error('independent BLS verification accepted weight mismatch');
      }
      browserBlsVerified = true;
      browserBlsAcceptedWeight = result.acceptedWeight;
    }
    return {
      ok: true,
      status: requireIndependentBls ? 'accepted' : 'accepted_with_builder_bls_trust',
      trust_model: trustModel,
      bundle_hash: bundle.bundle_hash,
      chain_id: bundle.chain_id,
      height: checkpoint.height,
      checkpoint_hash: checkpointHash,
      target_header_hash: targetHeaderHash,
      trusted_prev_header_hash: trustedPrevHeaderHash,
      signer_registry_hash: signerRegistry.registry_hash,
      browser_range_replay_verified: true,
      browser_range_last_header_hash: rangeReplay.lastHeaderHash,
      browser_bls_quorum_verified: browserBlsVerified,
      browser_bls_accepted_weight: browserBlsAcceptedWeight,
      builder_bls_quorum_verified: true,
      gaps,
    };
  } catch (err) {
    gaps.push(err?.message || 'browser checkpoint bundle rejected');
    return {
      ok: false,
      status: 'rejected',
      gaps,
      browser_bls_quorum_verified: false,
      builder_bls_quorum_verified: false,
    };
  }
}

async function validateWalletSyncStateInternal(state) {
  const obj = requireRecord(state, 'wallet sync state');
  exactKeys(obj, WALLET_SYNC_STATE_KEYS_V0, 'wallet sync state');
  if (obj.schema !== BROWSER_WALLET_SYNC_STATE_SCHEMA_V0) {
    throw new Error('wallet sync state schema mismatch');
  }
  requireNonEmptyString(obj.surface, 'wallet sync state surface');
  requireNonEmptyString(obj.chain_id, 'wallet sync state chain_id');
  requireNonnegativeInt(obj.height, 'wallet sync state height');
  requireRoot(obj.app_hash, 'wallet sync state app_hash');
  requireRoot(obj.target_header_hash, 'wallet sync state target_header_hash');
  requireRoot(obj.checkpoint_hash, 'wallet sync state checkpoint_hash');
  requireRoot(obj.signer_registry_hash, 'wallet sync state signer_registry_hash');
  if (!['independent_bls', 'builder_bls_claim'].includes(obj.trust_model)) {
    throw new Error('wallet sync state trust_model mismatch');
  }
  requireRoot(obj.bundle_hash, 'wallet sync state bundle_hash');
  requireNonnegativeInt(obj.updated_at_ms, 'wallet sync state updated_at_ms');
  requireRoot(obj.state_hash, 'wallet sync state state_hash');
  const body = bodyWithoutHash(obj, 'state_hash');
  const expected = await hashV0('wallet_sync_state_v0', body);
  if (obj.state_hash !== expected) {
    throw new Error('wallet sync state hash mismatch');
  }
}

export async function advanceWalletSyncStateV0({
  currentState = null,
  bundle,
  surface = 'wallet',
  updatedAtMs = Date.now(),
  requireIndependentBls = undefined,
  trustBuilderBls = false,
  expectedTrustedPrevHeaderHash = null,
  expectedSignerRegistryHash = null,
} = {}) {
  let validatedCurrentState = null;
  if (currentState) {
    try {
      await validateWalletSyncStateInternal(currentState);
      validatedCurrentState = currentState;
    } catch (err) {
      return {
        ok: false,
        status: 'rejected',
        gaps: [err?.message || 'wallet sync state rejected'],
      };
    }
  }

  const bundleCheckpoint = isRecord(bundle) && isRecord(bundle.target_checkpoint) ? bundle.target_checkpoint : null;
  const candidateHeight = bundleCheckpoint && Number.isSafeInteger(bundleCheckpoint.height)
    ? bundleCheckpoint.height
    : null;
  if (
    validatedCurrentState
    && candidateHeight !== null
    && candidateHeight < validatedCurrentState.height
  ) {
    return { ok: false, status: 'rejected', gaps: ['wallet sync rollback rejected'] };
  }

  let effectiveExpectedTrustedPrevHeaderHash = expectedTrustedPrevHeaderHash;
  if (
    effectiveExpectedTrustedPrevHeaderHash === null
    && validatedCurrentState
    && candidateHeight !== null
    && candidateHeight > validatedCurrentState.height
  ) {
    // Continue only from the header the wallet already accepted; a replay from
    // a different root is an alternate history even if its constituent hashes line up.
    effectiveExpectedTrustedPrevHeaderHash = validatedCurrentState.target_header_hash;
  }
  const effectiveExpectedSignerRegistryHash = expectedSignerRegistryHash
    ?? validatedCurrentState?.signer_registry_hash
    ?? null;

  const verification = await verifyBrowserCheckpointBundleV0(bundle, {
    requireIndependentBls,
    trustBuilderBls,
    expectedTrustedPrevHeaderHash: effectiveExpectedTrustedPrevHeaderHash,
    expectedSignerRegistryHash: effectiveExpectedSignerRegistryHash,
  });
  if (!verification.ok) {
    return { ok: false, status: 'rejected', gaps: verification.gaps };
  }
  const checkpoint = bundle.target_checkpoint;
  if (validatedCurrentState) {
    if (validatedCurrentState.chain_id !== checkpoint.chain_id) {
      return { ok: false, status: 'rejected', gaps: ['wallet sync chain_id mismatch'] };
    }
    if (checkpoint.height < validatedCurrentState.height) {
      return { ok: false, status: 'rejected', gaps: ['wallet sync rollback rejected'] };
    }
    if (
      checkpoint.height === validatedCurrentState.height
      && (
        validatedCurrentState.checkpoint_hash !== verification.checkpoint_hash
        || validatedCurrentState.app_hash !== checkpoint.app_hash
      )
    ) {
      return { ok: false, status: 'rejected', gaps: ['wallet sync same-height drift rejected'] };
    }
    if (
      checkpoint.height > validatedCurrentState.height
      && verification.trusted_prev_header_hash !== validatedCurrentState.target_header_hash
    ) {
      return { ok: false, status: 'rejected', gaps: ['wallet sync extension root mismatch'] };
    }
  }
  const body = {
    schema: BROWSER_WALLET_SYNC_STATE_SCHEMA_V0,
    surface: requireNonEmptyString(surface, 'surface'),
    chain_id: checkpoint.chain_id,
    height: checkpoint.height,
    app_hash: checkpoint.app_hash,
    target_header_hash: verification.target_header_hash,
    checkpoint_hash: verification.checkpoint_hash,
    signer_registry_hash: verification.signer_registry_hash,
    trust_model: verification.trust_model,
    bundle_hash: bundle.bundle_hash,
    updated_at_ms: requireNonnegativeInt(Math.trunc(updatedAtMs), 'updated_at_ms'),
  };
  return {
    ok: true,
    status: verification.status,
    state: {
      ...body,
      state_hash: await hashV0('wallet_sync_state_v0', body),
    },
    verification,
  };
}
