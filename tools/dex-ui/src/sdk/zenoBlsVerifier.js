/**
 * Independent BLS12-381 G2 Basic signature verification for ZenoLedger
 * signed-artifact envelopes.
 *
 * Mirrors `src/integration/zeno_ledger_signature.py::validate_bls_signed_artifact_envelope_v0`
 * byte-for-byte:
 *
 *   1. Build the signing body (schema, algorithm, payload_kind, payload_hash,
 *      signer_id, key_id, public_key) — order does NOT matter because the body
 *      is canonical-JSON sorted by key.
 *   2. Wrap the body in `{"domain": "zenodex.zeno_ledger.signed_artifact.v0", "body": ...}`.
 *   3. Compute SHA-256 of the canonical JSON bytes.
 *   4. Verify the 96-byte G2 signature against the 48-byte G1 public key.
 *
 * Why we use @noble/curves:
 *   - Pure JS, audited, no native bindings — works in browser AND Node.
 *   - `bls12_381.verify` defaults match py_ecc.bls.G2Basic exactly (DST,
 *     curve point ordering, hash-to-curve).
 *
 * This module is import-light: it only loads @noble/curves when actually
 * called, so consumers that don't use independent BLS pay zero cost.
 */

import { stableStringify, hashV0, BROWSER_CHECKPOINT_BUNDLE_SCHEMA_V0 } from './zenoProofClient.js';

const SIGNED_ARTIFACT_ENVELOPE_SCHEMA_V0 = 'zenodex/zeno_ledger/signed_artifact_envelope/v0';
const SIGNER_REGISTRY_SCHEMA_V0 = 'zenodex/zeno_ledger/signer_registry/v0';
const SIGNATURE_QUORUM_REPORT_SCHEMA_V0 = 'zenodex/zeno_ledger/signature_quorum_report/v0';
const SIGNED_ARTIFACT_ALGORITHM_BLS_V0 = 'bls12-381-g2-basic-release-v0';
const SIGNATURE_DOMAIN = 'zenodex.zeno_ledger.signed_artifact.v0';
const PUBLIC_KEY_HEX_LEN = 96; // 48 bytes
const SIGNATURE_HEX_LEN = 192; // 96 bytes
const ROOT_HEX_LEN = 64; // 32 bytes
const MAX_SIGNATURE_ENVELOPES = 64;

const textEncoder = new TextEncoder();
const ROOT_RE = /^0x[0-9a-f]{64}$/;
const PUBLIC_KEY_RE = /^0x[0-9a-f]{96}$/;
const SIGNATURE_RE = /^0x[0-9a-f]{192}$/;

function exactKeys(obj, keys) {
  const actual = Object.keys(obj).sort();
  const expected = [...keys].sort();
  return actual.length === expected.length && actual.every((key, index) => key === expected[index]);
}

function requireNonEmptyString(value, name) {
  if (typeof value !== 'string' || value === '') {
    throw new Error(`${name} must be a non-empty string`);
  }
  return value;
}

function requirePositiveSafeInt(value, name) {
  if (!Number.isSafeInteger(value) || value <= 0) {
    throw new Error(`${name} must be a positive safe integer`);
  }
  return value;
}

function requireRoot(value, name) {
  if (typeof value !== 'string' || !ROOT_RE.test(value)) {
    throw new Error(`${name} must be a canonical 32-byte root`);
  }
  return value;
}

function requirePublicKey(value, name = 'public_key') {
  if (typeof value !== 'string' || !PUBLIC_KEY_RE.test(value)) {
    throw new Error(`${name} must be lowercase canonical 0x-prefixed BLS public-key hex`);
  }
  return value;
}

function requireSignature(value, name = 'signature') {
  if (typeof value !== 'string' || !SIGNATURE_RE.test(value)) {
    throw new Error(`${name} must be lowercase canonical 0x-prefixed BLS signature hex`);
  }
  return value;
}

function hexToBytes(hex, expectedLen) {
  if (typeof hex !== 'string') {
    throw new Error('hex must be a string');
  }
  const body = hex.startsWith('0x') ? hex.slice(2) : hex;
  if (body.length !== expectedLen) {
    throw new Error(`hex must be exactly ${expectedLen} chars (got ${body.length})`);
  }
  if (!/^[0-9a-f]+$/.test(body)) {
    throw new Error('hex must be lowercase canonical');
  }
  const out = new Uint8Array(body.length / 2);
  for (let i = 0; i < out.length; i += 1) {
    out[i] = parseInt(body.slice(i * 2, i * 2 + 2), 16);
  }
  return out;
}

async function sha256(bytes) {
  const webCrypto = globalThis.crypto?.subtle;
  if (webCrypto) {
    const digest = await webCrypto.digest('SHA-256', bytes);
    return new Uint8Array(digest);
  }
  const { createHash } = await import('node:crypto');
  return new Uint8Array(createHash('sha256').update(bytes).digest());
}

function envelopeBody(envelope) {
  return {
    schema: SIGNED_ARTIFACT_ENVELOPE_SCHEMA_V0,
    algorithm: SIGNED_ARTIFACT_ALGORITHM_BLS_V0,
    payload_kind: requireNonEmptyString(envelope.payload_kind, 'envelope.payload_kind'),
    payload_hash: requireRoot(envelope.payload_hash, 'envelope.payload_hash'),
    signer_id: requireNonEmptyString(envelope.signer_id, 'envelope.signer_id'),
    key_id: requireNonEmptyString(envelope.key_id, 'envelope.key_id'),
    public_key: requirePublicKey(envelope.public_key, 'envelope.public_key'),
  };
}

async function signatureMessageDigest(body) {
  const canonical = stableStringify({ body, domain: SIGNATURE_DOMAIN });
  return sha256(textEncoder.encode(canonical));
}

let _bls = null;
async function getBls() {
  if (_bls === null) {
    const mod = await import('@noble/curves/bls12-381');
    _bls = mod.bls12_381;
  }
  return _bls;
}

/**
 * Verify a single BLS-signed envelope against its declared public key.
 *
 * Returns `{ ok: true }` on success, or `{ ok: false, error: <string> }` on
 * any structural or cryptographic failure. Never raises in the success path;
 * raises only on argument type errors (invalid inputs to the function itself,
 * not invalid envelopes).
 */
export async function verifyBlsEnvelopeV0(envelope, { expectedPayloadKind, expectedPayloadHash } = {}) {
  if (envelope === null || typeof envelope !== 'object') {
    return { ok: false, error: 'envelope must be an object' };
  }
  if (!exactKeys(envelope, [
    'schema',
    'algorithm',
    'payload_kind',
    'payload_hash',
    'signer_id',
    'key_id',
    'public_key',
    'signature',
    'envelope_hash',
  ])) {
    return { ok: false, error: 'signed artifact envelope keys mismatch' };
  }
  if (envelope.algorithm !== SIGNED_ARTIFACT_ALGORITHM_BLS_V0) {
    return { ok: false, error: 'envelope algorithm is not BLS' };
  }
  if (envelope.schema !== SIGNED_ARTIFACT_ENVELOPE_SCHEMA_V0) {
    return { ok: false, error: 'envelope schema mismatch' };
  }
  if (typeof envelope.signer_id !== 'string' || !envelope.signer_id) {
    return { ok: false, error: 'envelope signer_id must be a non-empty string' };
  }
  if (typeof envelope.key_id !== 'string' || !envelope.key_id) {
    return { ok: false, error: 'envelope key_id must be a non-empty string' };
  }
  if (typeof envelope.payload_kind !== 'string' || !envelope.payload_kind) {
    return { ok: false, error: 'envelope payload_kind must be a non-empty string' };
  }
  if (expectedPayloadKind !== undefined && envelope.payload_kind !== expectedPayloadKind) {
    return { ok: false, error: 'envelope payload_kind mismatch' };
  }
  try {
    requireRoot(envelope.payload_hash, 'envelope.payload_hash');
    requireRoot(envelope.envelope_hash, 'envelope.envelope_hash');
  } catch (err) {
    return { ok: false, error: err?.message || 'envelope root validation failed' };
  }
  if (expectedPayloadHash !== undefined && envelope.payload_hash !== expectedPayloadHash) {
    return { ok: false, error: 'envelope payload_hash mismatch' };
  }
  const body = (() => {
    try {
      return envelopeBody(envelope);
    } catch (err) {
      return { error: err?.message || 'envelope body rejected' };
    }
  })();
  if (body.error) {
    return { ok: false, error: body.error };
  }
  let signature;
  try {
    signature = requireSignature(envelope.signature, 'envelope.signature');
  } catch (err) {
    return { ok: false, error: err?.message || 'envelope signature validation failed' };
  }
  const envelopeForHash = { ...body, signature };
  const expectedEnvelopeHash = await hashV0('signed_artifact_envelope_v0', envelopeForHash);
  if (envelope.envelope_hash !== expectedEnvelopeHash) {
    return { ok: false, error: 'signed artifact envelope signature binding mismatch' };
  }

  let pubkeyBytes;
  let signatureBytes;
  try {
    pubkeyBytes = hexToBytes(envelope.public_key, PUBLIC_KEY_HEX_LEN);
    signatureBytes = hexToBytes(signature, SIGNATURE_HEX_LEN);
  } catch (err) {
    return { ok: false, error: err?.message || 'envelope key/signature decode failed' };
  }

  let messageDigest;
  try {
    messageDigest = await signatureMessageDigest(body);
  } catch (err) {
    return { ok: false, error: err?.message || 'envelope signing-message hash failed' };
  }

  const bls = await getBls();
  let ok = false;
  try {
    ok = Boolean(bls.verify(signatureBytes, messageDigest, pubkeyBytes));
  } catch (err) {
    return { ok: false, error: err?.message || 'envelope BLS verify threw' };
  }
  if (!ok) {
    return { ok: false, error: 'envelope BLS signature invalid' };
  }
  return { ok: true, envelopeHash: expectedEnvelopeHash };
}

async function validateSignerRegistryV0(registry) {
  if (registry === null || typeof registry !== 'object') {
    throw new Error('signer registry must be an object');
  }
  if (!exactKeys(registry, ['schema', 'registry_id', 'payload_kind', 'threshold', 'signers', 'registry_hash'])) {
    throw new Error('signer registry keys mismatch');
  }
  if (registry.schema !== SIGNER_REGISTRY_SCHEMA_V0) {
    throw new Error('signer registry schema mismatch');
  }
  const registryId = requireNonEmptyString(registry.registry_id, 'registry.registry_id');
  const payloadKind = requireNonEmptyString(registry.payload_kind, 'registry.payload_kind');
  if (payloadKind !== 'checkpoint') {
    throw new Error('signer registry payload_kind must be checkpoint');
  }
  const threshold = requirePositiveSafeInt(registry.threshold, 'registry.threshold');
  requireRoot(registry.registry_hash, 'registry.registry_hash');
  if (!Array.isArray(registry.signers) || registry.signers.length === 0) {
    throw new Error('signer registry must contain at least one signer');
  }

  const entries = [];
  const seenIdentities = new Set();
  const seenPublicKeys = new Set();
  let activeWeight = 0;
  for (let i = 0; i < registry.signers.length; i += 1) {
    const signer = registry.signers[i];
    if (signer === null || typeof signer !== 'object') {
      throw new Error(`signers[${i}] must be an object`);
    }
    if (!exactKeys(signer, ['signer_id', 'key_id', 'algorithm', 'public_key', 'weight', 'status', 'signer_hash'])) {
      throw new Error(`signers[${i}] keys mismatch`);
    }
    const status = requireNonEmptyString(signer.status, `signers[${i}].status`);
    if (!['active', 'revoked'].includes(status)) {
      throw new Error(`signers[${i}] status must be active or revoked`);
    }
    if (signer.algorithm !== SIGNED_ARTIFACT_ALGORITHM_BLS_V0) {
      throw new Error(`signers[${i}] algorithm is not allowed`);
    }
    const entryBody = {
      signer_id: requireNonEmptyString(signer.signer_id, `signers[${i}].signer_id`),
      key_id: requireNonEmptyString(signer.key_id, `signers[${i}].key_id`),
      algorithm: SIGNED_ARTIFACT_ALGORITHM_BLS_V0,
      public_key: requirePublicKey(signer.public_key, `signers[${i}].public_key`),
      weight: requirePositiveSafeInt(signer.weight, `signers[${i}].weight`),
      status,
    };
    const identity = `${entryBody.signer_id}\u0001${entryBody.key_id}`;
    if (seenIdentities.has(identity)) {
      throw new Error('duplicate signer_id/key_id');
    }
    if (seenPublicKeys.has(entryBody.public_key)) {
      throw new Error('duplicate signer public_key');
    }
    seenIdentities.add(identity);
    seenPublicKeys.add(entryBody.public_key);
    if (status === 'active') {
      activeWeight += entryBody.weight;
      if (!Number.isSafeInteger(activeWeight)) {
        throw new Error('active signer weight exceeds safe integer range');
      }
    }
    const expectedSigner = {
      ...entryBody,
      signer_hash: await hashV0('signer_registry_entry_v0', entryBody),
    };
    if (stableStringify(signer) !== stableStringify(expectedSigner)) {
      throw new Error(`signers[${i}] binding mismatch`);
    }
    entries.push(expectedSigner);
  }
  entries.sort((a, b) => (
    a.signer_id < b.signer_id
      ? -1
      : a.signer_id > b.signer_id
        ? 1
        : a.key_id < b.key_id
          ? -1
          : a.key_id > b.key_id
            ? 1
            : 0
  ));
  if (threshold > activeWeight) {
    throw new Error('threshold exceeds active signer weight');
  }
  const expectedBody = {
    schema: SIGNER_REGISTRY_SCHEMA_V0,
    registry_id: registryId,
    payload_kind: payloadKind,
    threshold,
    signers: entries,
  };
  const expectedRegistry = {
    ...expectedBody,
    registry_hash: await hashV0('signer_registry_v0', expectedBody),
  };
  if (stableStringify(registry) !== stableStringify(expectedRegistry)) {
    throw new Error('signer registry binding mismatch');
  }
  return expectedRegistry;
}

/**
 * Verify the BLS signature quorum for a browser checkpoint bundle.
 *
 * Mirrors `src/integration/zeno_ledger_signer_registry.py::verify_signature_quorum_v0`:
 *
 *  - Each envelope must correspond to an *active* signer in the registry,
 *    matched by both signer_id AND key_id.
 *  - Each envelope's algorithm must match the registry's expected algorithm.
 *  - Each envelope's public_key must match the registry entry's public_key.
 *  - Each envelope's signature must verify cryptographically.
 *  - Duplicate signer identities or BLS public keys are rejected.
 *  - Sum of accepted weights must be ≥ registry.threshold.
 *
 * Returns `{ ok: true, acceptedWeight, threshold, acceptedSigners: [...] }`
 * on success, or `{ ok: false, error: <string>, accepted: [...] }` with the
 * specific failure cause.
 */
export async function verifyBlsQuorumV0(bundle, { expectedPayloadHash } = {}) {
  if (bundle === null || typeof bundle !== 'object') {
    return { ok: false, error: 'bundle must be an object' };
  }
  if (bundle.schema !== BROWSER_CHECKPOINT_BUNDLE_SCHEMA_V0) {
    return { ok: false, error: 'bundle schema mismatch' };
  }
  let registry;
  try {
    registry = await validateSignerRegistryV0(bundle.signer_registry);
  } catch (err) {
    return { ok: false, error: err?.message || 'signer registry rejected' };
  }
  const envelopes = bundle.signature_envelopes;
  if (!Array.isArray(envelopes) || envelopes.length === 0 || envelopes.length > MAX_SIGNATURE_ENVELOPES) {
    return { ok: false, error: 'bundle.signature_envelopes length rejected' };
  }
  const payloadHash = expectedPayloadHash ?? envelopes[0]?.payload_hash;
  try {
    requireRoot(payloadHash, 'expected payload_hash');
  } catch (err) {
    return { ok: false, error: err?.message || 'expected payload_hash rejected' };
  }

  // Build an active-signer lookup indexed by (signer_id, key_id).
  const activeByIdentity = new Map();
  for (const signer of registry.signers) {
    if (signer === null || typeof signer !== 'object') {
      return { ok: false, error: 'signer registry entry must be an object' };
    }
    if (signer.status === 'active') {
      const identity = `${signer.signer_id}\u0001${signer.key_id}`;
      activeByIdentity.set(identity, signer);
    }
  }

  const seenIdentities = new Set();
  const seenPublicKeys = new Set();
  const accepted = [];
  let acceptedWeight = 0;
  const payloadKind = 'checkpoint';

  for (let i = 0; i < envelopes.length; i += 1) {
    const envelope = envelopes[i];
    if (envelope === null || typeof envelope !== 'object') {
      return { ok: false, error: `envelope[${i}] must be an object`, accepted };
    }
    if (envelope.payload_hash !== payloadHash) {
      return { ok: false, error: `envelope[${i}] payload_hash diverges from envelope[0]`, accepted };
    }
    const identity = `${envelope.signer_id}\u0001${envelope.key_id}`;
    if (seenIdentities.has(identity)) {
      return { ok: false, error: `envelope[${i}] duplicate (signer_id, key_id)`, accepted };
    }
    seenIdentities.add(identity);
    const signer = activeByIdentity.get(identity);
    if (signer === undefined) {
      return { ok: false, error: `envelope[${i}] signer not active in registry`, accepted };
    }
    if (envelope.public_key !== signer.public_key) {
      return { ok: false, error: `envelope[${i}] public_key does not match registry`, accepted };
    }
    if (envelope.algorithm !== signer.algorithm) {
      return { ok: false, error: `envelope[${i}] algorithm does not match registry`, accepted };
    }
    if (seenPublicKeys.has(signer.public_key)) {
      return { ok: false, error: 'duplicate envelope signer public_key', accepted };
    }
    const verification = await verifyBlsEnvelopeV0(envelope, {
      expectedPayloadKind: payloadKind,
      expectedPayloadHash: payloadHash,
    });
    if (!verification.ok) {
      return { ok: false, error: `envelope[${i}] ${verification.error}`, accepted };
    }
    seenPublicKeys.add(signer.public_key);
    const weight = requirePositiveSafeInt(signer.weight, `signers[${i}].weight`);
    acceptedWeight += weight;
    if (!Number.isSafeInteger(acceptedWeight)) {
      return { ok: false, error: 'accepted weight exceeds safe integer range', accepted };
    }
    accepted.push({ signer_id: signer.signer_id, key_id: signer.key_id, weight });
  }

  if (acceptedWeight < registry.threshold) {
    return {
      ok: false,
      error: `accepted weight ${acceptedWeight} below threshold ${registry.threshold}`,
      accepted,
      acceptedWeight,
      threshold: registry.threshold,
    };
  }
  const quorumBody = {
    schema: SIGNATURE_QUORUM_REPORT_SCHEMA_V0,
    registry_hash: registry.registry_hash,
    payload_kind: payloadKind,
    payload_hash: payloadHash,
    threshold: registry.threshold,
    accepted_weight: acceptedWeight,
    accepted_signatures: accepted.map((entry, index) => ({
      ...entry,
      envelope_hash: envelopes[index].envelope_hash,
    })),
  };
  return {
    ok: true,
    acceptedWeight,
    threshold: registry.threshold,
    acceptedSigners: accepted,
    acceptedSignatures: quorumBody.accepted_signatures,
    quorumReportHash: await hashV0('signature_quorum_report_v0', quorumBody),
    payloadKind,
    payloadHash,
  };
}
