/**
 * Cross-language BLS verification tests.
 *
 * Each test builds a signed envelope in Python (using ``py_ecc.bls.G2Basic``)
 * and hands it to the JS verifier (``@noble/curves/bls12-381``). If both
 * libraries agree on the signature, we have cross-language confidence that
 * a browser running the SDK reaches the same accept/reject verdict as the
 * Python builder.
 *
 * The Python side is invoked via ``child_process.spawnSync`` so this test
 * doubles as a smoke test that the SDK package can fall back to a Python
 * companion process for envelope generation if needed.
 */

import assert from 'node:assert/strict';
import test from 'node:test';
import { spawnSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, resolve } from 'node:path';

import { verifyBlsEnvelopeV0, verifyBlsQuorumV0 } from './zenoBlsVerifier.js';
import {
  BROWSER_CHECKPOINT_BUNDLE_SCHEMA_V0,
  hashV0,
  verifyBrowserCheckpointBundleV0,
} from './zenoProofClient.js';

const _here = dirname(fileURLToPath(import.meta.url));
const REPO_ROOT = resolve(_here, '../../../..');
const PUBLIC_KEY_DEDUPE_VECTORS = JSON.parse(readFileSync(
  resolve(REPO_ROOT, 'tests/fixtures/zeno_bls_public_key_dedupe_v0.json'),
  'utf-8',
));

async function buildSelfConsistentRegistryVector(vector) {
  const signers = [];
  for (const signer of vector.signers) {
    const body = {
      signer_id: signer.signer_id,
      key_id: signer.key_id,
      algorithm: 'bls12-381-g2-basic-release-v0',
      public_key: signer.public_key,
      weight: signer.weight,
      status: signer.status,
    };
    signers.push({
      ...body,
      signer_hash: await hashV0('signer_registry_entry_v0', body),
    });
  }
  signers.sort((a, b) => (
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
  const body = {
    schema: 'zenodex/zeno_ledger/signer_registry/v0',
    registry_id: vector.registry_id,
    payload_kind: 'checkpoint',
    threshold: vector.threshold,
    signers,
  };
  return {
    ...body,
    registry_hash: await hashV0('signer_registry_v0', body),
  };
}

/** Run a Python snippet against the repo's venv-equivalent interpreter. */
function pyRun(snippet) {
  const proc = spawnSync('python3', ['-c', snippet], {
    cwd: REPO_ROOT,
    env: { ...process.env, PYTHONPATH: REPO_ROOT },
    encoding: 'utf-8',
    timeout: 30_000,
  });
  if (proc.status !== 0) {
    throw new Error(`Python failed: ${proc.stderr || proc.stdout}`);
  }
  return JSON.parse(proc.stdout);
}

function pyEccAvailable() {
  const probe = spawnSync('python3', ['-c', "import py_ecc.bls; print('ok')"], {
    cwd: REPO_ROOT,
    encoding: 'utf-8',
    timeout: 10_000,
  });
  return probe.status === 0;
}

const _PY_ECC = pyEccAvailable();

/** Build one BLS envelope in Python via the production code path. */
function buildPyEnvelope({ payloadHash, signerId, keyId, privateKeyHex }) {
  const snippet = `
import json
from src.integration.zeno_ledger_signature import build_bls_signed_artifact_envelope_v0
env = build_bls_signed_artifact_envelope_v0(
    payload_kind='checkpoint',
    payload_hash=${JSON.stringify(payloadHash)},
    signer_id=${JSON.stringify(signerId)},
    key_id=${JSON.stringify(keyId)},
    private_key_hex=${JSON.stringify(privateKeyHex)},
)
print(json.dumps(env, sort_keys=True))
`;
  return pyRun(snippet);
}

function buildPySignerEntry({ signerId, keyId, privateKeyHex, weight = 1, status = 'active' }) {
  const snippet = `
import json
from src.integration.zeno_ledger_signer_registry import build_signer_registry_v0
from src.integration.zeno_ledger_signature import bls_public_key_hex_from_private_key_v0
pk = bls_public_key_hex_from_private_key_v0(${JSON.stringify(privateKeyHex)})
reg = build_signer_registry_v0(
    registry_id='sdk-cross-lang',
    payload_kind='checkpoint',
    threshold=${weight},
    signers=[{
        'signer_id': ${JSON.stringify(signerId)},
        'key_id': ${JSON.stringify(keyId)},
        'public_key': pk,
        'weight': ${weight},
        'status': ${JSON.stringify(status)},
    }],
)
print(json.dumps(reg, sort_keys=True))
`;
  return pyRun(snippet);
}

test('envelope signed by py_ecc verifies under noble', { skip: !_PY_ECC }, async () => {
  const privateKeyHex = `0x${'11'.repeat(32)}`;
  const payloadHash = `0x${'ab'.repeat(32)}`;
  const envelope = buildPyEnvelope({
    payloadHash,
    signerId: 'alice',
    keyId: 'k1',
    privateKeyHex,
  });
  const result = await verifyBlsEnvelopeV0(envelope, {
    expectedPayloadKind: 'checkpoint',
    expectedPayloadHash: payloadHash,
  });
  assert.equal(result.ok, true, result.error);
});

test('envelope with tampered signature rejected', { skip: !_PY_ECC }, async () => {
  const envelope = buildPyEnvelope({
    payloadHash: `0x${'ab'.repeat(32)}`,
    signerId: 'alice',
    keyId: 'k1',
    privateKeyHex: `0x${'11'.repeat(32)}`,
  });
  // Flip the first hex digit of the signature.
  const flipped = envelope.signature.slice(0, 2) + (envelope.signature[2] === '8' ? '7' : '8') + envelope.signature.slice(3);
  const tampered = { ...envelope, signature: flipped };
  const result = await verifyBlsEnvelopeV0(tampered);
  assert.equal(result.ok, false);
  // Verify error is meaningful — either an invalid-signature reject, a
  // decode/verify error, or a curve-validity failure raised by noble when
  // the tampered bytes don't decode to a valid G2 point.
  assert.match(result.error, /invalid|verify|signature|zero point|not on curve|deserialize/i);
});

test('envelope with swapped pubkey rejected', { skip: !_PY_ECC }, async () => {
  const envelope = buildPyEnvelope({
    payloadHash: `0x${'cd'.repeat(32)}`,
    signerId: 'bob',
    keyId: 'k2',
    privateKeyHex: `0x${'22'.repeat(32)}`,
  });
  // Compute a different pubkey for an unrelated private key, then swap it in.
  const other = buildPyEnvelope({
    payloadHash: `0x${'ef'.repeat(32)}`,
    signerId: 'attacker',
    keyId: 'k',
    privateKeyHex: `0x${'33'.repeat(32)}`,
  });
  const swapped = { ...envelope, public_key: other.public_key };
  const result = await verifyBlsEnvelopeV0(swapped);
  assert.equal(result.ok, false);
});

test('envelope with mismatched payload_hash rejected', { skip: !_PY_ECC }, async () => {
  const envelope = buildPyEnvelope({
    payloadHash: `0x${'11'.repeat(32)}`,
    signerId: 'alice',
    keyId: 'k1',
    privateKeyHex: `0x${'1a'.repeat(32)}`,
  });
  const result = await verifyBlsEnvelopeV0(envelope, {
    expectedPayloadHash: `0x${'22'.repeat(32)}`, // wrong expected hash
  });
  assert.equal(result.ok, false);
  assert.match(result.error, /payload_hash mismatch/);
});

test('envelope with non-canonical hex rejected', { skip: !_PY_ECC }, async () => {
  const envelope = buildPyEnvelope({
    payloadHash: `0x${'11'.repeat(32)}`,
    signerId: 'alice',
    keyId: 'k1',
    privateKeyHex: `0x${'1a'.repeat(32)}`,
  });
  // Uppercase the signature hex.
  const upperSig = '0x' + envelope.signature.slice(2).toUpperCase();
  const result = await verifyBlsEnvelopeV0({ ...envelope, signature: upperSig });
  assert.equal(result.ok, false);
  assert.match(result.error, /lowercase canonical/);
});

test('quorum accepts when signers reach threshold', { skip: !_PY_ECC }, async () => {
  // Build two signers each with weight 1, threshold 2 → unanimity.
  const payloadHash = `0x${'ab'.repeat(32)}`;
  const alice = buildPyEnvelope({
    payloadHash,
    signerId: 'alice',
    keyId: 'k1',
    privateKeyHex: `0x${'11'.repeat(32)}`,
  });
  const bob = buildPyEnvelope({
    payloadHash,
    signerId: 'bob',
    keyId: 'k1',
    privateKeyHex: `0x${'22'.repeat(32)}`,
  });
  // Build a manual registry with both signers, threshold 2.
  const registrySnippet = `
import json
from src.integration.zeno_ledger_signer_registry import build_signer_registry_v0
from src.integration.zeno_ledger_signature import bls_public_key_hex_from_private_key_v0
reg = build_signer_registry_v0(
    registry_id='sdk-cross-lang',
    payload_kind='checkpoint',
    threshold=2,
    signers=[
        {
            'signer_id': 'alice', 'key_id': 'k1',
            'public_key': bls_public_key_hex_from_private_key_v0('0x' + '11' * 32),
            'weight': 1, 'status': 'active',
        },
        {
            'signer_id': 'bob', 'key_id': 'k1',
            'public_key': bls_public_key_hex_from_private_key_v0('0x' + '22' * 32),
            'weight': 1, 'status': 'active',
        },
    ],
)
print(json.dumps(reg, sort_keys=True))
`;
  const registry = pyRun(registrySnippet);
  const bundle = {
    schema: BROWSER_CHECKPOINT_BUNDLE_SCHEMA_V0,
    signer_registry: registry,
    signature_envelopes: [alice, bob],
  };
  const result = await verifyBlsQuorumV0(bundle);
  assert.equal(result.ok, true, result.error);
  assert.equal(result.acceptedWeight, 2);
  assert.equal(result.threshold, 2);
  assert.equal(result.payloadHash, payloadHash);
  assert.match(result.quorumReportHash, /^0x[0-9a-f]{64}$/);
});

test('fixed public-key dedupe vectors match Python registry verdicts', async () => {
  assert.equal(
    PUBLIC_KEY_DEDUPE_VECTORS.schema,
    'zenodex/test/zeno_bls_public_key_dedupe_vectors/v0',
  );
  for (const vector of PUBLIC_KEY_DEDUPE_VECTORS.cases) {
    const registry = await buildSelfConsistentRegistryVector(vector);
    const result = await verifyBlsQuorumV0({
      schema: BROWSER_CHECKPOINT_BUNDLE_SCHEMA_V0,
      signer_registry: registry,
      signature_envelopes: [],
    });
    if (vector.expected_registry_status === 'rejected') {
      assert.equal(result.ok, false, vector.name);
      assert.equal(result.error, vector.expected_error, vector.name);
    } else {
      assert.equal(result.ok, false, vector.name);
      assert.equal(result.error, 'bundle.signature_envelopes length rejected', vector.name);
    }
  }
});

test('quorum rejects when expected checkpoint payload hash differs', { skip: !_PY_ECC }, async () => {
  const payloadHash = `0x${'ab'.repeat(32)}`;
  const alice = buildPyEnvelope({
    payloadHash,
    signerId: 'alice',
    keyId: 'k1',
    privateKeyHex: `0x${'11'.repeat(32)}`,
  });
  const registry = buildPySignerEntry({
    signerId: 'alice',
    keyId: 'k1',
    privateKeyHex: `0x${'11'.repeat(32)}`,
    weight: 1,
  });
  const bundle = {
    schema: BROWSER_CHECKPOINT_BUNDLE_SCHEMA_V0,
    signer_registry: registry,
    signature_envelopes: [alice],
  };
  const result = await verifyBlsQuorumV0(bundle, {
    expectedPayloadHash: `0x${'cd'.repeat(32)}`,
  });

  assert.equal(result.ok, false);
  assert.match(result.error, /payload_hash diverges|payload_hash mismatch/);
});

test('quorum rejects tampered signer registry hash', { skip: !_PY_ECC }, async () => {
  const payloadHash = `0x${'ab'.repeat(32)}`;
  const alice = buildPyEnvelope({
    payloadHash,
    signerId: 'alice',
    keyId: 'k1',
    privateKeyHex: `0x${'11'.repeat(32)}`,
  });
  const registry = buildPySignerEntry({
    signerId: 'alice',
    keyId: 'k1',
    privateKeyHex: `0x${'11'.repeat(32)}`,
    weight: 1,
  });
  const tamperedRegistry = { ...registry, registry_hash: `0x${'cd'.repeat(32)}` };
  const bundle = {
    schema: BROWSER_CHECKPOINT_BUNDLE_SCHEMA_V0,
    signer_registry: tamperedRegistry,
    signature_envelopes: [alice],
  };
  const result = await verifyBlsQuorumV0(bundle);

  assert.equal(result.ok, false);
  assert.match(result.error, /signer registry binding mismatch/);
});

test('quorum rejects tampered envelope_hash', { skip: !_PY_ECC }, async () => {
  const payloadHash = `0x${'ab'.repeat(32)}`;
  const alice = buildPyEnvelope({
    payloadHash,
    signerId: 'alice',
    keyId: 'k1',
    privateKeyHex: `0x${'11'.repeat(32)}`,
  });
  const registry = buildPySignerEntry({
    signerId: 'alice',
    keyId: 'k1',
    privateKeyHex: `0x${'11'.repeat(32)}`,
    weight: 1,
  });
  const bundle = {
    schema: BROWSER_CHECKPOINT_BUNDLE_SCHEMA_V0,
    signer_registry: registry,
    signature_envelopes: [{ ...alice, envelope_hash: `0x${'ef'.repeat(32)}` }],
  };
  const result = await verifyBlsQuorumV0(bundle);

  assert.equal(result.ok, false);
  assert.match(result.error, /envelope\[0\].*binding mismatch/);
});

test('quorum rejects when below threshold', { skip: !_PY_ECC }, async () => {
  // Build a registry with threshold 2 but only deliver one envelope.
  const payloadHash = `0x${'ab'.repeat(32)}`;
  const alice = buildPyEnvelope({
    payloadHash,
    signerId: 'alice',
    keyId: 'k1',
    privateKeyHex: `0x${'11'.repeat(32)}`,
  });
  const registrySnippet = `
import json
from src.integration.zeno_ledger_signer_registry import build_signer_registry_v0
from src.integration.zeno_ledger_signature import bls_public_key_hex_from_private_key_v0
reg = build_signer_registry_v0(
    registry_id='sdk-cross-lang',
    payload_kind='checkpoint',
    threshold=2,
    signers=[
        {
            'signer_id': 'alice', 'key_id': 'k1',
            'public_key': bls_public_key_hex_from_private_key_v0('0x' + '11' * 32),
            'weight': 1, 'status': 'active',
        },
        {
            'signer_id': 'bob', 'key_id': 'k1',
            'public_key': bls_public_key_hex_from_private_key_v0('0x' + '22' * 32),
            'weight': 1, 'status': 'active',
        },
    ],
)
print(json.dumps(reg, sort_keys=True))
`;
  const registry = pyRun(registrySnippet);
  const bundle = {
    schema: BROWSER_CHECKPOINT_BUNDLE_SCHEMA_V0,
    signer_registry: registry,
    signature_envelopes: [alice], // only one signer present
  };
  const result = await verifyBlsQuorumV0(bundle);
  assert.equal(result.ok, false);
  assert.match(result.error, /below threshold/);
});

test('quorum rejects when envelope signer is not in registry', { skip: !_PY_ECC }, async () => {
  const payloadHash = `0x${'ab'.repeat(32)}`;
  const phantom = buildPyEnvelope({
    payloadHash,
    signerId: 'phantom',
    keyId: 'k1',
    privateKeyHex: `0x${'44'.repeat(32)}`,
  });
  const registry = buildPySignerEntry({
    signerId: 'alice',
    keyId: 'k1',
    privateKeyHex: `0x${'11'.repeat(32)}`,
    weight: 1,
  });
  const bundle = {
    schema: BROWSER_CHECKPOINT_BUNDLE_SCHEMA_V0,
    signer_registry: registry,
    signature_envelopes: [phantom],
  };
  const result = await verifyBlsQuorumV0(bundle);
  assert.equal(result.ok, false);
  assert.match(result.error, /not active in registry/);
});

test('quorum rejects duplicate envelopes for same signer', { skip: !_PY_ECC }, async () => {
  const payloadHash = `0x${'ab'.repeat(32)}`;
  const alice = buildPyEnvelope({
    payloadHash,
    signerId: 'alice',
    keyId: 'k1',
    privateKeyHex: `0x${'11'.repeat(32)}`,
  });
  const registry = buildPySignerEntry({
    signerId: 'alice',
    keyId: 'k1',
    privateKeyHex: `0x${'11'.repeat(32)}`,
    weight: 1,
  });
  const bundle = {
    schema: BROWSER_CHECKPOINT_BUNDLE_SCHEMA_V0,
    signer_registry: registry,
    signature_envelopes: [alice, alice],
  };
  const result = await verifyBlsQuorumV0(bundle);
  assert.equal(result.ok, false);
  assert.match(result.error, /duplicate/);
});

test('quorum rejects when envelopes disagree on payload_hash', { skip: !_PY_ECC }, async () => {
  const alice = buildPyEnvelope({
    payloadHash: `0x${'ab'.repeat(32)}`,
    signerId: 'alice',
    keyId: 'k1',
    privateKeyHex: `0x${'11'.repeat(32)}`,
  });
  const bobDifferent = buildPyEnvelope({
    payloadHash: `0x${'cd'.repeat(32)}`, // different payload!
    signerId: 'bob',
    keyId: 'k1',
    privateKeyHex: `0x${'22'.repeat(32)}`,
  });
  const registrySnippet = `
import json
from src.integration.zeno_ledger_signer_registry import build_signer_registry_v0
from src.integration.zeno_ledger_signature import bls_public_key_hex_from_private_key_v0
reg = build_signer_registry_v0(
    registry_id='sdk-cross-lang',
    payload_kind='checkpoint',
    threshold=2,
    signers=[
        {
            'signer_id': 'alice', 'key_id': 'k1',
            'public_key': bls_public_key_hex_from_private_key_v0('0x' + '11' * 32),
            'weight': 1, 'status': 'active',
        },
        {
            'signer_id': 'bob', 'key_id': 'k1',
            'public_key': bls_public_key_hex_from_private_key_v0('0x' + '22' * 32),
            'weight': 1, 'status': 'active',
        },
    ],
)
print(json.dumps(reg, sort_keys=True))
`;
  const registry = pyRun(registrySnippet);
  const bundle = {
    schema: BROWSER_CHECKPOINT_BUNDLE_SCHEMA_V0,
    signer_registry: registry,
    signature_envelopes: [alice, bobDifferent],
  };
  const result = await verifyBlsQuorumV0(bundle);
  assert.equal(result.ok, false);
  assert.match(result.error, /payload_hash diverges/);
});
