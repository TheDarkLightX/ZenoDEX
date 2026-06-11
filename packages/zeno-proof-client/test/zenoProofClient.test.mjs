import assert from 'node:assert/strict';
import test from 'node:test';

import {
  BROWSER_CHECKPOINT_BUNDLE_SCHEMA_V0,
  advanceWalletSyncStateV0,
  hashV0,
  parseZkProofStatusV0,
  verifyBrowserCheckpointBundleV0,
} from '../src/zenoProofClient.js';

function root(byte) {
  return `0x${byte.repeat(64)}`;
}

function publicKey(byte) {
  return `0x${byte.repeat(96)}`;
}

function builderTrustOptions(bundle, overrides = {}) {
  return {
    trustBuilderBls: true,
    expectedTrustedPrevHeaderHash: bundle.trusted_prev_header_hash,
    expectedSignerRegistryHash: bundle.signer_registry.registry_hash,
    ...overrides,
  };
}

async function makeBundle({
  height = 2,
  fromHeight = 1,
  trustedPrevHeaderHash = root('0'),
  chainId = 'zeno-ledger-sdk-testnet-0',
} = {}) {
  const signerA = {
    signer_id: 'a',
    key_id: 'a',
    algorithm: 'bls12-381-g2-basic-release-v0',
    public_key: publicKey('1'),
    weight: 1,
    status: 'active',
  };
  const signerB = {
    signer_id: 'b',
    key_id: 'b',
    algorithm: 'bls12-381-g2-basic-release-v0',
    public_key: publicKey('2'),
    weight: 1,
    status: 'active',
  };
  const signers = [
    {
      ...signerA,
      signer_hash: await hashV0('signer_registry_entry_v0', signerA),
    },
    {
      ...signerB,
      signer_hash: await hashV0('signer_registry_entry_v0', signerB),
    },
  ];
  const registryBody = {
    schema: 'zenodex/zeno_ledger/signer_registry/v0',
    registry_id: 'sdk-test-registry',
    payload_kind: 'checkpoint',
    threshold: 2,
    signers,
  };
  const registry = {
    ...registryBody,
    registry_hash: await hashV0('signer_registry_v0', registryBody),
  };
  const signatureSetRoot = await hashV0('light_client_signature_set_root_v0', {
    registry_hash: registry.registry_hash,
    payload_kind: 'checkpoint',
    threshold: registry.threshold,
  });
  const headerChain = [];
  let prevHeaderHash = trustedPrevHeaderHash;
  for (let currentHeight = fromHeight; currentHeight <= height; currentHeight += 1) {
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
      time_ms: 1_778_730_000_000 + currentHeight,
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
    from_height: fromHeight,
    to_height: height,
    trusted_prev_header_hash: trustedPrevHeaderHash,
  };
  const body = {
    schema: BROWSER_CHECKPOINT_BUNDLE_SCHEMA_V0,
    chain_id: chainId,
    from_height: fromHeight,
    to_height: height,
    trusted_prev_header_hash: trustedPrevHeaderHash,
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
      builder_id: 'node-test',
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

test('browser checkpoint bundle verifies shape and hash binding', async () => {
  const bundle = await makeBundle();
  const report = await verifyBrowserCheckpointBundleV0(bundle, builderTrustOptions(bundle));

  assert.equal(report.ok, true);
  assert.equal(report.status, 'accepted_with_builder_bls_trust');
  assert.equal(report.trust_model, 'builder_bls_claim');
  assert.equal(report.height, 2);
  assert.equal(report.builder_bls_quorum_verified, true);
  assert.equal(report.browser_range_replay_verified, true);
  assert.equal(report.browser_bls_quorum_verified, false);
});

test('browser checkpoint bundle requires caller-pinned trust anchors by default', async () => {
  const bundle = await makeBundle();
  const report = await verifyBrowserCheckpointBundleV0(bundle);

  assert.equal(report.ok, false);
  assert.match(report.gaps.join('\n'), /expectedTrustedPrevHeaderHash/);
});

test('browser checkpoint bundle rejects mismatched trust anchors', async () => {
  const bundle = await makeBundle();

  const wrongPrev = await verifyBrowserCheckpointBundleV0(
    bundle,
    builderTrustOptions(bundle, { expectedTrustedPrevHeaderHash: root('1') }),
  );
  assert.equal(wrongPrev.ok, false);
  assert.match(wrongPrev.gaps.join('\n'), /trusted_prev_header_hash trust anchor mismatch/);

  const wrongRegistry = await verifyBrowserCheckpointBundleV0(
    bundle,
    builderTrustOptions(bundle, { expectedSignerRegistryHash: root('1') }),
  );
  assert.equal(wrongRegistry.ok, false);
  assert.match(wrongRegistry.gaps.join('\n'), /signer registry trust anchor mismatch/);
});

test('browser checkpoint bundle rejects tampering', async () => {
  const bundle = await makeBundle();
  bundle.target_checkpoint.height = 3;

  const report = await verifyBrowserCheckpointBundleV0(bundle, builderTrustOptions(bundle));

  assert.equal(report.ok, false);
  assert.match(report.gaps.join('\n'), /bundle_hash mismatch/);
});

test('browser checkpoint bundle rejects unknown top-level fields with recomputed hash', async () => {
  const bundle = await makeBundle();
  const { bundle_hash: _drop, ...body } = { ...bundle, attacker_extra: true };
  void _drop;
  const tampered = {
    ...body,
    bundle_hash: await hashV0('browser_checkpoint_bundle_v0', body),
  };

  const report = await verifyBrowserCheckpointBundleV0(tampered, builderTrustOptions(tampered));

  assert.equal(report.ok, false);
  assert.match(report.gaps.join('\n'), /bundle keys mismatch/);
});

test('browser checkpoint bundle rejects unknown verification summary fields', async () => {
  const bundle = await makeBundle();
  bundle.verification_summary.extra = true;
  const { bundle_hash: _drop, ...body } = bundle;
  void _drop;
  bundle.bundle_hash = await hashV0('browser_checkpoint_bundle_v0', body);

  const report = await verifyBrowserCheckpointBundleV0(bundle, builderTrustOptions(bundle));

  assert.equal(report.ok, false);
  assert.match(report.gaps.join('\n'), /verification summary keys mismatch/);
});

test('browser checkpoint bundle replays header chain', async () => {
  const bundle = await makeBundle({ height: 3 });
  bundle.header_chain[1].prev_header_hash = root('f');
  const { bundle_hash: _drop, ...rest } = bundle;
  void _drop;
  bundle.bundle_hash = await hashV0('browser_checkpoint_bundle_v0', rest);

  const report = await verifyBrowserCheckpointBundleV0(bundle, builderTrustOptions(bundle));

  assert.equal(report.ok, false);
  assert.match(report.gaps.join('\n'), /prev_header_hash/);
});

test('browser checkpoint bundle rejects inconsistent header app hash', async () => {
  const bundle = await makeBundle();
  bundle.header_chain[0].app_hash = root('1');
  const { bundle_hash: _drop, ...rest } = bundle;
  void _drop;
  bundle.bundle_hash = await hashV0('browser_checkpoint_bundle_v0', rest);

  const report = await verifyBrowserCheckpointBundleV0(bundle, builderTrustOptions(bundle));

  assert.equal(report.ok, false);
  assert.match(report.gaps.join('\n'), /app_hash mismatch/);
});

test('wallet sync rejects tampered current state hash before using height', async () => {
  const first = await makeBundle({ height: 2 });
  const second = await makeBundle({ height: 3 });
  const current = await advanceWalletSyncStateV0({
    bundle: first,
    surface: 'zusd',
    updatedAtMs: 1_778_730_000_000,
    ...builderTrustOptions(first),
  });
  assert.equal(current.ok, true);
  const tampered = {
    ...current.state,
    height: 99,
  };

  const advanced = await advanceWalletSyncStateV0({
    currentState: tampered,
    bundle: second,
    surface: 'zusd',
    updatedAtMs: 1_778_730_001_000,
  });

  assert.equal(advanced.ok, false);
  assert.deepEqual(advanced.gaps, ['wallet sync state hash mismatch']);
});

test('wallet sync advances monotonically and rejects rollback', async () => {
  const first = await makeBundle({ height: 2 });
  const second = await makeBundle({ height: 3 });
  const initial = await advanceWalletSyncStateV0({
    bundle: first,
    surface: 'zusd',
    updatedAtMs: 1_778_730_000_000,
    ...builderTrustOptions(first),
  });
  assert.equal(initial.ok, true);

  const extension = await makeBundle({
    height: 3,
    fromHeight: 3,
    trustedPrevHeaderHash: initial.state.target_header_hash,
  });
  const advanced = await advanceWalletSyncStateV0({
    currentState: initial.state,
    bundle: extension,
    surface: 'zusd',
    updatedAtMs: 1_778_730_001_000,
    trustBuilderBls: true,
  });
  assert.equal(advanced.ok, true);
  assert.equal(advanced.state.height, 3);

  const rollback = await advanceWalletSyncStateV0({
    currentState: advanced.state,
    bundle: first,
    surface: 'zusd',
    updatedAtMs: 1_778_730_002_000,
  });
  assert.equal(rollback.ok, false);
  assert.deepEqual(rollback.gaps, ['wallet sync rollback rejected']);
});

test('independent BLS verification rejects fake signature envelopes', async () => {
  // The synthetic bundle has structurally valid signers but placeholder
  // envelopes, so independent cryptographic verification must fail closed.
  const bundle = await makeBundle();
  const report = await verifyBrowserCheckpointBundleV0(
    bundle,
    {
      requireIndependentBls: true,
      expectedTrustedPrevHeaderHash: bundle.trusted_prev_header_hash,
      expectedSignerRegistryHash: bundle.signer_registry.registry_hash,
    },
  );

  assert.equal(report.ok, false);
  assert.match(
    report.gaps.join('\n'),
    /independent BLS verification failed:/,
  );
});

test('independent BLS verification rejects bundle with no envelopes', async () => {
  const bundle = await makeBundle();
  bundle.signature_envelopes = [];
  const { bundle_hash: _drop, ...rest } = bundle;
  void _drop;
  bundle.bundle_hash = await hashV0('browser_checkpoint_bundle_v0', rest);

  const report = await verifyBrowserCheckpointBundleV0(bundle, builderTrustOptions(bundle));
  // Empty envelope list is rejected by the structural check too.
  assert.equal(report.ok, false);
  assert.match(report.gaps.join('\n'), /signature_envelopes length rejected/);
});

test('zk proof status parser enforces caller-pinned proof artifacts', () => {
  const artifactHashes = {
    verifier: `sha256:${'1'.repeat(64)}`,
    circuit: `0x${'2'.repeat(64)}`,
    image: `0x${'3'.repeat(64)}`,
  };
  const status = {
    zk_mode_requested: 'strict',
    zk_mode_effective: 'strict',
    zk_required: true,
    proof_verifier_kind: 'subprocess',
    proof_artifact_hashes: artifactHashes,
    production_security_claim: false,
  };

  const pinned = parseZkProofStatusV0(status, {
    expectedProofArtifactHashes: {
      verifier: artifactHashes.verifier,
      circuit: artifactHashes.circuit,
      image: artifactHashes.image,
    },
  });
  assert.equal(pinned.ok, true);
  assert.equal(pinned.artifact_pinning_verified, true);

  const wrongImage = parseZkProofStatusV0(status, {
    expectedProofArtifactHashes: {
      verifier: artifactHashes.verifier,
      circuit: artifactHashes.circuit,
      image: `0x${'4'.repeat(64)}`,
    },
  });
  assert.equal(wrongImage.ok, false);
  assert.equal(wrongImage.artifact_pinning_verified, false);
  assert.match(wrongImage.gaps.join('\n'), /proof artifact hash mismatch:image/);

  const missingImage = parseZkProofStatusV0(
    {
      ...status,
      proof_artifact_hashes: {
        verifier: artifactHashes.verifier,
        circuit: artifactHashes.circuit,
      },
    },
    { expected_proof_artifact_hashes: { image: artifactHashes.image } },
  );
  assert.equal(missingImage.ok, false);
  assert.match(missingImage.gaps.join('\n'), /expected proof artifact hash missing:image/);
});
