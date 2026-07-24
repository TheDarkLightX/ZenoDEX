import assert from 'node:assert/strict';
import test from 'node:test';

import {
  BROWSER_CHECKPOINT_BUNDLE_SCHEMA_V0,
  advanceWalletSyncStateV0,
  hashV0,
  verifyBrowserCheckpointBundleV0,
} from './zenoProofClient.js';

function root(byte) {
  return `0x${byte.repeat(64)}`;
}

async function makeBundle({ height = 2, chainId = 'zeno-ledger-sdk-testnet-0' } = {}) {
  const registry = {
    schema: 'zenodex/zeno_ledger/signer_registry/v0',
    registry_id: 'sdk-test-registry',
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
    verification_mode: 'structural_diagnostic',
    structural_diagnostic_verified: true,
    range_replay_verified: false,
    proof_authority_satisfied: false,
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
      builder_id: 'node-test',
      proof_authority_required: false,
      proof_authority_satisfied: false,
      proof_authority_capable: false,
      settlement_authority: false,
      production_authority: false,
      python_structural_range_verified: true,
      python_range_replay_verified: false,
      python_bls_quorum_verified: true,
      browser_header_chain_verified: false,
      browser_header_chain_available: true,
      browser_range_replay_verified: false,
      browser_range_replay_available: false,
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
      proof_authority_satisfied: false,
      proof_authority_capable: false,
      settlement_authority: false,
      production_authority: false,
      python_structural_range_verified: true,
      python_range_replay_verified: false,
      python_bls_quorum_verified: true,
      browser_shape_and_hash_available: true,
      browser_shape_and_hash_verified: false,
      browser_header_chain_verified: false,
      browser_header_chain_available: true,
      browser_range_replay_verified: false,
      browser_range_replay_available: false,
      browser_bls_quorum_verified: false,
    },
    non_claims: [
      'browser package v0 has no proof, settlement, or production authority',
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
  const report = await verifyBrowserCheckpointBundleV0(bundle);

  assert.equal(report.ok, true);
  assert.equal(report.height, 2);
  assert.equal(report.builder_bls_quorum_verified, true);
  assert.equal(report.status, 'structural_diagnostic_accepted');
  assert.equal(report.browser_shape_and_hash_verified, true);
  assert.equal(report.browser_header_chain_verified, true);
  assert.equal(report.browser_range_replay_verified, false);
  assert.equal(report.browser_bls_quorum_verified, false);
});

test('browser checkpoint bundle rejects tampering', async () => {
  const bundle = await makeBundle();
  bundle.target_checkpoint.height = 3;

  const report = await verifyBrowserCheckpointBundleV0(bundle);

  assert.equal(report.ok, false);
  assert.match(report.gaps.join('\n'), /bundle_hash mismatch/);
});

test('browser checkpoint bundle rejects forged proof authority', async () => {
  const bundle = await makeBundle();
  bundle.capabilities.proof_authority_satisfied = true;
  const { bundle_hash: _drop, ...body } = bundle;
  void _drop;
  bundle.bundle_hash = await hashV0('browser_checkpoint_bundle_v0', body);

  const report = await verifyBrowserCheckpointBundleV0(bundle);

  assert.equal(report.ok, false);
  assert.match(report.gaps.join('\n'), /authority capability flags must remain false/);
});

test('browser checkpoint bundle rejects structural evidence promoted to range replay', async () => {
  const bundle = await makeBundle();
  bundle.verification_summary.python_range_replay_verified = true;
  const { bundle_hash: _drop, ...body } = bundle;
  void _drop;
  bundle.bundle_hash = await hashV0('browser_checkpoint_bundle_v0', body);

  const report = await verifyBrowserCheckpointBundleV0(bundle);

  assert.equal(report.ok, false);
  assert.match(report.gaps.join('\n'), /must remain a structural diagnostic/);
});

test('browser checkpoint bundle rejects unknown top-level fields with recomputed hash', async () => {
  const bundle = await makeBundle();
  const { bundle_hash: _drop, ...body } = { ...bundle, attacker_extra: true };
  void _drop;
  const tampered = {
    ...body,
    bundle_hash: await hashV0('browser_checkpoint_bundle_v0', body),
  };

  const report = await verifyBrowserCheckpointBundleV0(tampered);

  assert.equal(report.ok, false);
  assert.match(report.gaps.join('\n'), /bundle keys mismatch/);
});

test('browser checkpoint bundle rejects unknown verification summary fields', async () => {
  const bundle = await makeBundle();
  bundle.verification_summary.extra = true;
  const { bundle_hash: _drop, ...body } = bundle;
  void _drop;
  bundle.bundle_hash = await hashV0('browser_checkpoint_bundle_v0', body);

  const report = await verifyBrowserCheckpointBundleV0(bundle);

  assert.equal(report.ok, false);
  assert.match(report.gaps.join('\n'), /verification summary keys mismatch/);
});

test('browser checkpoint bundle replays header chain', async () => {
  const bundle = await makeBundle({ height: 3 });
  bundle.header_chain[1].prev_header_hash = root('f');
  const { bundle_hash: _drop, ...rest } = bundle;
  void _drop;
  bundle.bundle_hash = await hashV0('browser_checkpoint_bundle_v0', rest);

  const report = await verifyBrowserCheckpointBundleV0(bundle);

  assert.equal(report.ok, false);
  assert.match(report.gaps.join('\n'), /prev_header_hash/);
});

test('browser checkpoint bundle rejects inconsistent header app hash', async () => {
  const bundle = await makeBundle();
  bundle.header_chain[0].app_hash = root('1');
  const { bundle_hash: _drop, ...rest } = bundle;
  void _drop;
  bundle.bundle_hash = await hashV0('browser_checkpoint_bundle_v0', rest);

  const report = await verifyBrowserCheckpointBundleV0(bundle);

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
  });
  assert.equal(initial.ok, true);
  assert.equal(initial.status, 'structural_checkpoint_tracked');
  assert.equal(initial.proof_authority_capable, false);
  assert.equal(initial.settlement_authority, false);

  const advanced = await advanceWalletSyncStateV0({
    currentState: initial.state,
    bundle: second,
    surface: 'zusd',
    updatedAtMs: 1_778_730_001_000,
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

test('independent BLS verification rejects empty signer registry', async () => {
  // The synthetic bundle has an empty signers list — independent verification
  // requires at least one active signer, so it must fail.
  const bundle = await makeBundle();
  const report = await verifyBrowserCheckpointBundleV0(bundle, { requireIndependentBls: true });

  assert.equal(report.ok, false);
  assert.match(
    report.gaps.join('\n'),
    /independent BLS verification failed: signer registry must contain at least one signer/,
  );
});

test('independent BLS verification rejects bundle with no envelopes', async () => {
  const bundle = await makeBundle();
  bundle.signature_envelopes = [];
  const { bundle_hash: _drop, ...rest } = bundle;
  void _drop;
  bundle.bundle_hash = await hashV0('browser_checkpoint_bundle_v0', rest);

  const report = await verifyBrowserCheckpointBundleV0(bundle);
  // Empty envelope list is rejected by the structural check too.
  assert.equal(report.ok, false);
  assert.match(report.gaps.join('\n'), /signature_envelopes length rejected/);
});
