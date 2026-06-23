// Honest live-vs-preview classification of the proof-mining workbench surface.
//
// This is a self-contained bridge/contract test (node --test, mocked fetch). It
// pins which proof-mining actions are wired to a real backend route versus which
// are preview/placeholder, so the classification cannot silently regress to a
// misleading "live" label.
//
// Ground truth (verified against the running backends):
//   - apiCheckProofMiningStatus  -> POST /api/dex/proof_mining_status
//       LIVE but PREFLIGHT-ONLY: the handler rejects any `proof_mining_context`
//       and forces verified-context = absent, so it validates claim shape but can
//       never return `claimable: true` over HTTP (fail-closed).
//       See src/integration/api_server.py (proof_mining_status branch) and
//       tests/integration/test_api_server_proof_mining_status.py.
//   - apiSubmitLedgerTransaction -> POST /tx
//       LIVE on the zeno-ledger node (tools/zeno_ledger_node.py), NOT on the local
//       DEX API. Live only when the UI is pointed at a running ledger node.
//   - apiBuildProofMiningPayoutTemplate -> POST /api/dex/proof_mining_payout_template
//       LIVE: src/integration/api_server.py serves a deterministic payout
//       template (real claim via build_proof_mining_claim + the submit tx). The
//       "Load sample" primary path now resolves a live, preflight-consistent
//       template. See tests/integration/test_api_server_proof_mining_payout_template.py.

import assert from 'node:assert/strict';
import { test } from 'node:test';
import {
  apiBuildProofMiningPayoutTemplate,
  apiCheckProofMiningStatus,
  apiSubmitLedgerTransaction,
} from '../lib/api.js';

function withMockFetch(handler, run) {
  return async () => {
    const calls = [];
    const previousFetch = globalThis.fetch;
    globalThis.fetch = async (url, options = {}) => {
      calls.push({ url, options });
      return handler({ url, options });
    };
    try {
      await run(calls);
    } finally {
      globalThis.fetch = previousFetch;
    }
  };
}

test(
  'apiCheckProofMiningStatus posts to the live preflight route and is fail-closed',
  withMockFetch(
    () => ({
      ok: true,
      // The real endpoint shape for an absent verified DEX proof context: a valid
      // claim shape that is nonetheless not claimable over HTTP.
      text: async () =>
        JSON.stringify({
          ok: true,
          status: {
            enabled: true,
            claimable: false,
            error: 'proof mining claim requires verified DEX proof context',
            checks: {
              winner_matches_sender: true,
              proposal_hash_matches_context: true,
              verified_context_present: false,
              runtime_apply_ok: false,
            },
          },
        }),
    }),
    async (calls) => {
      const result = await apiCheckProofMiningStatus({
        app_state_json: '',
        chain_balances: {},
        claim: { body: { proposal_hash: '0xabc' } },
        tx_sender_pubkey: `0x${'11'.repeat(48)}`,
        expected_proposal_hash: '0xabc',
      });
      assert.equal(calls.length, 1);
      assert.equal(calls[0].url, '/api/dex/proof_mining_status');
      assert.equal(calls[0].options.method, 'POST');
      // Preflight contract: a verified DEX proof context is never accepted over
      // HTTP, so the surface can only ever report `claimable: false` here.
      assert.equal(result.status.claimable, false);
      assert.equal(result.status.checks.verified_context_present, false);
      assert.equal(
        result.status.error,
        'proof mining claim requires verified DEX proof context',
      );
    },
  ),
);

test(
  'apiSubmitLedgerTransaction posts to the zeno-ledger node /tx route, not the local DEX API',
  withMockFetch(
    () => ({
      ok: true,
      text: async () => JSON.stringify({ ok: true, tx_accepted: true, height: 7 }),
    }),
    async (calls) => {
      const result = await apiSubmitLedgerTransaction({ tx: { tx_id: 'pm-submit-regression-v0' } });
      assert.equal(calls.length, 1);
      // Cross-server dependency: this is the ledger-node route, not /api/dex/*.
      assert.equal(calls[0].url, '/tx');
      assert.equal(calls[0].options.method, 'POST');
      const body = JSON.parse(calls[0].options.body);
      assert.equal(body.tx.tx_id, 'pm-submit-regression-v0');
      assert.equal(result.tx_accepted, true);
    },
  ),
);

// Now LIVE: the payout-template backend route is served by the local DEX API
// (src/integration/api_server.py). This pins the api.js client contract — the
// exact route, method, request passthrough, and the response shape the
// ProofMiningWorkbench consumes (status_request + submit tx + reward fields).
test(
  'apiBuildProofMiningPayoutTemplate posts to the live payout-template route',
  withMockFetch(
    () => ({
      ok: true,
      text: async () =>
        JSON.stringify({
          ok: true,
          template_mode: 'preview_v1',
          status_request: {
            claim: { body: { proposal_hash: '0xfeed' } },
            chain_balances: { [`0x${'cd'.repeat(48)}`]: 64, [`0x${'ab'.repeat(48)}`]: 0 },
            app_state_json: '{"schema":"zenodex/tau_app_state/v1"}',
            tx_sender_pubkey: `0x${'ab'.repeat(48)}`,
            expected_proposal_hash: '0xfeed',
          },
          proof_mining_context: { proposal_hash: '0xfeed', proof_scheme: 'template_preview_v1' },
          tx: {
            tx_id: 'proof-mining-payout-deadbeef',
            tx_sender_pubkey: `0x${'ab'.repeat(48)}`,
            operations: {
              10: { module: 'ZenoProofMining', action: 'submit_proof', claim: { body: {} }, recipient_pubkey: `0x${'ab'.repeat(48)}` },
            },
          },
          reward_pool_pubkey: `0x${'cd'.repeat(48)}`,
          reward_asset_id: null,
          reward_pool_before: 64,
          reward_amount: 4,
        }),
    }),
    async (calls) => {
      const result = await apiBuildProofMiningPayoutTemplate({
        chain_id: 'zeno-ledger-localtest-v0',
        tx_sender_pubkey: `0x${'ab'.repeat(48)}`,
        reward_pool_pubkey: `0x${'cd'.repeat(48)}`,
        reward_pool_before: 64,
        base_reward: 8,
        epoch: 1,
      });
      assert.equal(calls.length, 1);
      assert.equal(calls[0].url, '/api/dex/proof_mining_payout_template');
      assert.equal(calls[0].options.method, 'POST');
      const sentBody = JSON.parse(calls[0].options.body);
      assert.equal(sentBody.reward_pool_before, 64);
      assert.equal(sentBody.reward_pool_pubkey, `0x${'cd'.repeat(48)}`);
      // Response shape the ProofMiningWorkbench consumes.
      assert.equal(result.ok, true);
      assert.equal(result.template_mode, 'preview_v1');
      assert.ok(result.status_request.claim);
      assert.equal(
        result.status_request.expected_proposal_hash,
        result.status_request.claim.body.proposal_hash,
      );
      assert.equal(result.tx.operations['10'].action, 'submit_proof');
      assert.equal(result.reward_pool_before, 64);
    },
  ),
);
