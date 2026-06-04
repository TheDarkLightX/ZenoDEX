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
//       MISSING BACKEND: no handler exists anywhere in src/. The "Load sample"
//       primary path 404s and falls back to an offline preview sample.

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

// Skipped-with-reason: the live payout-template backend route is not served by
// the local DEX API (no handler for POST /api/dex/proof_mining_payout_template in
// src/). The UI "Load sample" primary path 404s and falls back to an offline
// preview sample. This test documents the exact missing piece and stays skipped
// (fail-closed/visible) until a backend handler is added.
test(
  'apiBuildProofMiningPayoutTemplate has no live backend handler (preview only)',
  { skip: 'no backend handler for POST /api/dex/proof_mining_payout_template (src/ has no route); Load sample falls back to an offline preview sample' },
  async () => {
    // When a handler is added, mock fetch returning a status_request + tx, assert
    // the route + response shape, and remove the skip.
    await apiBuildProofMiningPayoutTemplate({});
  },
);
