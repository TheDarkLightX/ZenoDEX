// Cross-language CONSENSUS parity for atomic route (split-routing) intents.
//
// The UI route signer must reproduce the Python reference builder
// (src/agents/intent_signer.py::create_route_intent_from_quote_receipt)
// BYTE-FOR-BYTE, or the BLS signature will not verify against the ledger's
// recomputed signing dict. This pins that invariant across the language
// boundary, the same way dexIntentSignerSwapExactOutParity.test.mjs does for
// exact-out swaps.
//
//   * A Python subprocess builds a real route quote receipt (the same
//     best_route_exact_in_2hop / best_route_exact_out_2hop + make_route_quote_
//     receipt path the engine tests use), calls the reference route-intent
//     builder, and emits BOTH the receipt AND the resulting intent_id / inputs.
//   * The JS signer (buildAndSignRouteIntent) is driven with that SAME receipt
//     and the SAME inputs — nothing is independently hardcoded on both sides,
//     so the test cannot pass by coincidence of two divergent constants.
//
// It asserts:
//   (a) JS route intent_id === Python intent_id (field SET + VALUES bind);
//   (b) the route signature verifies in the Python engine signature policy;
//   (c) DIVERGENCE is caught: ROUTE_EXACT_IN and ROUTE_EXACT_OUT over the same
//       receipt yield different intent_ids (the kind + total field NAMES bind).
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { test } from 'node:test';
import { bls12_381 as bls } from '@noble/curves/bls12-381';
import { buildAndSignRouteIntent } from './dexIntentSigner.js';

const REPO_ROOT = fileURLToPath(new URL('../../../..', import.meta.url));
const CHAIN_ID = 'zeno-ledger-localtest-v0';
const PRIVKEY = `0x${'11'.repeat(32)}`;
const PUBKEY = `0x${Buffer.from(bls.getPublicKey(PRIVKEY.slice(2))).toString('hex')}`;

// Build the REAL route receipt + reference route intent in Python. `kind` selects
// exact_in vs exact_out. Emits the receipt (so JS uses the identical one), the
// reference intent_id, and the deadline/nonce/slippage fed to the builder.
function backendRouteIntent({ kind, slippageBps, nonce, deadline }) {
  const script = `
import json, sys

from src.agents.intent_signer import create_route_intent_from_quote_receipt
from src.core.quote_receipts import make_route_quote_receipt
from src.core.routing import best_route_exact_in_2hop, best_route_exact_out_2hop
from src.state.pools import PoolState, PoolStatus

req = json.load(sys.stdin)
sender = req["sender"]

def pool(pid):
    return PoolState(
        pool_id=pid, asset0="A", asset1="B",
        reserve0=1_000, reserve1=1_000, fee_bps=0,
        lp_supply=1, status=PoolStatus.ACTIVE, created_at=0,
    )

pools = {"p1": pool("p1"), "p2": pool("p2")}
if req["kind"] == "exact_in":
    quote = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=600)
else:
    quote = best_route_exact_out_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_out=400)
assert quote is not None
receipt = make_route_quote_receipt(kind=req["kind"], quote=quote, pools_by_id=pools)

intent = create_route_intent_from_quote_receipt(
    receipt=receipt,
    pools_by_id=pools,
    sender_pubkey=sender,
    deadline=req["deadline"],
    slippage_bps=req["slippage_bps"],
    nonce=req["nonce"],
)
print(json.dumps({
    "receipt": receipt,
    "intent_id": intent.intent_id,
    "kind": intent.kind.value,
    "fields": intent.fields,
}))
`;
  const result = spawnSync('python3', ['-c', script], {
    cwd: REPO_ROOT,
    input: JSON.stringify({
      sender: PUBKEY,
      kind,
      slippage_bps: slippageBps,
      nonce,
      deadline,
    }),
    encoding: 'utf8',
    env: { ...process.env, PYTHONPATH: REPO_ROOT },
  });
  assert.equal(result.status, 0, result.stderr);
  return JSON.parse(result.stdout);
}

// Verify a signed route intent against the real Python engine signature policy.
function pythonVerify(intent, signature) {
  const script = `
import json, sys
from src.core.dex_intent_auth_message import build_dex_intent_signing_dict_v1
from src.state.canonical import canonical_json_bytes
from src.integration.dex_engine import _verify_intent_signature_bytes

obj = json.load(sys.stdin)
payload = canonical_json_bytes(build_dex_intent_signing_dict_v1(obj["intent"]))
ok, err = _verify_intent_signature_bytes(
    sender_pubkey_hex=obj["intent"]["sender_pubkey"],
    signature_hex=obj["signature"],
    signing_payload_bytes=payload,
    chain_id=obj["chain_id"],
)
print(json.dumps({"ok": ok, "error": err}))
`;
  const result = spawnSync('python3', ['-c', script], {
    cwd: REPO_ROOT,
    input: JSON.stringify({ intent, signature, chain_id: CHAIN_ID }),
    encoding: 'utf8',
    env: { ...process.env, PYTHONPATH: REPO_ROOT },
  });
  assert.equal(result.status, 0, result.stderr);
  return JSON.parse(result.stdout);
}

test('ROUTE_EXACT_IN intent_id matches Python create_route_intent_from_quote_receipt byte-for-byte', async () => {
  const slippageBps = 0;
  const nonce = 7;
  const deadline = 1_999_999_999;

  const backend = backendRouteIntent({ kind: 'exact_in', slippageBps, nonce, deadline });
  assert.equal(backend.kind, 'ROUTE_EXACT_IN');

  const signed = await buildAndSignRouteIntent({
    receipt: backend.receipt,
    payload: {
      senderPubkey: PUBKEY,
      recipient: PUBKEY,
      deadline,
      nonce,
      slippageBps,
    },
    privkey: PRIVKEY,
    chainId: CHAIN_ID,
  });

  // (a) intent_id parity — the consensus invariant.
  assert.equal(signed.intent.kind, 'ROUTE_EXACT_IN');
  assert.match(signed.intent.intent_id, /^0x[0-9a-f]{64}$/);
  assert.equal(
    signed.intent.intent_id,
    backend.intent_id,
    'UI route intent_id must equal Python create_route_intent_from_quote_receipt intent_id',
  );
  // JS op carries the route field mapping the backend expects.
  assert.equal(signed.intent.total_amount_in, backend.fields.total_amount_in);
  assert.equal(signed.intent.total_min_amount_out, backend.fields.total_min_amount_out);
  assert.deepEqual(signed.intent.leg_indices, backend.fields.leg_indices);
  assert.equal('total_amount_out' in signed.intent, false);
  assert.equal('total_max_amount_in' in signed.intent, false);

  // (b) signature binding verifies in the Python engine.
  assert.deepEqual(pythonVerify(signed.intent, signed.signature), { ok: true, error: null });
});

test('ROUTE_EXACT_OUT intent_id matches Python builder byte-for-byte (with slippage)', async () => {
  const slippageBps = 50;
  const nonce = 12;
  const deadline = 1_888_888_888;

  const backend = backendRouteIntent({ kind: 'exact_out', slippageBps, nonce, deadline });
  assert.equal(backend.kind, 'ROUTE_EXACT_OUT');

  const signed = await buildAndSignRouteIntent({
    receipt: backend.receipt,
    payload: {
      senderPubkey: PUBKEY,
      recipient: PUBKEY,
      deadline,
      nonce,
      slippageBps,
    },
    privkey: PRIVKEY,
    chainId: CHAIN_ID,
  });

  assert.equal(signed.intent.kind, 'ROUTE_EXACT_OUT');
  assert.equal(
    signed.intent.intent_id,
    backend.intent_id,
    'UI route exact-out intent_id must equal the Python builder intent_id',
  );
  // exact-out total fields, no exact-in residue (slippage-derived max-in matches).
  assert.equal(signed.intent.total_amount_out, backend.fields.total_amount_out);
  assert.equal(signed.intent.total_max_amount_in, backend.fields.total_max_amount_in);
  assert.equal('total_amount_in' in signed.intent, false);
  assert.equal('total_min_amount_out' in signed.intent, false);

  assert.deepEqual(pythonVerify(signed.intent, signed.signature), { ok: true, error: null });
});

test('route parity FAILS on kind divergence (exact-in vs exact-out bind differently)', async () => {
  // Same pools/sender/nonce, but exact-in vs exact-out receipts produce
  // different total field NAMES (total_amount_in/total_min_amount_out vs
  // total_amount_out/total_max_amount_in) and a different kind, so the canonical
  // intent_id payload differs. This is the property that makes (a) meaningful.
  const nonce = 21;
  const deadline = 1_999_999_999;
  const exactIn = backendRouteIntent({ kind: 'exact_in', slippageBps: 0, nonce, deadline });
  const exactOut = backendRouteIntent({ kind: 'exact_out', slippageBps: 0, nonce, deadline });

  assert.notEqual(
    exactIn.intent_id,
    exactOut.intent_id,
    'exact-in and exact-out route intent_ids must differ',
  );

  const jsIn = await buildAndSignRouteIntent({
    receipt: exactIn.receipt,
    payload: { senderPubkey: PUBKEY, recipient: PUBKEY, deadline, nonce, slippageBps: 0 },
    privkey: PRIVKEY,
    chainId: CHAIN_ID,
  });
  const jsOut = await buildAndSignRouteIntent({
    receipt: exactOut.receipt,
    payload: { senderPubkey: PUBKEY, recipient: PUBKEY, deadline, nonce, slippageBps: 0 },
    privkey: PRIVKEY,
    chainId: CHAIN_ID,
  });

  // JS reproduces BOTH Python ids — proving the JS mapping tracks kind + field
  // names, not just the numbers.
  assert.equal(jsIn.intent.intent_id, exactIn.intent_id);
  assert.equal(jsOut.intent.intent_id, exactOut.intent_id);
  assert.notEqual(jsIn.intent.intent_id, jsOut.intent.intent_id);
});
