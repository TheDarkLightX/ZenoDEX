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

function backendRouteOp({ mode, nonce }) {
  const script = `
import json, sys, tempfile
from pathlib import Path

from src.core.dex import DexState
from src.core.quote_receipts import make_route_quote_receipt
from src.core.routing import best_route_exact_in_2hop, best_route_exact_out_2hop
from src.integration.dex_snapshot import snapshot_from_state
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus
from tools.zeno_ledger_make_testnet_bundle import DEFAULT_ASSET0, DEFAULT_ASSET1
import tools.zeno_ledger_node as node

req = json.load(sys.stdin)
sender = req["sender"]
pools = {
    "p1": PoolState("p1", DEFAULT_ASSET0, DEFAULT_ASSET1, 100_000, 100_000, 0, 100_000, PoolStatus.ACTIVE, 1),
    "p2": PoolState("p2", DEFAULT_ASSET0, DEFAULT_ASSET1, 100_000, 100_000, 0, 100_000, PoolStatus.ACTIVE, 1),
}
balances = BalanceTable()
balances.set(sender, DEFAULT_ASSET0, 1_000_000)
snapshot = snapshot_from_state(DexState(balances=balances, pools=pools, lp_balances=LPTable())).data
if req["mode"] == "exact_out":
    quote = best_route_exact_out_2hop(pools_by_id=pools, asset_in=DEFAULT_ASSET0, asset_out=DEFAULT_ASSET1, amount_out=60_000)
    kind = "exact_out"
else:
    quote = best_route_exact_in_2hop(pools_by_id=pools, asset_in=DEFAULT_ASSET0, asset_out=DEFAULT_ASSET1, amount_in=60_000)
    kind = "exact_in"
assert quote is not None and len(quote.legs) >= 2
receipt = make_route_quote_receipt(kind=kind, quote=quote, pools_by_id=pools)

with tempfile.TemporaryDirectory() as td:
    node_status = {
        "bundle_root": td,
        "test_token_catalog": [
            {"symbol": "tASSET0", "asset_id": DEFAULT_ASSET0},
            {"symbol": "tASSET1", "asset_id": DEFAULT_ASSET1},
        ],
    }
    node._latest_snapshot_for_ui_v0 = lambda **_kw: (41, snapshot)
    payload = {
        "quote_receipt": receipt,
        "kind": "ROUTE_EXACT_OUT" if kind == "exact_out" else "ROUTE_EXACT_IN",
        "senderPubkey": sender,
        "recipient": sender,
        "nonce": req["nonce"],
    }
    tx = node._ui_route_tx_v0(
        data_dir=Path(td), node_status=node_status, payload=payload, time_ms=1_778_740_101_000,
    )
    op = tx["operations"]["5"][0]
    print(json.dumps({"op": op, "receipt": receipt}))
`;
  const result = spawnSync('python3', ['-c', script], {
    cwd: REPO_ROOT,
    input: JSON.stringify({ sender: PUBKEY, mode, nonce }),
    encoding: 'utf8',
    env: { ...process.env, PYTHONPATH: REPO_ROOT },
  });
  assert.equal(result.status, 0, result.stderr);
  return JSON.parse(result.stdout);
}

function pythonVerify(intent, signature) {
  const script = `
import json, sys
from src.core.dex_intent_auth_message import build_dex_intent_signing_dict_v1
from src.state.canonical import canonical_json_bytes
from src.integration.dex_engine import _verify_intent_signature_bytes

obj = json.load(sys.stdin)
intent = dict(obj["intent"])
intent.pop("quote_receipt", None)
payload = canonical_json_bytes(build_dex_intent_signing_dict_v1(intent))
ok, err = _verify_intent_signature_bytes(
    sender_pubkey_hex=intent["sender_pubkey"],
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

test('route exact-in signer emits backend-parseable per-leg swap intents', async () => {
  const backend = backendRouteOp({ mode: 'exact_in', nonce: 31 });
  const signed = await buildAndSignRouteIntent({
    payload: {
      quoteReceipt: backend.receipt,
      kind: 'ROUTE_EXACT_IN',
      senderPubkey: PUBKEY,
      recipient: PUBKEY,
      nonce: backend.op.nonce,
      deadline: backend.op.deadline,
    },
    privkey: PRIVKEY,
    chainId: CHAIN_ID,
  });
  assert.equal(signed.intents.length, backend.receipt.body.legs.length);
  assert.deepEqual(signed.intents.map((intent) => intent.kind), ['SWAP_EXACT_IN', 'SWAP_EXACT_IN']);
  assert.deepEqual(signed.intents.map((intent) => intent.quote_receipt_leg_index).sort(), [0, 1]);
  assert.deepEqual(signed.intents.map((intent) => intent.nonce), [backend.op.nonce, backend.op.nonce + 1]);
  for (const [i, intent] of signed.intents.entries()) {
    assert.equal(intent.quote_receipt_hash, backend.receipt.receipt_hash);
    assert.notEqual(intent.quote_receipt_hash, backend.receipt.risc0_route_quote_receipt_binding_hash);
    assert.ok(intent.quote_pool_fingerprint);
    assert.equal(intent.quote_receipt, backend.receipt);
    assert.deepEqual(pythonVerify(intent, signed.signatures[i]), { ok: true, error: null });
  }
});

test('route exact-out signer emits backend-parseable per-leg swap intents', async () => {
  const backend = backendRouteOp({ mode: 'exact_out', nonce: 32 });
  const signed = await buildAndSignRouteIntent({
    payload: {
      quoteReceipt: backend.receipt,
      kind: 'ROUTE_EXACT_OUT',
      senderPubkey: PUBKEY,
      recipient: PUBKEY,
      nonce: backend.op.nonce,
      deadline: backend.op.deadline,
    },
    privkey: PRIVKEY,
    chainId: CHAIN_ID,
  });
  assert.equal(signed.intents.length, backend.receipt.body.legs.length);
  assert.deepEqual(signed.intents.map((intent) => intent.kind), ['SWAP_EXACT_OUT', 'SWAP_EXACT_OUT']);
  assert.deepEqual(signed.intents.map((intent) => intent.quote_receipt_leg_index).sort(), [0, 1]);
  assert.deepEqual(signed.intents.map((intent) => intent.nonce), [backend.op.nonce, backend.op.nonce + 1]);
  for (const [i, intent] of signed.intents.entries()) {
    assert.equal(intent.quote_receipt_hash, backend.receipt.receipt_hash);
    assert.notEqual(intent.quote_receipt_hash, backend.receipt.risc0_route_quote_receipt_binding_hash);
    assert.ok(intent.quote_pool_fingerprint);
    assert.equal(intent.quote_receipt, backend.receipt);
    assert.deepEqual(pythonVerify(intent, signed.signatures[i]), { ok: true, error: null });
  }
});

test('route parity rejects incomplete leg coverage before signing', async () => {
  const backend = backendRouteOp({ mode: 'exact_in', nonce: 33 });
  await assert.rejects(
    () => buildAndSignRouteIntent({
      payload: {
        quoteReceipt: backend.receipt,
        kind: 'ROUTE_EXACT_IN',
        senderPubkey: PUBKEY,
        recipient: PUBKEY,
        nonce: backend.op.nonce,
        deadline: backend.op.deadline,
        legIndices: [0],
      },
      privkey: PRIVKEY,
      chainId: CHAIN_ID,
    }),
    /leg_indices_must_cover_full_receipt/,
  );
});

test('route signer does not require RISC0 route binding hash for direct swap intents', async () => {
  const backend = backendRouteOp({ mode: 'exact_in', nonce: 35 });
  const receipt = {
    ...backend.receipt,
    risc0_route_quote_receipt_binding_hash: undefined,
  };

  const signed = await buildAndSignRouteIntent({
    payload: {
      quoteReceipt: receipt,
      kind: 'ROUTE_EXACT_IN',
      senderPubkey: PUBKEY,
      recipient: PUBKEY,
      nonce: backend.op.nonce,
      deadline: backend.op.deadline,
    },
    privkey: PRIVKEY,
    chainId: CHAIN_ID,
  });
  assert.equal(signed.intent.quote_receipt_hash, backend.receipt.receipt_hash);
  assert.equal(signed.intent.kind, 'SWAP_EXACT_IN');
});

test('route signer rejects nonce outside consensus u32 before signing', async () => {
  const backend = backendRouteOp({ mode: 'exact_in', nonce: 34 });
  await assert.rejects(
    () => buildAndSignRouteIntent({
      payload: {
        quoteReceipt: backend.receipt,
        kind: 'ROUTE_EXACT_IN',
        senderPubkey: PUBKEY,
        recipient: PUBKEY,
        nonce: 0x1_0000_0000,
        deadline: backend.op.deadline,
      },
      privkey: PRIVKEY,
      chainId: CHAIN_ID,
    }),
    /nonce_must_fit_u32/,
  );
});

test('route signer rejects multi-hop receipts outside the current execution scope', async () => {
  const receipt = {
    receipt_hash: `0x${'cd'.repeat(32)}`,
    body: {
      schema: 'zenodex/route_quote_receipt/v1',
      kind: 'exact_in',
      asset_in: `0x${'01'.repeat(32)}`,
      asset_out: `0x${'02'.repeat(32)}`,
      amount_in: 100,
      amount_out: 90,
      legs: [
        {
          amount_in: 100,
          amount_out: 90,
          hops: [
            { pool_id: 'p1', asset_in: `0x${'01'.repeat(32)}`, asset_out: `0x${'03'.repeat(32)}`, amount_in: 100, amount_out: 95 },
            { pool_id: 'p2', asset_in: `0x${'03'.repeat(32)}`, asset_out: `0x${'02'.repeat(32)}`, amount_in: 95, amount_out: 90 },
          ],
        },
      ],
    },
  };
  await assert.rejects(
    () => buildAndSignRouteIntent({
      payload: {
        quoteReceipt: receipt,
        kind: 'ROUTE_EXACT_IN',
        senderPubkey: PUBKEY,
        recipient: PUBKEY,
        nonce: 34,
      },
      privkey: PRIVKEY,
      chainId: CHAIN_ID,
    }),
    /route_multihop_unsupported/,
  );
});
