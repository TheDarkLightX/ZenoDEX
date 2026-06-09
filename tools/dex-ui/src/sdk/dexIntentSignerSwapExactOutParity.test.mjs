// Cross-language CONSENSUS parity for exact-out swap intents.
//
// The UI signer must reproduce the backend's exact-out intent_id BYTE-FOR-BYTE,
// or the BLS signature will not verify against the ledger's recomputed signing
// dict. This test pins that invariant across the language boundary:
//
//   * The Python subprocess calls the REAL backend builder
//     (tools/zeno_ledger_node.py::_ui_swap_tx_v0) on a fixed exact-out request,
//     using the same snapshot/node_status fixture as
//     tests/integration/test_zeno_ledger_node.py, and emits BOTH the resulting
//     intent_id AND the exact inputs it fed the builder.
//   * The JS signer (buildAndSignSwapIntent) is then driven with those SAME
//     emitted inputs -- nothing is independently hardcoded on both sides, so the
//     test cannot pass by coincidence of two divergent constants.
//
// It asserts all three of:
//   (a) JS intent_id === backend intent_id (field SET + VALUES bind);
//   (b) the exact-out signature verifies in the Python engine signature policy
//       (the signed `fields` -- a SEPARATE canonical form from the intent_id --
//       carry amount_out/max_amount_in on both sides);
//   (c) DIVERGENCE is caught: the exact-out intent_id differs from the exact-in
//       intent_id for the SAME numeric amounts, proving the field NAMES bind and
//       a mislabeled amount field would fail (a) rather than silently agree.
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { test } from 'node:test';
import { bls12_381 as bls } from '@noble/curves/bls12-381';
import { buildAndSignSwapIntent, isSwapExactOutPayload } from './dexIntentSigner.js';

const REPO_ROOT = fileURLToPath(new URL('../../../..', import.meta.url));
const CHAIN_ID = 'zeno-ledger-localtest-v0';
const PRIVKEY = `0x${'11'.repeat(32)}`;
const PUBKEY = `0x${Buffer.from(bls.getPublicKey(PRIVKEY.slice(2))).toString('hex')}`;

// Build the REAL backend op via _ui_swap_tx_v0 on the pinned snapshot fixture.
// `mode` selects exact-out ("out") vs exact-in ("in"). Emits the op fields plus
// the canonical asset ids / pool id the builder resolved, so JS can mirror them.
function backendSwapOp({ mode, amountOut, maxAmountIn, amountIn, minAmountOut, nonce }) {
  const script = `
import json, sys, tempfile
from pathlib import Path

from src.core.dex import DexState
from src.integration.dex_snapshot import snapshot_from_state
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus, compute_pool_id
from tools.zeno_ledger_make_testnet_bundle import DEFAULT_ASSET0, DEFAULT_ASSET1
import tools.zeno_ledger_node as node

req = json.load(sys.stdin)
sender = req["sender"]

pool_id = compute_pool_id(DEFAULT_ASSET0, DEFAULT_ASSET1, 30)
balances = BalanceTable()
balances.set(sender, DEFAULT_ASSET0, 10_000)
balances.set(sender, DEFAULT_ASSET1, 10_000)
snapshot = snapshot_from_state(
    DexState(
        balances=balances,
        pools={
            pool_id: PoolState(
                pool_id=pool_id, asset0=DEFAULT_ASSET0, asset1=DEFAULT_ASSET1,
                reserve0=100_000, reserve1=100_000, fee_bps=30,
                lp_supply=100_000, status=PoolStatus.ACTIVE, created_at=1,
            )
        },
        lp_balances=LPTable(),
    )
).data

with tempfile.TemporaryDirectory() as td:
    node_status = {
        "bundle_root": td,
        "test_token_catalog": [
            {"symbol": "tASSET0", "asset_id": DEFAULT_ASSET0},
            {"symbol": "tASSET1", "asset_id": DEFAULT_ASSET1},
        ],
    }
    # Pin the snapshot loader: deterministic, no disk/settlement dependency.
    node._latest_snapshot_for_ui_v0 = lambda **_kw: (41, snapshot)

    payload = {
        "from": "tASSET0", "to": "tASSET1", "poolId": pool_id,
        "senderPubkey": sender, "recipient": sender, "nonce": req["nonce"],
    }
    if req["mode"] == "out":
        payload["kind"] = "SWAP_EXACT_OUT"
        payload["amountOut"] = req["amount_out"]
        payload["maxAmountIn"] = req["max_amount_in"]
    else:
        payload["amountIn"] = req["amount_in"]
        payload["minAmountOut"] = req["min_amount_out"]

    tx = node._ui_swap_tx_v0(
        data_dir=Path(td), node_status=node_status, payload=payload, time_ms=1_778_740_101_000,
    )
    op = tx["operations"]["5"][0]
    print(json.dumps({"op": op, "pool_id": pool_id, "asset_in": op["asset_in"], "asset_out": op["asset_out"]}))
`;
  const result = spawnSync('python3', ['-c', script], {
    cwd: REPO_ROOT,
    input: JSON.stringify({
      sender: PUBKEY,
      mode,
      amount_out: amountOut ?? null,
      max_amount_in: maxAmountIn ?? null,
      amount_in: amountIn ?? null,
      min_amount_out: minAmountOut ?? null,
      nonce,
    }),
    encoding: 'utf8',
    env: { ...process.env, PYTHONPATH: REPO_ROOT },
  });
  assert.equal(result.status, 0, result.stderr);
  return JSON.parse(result.stdout);
}

// Verify a signed DEX intent against the real Python engine signature policy
// (build_dex_intent_signing_dict_v1 -> _verify_intent_signature_bytes). This
// checks the SIGNATURE binding, which is a separate canonical form from the
// intent_id: the signed `fields` must carry amount_out/max_amount_in.
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

test('exact-out swap intent_id matches backend _ui_swap_tx_v0 byte-for-byte', async () => {
  const amountOut = 1_000;
  const maxAmountIn = 2_000;
  const nonce = 9;

  const backend = backendSwapOp({ mode: 'out', amountOut, maxAmountIn, nonce });
  const op = backend.op;

  // Backend produced an exact-out op with the expected field mapping.
  assert.equal(op.kind, 'SWAP_EXACT_OUT');
  assert.equal(op.amount_out, amountOut);
  assert.equal(op.max_amount_in, maxAmountIn);
  assert.equal('amount_in' in op, false);
  assert.equal('min_amount_out' in op, false);

  // Drive the JS signer with the EXACT inputs the backend resolved/used --
  // pool id + canonical asset ids come from the backend output, not hardcoded.
  const signed = await buildAndSignSwapIntent({
    pool: { poolId: backend.pool_id, asset0: backend.asset_in, asset1: backend.asset_out, reserve0: 100_000, reserve1: 100_000 },
    payload: {
      poolId: backend.pool_id,
      assetIn: backend.asset_in,
      assetOut: backend.asset_out,
      kind: 'SWAP_EXACT_OUT',
      amountOut,
      maxAmountIn,
      senderPubkey: PUBKEY,
      recipient: PUBKEY,
      nonce,
      deadline: op.deadline,
    },
    privkey: PRIVKEY,
    chainId: CHAIN_ID,
  });

  // (a) intent_id parity -- the consensus invariant.
  assert.equal(signed.intent.kind, 'SWAP_EXACT_OUT');
  assert.match(signed.intent.intent_id, /^0x[0-9a-f]{64}$/);
  assert.equal(
    signed.intent.intent_id,
    op.intent_id,
    'UI exact-out intent_id must equal backend _ui_swap_tx_v0 intent_id',
  );
  // JS op carries the same exact-out field mapping, no exact-in residue.
  assert.equal(signed.intent.amount_out, amountOut);
  assert.equal(signed.intent.max_amount_in, maxAmountIn);
  assert.equal('amount_in' in signed.intent, false);
  assert.equal('min_amount_out' in signed.intent, false);

  // (b) signature binding -- the SEPARATE canonical form (signed `fields`).
  assert.deepEqual(pythonVerify(signed.intent, signed.signature), { ok: true, error: null });
});

test('exact-out parity test FAILS on field-name divergence (in vs out bind differently)', async () => {
  // Same numeric amounts (1000, 1) routed as exact-in vs exact-out MUST yield
  // different intent_ids: the field NAMES (amount_in/min_amount_out vs
  // amount_out/max_amount_in) are part of the hashed payload. If a future edit
  // mislabeled the exact-out amounts, intent_id (a) above would diverge from the
  // backend and this guard documents why.
  const nonce = 11;
  const exactIn = backendSwapOp({ mode: 'in', amountIn: 1_000, minAmountOut: 1, nonce });
  const exactOut = backendSwapOp({ mode: 'out', amountOut: 1_000, maxAmountIn: 1, nonce });

  assert.equal(exactIn.op.kind, 'SWAP_EXACT_IN');
  assert.equal(exactOut.op.kind, 'SWAP_EXACT_OUT');
  // Identical numbers, identical everything-else, but the field names differ ->
  // the canonical hash differs. This is the property that makes (a) meaningful.
  assert.notEqual(
    exactOut.op.intent_id,
    exactIn.op.intent_id,
    'exact-out and exact-in intent_ids must differ for identical numeric amounts',
  );

  // And the JS signer reproduces BOTH backend ids -- proving the JS mapping
  // tracks the field NAMES, not just the numbers.
  const common = {
    senderPubkey: PUBKEY,
    recipient: PUBKEY,
    nonce,
    deadline: exactOut.op.deadline,
    poolId: exactOut.pool_id,
    assetIn: exactOut.asset_in,
    assetOut: exactOut.asset_out,
  };
  const pool = { poolId: exactOut.pool_id, asset0: exactOut.asset_in, asset1: exactOut.asset_out, reserve0: 100_000, reserve1: 100_000 };
  const jsOut = await buildAndSignSwapIntent({
    pool,
    payload: { ...common, kind: 'SWAP_EXACT_OUT', amountOut: 1_000, maxAmountIn: 1 },
    privkey: PRIVKEY,
    chainId: CHAIN_ID,
  });
  const jsIn = await buildAndSignSwapIntent({
    pool,
    payload: { ...common, kind: 'SWAP_EXACT_IN', amountIn: 1_000, minAmountOut: 1 },
    privkey: PRIVKEY,
    chainId: CHAIN_ID,
  });
  assert.equal(jsOut.intent.intent_id, exactOut.op.intent_id);
  assert.equal(jsIn.intent.intent_id, exactIn.op.intent_id);
  assert.notEqual(jsOut.intent.intent_id, jsIn.intent.intent_id);
});

// Capture the apiSwap request body (stub the global fetch). api.js imports
// cleanly under plain Node ESM (import.meta.env only via optional chaining).
async function captureSwapBody(args) {
  let captured = null;
  const priorFetch = globalThis.fetch;
  globalThis.fetch = async (url, opts) => {
    captured = { body: JSON.parse(opts.body) };
    return { ok: true, status: 200, text: async () => JSON.stringify({ ok: true }) };
  };
  try {
    const { apiSwap } = await import('../lib/api.js');
    await apiSwap(args);
  } finally {
    globalThis.fetch = priorFetch;
  }
  assert.ok(captured, 'fetch was not invoked');
  return captured.body;
}

test('exact-out: signed nonce N reaches the wire AND the signature verifies with N', async () => {
  // End-to-end nonce coherence: sign with an EXPLICIT nonce N, prove (1) the
  // apiSwap request body carries exactly N (so the wire matches what was signed),
  // and (2) the Python engine verifies the BLS signature over the signed
  // operation -- which embeds N. If apiSwap dropped the nonce, the backend would
  // re-derive a (possibly different, under concurrency) nonce and the signature
  // would be rejected. This is the regression guard for that footgun.
  const N = 123;
  const backend = backendSwapOp({ mode: 'out', amountOut: 1_000, maxAmountIn: 2_000, nonce: N });

  const signed = await buildAndSignSwapIntent({
    pool: { poolId: backend.pool_id, asset0: backend.asset_in, asset1: backend.asset_out, reserve0: 100_000, reserve1: 100_000 },
    payload: {
      poolId: backend.pool_id,
      assetIn: backend.asset_in,
      assetOut: backend.asset_out,
      kind: 'SWAP_EXACT_OUT',
      amountOut: 1_000,
      maxAmountIn: 2_000,
      senderPubkey: PUBKEY,
      recipient: PUBKEY,
      nonce: N,
      deadline: backend.op.deadline,
    },
    privkey: PRIVKEY,
    chainId: CHAIN_ID,
  });

  // The signed operation embeds N, and its intent_id matches the backend.
  assert.equal(signed.intent.nonce, N);
  assert.equal(signed.intent.intent_id, backend.op.intent_id);

  // (1) The apiSwap body carries exactly the signed nonce N -- mirroring how
  // SwapInterface forwards { nonce: signed.intent.nonce } to apiSwap.
  const body = await captureSwapBody({
    from: 'tASSET0',
    to: 'tASSET1',
    kind: 'SWAP_EXACT_OUT',
    amountOut: 1_000,
    maxAmountIn: 2_000,
    poolId: backend.pool_id,
    assetIn: backend.asset_in,
    assetOut: backend.asset_out,
    senderPubkey: PUBKEY,
    recipient: PUBKEY,
    signature: signed.signature,
    nonce: signed.intent.nonce,
    deadline: signed.intent.deadline,
  });
  assert.equal(body.nonce, N, 'apiSwap must put the signed nonce on the wire');
  assert.equal(body.kind, 'SWAP_EXACT_OUT');

  // (2) The signature verifies in the Python engine over the operation that
  // embeds N. (The signing dict flattens nonce into `fields`, so a wire nonce
  // != signed nonce would change the recomputed dict and reject.)
  assert.deepEqual(pythonVerify(signed.intent, signed.signature), { ok: true, error: null });
});

// Classify a payload with the REAL backend _ui_swap_is_exact_out_v0.
function backendClassify(payload) {
  const script = `
import json, sys
import tools.zeno_ledger_node as node
print(json.dumps({"out": node._ui_swap_is_exact_out_v0(json.load(sys.stdin))}))
`;
  const result = spawnSync('python3', ['-c', script], {
    cwd: REPO_ROOT,
    input: JSON.stringify(payload),
    encoding: 'utf8',
    env: { ...process.env, PYTHONPATH: REPO_ROOT },
  });
  assert.equal(result.status, 0, result.stderr);
  return JSON.parse(result.stdout).out;
}

test('isSwapExactOutPayload mirrors backend mode/kind precedence (incl. mode:null edge)', async () => {
  // The marker lookup must match Python get("mode", get("kind")): an explicit
  // mode:null SHADOWS kind (key present -> None), which a `??` would have gotten
  // wrong. Cross-check JS vs the real backend classifier on the edge cases.
  const cases = [
    { mode: null, kind: 'SWAP_EXACT_OUT' }, // null mode shadows kind -> exact-in
    { kind: 'SWAP_EXACT_OUT' },             // no mode -> kind marker -> exact-out
    { mode: 'exact_out' },                  // mode marker -> exact-out
    { mode: 'exact_in', kind: 'SWAP_EXACT_OUT' }, // mode wins -> exact-in
    { amountOut: 5 },                       // amount key -> exact-out
    { amount_in: 5 },                       // exact-in default
    {},                                     // default exact-in
  ];
  for (const c of cases) {
    const js = isSwapExactOutPayload(c);
    const py = backendClassify(c);
    assert.equal(js, py, `classifier diverged on ${JSON.stringify(c)}: js=${js} py=${py}`);
  }
});
