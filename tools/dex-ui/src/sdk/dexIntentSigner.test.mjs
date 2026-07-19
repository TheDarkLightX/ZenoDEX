import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { test } from 'node:test';
import { bls12_381 as bls } from '@noble/curves/bls12-381';
import {
  buildAndSignCreatePoolIntent,
  buildAndSignLiquidityIntent,
  buildAndSignSwapIntent,
} from './dexIntentSigner.js';
import {
  buildSignedTauTransaction,
  signDexIntentForEngine,
  signPerpOpForEngine,
} from '../../test-support/rawKeySigner.mjs';

const REPO_ROOT = fileURLToPath(new URL('../../../..', import.meta.url));
const CHAIN_ID = 'zeno-ledger-localtest-v0';
const PRIVKEY = `0x${'11'.repeat(32)}`;
const PUBKEY = `0x${Buffer.from(bls.getPublicKey(PRIVKEY.slice(2))).toString('hex')}`;
const externalDexSigner = (intent, { chainId }) => signDexIntentForEngine(intent, {
  privkey: PRIVKEY,
  chainId,
});

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
  });
  assert.equal(result.status, 0, result.stderr);
  return JSON.parse(result.stdout);
}

function pythonVerifyTauPayload(payload) {
  const script = `
import json, sys
from src.integration.tau_net_client import verify_tau_transaction_payload_signature

payload = json.load(sys.stdin)
print(json.dumps({"ok": verify_tau_transaction_payload_signature(payload)}))
`;
  const result = spawnSync('python3', ['-c', script], {
    cwd: REPO_ROOT,
    input: JSON.stringify(payload),
    encoding: 'utf8',
  });
  assert.equal(result.status, 0, result.stderr);
  return JSON.parse(result.stdout);
}

function pythonVerifyPerpSignature({ op, signature, signerPubkey, nonce }) {
  const script = `
import json, sys
from py_ecc.bls import G2Basic
from src.core.perp_submission_auth_message import hash_perp_op_auth_message_v1

obj = json.load(sys.stdin)
msg_hash = hash_perp_op_auth_message_v1(
    obj["op"],
    chain_id=obj["chain_id"],
    signer_pubkey=obj["signer_pubkey"],
    nonce=obj["nonce"],
)
signature = obj["signature"]
if signature.startswith("0x"):
    signature = signature[2:]
print(json.dumps({
    "ok": bool(G2Basic.Verify(bytes.fromhex(obj["signer_pubkey"].removeprefix("0x")), msg_hash, bytes.fromhex(signature)))
}))
`;
  const result = spawnSync('python3', ['-c', script], {
    cwd: REPO_ROOT,
    input: JSON.stringify({
      op,
      signature,
      signer_pubkey: signerPubkey,
      nonce,
      chain_id: CHAIN_ID,
    }),
    encoding: 'utf8',
  });
  assert.equal(result.status, 0, result.stderr);
  return JSON.parse(result.stdout);
}

test('browser DEX intent signature verifies in Python engine policy', async () => {
  const intent = {
    module: 'TauSwap',
    version: '0.1',
    kind: 'REMOVE_LIQUIDITY',
    intent_id: `0x${'ab'.repeat(32)}`,
    sender_pubkey: PUBKEY,
    deadline: 1999999999,
    pool_id: `0x${'cd'.repeat(32)}`,
    amount0_min: 0,
    amount1_min: 0,
    recipient: PUBKEY,
    nonce: 1,
    lp_amount: 1,
  };
  const signature = await signDexIntentForEngine(intent, { privkey: PRIVKEY, chainId: CHAIN_ID });
  assert.match(signature, /^0x[0-9a-f]{192}$/);
  assert.deepEqual(pythonVerify(intent, signature), { ok: true, error: null });
});

test('external liquidity signer builds an add-liquidity intent accepted by Python signature policy', async () => {
  const pool = {
    poolId: `0x${'ef'.repeat(32)}`,
    reserve0: 10000,
    reserve1: 20000,
    lpSupply: 15000,
  };
  const payload = {
    poolId: pool.poolId,
    amount0Desired: 20,
    amount1Desired: 40,
    amount0Min: 0,
    amount1Min: 0,
    senderPubkey: PUBKEY,
    recipient: PUBKEY,
    deadline: 1999999999,
    nonce: 2,
  };
  const signed = await buildAndSignLiquidityIntent({
    kind: 'ADD_LIQUIDITY',
    pool,
    payload,
    signDexIntent: externalDexSigner,
    chainId: CHAIN_ID,
  });
  assert.equal(signed.intent.kind, 'ADD_LIQUIDITY');
  assert.match(signed.intent.intent_id, /^0x[0-9a-f]{64}$/);
  assert.deepEqual(pythonVerify(signed.intent, signed.signature), { ok: true, error: null });
});

test('external swap signer builds an exact-in swap intent accepted by Python signature policy', async () => {
  const pool = {
    poolId: `0x${'ef'.repeat(32)}`,
    asset0: `0x${'01'.repeat(32)}`,
    asset1: `0x${'02'.repeat(32)}`,
    reserve0: 10000,
    reserve1: 20000,
  };
  const payload = {
    poolId: pool.poolId,
    assetIn: pool.asset0,
    assetOut: pool.asset1,
    amountIn: 20,
    minAmountOut: 1,
    senderPubkey: PUBKEY,
    recipient: PUBKEY,
    deadline: 1999999999,
    nonce: 5,
  };
  const signed = await buildAndSignSwapIntent({
    pool,
    payload,
    signDexIntent: externalDexSigner,
    chainId: CHAIN_ID,
  });
  assert.equal(signed.intent.kind, 'SWAP_EXACT_IN');
  assert.match(signed.intent.intent_id, /^0x[0-9a-f]{64}$/);
  assert.deepEqual(pythonVerify(signed.intent, signed.signature), { ok: true, error: null });
});

test('DEX intent builders can delegate signing to an external signer without a browser private key', async () => {
  const signature = `0x${'ab'.repeat(96)}`;
  const seen = [];
  const signed = await buildAndSignCreatePoolIntent({
    payload: {
      senderPubkey: PUBKEY,
      asset0: `0x${'01'.repeat(32)}`,
      asset1: `0x${'02'.repeat(32)}`,
      amount0: 2000,
      amount1: 3000,
      feeBps: 30,
      deadline: 1999999999,
      nonce: 3,
      createdAt: 123,
    },
    chainId: CHAIN_ID,
    signDexIntent: async (intent, options) => {
      seen.push({ intent, options });
      return signature;
    },
  });

  assert.equal(signed.signature, signature);
  assert.equal(signed.intent.kind, 'CREATE_POOL');
  assert.equal(seen.length, 1);
  assert.equal(seen[0].options.chainId, CHAIN_ID);
  assert.equal(seen[0].intent.intent_id, signed.intent.intent_id);
});

test('browser Tau transaction payload signature verifies in Python Tau client policy', async () => {
  const payload = await buildSignedTauTransaction({
    privkey: PRIVKEY,
    sequence_number: 7,
    expiration_time: 1999999999,
    fee_limit: '0',
    operations: {
      '8': [
        {
          module: 'TauPerp',
          version: '1.0',
          market_id: 'perp:ch2p:test',
          action: 'deposit_collateral',
          account_pubkey: PUBKEY.slice(2),
          amount: 1000,
        },
      ],
    },
  });
  assert.equal(payload.sender_pubkey, PUBKEY.slice(2));
  assert.match(payload.signature, /^[0-9a-f]{192}$/);
  assert.deepEqual(pythonVerifyTauPayload(payload), { ok: true });
});

test('browser perps op signature verifies against Python engine auth message', async () => {
  const op = {
    module: 'TauPerp',
    version: '1.0',
    market_id: 'perp:ch2p:test',
    action: 'set_position_pair',
    account_a_pubkey: PUBKEY.slice(2),
    account_b_pubkey: '22'.repeat(48),
    new_position_base_a: 15,
    new_position_base_b: -15,
    deadline: 1999999999,
    nonce_a: 3,
    nonce_b: 8,
  };
  const signature = await signPerpOpForEngine(op, {
    privkey: PRIVKEY,
    chainId: CHAIN_ID,
    signerPubkey: PUBKEY.slice(2),
    nonce: 3,
  });
  assert.match(signature, /^0x[0-9a-f]{192}$/);
  assert.deepEqual(
    pythonVerifyPerpSignature({
      op,
      signature,
      signerPubkey: PUBKEY.slice(2),
      nonce: 3,
    }),
    { ok: true },
  );
});
