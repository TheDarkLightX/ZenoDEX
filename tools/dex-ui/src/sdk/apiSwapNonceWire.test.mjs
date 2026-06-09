// Wire contract: apiSwap MUST serialize the SIGNED nonce into the request body.
//
// SwapInterface signs the swap intent over an explicit nonce (signed.intent.nonce)
// and passes that same nonce to apiSwap. If apiSwap drops it, the backend
// re-derives the nonce from its snapshot; under concurrency (another tx bumps the
// sender nonce between sign and submit) the derived nonce differs from the signed
// one -> different intent_id + signing dict -> BLS signature REJECTED. These tests
// pin that the nonce reaches the wire (so the wire matches the signature) for both
// exact-in and exact-out, and that an absent nonce is omitted (backend re-derives,
// the prior fallback).
import assert from 'node:assert/strict';
import { test } from 'node:test';

// apiSwap calls the global fetch; stub it to capture the serialized request body.
// (api.js accesses import.meta.env only via optional chaining, so it imports
// cleanly under plain Node ESM with no Vite transform.)
async function captureSwapBody(args) {
  let captured = null;
  const priorFetch = globalThis.fetch;
  globalThis.fetch = async (url, opts) => {
    captured = { url, body: JSON.parse(opts.body), method: opts.method };
    return { ok: true, status: 200, text: async () => JSON.stringify({ ok: true }) };
  };
  try {
    const { apiSwap } = await import('../lib/api.js');
    await apiSwap(args);
  } finally {
    globalThis.fetch = priorFetch;
  }
  assert.ok(captured, 'fetch was not invoked');
  return captured;
}

test('apiSwap serializes the signed nonce into the exact-in request body', async () => {
  const signedNonce = 42;
  const captured = await captureSwapBody({
    from: 'tA',
    to: 'tB',
    amountIn: 10,
    minAmountOut: 1,
    nonce: signedNonce,
    senderPubkey: `0x${'aa'.repeat(48)}`,
    signature: `0x${'bb'.repeat(96)}`,
  });
  assert.equal(captured.method, 'POST');
  assert.equal(captured.body.nonce, signedNonce, 'wire nonce must equal the signed nonce');
  assert.equal(captured.body.amountIn, 10);
  assert.equal(captured.body.minAmountOut, 1);
  assert.equal('amountOut' in captured.body, false);
});

test('apiSwap serializes the signed nonce into the exact-out request body', async () => {
  const signedNonce = 7;
  const captured = await captureSwapBody({
    from: 'tA',
    to: 'tB',
    kind: 'SWAP_EXACT_OUT',
    amountOut: 100,
    maxAmountIn: 200,
    nonce: signedNonce,
    senderPubkey: `0x${'aa'.repeat(48)}`,
    signature: `0x${'bb'.repeat(96)}`,
  });
  assert.equal(captured.body.nonce, signedNonce, 'wire nonce must equal the signed nonce');
  assert.equal(captured.body.kind, 'SWAP_EXACT_OUT');
  assert.equal(captured.body.amountOut, 100);
  assert.equal(captured.body.maxAmountIn, 200);
  // Unambiguous exact-out body: no exact-in keys (passes the backend's
  // _require_unambiguous_swap_payload_v0 gate).
  assert.equal('amountIn' in captured.body, false);
  assert.equal('minAmountOut' in captured.body, false);
});

test('apiSwap omits nonce when none is supplied (backend re-derives -- fallback preserved)', async () => {
  const captured = await captureSwapBody({
    from: 'tA',
    to: 'tB',
    amountIn: 10,
    minAmountOut: 1,
    signature: `0x${'bb'.repeat(96)}`,
    // no nonce
  });
  assert.equal('nonce' in captured.body, false);
});
