import assert from 'node:assert/strict';
import test from 'node:test';

import { deriveSwapFinality } from './swapFinality.js';

// Regression net for the removed fake-green timer. Finality must come ONLY from the
// ledger's synchronous acceptance signal — never from an optimistic auto-confirm.

test('(a) tx_accepted === true => confirmed', () => {
  const out = deriveSwapFinality({
    ok: true,
    tx_accepted: true,
    txHash: '0xabc',
    height: 42,
  });
  assert.equal(out.accepted, true);
  assert.equal(out.status, 'confirmed');
  assert.equal(out.txHash, '0xabc');
  assert.equal(out.height, 42);
});

test('(b) receipt.accepted === true => confirmed', () => {
  const receipt = { accepted: true, receipt_hash: '0xdeadbeef' };
  const out = deriveSwapFinality({
    ok: true,
    tx_hash: '0xfeed',
    receipt,
  });
  assert.equal(out.accepted, true);
  assert.equal(out.status, 'confirmed');
  assert.equal(out.txHash, '0xfeed');
  assert.equal(out.receipt, receipt);
});

test('(c) neither acceptance flag => pending (NOT confirmed)', () => {
  const out = deriveSwapFinality({
    ok: true,
    txHash: '0x123',
    receipt: { accepted: false },
  });
  assert.equal(out.accepted, false);
  assert.equal(out.status, 'pending');
  // Honest: an unconfirmed swap is never reported as confirmed.
  assert.notEqual(out.status, 'confirmed');
});

test('(c2) no acceptance fields at all => pending', () => {
  const out = deriveSwapFinality({ ok: true });
  assert.equal(out.accepted, false);
  assert.equal(out.status, 'pending');
  assert.equal(out.txHash, '');
  assert.equal(out.height, null);
  assert.equal(out.receipt, null);
});

test('(d) ok === false => throws (rejected), preserving call-site catch', () => {
  assert.throws(
    () => deriveSwapFinality({ ok: false, error: 'insufficient_liquidity' }),
    /insufficient_liquidity/,
  );
  // Default rejection message when none provided.
  assert.throws(
    () => deriveSwapFinality({ ok: false }),
    /swap_rejected/,
  );
});

test('acceptance requires strict true (truthy non-true does not confirm)', () => {
  // tx_accepted must be exactly true; a stray truthy value must not fabricate finality.
  const out = deriveSwapFinality({ ok: true, tx_accepted: 1, txHash: '0x9' });
  assert.equal(out.accepted, false);
  assert.equal(out.status, 'pending');
});

test('missing txHash stays falsy so the call-site missing-hash branch fires', () => {
  const out = deriveSwapFinality({ ok: true, tx_accepted: true });
  assert.equal(out.txHash, '');
  assert.equal(Boolean(out.txHash), false);
});

test('null/undefined response => pending, no throw', () => {
  for (const value of [null, undefined]) {
    const out = deriveSwapFinality(value);
    assert.equal(out.accepted, false);
    assert.equal(out.status, 'pending');
    assert.equal(out.txHash, '');
    assert.equal(out.height, null);
    assert.equal(out.receipt, null);
  }
});
