// Copyright (c) DarkLightX/Dana Edwards. All rights reserved.

import assert from 'node:assert/strict';
import test from 'node:test';
import { deriveSwapFinality, extractReceiptHash } from './swapFinality.js';

test('swap finality remains pending for a tx hash without acceptance evidence', () => {
  const finality = deriveSwapFinality({ txHash: '0xabc123' });
  assert.equal(finality.accepted, false);
  assert.equal(finality.status, 'pending');
  assert.equal(finality.txHash, '0xabc123');
  assert.equal(finality.acceptanceEvidence, '');
});

test('tx_accepted must be exactly true to mark a swap accepted', () => {
  assert.equal(deriveSwapFinality({ tx_accepted: true }).accepted, true);
  assert.equal(deriveSwapFinality({ tx_accepted: 1 }).accepted, false);
  assert.equal(deriveSwapFinality({ tx_accepted: 'true' }).accepted, false);
});

test('receipt.accepted=true marks a swap accepted and reports receipt evidence', () => {
  const finality = deriveSwapFinality({
    receipt: {
      accepted: true,
      receipt_hash: 'receipt-123',
    },
  });
  assert.equal(finality.accepted, true);
  assert.equal(finality.status, 'confirmed');
  assert.equal(finality.receiptHash, 'receipt-123');
  assert.equal(finality.acceptanceEvidence, 'receipt.accepted=true');
});

test('receipt hash extraction accepts top-level and body hashes only', () => {
  assert.equal(extractReceiptHash({ body: { receipt_hash: 'nested-123' } }), 'nested-123');
  assert.equal(extractReceiptHash({ receiptHash: 'camel-123' }), 'camel-123');
  assert.equal(extractReceiptHash({ accepted: true }), '');
  assert.equal(extractReceiptHash(null), '');
});
