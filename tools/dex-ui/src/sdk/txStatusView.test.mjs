import assert from 'node:assert/strict';
import test from 'node:test';

import {
  PENDING_STALE_MS,
  isPendingStale,
  humanizeErrorCode,
  buildExplorerTxUrl,
} from './txStatusView.js';

// ── isPendingStale ────────────────────────────────────────────────────────────
// Pure staleness check. Must NEVER report stale for a non-pending status, and
// must only flip after the threshold elapses. It does not change the status.

test('isPendingStale: only pending can be stale', () => {
  const t0 = 1_000_000;
  assert.equal(isPendingStale('confirmed', t0, t0 + PENDING_STALE_MS + 1), false);
  assert.equal(isPendingStale('failed', t0, t0 + PENDING_STALE_MS + 1), false);
  assert.equal(isPendingStale(undefined, t0, t0 + PENDING_STALE_MS + 1), false);
});

test('isPendingStale: flips exactly at the threshold', () => {
  const t0 = 5_000;
  assert.equal(isPendingStale('pending', t0, t0 + PENDING_STALE_MS - 1), false);
  assert.equal(isPendingStale('pending', t0, t0 + PENDING_STALE_MS), true);
  assert.equal(isPendingStale('pending', t0, t0 + PENDING_STALE_MS + 5_000), true);
});

test('isPendingStale: custom threshold honored', () => {
  assert.equal(isPendingStale('pending', 0, 9_999, 10_000), false);
  assert.equal(isPendingStale('pending', 0, 10_000, 10_000), true);
});

test('isPendingStale: non-finite timestamps => not stale (fail-closed)', () => {
  assert.equal(isPendingStale('pending', NaN, 999_999), false);
  assert.equal(isPendingStale('pending', 0, NaN), false);
  assert.equal(isPendingStale('pending', undefined, undefined), false);
});

// ── humanizeErrorCode ─────────────────────────────────────────────────────────
// Best-effort label map. The raw code is always shown by the caller, so unknown
// codes still surface; here we only assert the humanization is non-fabricating.

test('humanizeErrorCode: no code => null (renders nothing)', () => {
  assert.equal(humanizeErrorCode(null), null);
  assert.equal(humanizeErrorCode(undefined), null);
  assert.equal(humanizeErrorCode(''), null);
  assert.equal(humanizeErrorCode('   '), null);
  assert.equal(humanizeErrorCode(42), null);
});

test('humanizeErrorCode: exact ledger codes map to readable text', () => {
  assert.equal(humanizeErrorCode('bad_intent_nonce'), 'Invalid transaction nonce');
  assert.equal(humanizeErrorCode('replay_guard_failed'), 'Rejected by replay guard (nonce already spent)');
  assert.equal(humanizeErrorCode('bad_assets'), 'Unrecognized token pair for this pool');
  // Case-insensitive on the normalized code.
  assert.equal(humanizeErrorCode('BAD_INTENT_NONCE'), 'Invalid transaction nonce');
});

test('humanizeErrorCode: substring families for free-form settlement reasons', () => {
  // stable_error_code_v0 normalizes "redemption blocked by stale oracle".
  assert.equal(humanizeErrorCode('redemption_blocked_by_stale_oracle'), 'Blocked by a stale price oracle');
  assert.equal(humanizeErrorCode('swap_deadline_passed_height'), 'Transaction deadline passed before inclusion');
  assert.equal(humanizeErrorCode('output_below_min_amount_out'), 'Output fell below your minimum received');
});

test('humanizeErrorCode: unknown code => neutral humanization (no fabricated reason)', () => {
  const out = humanizeErrorCode('some_brand_new_code');
  assert.equal(out, 'Some brand new code');
  // It is a generic readable phrase, not an invented specific cause.
});

// ── buildExplorerTxUrl ────────────────────────────────────────────────────────
// Honesty gate: a URL is built ONLY from an operator-configured template. No
// template => null (skip the link). We never invent an explorer host.

test('buildExplorerTxUrl: no template configured => null', () => {
  assert.equal(buildExplorerTxUrl({}, '0xabc'), null);
  assert.equal(buildExplorerTxUrl(null, '0xabc'), null);
  assert.equal(buildExplorerTxUrl(undefined, '0xabc'), null);
  // Field present but not a valid template.
  assert.equal(buildExplorerTxUrl({ explorerTxUrlTemplate: 'https://x/tx/' }, '0xabc'), null);
});

test('buildExplorerTxUrl: template + hash => substituted URL', () => {
  const cfg = { explorerTxUrlTemplate: 'https://explorer.example.org/tx/{txHash}' };
  assert.equal(buildExplorerTxUrl(cfg, '0xABC123'), 'https://explorer.example.org/tx/0xABC123');
});

test('buildExplorerTxUrl: missing hash => null even with template', () => {
  const cfg = { explorerTxUrlTemplate: 'https://explorer.example.org/tx/{txHash}' };
  assert.equal(buildExplorerTxUrl(cfg, ''), null);
  assert.equal(buildExplorerTxUrl(cfg, null), null);
  assert.equal(buildExplorerTxUrl(cfg, '   '), null);
});

test('buildExplorerTxUrl: hash is URI-encoded into the template', () => {
  const cfg = { explorerTxUrlTemplate: 'https://explorer.example.org/tx/{txHash}' };
  // A stray space/slash must not break out of the path segment.
  assert.equal(
    buildExplorerTxUrl(cfg, 'a b/c'),
    'https://explorer.example.org/tx/a%20b%2Fc',
  );
});
