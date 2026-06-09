// txStatusView.js — pure, dependency-free helpers for honest transaction status UX.
//
// No-fake-green contract: nothing here ever upgrades a status the ledger did not
// assert. These helpers only *describe* a status that was already derived from a
// real source (deriveSwapFinality for the live swap response, or the committed
// /api/history receipt). They add NO confirmation signal of their own.
//
// Dependency-free so the SDK test tier (node:test, src/sdk/*.test.mjs) can import
// it without pulling in React.

// How long a swap may sit in the honest 'pending' state before we surface a
// "taking longer than expected" affordance. This does NOT change the status —
// it only offers the user a way to re-check a REAL source (history backfill).
export const PENDING_STALE_MS = 45_000;

/**
 * Has a pending swap been awaiting confirmation long enough to warrant a manual
 * "Refresh status" affordance?  Pure function of timestamps; never mutates status.
 *
 * @param {('pending'|'confirmed'|'failed'|string|null|undefined)} status
 * @param {number|null|undefined} submittedAt epoch ms the swap was submitted
 * @param {number} nowMs current epoch ms
 * @param {number} [thresholdMs=PENDING_STALE_MS]
 * @returns {boolean}
 */
export function isPendingStale(status, submittedAt, nowMs, thresholdMs = PENDING_STALE_MS) {
  if (status !== 'pending') return false;
  const started = Number(submittedAt);
  const now = Number(nowMs);
  if (!Number.isFinite(started) || !Number.isFinite(now)) return false;
  return now - started >= Number(thresholdMs);
}

// Human-readable labels for the error_code families the ZenoLedger emits on a
// rejected/failed transaction (normalized by stable_error_code_v0: lowercased,
// non-alnum -> '_'). This is a BEST-EFFORT map: an unmapped code falls back to a
// neutral humanization and the raw code is ALWAYS kept visible by the caller.
//
// Exact codes (request-validation 'bad_*' family + common settlement reasons).
const EXACT_ERROR_LABELS = Object.freeze({
  bad_assets: 'Unrecognized token pair for this pool',
  bad_amount_in: 'Invalid input amount',
  bad_min_amount_out: 'Invalid minimum-output amount',
  min_amount_out_too_high: 'Minimum output set too high — price moved against this size',
  bad_intent: 'Malformed swap intent',
  bad_signed_intent: 'Malformed or unsigned swap intent',
  bad_intent_nonce: 'Invalid transaction nonce',
  bad_nonce_unused: 'Transaction nonce already used',
  missing_signature: 'Missing transaction signature',
  replay_guard_failed: 'Rejected by replay guard (nonce already spent)',
  request_replay: 'Duplicate request rejected by replay guard',
  strong_replay: 'Duplicate request rejected by replay guard',
  pool_event_replay: 'Pool state changed; quote no longer valid',
  insufficient_collateral: 'Insufficient collateral',
  insufficient_liquidity: 'Insufficient pool liquidity for this trade',
  unknown_error: 'Rejected by the ledger',
});

// Substring matchers for the longer free-form settlement reasons that get
// normalized into error_code (e.g. "redemption blocked by stale oracle" ->
// "redemption_blocked_by_stale_oracle"). Ordered; first hit wins.
const SUBSTRING_ERROR_LABELS = Object.freeze([
  ['nonce', 'Transaction nonce was rejected'],
  ['signature', 'Transaction signature was rejected'],
  ['deadline', 'Transaction deadline passed before inclusion'],
  ['expired', 'Transaction expired before inclusion'],
  ['min_amount_out', 'Output fell below your minimum received'],
  ['slippage', 'Price moved beyond your slippage tolerance'],
  ['insufficient', 'Insufficient balance or liquidity'],
  ['stale_oracle', 'Blocked by a stale price oracle'],
  ['replay', 'Rejected by replay protection'],
]);

/**
 * Convert a raw, normalized error_code into a human sentence. Returns null when
 * there is no code (so the caller renders nothing) — never invents a reason.
 *
 * @param {string|null|undefined} rawCode normalized error_code from the receipt
 * @returns {string|null} human-readable text, or null when no code is present
 */
export function humanizeErrorCode(rawCode) {
  if (typeof rawCode !== 'string') return null;
  const code = rawCode.trim();
  if (!code) return null;
  const lower = code.toLowerCase();

  if (Object.prototype.hasOwnProperty.call(EXACT_ERROR_LABELS, lower)) {
    return EXACT_ERROR_LABELS[lower];
  }
  for (const [needle, label] of SUBSTRING_ERROR_LABELS) {
    if (lower.includes(needle)) return label;
  }
  // Neutral fallback: turn snake_case into a readable phrase. The caller still
  // shows the raw code, so this never hides the underlying machine reason.
  const words = lower.replace(/[_]+/g, ' ').trim();
  if (!words) return null;
  return words.charAt(0).toUpperCase() + words.slice(1);
}

/**
 * Build a block-explorer transaction URL ONLY from an operator-configured
 * template. Returns null when no template is configured — we never fabricate a
 * URL (an invented explorer host would be a dishonest dead link).
 *
 * Supported config field (via getRuntimeConfig()): `explorerTxUrlTemplate`, a
 * string containing the `{txHash}` placeholder, e.g.
 *   "https://explorer.example.org/tx/{txHash}".
 *
 * @param {object|null|undefined} runtimeConfig result of getRuntimeConfig()
 * @param {string|null|undefined} txHash
 * @returns {string|null} absolute URL, or null when not configured / invalid
 */
export function buildExplorerTxUrl(runtimeConfig, txHash) {
  const template = runtimeConfig && typeof runtimeConfig === 'object'
    ? runtimeConfig.explorerTxUrlTemplate
    : null;
  if (typeof template !== 'string' || !template.includes('{txHash}')) {
    return null;
  }
  const hash = typeof txHash === 'string' ? txHash.trim() : '';
  if (!hash) return null;
  return template.replace('{txHash}', encodeURIComponent(hash));
}
