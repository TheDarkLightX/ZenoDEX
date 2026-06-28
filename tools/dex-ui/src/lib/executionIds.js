const SUPERVISOR_EXECUTION_ID_PREFIX = 'strategy-ui-supervisor';
const SUPERVISOR_RANDOM_BYTE_COUNT = 16;
const MAX_EXECUTION_ID_LENGTH = 128;

function bytesToHex(bytes) {
  return Array.from(bytes, (byte) => byte.toString(16).padStart(2, '0')).join('');
}

function cryptoRandomHex(cryptoProvider) {
  if (typeof cryptoProvider?.getRandomValues !== 'function') {
    return '';
  }
  const bytes = new Uint8Array(SUPERVISOR_RANDOM_BYTE_COUNT);
  cryptoProvider.getRandomValues(bytes);
  return bytesToHex(bytes);
}

function fallbackRandomToken(randomProvider) {
  const rawValue = typeof randomProvider === 'function' ? randomProvider() : Math.random();
  const finiteValue = Number.isFinite(rawValue) ? Math.abs(rawValue) : Math.random();
  const token = finiteValue.toString(36).replace('0.', '');
  return token || '0';
}

/**
 * Design by Contract:
 * - Precondition: callers generate this at the request boundary for one supervisor tick.
 * - Invariant: the returned replay key is non-empty, whitespace-free, and <= 128 chars.
 * - Postcondition: cryptographic browser randomness is preferred; fallback entropy is
 *   still per-call and non-constant so the UI no longer has a predictable single-use key.
 */
export function createSupervisorExecutionId({
  now = Date.now,
  random = Math.random,
  crypto = globalThis.crypto,
} = {}) {
  const rawTimestamp = typeof now === 'function' ? now() : Date.now();
  const timestamp = Number.isFinite(rawTimestamp) ? Math.trunc(rawTimestamp) : Date.now();
  const entropy = cryptoRandomHex(crypto) || fallbackRandomToken(random);
  const executionId = `${SUPERVISOR_EXECUTION_ID_PREFIX}-${timestamp.toString(36)}-${entropy}`;
  return executionId.slice(0, MAX_EXECUTION_ID_LENGTH);
}
