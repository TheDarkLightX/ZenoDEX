import assert from 'node:assert/strict';
import { test } from 'node:test';
import {
  apiGetPerpsWalletStatus,
  apiGetZusdWalletStatus,
  apiGetZusdMonetaryStatus,
} from '../lib/api.js';

// Regression for the community report "I got 50k of both but it only shows at LP
// Pool, not swap or perps". The Pool surface forwards ?account= to the backend;
// these status fns must do the same so Perps + zUSD become account-aware too.

const ACCOUNT = `0x${'ab'.repeat(48)}`;

async function captureStatusUrl(fn, options) {
  const calls = [];
  const previousFetch = globalThis.fetch;
  globalThis.fetch = async (url) => {
    calls.push(url);
    return {
      ok: true,
      text: async () => JSON.stringify({ ok: true, status: {} }),
    };
  };
  try {
    await fn(options);
  } finally {
    globalThis.fetch = previousFetch;
  }
  assert.equal(calls.length, 1);
  return calls[0];
}

const CASES = [
  ['apiGetPerpsWalletStatus', apiGetPerpsWalletStatus, '/api/perps/wallet/status'],
  ['apiGetZusdWalletStatus', apiGetZusdWalletStatus, '/api/zusd/wallet/status'],
  ['apiGetZusdMonetaryStatus', apiGetZusdMonetaryStatus, '/api/zusd/monetary/status'],
];

for (const [name, fn, base] of CASES) {
  test(`${name} forwards account as an encoded query param`, async () => {
    const url = await captureStatusUrl(fn, { account: ACCOUNT });
    assert.equal(url, `${base}?account=${encodeURIComponent(ACCOUNT)}`);
  });

  test(`${name} omits the account param when no account is provided`, async () => {
    const url = await captureStatusUrl(fn, {});
    assert.equal(url, base);
  });

  test(`${name} treats a blank account as unauthenticated (no param)`, async () => {
    const url = await captureStatusUrl(fn, { account: '   ' });
    assert.equal(url, base);
  });

  test(`${name} does not leak account into fetch options`, async () => {
    let seenOptions = null;
    const previousFetch = globalThis.fetch;
    globalThis.fetch = async (_url, options = {}) => {
      seenOptions = options;
      return { ok: true, text: async () => JSON.stringify({ ok: true, status: {} }) };
    };
    try {
      await fn({ account: ACCOUNT, timeoutMs: 1234 });
    } finally {
      globalThis.fetch = previousFetch;
    }
    assert.ok(seenOptions, 'fetch should have been called');
    assert.equal(seenOptions.account, undefined);
    assert.equal(seenOptions.method, 'GET');
  });
}
