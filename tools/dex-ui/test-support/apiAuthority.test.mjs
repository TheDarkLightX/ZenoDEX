import assert from 'node:assert/strict';
import test from 'node:test';

import { apiFetchZenoOracleJson } from '../src/lib/api.js';

test('Oracle API authority is explicit and fail closed', async (t) => {
  const originalWindow = globalThis.window;
  const originalFetch = globalThis.fetch;
  t.after(() => {
    globalThis.window = originalWindow;
    globalThis.fetch = originalFetch;
  });

  let requestedUrl = null;
  globalThis.fetch = async (url) => {
    requestedUrl = String(url);
    return {
      ok: true,
      text: async () => '{"ok":true}',
    };
  };

  globalThis.window = { __ZENODEX_CONFIG__: {} };
  await assert.rejects(
    apiFetchZenoOracleJson('/api/oracle/dashboard'),
    /zeno_oracle_api_base_unconfigured/,
  );
  assert.equal(requestedUrl, null);

  globalThis.window.__ZENODEX_CONFIG__ = { zenoOracleApiBase: '' };
  assert.deepEqual(await apiFetchZenoOracleJson('/api/oracle/dashboard'), { ok: true });
  assert.equal(requestedUrl, '/api/oracle/dashboard');

  globalThis.window.__ZENODEX_CONFIG__ = {
    zenoOracleApiBase: 'https://oracle.example.invalid/',
  };
  assert.deepEqual(await apiFetchZenoOracleJson('/api/oracle/dashboard'), { ok: true });
  assert.equal(requestedUrl, 'https://oracle.example.invalid/api/oracle/dashboard');

  globalThis.window.__ZENODEX_CONFIG__ = { zenoOracleApiBase: null };
  await assert.rejects(
    apiFetchZenoOracleJson('/api/oracle/dashboard'),
    /zeno_oracle_api_base_unconfigured/,
  );
});
