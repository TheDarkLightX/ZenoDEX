import assert from 'node:assert/strict';
import { test } from 'node:test';
import { apiSwap } from '../lib/api.js';
import { loadSwapPools, resolveWalletTokenBalance } from '../lib/swapData.js';

test('apiSwap preserves signed intent nonce and idempotency fields', async () => {
  const calls = [];
  const previousFetch = globalThis.fetch;
  globalThis.fetch = async (url, options = {}) => {
    calls.push({ url, options });
    return {
      ok: true,
      text: async () => JSON.stringify({ ok: true, tx_accepted: true, txHash: '0xabc' }),
    };
  };
  try {
    await apiSwap({
      from: 'tAGRS',
      to: 'tZDEX',
      amountIn: 100,
      minAmountOut: 1,
      senderPubkey: `0x${'11'.repeat(48)}`,
      recipient: `0x${'11'.repeat(48)}`,
      nonce: 7,
      deadline: 1999999999,
      signature: `0x${'22'.repeat(96)}`,
      timeMs: 1778740101000,
      txId: 'ui-swap-regression-v0',
    });
  } finally {
    globalThis.fetch = previousFetch;
  }
  assert.equal(calls.length, 1);
  assert.equal(calls[0].url, '/api/swap');
  const body = JSON.parse(calls[0].options.body);
  assert.equal(body.nonce, 7);
  assert.equal(body.deadline, 1999999999);
  assert.equal(body.time_ms, 1778740101000);
  assert.equal(body.tx_id, 'ui-swap-regression-v0');
});

test('loadSwapPools exposes live account balances for swap validation', async () => {
  const previousFetch = globalThis.fetch;
  globalThis.fetch = async (url) => {
    assert.equal(url, '/api/pools?account=0xabc');
    return {
      ok: true,
      text: async () => JSON.stringify({
        ok: true,
        source: 'zeno_ledger_node_live',
        account: '0xabc',
        account_last_nonce: 4,
        tokens: [
          { symbol: 'tAGRS', asset_id: `0x${'01'.repeat(32)}` },
          { symbol: 'tZDEX', asset_id: `0x${'02'.repeat(32)}` },
        ],
        pools: [
          {
            pool_id: `0x${'aa'.repeat(32)}`,
            token0: 'tAGRS',
            token1: 'tZDEX',
            asset0: `0x${'01'.repeat(32)}`,
            asset1: `0x${'02'.repeat(32)}`,
            reserve0: 100000,
            reserve1: 100000,
            fee_bps: 30,
            account_balance0: 50000,
            account_balance1: 50000,
          },
        ],
      }),
    };
  };
  let feed;
  try {
    feed = await loadSwapPools({ account: '0xabc' });
  } finally {
    globalThis.fetch = previousFetch;
  }
  assert.equal(feed.source, 'api');
  assert.equal(feed.accountLastNonce, 4);
  assert.equal(feed.accountBalances.TAGRS, 50000);
  assert.equal(feed.accountBalances.TZDEX, 50000);
  assert.equal(resolveWalletTokenBalance({ balance: feed.accountBalances }, 'tAGRS'), 50000);
  assert.equal(resolveWalletTokenBalance({ balance: feed.accountBalances }, 'tZDEX'), 50000);
});
