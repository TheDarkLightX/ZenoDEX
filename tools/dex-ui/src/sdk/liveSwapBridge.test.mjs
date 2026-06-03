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

// Mirror of PoolDashboard.normalizeLivePool's per-account balance accessors. The
// Pool surface reads `accountBalance0 ?? account_balance0` (and ...1) straight off
// the same /api/pools row that the Swap feed aggregates. Replicated inline (one
// line each) so this pure node:test can assert cross-surface equality without a
// JSX/DOM runner. If PoolDashboard changes those accessors, update this mirror.
function poolSurfaceBalance0(row) {
  const v = Number(row?.accountBalance0 ?? row?.account_balance0);
  return Number.isFinite(v) ? v : null;
}
function poolSurfaceBalance1(row) {
  const v = Number(row?.accountBalance1 ?? row?.account_balance1);
  return Number.isFinite(v) ? v : null;
}

// REGRESSION (community bug, swap/pool side): a funded account must show the SAME
// token balance on the Pool feed and the Swap feed because both read the same
// /api/pools?account= row whose account_balance{0,1} come from the single ledger
// account_state.balances source (tools/zeno_ledger_node.py). Swap previously
// ignored that feed and showed a stale local-wallet balance; this asserts parity.
test('funded account shows identical token balance on Pool feed and Swap feed', async () => {
  const account = `0x${'77'.repeat(48)}`;
  const poolRow = {
    pool_id: `0x${'aa'.repeat(32)}`,
    token0: 'tAGRS',
    token1: 'tZDEX',
    asset0: `0x${'01'.repeat(32)}`,
    asset1: `0x${'02'.repeat(32)}`,
    reserve0: 100000,
    reserve1: 100000,
    fee_bps: 30,
    // Node emits both snake_case and camelCase mirrors; use snake_case here so the
    // test also exercises the `?? account_balance0` fallback in both surfaces.
    account_balance0: 42000,
    account_balance1: 31000,
    account_lp_balance: 1234,
  };
  const previousFetch = globalThis.fetch;
  globalThis.fetch = async (url) => {
    assert.equal(url, `/api/pools?account=${encodeURIComponent(account)}`);
    return {
      ok: true,
      text: async () => JSON.stringify({
        ok: true,
        source: 'zeno_ledger_node_live',
        account,
        account_last_nonce: 9,
        tokens: [
          { symbol: 'tAGRS', asset_id: poolRow.asset0 },
          { symbol: 'tZDEX', asset_id: poolRow.asset1 },
        ],
        pools: [poolRow],
      }),
    };
  };
  let feed;
  try {
    feed = await loadSwapPools({ account });
  } finally {
    globalThis.fetch = previousFetch;
  }

  // Pool-surface view of this account's per-token balances.
  const poolBalAgrs = poolSurfaceBalance0(poolRow);
  const poolBalZdex = poolSurfaceBalance1(poolRow);
  assert.equal(poolBalAgrs, 42000);
  assert.equal(poolBalZdex, 31000);

  // Swap-surface view of the SAME account's per-token balances (live feed merged
  // into the wallet exactly as SwapInterface.liveWallet does).
  const swapWallet = { balance: { ...feed.accountBalances } };
  const swapBalAgrs = resolveWalletTokenBalance(swapWallet, 'tAGRS');
  const swapBalZdex = resolveWalletTokenBalance(swapWallet, 'tZDEX');

  // The core consistency assertion: Pool feed balance === Swap feed balance.
  assert.equal(swapBalAgrs, poolBalAgrs, 'tAGRS balance must match across Pool and Swap feeds');
  assert.equal(swapBalZdex, poolBalZdex, 'tZDEX balance must match across Pool and Swap feeds');
  // And both must equal the single ledger source value (no surface-local drift).
  assert.equal(swapBalAgrs, 42000);
  assert.equal(swapBalZdex, 31000);
});

// REGRESSION (token-order alignment): when the node emits a pool whose token0 is
// lexicographically AFTER token1, loadSwapPools canonicalizes to sorted order. The
// per-account balances MUST be swapped together with the assets/reserves, or the
// Swap feed would label each token's balance with the WRONG token — diverging from
// the Pool surface, which reads the node order as-is. The node's own pools are not
// guaranteed to arrive pre-sorted, so this path is reachable in production.
test('canonical token re-ordering keeps each account balance with its own token', async () => {
  const account = `0x${'99'.repeat(48)}`;
  // Source order is reversed (token0 'ZDEX' > token1 'AGRS'): forces an alignment swap.
  const poolRow = {
    pool_id: `0x${'cc'.repeat(32)}`,
    token0: 'ZDEX',
    token1: 'AGRS',
    asset0: `0x${'02'.repeat(32)}`,
    asset1: `0x${'01'.repeat(32)}`,
    reserve0: 200000,
    reserve1: 100000,
    fee_bps: 30,
    account_balance0: 999, // belongs to ZDEX (source token0)
    account_balance1: 111, // belongs to AGRS (source token1)
  };
  const previousFetch = globalThis.fetch;
  globalThis.fetch = async () => ({
    ok: true,
    text: async () => JSON.stringify({
      ok: true,
      source: 'zeno_ledger_node_live',
      account,
      account_last_nonce: 2,
      tokens: [
        { symbol: 'ZDEX', asset_id: poolRow.asset0 },
        { symbol: 'AGRS', asset_id: poolRow.asset1 },
      ],
      pools: [poolRow],
    }),
  });
  let feed;
  try {
    feed = await loadSwapPools({ account });
  } finally {
    globalThis.fetch = previousFetch;
  }
  // Pool surface reads the node row as-is (no re-sort): ZDEX=999, AGRS=111.
  const poolZdex = Number(poolRow.account_balance0);
  const poolAgrs = Number(poolRow.account_balance1);
  // Swap surface must report the SAME mapping after canonicalization.
  const wallet = { balance: { ...feed.accountBalances } };
  assert.equal(resolveWalletTokenBalance(wallet, 'ZDEX'), poolZdex, 'ZDEX balance must not be swapped');
  assert.equal(resolveWalletTokenBalance(wallet, 'AGRS'), poolAgrs, 'AGRS balance must not be swapped');
  assert.equal(resolveWalletTokenBalance(wallet, 'ZDEX'), 999);
  assert.equal(resolveWalletTokenBalance(wallet, 'AGRS'), 111);
});

// FAIL-CLOSED: with no connected wallet/account, neither surface may fabricate a
// balance. loadSwapPools must expose an empty accountBalances map and
// resolveWalletTokenBalance must return null (not 0, not a fallback number).
test('no connected account fabricates no swap/pool balances', async () => {
  const previousFetch = globalThis.fetch;
  // Node omits account_* fields when no account is supplied (see
  // _ui_pool_rows_from_snapshot_v0: account fields only added when account_pubkey).
  globalThis.fetch = async (url) => {
    assert.equal(url, '/api/pools');
    return {
      ok: true,
      // Mirrors the real node's anonymous /api/pools response: top-level `account`
      // is null and `account_last_nonce` is OMITTED entirely (the node only adds
      // that key when an account_pubkey is supplied — see _ui_pools_response_v0).
      text: async () => JSON.stringify({
        ok: true,
        source: 'zeno_ledger_node_live',
        account: null,
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
            // No account_balance* fields: no wallet connected.
          },
        ],
      }),
    };
  };
  let feed;
  try {
    feed = await loadSwapPools({});
  } finally {
    globalThis.fetch = previousFetch;
  }
  assert.equal(feed.source, 'api');
  assert.deepEqual(feed.accountBalances, {}, 'no account => no fabricated balances');
  assert.equal(feed.accountLastNonce, null);
  // resolveWalletTokenBalance must not invent a balance from an empty feed.
  assert.equal(resolveWalletTokenBalance({ balance: feed.accountBalances }, 'tAGRS'), null);
  assert.equal(resolveWalletTokenBalance({ balance: feed.accountBalances }, 'tZDEX'), null);
  // A null wallet (truly disconnected) yields null, never a number.
  assert.equal(resolveWalletTokenBalance(null, 'tAGRS'), null);
});

// FAIL-CLOSED on feed failure: when /api/pools is unreachable, the feed falls back
// but MUST NOT carry per-account balances — the fallback is anonymous pool shape
// only, never a funded-looking account state.
test('fallback feed (api unreachable) carries no account balances', async () => {
  const account = `0x${'88'.repeat(48)}`;
  const previousFetch = globalThis.fetch;
  globalThis.fetch = async () => {
    throw new Error('network down');
  };
  let feed;
  try {
    feed = await loadSwapPools({ account });
  } finally {
    globalThis.fetch = previousFetch;
  }
  assert.equal(feed.source, 'fallback');
  assert.deepEqual(feed.accountBalances, {}, 'fallback must not fabricate account balances');
  assert.equal(feed.accountLastNonce, null);
  assert.equal(feed.account, account, 'fallback echoes the requested account but with no balances');
  assert.equal(resolveWalletTokenBalance({ balance: feed.accountBalances }, 'tAGRS'), null);
});
