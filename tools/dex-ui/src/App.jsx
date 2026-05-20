import { useCallback, useEffect, useMemo, useState } from 'react';
import './App.css';

const POOL_ID = '0xcc9c112f06b5ba4cd276419759e7b3e203ede2c64aa45ba75e24fa4609d9c686';
const ASSET0 = '0x1111111111111111111111111111111111111111111111111111111111111111';
const ASSET1 = '0x2222222222222222222222222222222222222222222222222222222222222222';

const NODES = {
  writer: {
    key: 'writer',
    label: 'Writer',
    role: 'direct write node',
    basePath: '/ledger/writer',
    writeExpectation: 'accepts faucet and swap writes',
  },
  forwarder: {
    key: 'forwarder',
    label: 'Forwarder',
    role: 'submission forwarding node',
    basePath: '/ledger/forwarder',
    writeExpectation: 'forwards accepted writes to writer',
  },
  readonly: {
    key: 'readonly',
    label: 'Readonly',
    role: 'watch-only node',
    basePath: '/ledger/readonly',
    writeExpectation: 'should reject writes',
  },
};

const TOKEN_SYMBOLS = {
  [ASSET0]: 'tASSET0',
  [ASSET1]: 'tASSET1',
};

function randomHex(bytes) {
  const out = new Uint8Array(bytes);
  window.crypto.getRandomValues(out);
  return Array.from(out, (b) => b.toString(16).padStart(2, '0')).join('');
}

function shortHash(value) {
  if (!value || typeof value !== 'string') {
    return '-';
  }
  if (value.length <= 18) {
    return value;
  }
  return `${value.slice(0, 10)}...${value.slice(-8)}`;
}

function formatAmount(value) {
  if (value === null || value === undefined || Number.isNaN(Number(value))) {
    return '-';
  }
  return new Intl.NumberFormat('en-US').format(Number(value));
}

function currentTimeMs() {
  return Date.now();
}

function positiveIntFromText(value) {
  const parsed = Number.parseInt(value, 10);
  return Number.isInteger(parsed) && parsed > 0 ? parsed : null;
}

function bpsFromText(value) {
  const parsed = Number.parseInt(value, 10);
  return Number.isInteger(parsed) && parsed >= 0 && parsed <= 10_000 ? parsed : null;
}

function resultAccepted(result) {
  return result?.data?.tx_accepted === true || result?.data?.receipt?.accepted === true;
}

function resultRejected(result) {
  return result?.data?.tx_accepted === false || result?.data?.receipt?.accepted === false || result?.ok === false;
}

function resultPill(result) {
  if (!result) {
    return { label: '', className: '' };
  }
  if (resultAccepted(result)) {
    return { label: `accepted ${result.status}`, className: 'good' };
  }
  if (resultRejected(result)) {
    return { label: `rejected ${result.status}`, className: 'bad' };
  }
  return { label: `HTTP ${result.status}`, className: result.ok ? 'warn' : 'bad' };
}

function clientErrorResult(message) {
  return {
    ok: false,
    status: 0,
    data: {
      error: message,
      ok: false,
    },
  };
}

function loadSmokeWallet() {
  const params = new URLSearchParams(window.location.search);
  if (params.get('zenodexUiSmokeSwap') !== '1') {
    return null;
  }
  const rawAddress = String(params.get('walletAddress') || '').trim();
  if (!/^(0x)?[0-9a-fA-F]{96}$/.test(rawAddress)) {
    return null;
  }
  const pubkey = rawAddress.toLowerCase().startsWith('0x')
    ? `0x${rawAddress.slice(2).toLowerCase()}`
    : `0x${rawAddress.toLowerCase()}`;
  return { pubkey, nextNonce: 1 };
}

function loadWallet() {
  const smokeWallet = loadSmokeWallet();
  if (smokeWallet) {
    return smokeWallet;
  }
  const raw = window.localStorage.getItem('zenodex.live.wallet.v0');
  if (raw) {
    try {
      const parsed = JSON.parse(raw);
      if (parsed && typeof parsed.pubkey === 'string' && parsed.pubkey.startsWith('0x')) {
        return {
          pubkey: parsed.pubkey,
          nextNonce: Number.isInteger(parsed.nextNonce) && parsed.nextNonce > 0 ? parsed.nextNonce : 1,
        };
      }
    } catch {
      // Fall through to a new local test wallet.
    }
  }
  const wallet = { pubkey: `0x${randomHex(48)}`, nextNonce: 1 };
  window.localStorage.setItem('zenodex.live.wallet.v0', JSON.stringify(wallet));
  return wallet;
}

function saveWallet(wallet) {
  window.localStorage.setItem('zenodex.live.wallet.v0', JSON.stringify(wallet));
}

function loadNodeTokens() {
  const params = new URLSearchParams(window.location.search);
  const sharedSmokeToken = params.get('zenodexUiSmokeToken') || '';
  let stored = {};
  const raw = window.localStorage.getItem('zenodex.live.nodeTokens.v0');
  if (raw) {
    try {
      const parsed = JSON.parse(raw);
      if (parsed && typeof parsed === 'object') {
        stored = parsed;
      }
    } catch {
      stored = {};
    }
  }
  const legacyToken = window.localStorage.getItem('zenodex.live.writerToken.v0') || '';
  return {
    writer: params.get('zenodexUiSmokeWriterToken') || sharedSmokeToken || stored.writer || legacyToken,
    forwarder: params.get('zenodexUiSmokeForwarderToken') || sharedSmokeToken || stored.forwarder || legacyToken,
    readonly: params.get('zenodexUiSmokeReadonlyToken') || stored.readonly || '',
  };
}

function nodePath(nodeKey, path) {
  const prefix = NODES[nodeKey].basePath;
  return `${prefix}${path.startsWith('/') ? path : `/${path}`}`;
}

async function fetchJson(path, options = {}) {
  const headers = { ...(options.headers || {}) };
  if (options.body !== undefined) {
    headers['Content-Type'] = 'application/json';
  }
  if (options.token) {
    headers.Authorization = `Bearer ${options.token}`;
  }
  const response = await fetch(path, {
    method: options.method || 'GET',
    headers,
    body: options.body === undefined ? undefined : JSON.stringify(options.body),
  });
  const text = await response.text();
  let data = null;
  try {
    data = text ? JSON.parse(text) : null;
  } catch {
    data = { raw: text };
  }
  return {
    ok: response.ok,
    status: response.status,
    data,
  };
}

function findWalletBalance(snapshot, pubkey, asset) {
  const entries = Array.isArray(snapshot?.balances) ? snapshot.balances : [];
  const found = entries.find((entry) => entry.pubkey === pubkey && entry.asset === asset);
  return found ? Number(found.amount || 0) : 0;
}

function findWalletNonce(snapshot, pubkey) {
  const entries = Array.isArray(snapshot?.nonces) ? snapshot.nonces : [];
  const found = entries.find((entry) => entry.pubkey === pubkey);
  return found ? Number(found.last_nonce || 0) : 0;
}

function findWalletLpBalance(snapshot, pubkey, poolId) {
  const entries = Array.isArray(snapshot?.lp_balances) ? snapshot.lp_balances : [];
  const found = entries.find((entry) => entry.pubkey === pubkey && entry.pool_id === poolId);
  return found ? Number(found.amount || 0) : 0;
}

function computeQuote(pool, assetIn, amountIn) {
  if (!pool || !Number.isFinite(amountIn) || amountIn <= 0) {
    return null;
  }
  const feeBps = Number(pool.fee_bps || 0);
  const reserve0 = Number(pool.reserve0 || 0);
  const reserve1 = Number(pool.reserve1 || 0);
  const reserveIn = assetIn === pool.asset0 ? reserve0 : reserve1;
  const reserveOut = assetIn === pool.asset0 ? reserve1 : reserve0;
  if (reserveIn <= 0 || reserveOut <= 0) {
    return null;
  }
  const amountInAfterFee = amountIn * (10_000 - feeBps);
  return Math.floor((amountInAfterFee * reserveOut) / (reserveIn * 10_000 + amountInAfterFee));
}

function statusClass(state) {
  if (state?.error) {
    return 'bad';
  }
  if (state?.network?.ok && state?.live?.live) {
    return 'good';
  }
  return 'warn';
}

function DetailRow({ label, value }) {
  return (
    <div className="detail-row">
      <span>{label}</span>
      <strong>{value}</strong>
    </div>
  );
}

function App() {
  const [selectedNode, setSelectedNode] = useState('writer');
  const [wallet, setWallet] = useState(loadWallet);
  const [nodeTokens, setNodeTokens] = useState(loadNodeTokens);
  const [states, setStates] = useState({});
  const [snapshot, setSnapshot] = useState(null);
  const [amountIn, setAmountIn] = useState('100');
  const [slippageBps, setSlippageBps] = useState('500');
  const [faucetAmount, setFaucetAmount] = useState('1000000');
  const [liquidityAmount0, setLiquidityAmount0] = useState('100');
  const [liquidityAmount1, setLiquidityAmount1] = useState('200');
  const [removeLpAmount, setRemoveLpAmount] = useState('10');
  const [assetIn, setAssetIn] = useState(ASSET0);
  const [busy, setBusy] = useState(false);
  const [lastResult, setLastResult] = useState(null);
  const [eventLog, setEventLog] = useState([]);
  const [smokeStatus, setSmokeStatus] = useState(null);
  const uiSmoke = useMemo(() => {
    const params = new URLSearchParams(window.location.search);
    const legacySwap = params.get('zenodexUiSmokeSwap') === '1';
    return {
      mode: params.get('zenodexUiSmokeScript') || (legacySwap ? 'swap' : ''),
      amountIn: params.get('smokeAmountIn') || '100',
    };
  }, []);
  const [smokeSubmitted, setSmokeSubmitted] = useState(false);

  const selectedState = states[selectedNode] || {};
  const latestHeight = selectedState?.network?.local_tip?.height || selectedState?.live?.state?.latest_height;
  const pool = useMemo(() => {
    const pools = Array.isArray(snapshot?.pools) ? snapshot.pools : [];
    return pools.find((entry) => entry.pool_id === POOL_ID) || pools[0] || null;
  }, [snapshot]);
  const assetOut = assetIn === ASSET0 ? ASSET1 : ASSET0;
  const amountInNumber = positiveIntFromText(amountIn);
  const faucetAmountNumber = positiveIntFromText(faucetAmount);
  const liquidityAmount0Number = positiveIntFromText(liquidityAmount0);
  const liquidityAmount1Number = positiveIntFromText(liquidityAmount1);
  const removeLpAmountNumber = positiveIntFromText(removeLpAmount);
  const slippageBpsNumber = bpsFromText(slippageBps);
  const quoteOut = computeQuote(pool, assetIn, amountInNumber);
  const minAmountOut = quoteOut === null
    ? 1
    : Math.max(1, Math.floor(quoteOut * (10_000 - slippageBpsNumber) / 10_000));
  const balanceIn = findWalletBalance(snapshot, wallet.pubkey, assetIn);
  const balanceOut = findWalletBalance(snapshot, wallet.pubkey, assetOut);
  const walletLpBalance = findWalletLpBalance(snapshot, wallet.pubkey, POOL_ID);
  const chainNonce = findWalletNonce(snapshot, wallet.pubkey);
  const walletLooksValid = /^0x[0-9a-fA-F]{96}$/.test(wallet.pubkey);
  const canSubmitSwap = !busy && walletLooksValid && amountInNumber !== null && slippageBpsNumber !== null;
  const canRequestFaucet = !busy && walletLooksValid && faucetAmountNumber !== null;
  const canAddLiquidity = !busy && walletLooksValid && liquidityAmount0Number !== null && liquidityAmount1Number !== null;
  const canRemoveLiquidity = !busy && walletLooksValid && removeLpAmountNumber !== null;

  const appendEvent = useCallback((kind, result, nodeKey = selectedNode) => {
    const entry = {
      id: `${Date.now()}-${Math.random().toString(16).slice(2)}`,
      at: new Date().toLocaleTimeString(),
      kind,
      node: nodeKey,
      status: result.status,
      ok: result.ok,
      accepted: resultAccepted(result) ? true : resultRejected(result) ? false : null,
      height: result.data?.height ?? null,
      error: result.data?.error || result.data?.receipt?.error_code || result.data?.receipt?.reject_code || null,
    };
    setEventLog((current) => [entry, ...current].slice(0, 12));
  }, [selectedNode]);

  const refresh = useCallback(async () => {
    const nextStates = {};
    await Promise.all(Object.keys(NODES).map(async (nodeKey) => {
      try {
        const [network, live, tokens] = await Promise.all([
          fetchJson(nodePath(nodeKey, '/network')),
          fetchJson(nodePath(nodeKey, '/live')),
          fetchJson(nodePath(nodeKey, '/tokens')),
        ]);
        nextStates[nodeKey] = {
          network: network.data,
          live: live.data,
          tokens: tokens.data,
          http: { network: network.status, live: live.status, tokens: tokens.status },
        };
      } catch (error) {
        nextStates[nodeKey] = { error: error instanceof Error ? error.message : String(error) };
      }
    }));
    setStates(nextStates);

    const selectedHeight = nextStates[selectedNode]?.network?.local_tip?.height
      || nextStates[selectedNode]?.live?.state?.latest_height;
    if (selectedHeight) {
      const result = await fetchJson(nodePath(selectedNode, `/live/snapshot/${selectedHeight}`));
      if (result.ok) {
        setSnapshot(result.data);
      }
    }
  }, [selectedNode]);

  useEffect(() => {
    window.localStorage.setItem('zenodex.live.nodeTokens.v0', JSON.stringify(nodeTokens));
  }, [nodeTokens]);

  useEffect(() => {
    const refreshLater = () => {
      refresh();
    };
    const firstRefresh = window.setTimeout(refreshLater, 0);
    const timer = window.setInterval(refreshLater, 5000);
    return () => {
      window.clearTimeout(firstRefresh);
      window.clearInterval(timer);
    };
  }, [refresh]);

  const resetWallet = () => {
    const next = { pubkey: `0x${randomHex(48)}`, nextNonce: 1 };
    setWallet(next);
    saveWallet(next);
    setLastResult(null);
  };

  const setNodeToken = (nodeKey, value) => {
    setNodeTokens((current) => ({ ...current, [nodeKey]: value }));
  };

  const requestFaucetForNode = async ({
    nodeKey = selectedNode,
    targetAsset = assetIn,
    amount = faucetAmountNumber,
  } = {}) => {
    if (!walletLooksValid) {
      const result = clientErrorResult('wallet pubkey must be 0x plus 96 hex characters');
      setLastResult({ kind: 'faucet', ...result });
      appendEvent('faucet', result, nodeKey);
      return result;
    }
    if (amount === null) {
      const result = clientErrorResult('faucet amount must be a positive integer');
      setLastResult({ kind: 'faucet', ...result });
      appendEvent('faucet', result, nodeKey);
      return result;
    }
    setBusy(true);
    setLastResult(null);
    try {
      const nowMs = currentTimeMs();
      const result = await fetchJson(nodePath(nodeKey, '/faucet'), {
        method: 'POST',
        token: nodeTokens[nodeKey] || '',
        body: {
          to_pubkey: wallet.pubkey,
          asset: targetAsset,
          amount,
          time_ms: nowMs,
          tx_id: `ui-faucet-${nodeKey}-${nowMs}`,
        },
      });
      setLastResult({ kind: 'faucet', ...result });
      appendEvent('faucet', result, nodeKey);
      return result;
    } catch (error) {
      const result = clientErrorResult(error instanceof Error ? error.message : String(error));
      setLastResult({ kind: 'faucet', ...result });
      appendEvent('faucet', result, nodeKey);
      return result;
    } finally {
      setBusy(false);
      await refresh();
    }
  };

  const requestFaucet = async () => requestFaucetForNode();

  const submitDexIntentForNode = async (nodeKey, eventKind, intentFields, options = {}) => {
    setBusy(true);
    setLastResult(null);
    try {
      const nowMs = currentTimeMs();
      const nowSec = Math.floor(nowMs / 1000);
      const nonce = options.nonce ?? Math.max(wallet.nextNonce, chainNonce + 1);
      const tx = {
        tx_id: `ui-${eventKind}-${nodeKey}-${nowMs}`,
        block_timestamp: nowSec,
        tx_sender_pubkey: wallet.pubkey,
        operations: {
          2: [
            {
              module: 'TauSwap',
              version: '0.1',
              intent_id: `0x${randomHex(32)}`,
              sender_pubkey: wallet.pubkey,
              deadline: nowSec + 3600,
              nonce,
              ...intentFields,
            },
          ],
        },
      };
      const result = await fetchJson(nodePath(nodeKey, '/tx'), {
        method: 'POST',
        token: nodeTokens[nodeKey] || '',
        body: { time_ms: nowMs, tx },
      });
      setLastResult({ kind: eventKind, ...result });
      appendEvent(eventKind, result, nodeKey);
      if (resultAccepted(result)) {
        const next = { ...wallet, nextNonce: nonce + 1 };
        setWallet(next);
        saveWallet(next);
      }
      return result;
    } catch (error) {
      const result = clientErrorResult(error instanceof Error ? error.message : String(error));
      setLastResult({ kind: eventKind, ...result });
      appendEvent(eventKind, result, nodeKey);
      return result;
    } finally {
      setBusy(false);
      await refresh();
    }
  };

  const submitDexIntent = async (eventKind, intentFields, options = {}) => (
    submitDexIntentForNode(selectedNode, eventKind, intentFields, options)
  );

  const submitSwap = async () => {
    if (!walletLooksValid) {
      const result = clientErrorResult('wallet pubkey must be 0x plus 96 hex characters');
      setLastResult({ kind: 'swap', ...result });
      appendEvent('swap', result);
      return result;
    }
    if (amountInNumber === null) {
      const result = clientErrorResult('amount in must be a positive integer');
      setLastResult({ kind: 'swap', ...result });
      appendEvent('swap', result);
      return result;
    }
    if (slippageBpsNumber === null) {
      const result = clientErrorResult('slippage bps must be between 0 and 10000');
      setLastResult({ kind: 'swap', ...result });
      appendEvent('swap', result);
      return result;
    }
    return submitDexIntent('swap', {
      kind: 'SWAP_EXACT_IN',
      pool_id: POOL_ID,
      asset_in: assetIn,
      asset_out: assetOut,
      amount_in: amountInNumber,
      min_amount_out: minAmountOut,
      recipient: wallet.pubkey,
    });
  };

  const submitAddLiquidity = async () => {
    if (!walletLooksValid) {
      const result = clientErrorResult('wallet pubkey must be 0x plus 96 hex characters');
      setLastResult({ kind: 'add_liquidity', ...result });
      appendEvent('add_liquidity', result);
      return result;
    }
    if (liquidityAmount0Number === null || liquidityAmount1Number === null) {
      const result = clientErrorResult('liquidity amounts must be positive integers');
      setLastResult({ kind: 'add_liquidity', ...result });
      appendEvent('add_liquidity', result);
      return result;
    }
    return submitDexIntent('add_liquidity', {
      kind: 'ADD_LIQUIDITY',
      pool_id: POOL_ID,
      amount0_desired: liquidityAmount0Number,
      amount1_desired: liquidityAmount1Number,
      amount0_min: 0,
      amount1_min: 0,
    });
  };

  const submitRemoveLiquidity = async () => {
    if (!walletLooksValid) {
      const result = clientErrorResult('wallet pubkey must be 0x plus 96 hex characters');
      setLastResult({ kind: 'remove_liquidity', ...result });
      appendEvent('remove_liquidity', result);
      return result;
    }
    if (removeLpAmountNumber === null) {
      const result = clientErrorResult('LP amount must be a positive integer');
      setLastResult({ kind: 'remove_liquidity', ...result });
      appendEvent('remove_liquidity', result);
      return result;
    }
    return submitDexIntent('remove_liquidity', {
      kind: 'REMOVE_LIQUIDITY',
      pool_id: POOL_ID,
      lp_amount: removeLpAmountNumber,
      amount0_min: 0,
      amount1_min: 0,
    });
  };

  useEffect(() => {
    if (!uiSmoke.mode || smokeSubmitted) {
      return;
    }
    if (selectedNode !== 'writer') {
      setSelectedNode('writer');
      return;
    }
    if (amountIn !== uiSmoke.amountIn) {
      setAmountIn(uiSmoke.amountIn);
      return;
    }
    if (!snapshot || busy || !canSubmitSwap) {
      return;
    }
    if (
      uiSmoke.mode === 'full'
      && (!canRequestFaucet || !canAddLiquidity || !canRemoveLiquidity)
    ) {
      return;
    }
    try {
      const smokeKey = `zenodex.uiSmoke.${uiSmoke.mode}.submitted`;
      if (window.sessionStorage.getItem(smokeKey) === '1') {
        return;
      }
      window.sessionStorage.setItem(smokeKey, '1');
    } catch {
      // Session storage only prevents duplicate smoke submissions during browser tests.
    }
    setSmokeSubmitted(true);
    setSmokeStatus({ mode: uiSmoke.mode, done: false, results: [] });

    const summarize = (step, result) => ({
      step,
      status: result?.status ?? 0,
      ok: result?.ok === true,
      accepted: resultAccepted(result) ? true : resultRejected(result) ? false : null,
      height: result?.data?.height ?? null,
      error: result?.data?.error || result?.data?.receipt?.error_code || result?.data?.receipt?.reject_code || null,
    });

    const validateSmokeResults = (results) => {
      const byStep = Object.fromEntries(results.map((row) => [row.step, row]));
      const expected = uiSmoke.mode === 'full'
        ? [
          ['writer_faucet_asset0', { accepted: true }],
          ['writer_swap', { accepted: true }],
          ['writer_add_liquidity', { accepted: true }],
          ['writer_remove_liquidity', { accepted: true }],
          ['forwarder_swap', { accepted: true }],
          ['readonly_swap', { accepted: false, status: 403, error: 'testnet_intake_disabled' }],
        ]
        : [
          ['writer_swap', { accepted: true }],
        ];
      for (const [step, want] of expected) {
        const got = byStep[step];
        if (!got) {
          return { ok: false, error: `missing smoke step: ${step}` };
        }
        if (got.accepted !== want.accepted) {
          return { ok: false, error: `${step} accepted=${got.accepted}, expected ${want.accepted}` };
        }
        if (want.status !== undefined && got.status !== want.status) {
          return { ok: false, error: `${step} status=${got.status}, expected ${want.status}` };
        }
        if (want.error !== undefined && got.error !== want.error) {
          return { ok: false, error: `${step} error=${got.error || 'none'}, expected ${want.error}` };
        }
      }
      return { ok: true, error: null };
    };

    const swapFields = () => ({
      kind: 'SWAP_EXACT_IN',
      pool_id: POOL_ID,
      asset_in: ASSET0,
      asset_out: ASSET1,
      amount_in: amountInNumber,
      min_amount_out: 1,
      recipient: wallet.pubkey,
    });

    const runSmoke = async () => {
      const results = [];
      let nextNonce = Math.max(wallet.nextNonce, chainNonce + 1);
      const record = (step, result) => {
        results.push(summarize(step, result));
        setSmokeStatus({ mode: uiSmoke.mode, done: false, results: [...results] });
        return result;
      };
      const submitWithNonce = async (nodeKey, eventKind, intentFields) => {
        const result = await submitDexIntentForNode(nodeKey, eventKind, intentFields, { nonce: nextNonce });
        record(`${nodeKey}_${eventKind}`, result);
        if (resultAccepted(result)) {
          nextNonce += 1;
        }
        return result;
      };

      try {
        if (uiSmoke.mode === 'full') {
          record('writer_faucet_asset0', await requestFaucetForNode({
            nodeKey: 'writer',
            targetAsset: ASSET0,
            amount: faucetAmountNumber,
          }));
          await submitWithNonce('writer', 'swap', swapFields());
          await submitWithNonce('writer', 'add_liquidity', {
            kind: 'ADD_LIQUIDITY',
            pool_id: POOL_ID,
            amount0_desired: liquidityAmount0Number,
            amount1_desired: liquidityAmount1Number,
            amount0_min: 0,
            amount1_min: 0,
          });
          await submitWithNonce('writer', 'remove_liquidity', {
            kind: 'REMOVE_LIQUIDITY',
            pool_id: POOL_ID,
            lp_amount: removeLpAmountNumber,
            amount0_min: 0,
            amount1_min: 0,
          });
          await submitWithNonce('forwarder', 'swap', swapFields());
          await submitWithNonce('readonly', 'swap', swapFields());
        } else {
          await submitWithNonce('writer', 'swap', swapFields());
        }
        const expectation = validateSmokeResults(results);
        setSmokeStatus({
          mode: uiSmoke.mode,
          done: expectation.ok,
          ok: expectation.ok,
          error: expectation.error,
          results: [...results],
        });
      } catch (error) {
        setSmokeStatus({
          mode: uiSmoke.mode,
          done: false,
          error: error instanceof Error ? error.message : String(error),
          results: [...results],
        });
      }
    };

    runSmoke();
    // The smoke script intentionally drives the current rendered console state once per browser profile.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [
    uiSmoke,
    smokeSubmitted,
    selectedNode,
    amountIn,
    snapshot,
    busy,
    canSubmitSwap,
    canRequestFaucet,
    canAddLiquidity,
    canRemoveLiquidity,
  ]);

  const lastResultPill = resultPill(lastResult);

  return (
    <div className="live-shell">
      <header className="live-header">
        <div className="brand-lockup">
          <img src={`${import.meta.env.BASE_URL}branding/zenodex/zenodex_icon_256.png`} alt="" />
          <div>
            <h1>ZenoDEX Live Test Console</h1>
            <p>Manual trades against the local multi-node Docker ledger</p>
          </div>
        </div>
        <div className="header-actions">
          <button type="button" className="secondary" onClick={refresh} disabled={busy}>Refresh</button>
          <button type="button" className="secondary" onClick={resetWallet} disabled={busy}>New wallet</button>
        </div>
      </header>

      <main className="live-grid">
        <section className="node-strip" aria-label="Node status">
          {Object.values(NODES).map((node) => {
            const state = states[node.key];
            const cls = statusClass(state);
            return (
              <button
                type="button"
                key={node.key}
                data-testid={`node-${node.key}`}
                className={`node-tile ${selectedNode === node.key ? 'active' : ''}`}
                onClick={() => setSelectedNode(node.key)}
              >
                <span className={`status-dot ${cls}`} />
                <span>
                  <strong>{node.label}</strong>
                  <small>{node.role}</small>
                </span>
                <span className="node-height">h{state?.network?.local_tip?.height ?? '-'}</span>
              </button>
            );
          })}
        </section>

        <section className="panel trade-panel">
          <div className="section-title">
            <div>
              <h2>Trade</h2>
              <p>{NODES[selectedNode].writeExpectation}</p>
            </div>
            <span className="pill">{NODES[selectedNode].label}</span>
          </div>

          <div className="field-stack">
            <label>
              <span>Wallet pubkey</span>
              <input data-testid="wallet-pubkey" value={wallet.pubkey} onChange={(event) => {
                const next = { ...wallet, pubkey: event.target.value.trim(), nextNonce: 1 };
                setWallet(next);
                saveWallet(next);
              }} spellCheck="false" />
            </label>
          </div>

          <div className="split-controls token-controls">
            <label>
              <span>Writer token</span>
              <input data-testid="writer-token" value={nodeTokens.writer} onChange={(event) => setNodeToken('writer', event.target.value)} spellCheck="false" />
            </label>
            <label>
              <span>Forwarder token</span>
              <input data-testid="forwarder-token" value={nodeTokens.forwarder} onChange={(event) => setNodeToken('forwarder', event.target.value)} spellCheck="false" />
            </label>
            <label>
              <span>Readonly token</span>
              <input data-testid="readonly-token" value={nodeTokens.readonly} onChange={(event) => setNodeToken('readonly', event.target.value)} spellCheck="false" />
            </label>
          </div>

          <div className="split-controls">
            <label>
              <span>Asset in</span>
              <select data-testid="asset-in" value={assetIn} onChange={(event) => setAssetIn(event.target.value)}>
                <option value={ASSET0}>tASSET0</option>
                <option value={ASSET1}>tASSET1</option>
              </select>
            </label>
            <label>
              <span>Amount in</span>
              <input data-testid="amount-in" type="text" inputMode="numeric" pattern="[0-9]*" value={amountIn} onChange={(event) => setAmountIn(event.target.value)} />
            </label>
            <label>
              <span>Slippage bps</span>
              <input data-testid="slippage-bps" type="text" inputMode="numeric" pattern="[0-9]*" value={slippageBps} onChange={(event) => setSlippageBps(event.target.value)} />
            </label>
          </div>

          <div className="quote-band">
            <DetailRow label="Expected out" value={`${formatAmount(quoteOut)} ${TOKEN_SYMBOLS[assetOut]}`} />
            <DetailRow label="Minimum out" value={`${formatAmount(minAmountOut)} ${TOKEN_SYMBOLS[assetOut]}`} />
            <DetailRow label="Next nonce" value={Math.max(wallet.nextNonce, chainNonce + 1)} />
          </div>
          {!walletLooksValid || amountInNumber === null || slippageBpsNumber === null ? (
            <div className="validation-line">
              {!walletLooksValid ? 'Wallet pubkey must be 0x plus 96 hex characters.' : null}
              {walletLooksValid && amountInNumber === null ? 'Amount in must be a positive integer.' : null}
              {walletLooksValid && amountInNumber !== null && slippageBpsNumber === null ? 'Slippage bps must be between 0 and 10000.' : null}
            </div>
          ) : null}

          <div className="button-row">
            <button type="button" data-testid="submit-swap" className="primary" onClick={submitSwap} disabled={!canSubmitSwap}>
              Submit swap
            </button>
            <div className="faucet-box">
              <input data-testid="faucet-amount" type="text" inputMode="numeric" pattern="[0-9]*" value={faucetAmount} onChange={(event) => setFaucetAmount(event.target.value)} aria-label="Faucet amount" />
              <button type="button" data-testid="faucet-submit" className="secondary" onClick={requestFaucet} disabled={!canRequestFaucet}>Faucet selected asset</button>
            </div>
          </div>
        </section>

        <section className="panel liquidity-panel">
          <div className="section-title">
            <div>
              <h2>Pool Actions</h2>
              <p>Add or remove liquidity on the same live CPMM pool</p>
            </div>
            <span className="pill">CPMM</span>
          </div>

          <div className="split-controls">
            <label>
              <span>tASSET0 add</span>
              <input data-testid="liquidity-amount0" type="text" inputMode="numeric" pattern="[0-9]*" value={liquidityAmount0} onChange={(event) => setLiquidityAmount0(event.target.value)} />
            </label>
            <label>
              <span>tASSET1 add</span>
              <input data-testid="liquidity-amount1" type="text" inputMode="numeric" pattern="[0-9]*" value={liquidityAmount1} onChange={(event) => setLiquidityAmount1(event.target.value)} />
            </label>
            <label>
              <span>LP remove</span>
              <input data-testid="remove-lp-amount" type="text" inputMode="numeric" pattern="[0-9]*" value={removeLpAmount} onChange={(event) => setRemoveLpAmount(event.target.value)} />
            </label>
          </div>

          <div className="quote-band">
            <DetailRow label="Wallet LP" value={formatAmount(walletLpBalance)} />
            <DetailRow label="LP supply" value={formatAmount(pool?.lp_supply)} />
            <DetailRow label="Pool status" value={pool?.status || '-'} />
          </div>

          <div className="button-row">
            <button type="button" data-testid="add-liquidity" className="primary" onClick={submitAddLiquidity} disabled={!canAddLiquidity}>
              Add liquidity
            </button>
            <button type="button" data-testid="remove-liquidity" className="secondary" onClick={submitRemoveLiquidity} disabled={!canRemoveLiquidity}>
              Remove liquidity
            </button>
          </div>
        </section>

        <section className="panel status-panel">
          <div className="section-title">
            <div>
              <h2>Ledger State</h2>
              <p>Selected node snapshot and pool reserves</p>
            </div>
            <span className={`pill ${statusClass(selectedState)}`}>{selectedState?.live?.live ? 'live' : 'offline'}</span>
          </div>
          <div className="detail-grid">
            <DetailRow label="Height" value={latestHeight ?? '-'} />
            <DetailRow label="Header" value={shortHash(selectedState?.network?.local_tip?.header_hash || selectedState?.live?.state?.latest_header_hash)} />
            <DetailRow label="App hash" value={shortHash(selectedState?.network?.local_tip?.app_hash || selectedState?.live?.state?.latest_app_hash)} />
            <DetailRow label="Chain" value={selectedState?.network?.chain_id || '-'} />
          </div>
          <div className="reserve-table">
            <div><span>Pool</span><strong>{shortHash(pool?.pool_id)}</strong></div>
            <div><span>tASSET0 reserve</span><strong>{formatAmount(pool?.reserve0)}</strong></div>
            <div><span>tASSET1 reserve</span><strong>{formatAmount(pool?.reserve1)}</strong></div>
            <div><span>Fee bps</span><strong>{pool?.fee_bps ?? '-'}</strong></div>
          </div>
          <div className="balance-strip">
            <div>
              <span>Wallet tASSET0</span>
              <strong>{formatAmount(findWalletBalance(snapshot, wallet.pubkey, ASSET0))}</strong>
            </div>
            <div>
              <span>Wallet tASSET1</span>
              <strong>{formatAmount(findWalletBalance(snapshot, wallet.pubkey, ASSET1))}</strong>
            </div>
            <div>
              <span>Selected balance</span>
              <strong>{formatAmount(balanceIn)} in / {formatAmount(balanceOut)} out</strong>
            </div>
            <div>
              <span>Wallet LP</span>
              <strong>{formatAmount(walletLpBalance)}</strong>
            </div>
          </div>
        </section>

        <section className="panel result-panel">
          <div className="section-title">
            <div>
              <h2>Last Response</h2>
              <p>Use readonly and bad-token tests here to confirm rejection paths</p>
            </div>
            {lastResult ? <span className={`pill ${lastResultPill.className}`}>{lastResultPill.label}</span> : null}
          </div>
          <pre data-testid="last-response">{lastResult ? JSON.stringify(lastResult.data, null, 2) : 'No submission yet.'}</pre>
          {smokeStatus ? (
            <pre data-testid="smoke-status" className="smoke-status">
              {JSON.stringify(smokeStatus, null, 2)}
            </pre>
          ) : null}
        </section>

        <section className="panel log-panel">
          <div className="section-title">
            <div>
              <h2>Run Log</h2>
              <p>Recent manual faucet and swap attempts</p>
            </div>
          </div>
          <div className="event-list">
            {eventLog.length === 0 ? (
              <span className="empty-log">No events yet.</span>
            ) : eventLog.map((entry) => (
              <div className="event-row" key={entry.id}>
                <span>{entry.at}</span>
                <strong>{entry.kind}</strong>
                <span>{entry.node}</span>
                <span>{entry.accepted === null ? `HTTP ${entry.status}` : entry.accepted ? 'accepted' : 'rejected'}</span>
                <small>{entry.error || (entry.height ? `h${entry.height}` : '')}</small>
              </div>
            ))}
          </div>
        </section>
      </main>
    </div>
  );
}

export default App;
