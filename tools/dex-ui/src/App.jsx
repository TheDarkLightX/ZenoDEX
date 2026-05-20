import { useCallback, useEffect, useMemo, useState } from 'react';
import './App.css';

const WRITER_TOKEN = 'local-multidocker-token';
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

function loadWallet() {
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
  const [token, setToken] = useState(() => window.localStorage.getItem('zenodex.live.writerToken.v0') || WRITER_TOKEN);
  const [states, setStates] = useState({});
  const [snapshot, setSnapshot] = useState(null);
  const [amountIn, setAmountIn] = useState('100');
  const [slippageBps, setSlippageBps] = useState('500');
  const [faucetAmount, setFaucetAmount] = useState('1000000');
  const [assetIn, setAssetIn] = useState(ASSET0);
  const [busy, setBusy] = useState(false);
  const [lastResult, setLastResult] = useState(null);
  const [eventLog, setEventLog] = useState([]);

  const selectedState = states[selectedNode] || {};
  const latestHeight = selectedState?.network?.local_tip?.height || selectedState?.live?.state?.latest_height;
  const pool = useMemo(() => {
    const pools = Array.isArray(snapshot?.pools) ? snapshot.pools : [];
    return pools.find((entry) => entry.pool_id === POOL_ID) || pools[0] || null;
  }, [snapshot]);
  const assetOut = assetIn === ASSET0 ? ASSET1 : ASSET0;
  const amountInNumber = Number.parseInt(amountIn, 10);
  const quoteOut = computeQuote(pool, assetIn, amountInNumber);
  const minAmountOut = quoteOut === null
    ? 1
    : Math.max(1, Math.floor(quoteOut * (10_000 - Number.parseInt(slippageBps || '0', 10)) / 10_000));
  const balanceIn = findWalletBalance(snapshot, wallet.pubkey, assetIn);
  const balanceOut = findWalletBalance(snapshot, wallet.pubkey, assetOut);
  const chainNonce = findWalletNonce(snapshot, wallet.pubkey);

  const appendEvent = useCallback((kind, result) => {
    const entry = {
      id: `${Date.now()}-${Math.random().toString(16).slice(2)}`,
      at: new Date().toLocaleTimeString(),
      kind,
      node: selectedNode,
      status: result.status,
      ok: result.ok,
      accepted: result.data?.tx_accepted ?? result.data?.receipt?.accepted ?? null,
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
    window.localStorage.setItem('zenodex.live.writerToken.v0', token);
  }, [token]);

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

  const requestFaucet = async () => {
    setBusy(true);
    setLastResult(null);
    const nowMs = currentTimeMs();
    const result = await fetchJson(nodePath(selectedNode, '/faucet'), {
      method: 'POST',
      token,
      body: {
        to_pubkey: wallet.pubkey,
        asset: assetIn,
        amount: Number.parseInt(faucetAmount, 10),
        time_ms: nowMs,
        tx_id: `ui-faucet-${selectedNode}-${nowMs}`,
      },
    });
    setLastResult({ kind: 'faucet', ...result });
    appendEvent('faucet', result);
    setBusy(false);
    await refresh();
  };

  const submitSwap = async () => {
    setBusy(true);
    setLastResult(null);
    const nowMs = currentTimeMs();
    const nowSec = Math.floor(nowMs / 1000);
    const nonce = Math.max(wallet.nextNonce, chainNonce + 1);
    const tx = {
      tx_id: `ui-swap-${selectedNode}-${nowMs}`,
      block_timestamp: nowSec,
      tx_sender_pubkey: wallet.pubkey,
      operations: {
        2: [
          {
            module: 'TauSwap',
            version: '0.1',
            kind: 'SWAP_EXACT_IN',
            intent_id: `0x${randomHex(32)}`,
            sender_pubkey: wallet.pubkey,
            deadline: nowSec + 3600,
            nonce,
            pool_id: POOL_ID,
            asset_in: assetIn,
            asset_out: assetOut,
            amount_in: amountInNumber,
            min_amount_out: minAmountOut,
            recipient: wallet.pubkey,
          },
        ],
      },
    };
    const result = await fetchJson(nodePath(selectedNode, '/tx'), {
      method: 'POST',
      token,
      body: { time_ms: nowMs, tx },
    });
    setLastResult({ kind: 'swap', ...result });
    appendEvent('swap', result);
    const accepted = result.data?.tx_accepted === true || result.data?.receipt?.accepted === true;
    if (accepted) {
      const next = { ...wallet, nextNonce: nonce + 1 };
      setWallet(next);
      saveWallet(next);
    }
    setBusy(false);
    await refresh();
  };

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
              <span>Auth token</span>
              <input value={token} onChange={(event) => setToken(event.target.value)} spellCheck="false" />
            </label>
            <label>
              <span>Wallet pubkey</span>
              <input value={wallet.pubkey} onChange={(event) => {
                const next = { ...wallet, pubkey: event.target.value.trim(), nextNonce: 1 };
                setWallet(next);
                saveWallet(next);
              }} spellCheck="false" />
            </label>
          </div>

          <div className="split-controls">
            <label>
              <span>Asset in</span>
              <select value={assetIn} onChange={(event) => setAssetIn(event.target.value)}>
                <option value={ASSET0}>tASSET0</option>
                <option value={ASSET1}>tASSET1</option>
              </select>
            </label>
            <label>
              <span>Amount in</span>
              <input type="number" min="1" step="1" value={amountIn} onChange={(event) => setAmountIn(event.target.value)} />
            </label>
            <label>
              <span>Slippage bps</span>
              <input type="number" min="0" max="10000" step="1" value={slippageBps} onChange={(event) => setSlippageBps(event.target.value)} />
            </label>
          </div>

          <div className="quote-band">
            <DetailRow label="Expected out" value={`${formatAmount(quoteOut)} ${TOKEN_SYMBOLS[assetOut]}`} />
            <DetailRow label="Minimum out" value={`${formatAmount(minAmountOut)} ${TOKEN_SYMBOLS[assetOut]}`} />
            <DetailRow label="Next nonce" value={Math.max(wallet.nextNonce, chainNonce + 1)} />
          </div>

          <div className="button-row">
            <button type="button" className="primary" onClick={submitSwap} disabled={busy || !Number.isFinite(amountInNumber) || amountInNumber <= 0}>
              Submit swap
            </button>
            <div className="faucet-box">
              <input type="number" min="1" step="1" value={faucetAmount} onChange={(event) => setFaucetAmount(event.target.value)} aria-label="Faucet amount" />
              <button type="button" className="secondary" onClick={requestFaucet} disabled={busy}>Faucet selected asset</button>
            </div>
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
          </div>
        </section>

        <section className="panel result-panel">
          <div className="section-title">
            <div>
              <h2>Last Response</h2>
              <p>Use readonly and bad-token tests here to confirm rejection paths</p>
            </div>
            {lastResult ? <span className={`pill ${lastResult.ok ? 'good' : 'bad'}`}>HTTP {lastResult.status}</span> : null}
          </div>
          <pre>{lastResult ? JSON.stringify(lastResult.data, null, 2) : 'No submission yet.'}</pre>
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
