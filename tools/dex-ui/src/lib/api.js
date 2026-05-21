const DEFAULT_API_BASE = '';
const DEFAULT_TIMEOUT_MS = 15_000;
const DEFAULT_ZENO_ORACLE_API_BASE = 'http://127.0.0.1:8787';

export function getRuntimeConfig() {
  if (typeof window === 'undefined') {
    return {};
  }
  const cfg = window.__ZENODEX_CONFIG__;
  return cfg && typeof cfg === 'object' ? cfg : {};
}

function parseBooleanLike(raw) {
  if (raw === true || raw === 'true' || raw === '1' || raw === 1) {
    return true;
  }
  if (raw === false || raw === 'false' || raw === '0' || raw === 0) {
    return false;
  }
  return undefined;
}

export function getRuntimeBooleanFlag({ queryKey, runtimeKey, envKey, defaultValue = false }) {
  if (typeof window !== 'undefined' && queryKey) {
    const params = new URLSearchParams(window.location.search);
    if (params.has(queryKey)) {
      return parseBooleanLike(params.get(queryKey)) ?? Boolean(defaultValue);
    }
  }

  if (runtimeKey) {
    const runtimeValue = getRuntimeConfig()?.[runtimeKey];
    const parsedRuntime = parseBooleanLike(runtimeValue);
    if (parsedRuntime !== undefined) {
      return parsedRuntime;
    }
  }

  if (typeof import.meta !== 'undefined' && import.meta.env && envKey && import.meta.env[envKey] !== undefined) {
    const parsedEnv = parseBooleanLike(import.meta.env[envKey]);
    if (parsedEnv !== undefined) {
      return parsedEnv;
    }
  }

  return Boolean(defaultValue);
}

function normalizeApiBase(raw) {
  const value = (raw ?? '').toString().trim();
  if (!value) {
    return '';
  }
  return value.endsWith('/') ? value.slice(0, -1) : value;
}

function getZenoOracleApiBase() {
  const runtimeBase = normalizeApiBase(getRuntimeConfig().zenoOracleApiBase);
  if (runtimeBase) {
    return runtimeBase;
  }
  const v = normalizeApiBase(import.meta?.env?.VITE_ZENO_ORACLE_API_URL ?? '');
  return v || DEFAULT_ZENO_ORACLE_API_BASE;
}

export function getApiBase() {
  const runtimeBase = normalizeApiBase(getRuntimeConfig().apiBase);
  if (runtimeBase) {
    return runtimeBase;
  }
  // Prefer explicit env override; fallback to same-origin.
  const v = normalizeApiBase(import.meta?.env?.VITE_API_BASE ?? '');
  return v || DEFAULT_API_BASE;
}

export async function apiFetchZenoOracleJson(path, options = {}) {
  const base = getZenoOracleApiBase();
  const { timeoutMs, ...fetchOptions } = options || {};
  return apiFetchJson(`${base}${path}`, { timeoutMs, ...fetchOptions });
}

export function getApiToken() {
  const v = (import.meta?.env?.VITE_API_TOKEN ?? '').toString().trim();
  return v || '';
}

export async function apiFetchJson(path, options = {}) {
  const base = getApiBase();
  const pathText = String(path || '');
  const url = /^https?:\/\//i.test(pathText) ? pathText : `${base}${pathText}`;
  const token = getApiToken();
  const { timeoutMs, ...fetchOptions } = options || {};
  const method = (fetchOptions.method || 'GET').toString().toUpperCase();
  const headers = {
    Accept: 'application/json',
    ...(fetchOptions.headers || {}),
  };
  const hasHeader = (name) => Object.keys(headers).some((k) => k.toLowerCase() === name);
  const hasBody = fetchOptions.body !== undefined && fetchOptions.body !== null;
  if (hasBody && !hasHeader('content-type')) {
    headers['Content-Type'] = 'application/json';
  }
  if (token && !hasHeader('authorization')) {
    headers.Authorization = `Bearer ${token}`;
  }

  const effectiveTimeoutMs = Number.isFinite(timeoutMs) && timeoutMs > 0
    ? Math.trunc(timeoutMs)
    : DEFAULT_TIMEOUT_MS;
  const controller = fetchOptions.signal ? null : new AbortController();
  const signal = fetchOptions.signal || controller?.signal;
  const timer = controller
    ? setTimeout(() => controller.abort(), effectiveTimeoutMs)
    : null;

  let res;
  try {
    res = await fetch(url, {
      ...fetchOptions,
      method,
      headers: {
        ...headers,
      },
      signal,
    });
  } catch (err) {
    if (timer) clearTimeout(timer);
    const name = err && typeof err === 'object' ? err.name : '';
    if (name === 'AbortError') {
      throw new Error('timeout');
    }
    throw err;
  } finally {
    if (timer) clearTimeout(timer);
  }

  const text = await res.text();
  let data;
  try {
    data = text ? JSON.parse(text) : null;
  } catch {
    data = null;
  }

  if (!res.ok) {
    const msg = (data && (data.error || data.message)) || `http_${res.status}`;
    throw new Error(msg);
  }
  return data;
}

export function apiGetConfidentialStatus(options = {}) {
  return apiFetchJson('/api/confidential/status', { method: 'GET', ...(options || {}) });
}

export function apiGetZusdWalletStatus(options = {}) {
  return apiFetchJson('/api/zusd/wallet/status', { method: 'GET', ...(options || {}) });
}

export function apiPrepareZusdWallet(body, options = {}) {
  return apiFetchJson('/api/zusd/wallet/prepare', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiSubmitZusdWallet(body, options = {}) {
  return apiFetchJson('/api/zusd/wallet/submit', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiGetZusdMonetaryStatus(options = {}) {
  return apiFetchJson('/api/zusd/monetary/status', { method: 'GET', ...(options || {}) });
}

export function apiPrepareZusdMonetary(body, options = {}) {
  return apiFetchJson('/api/zusd/monetary/prepare', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiSubmitZusdMonetary(body, options = {}) {
  return apiFetchJson('/api/zusd/monetary/submit', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiGetPerpsWalletStatus(options = {}) {
  return apiFetchJson('/api/perps/wallet/status', { method: 'GET', ...(options || {}) });
}

export function apiPreparePerpsWallet(body, options = {}) {
  return apiFetchJson('/api/perps/wallet/prepare', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiSubmitPerpsWallet(body, options = {}) {
  return apiFetchJson('/api/perps/wallet/submit', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiBuildPerpsOracleBridge(body, options = {}) {
  return apiFetchJson('/api/perps/wallet/oracle-bridge-template', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiInspectPerpsOracleBridge(body, options = {}) {
  return apiFetchJson('/api/perps/wallet/oracle-bridge/inspect', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiGetZenoOracleDashboard(options = {}) {
  return apiFetchZenoOracleJson('/api/oracle/dashboard', { method: 'GET', ...(options || {}) });
}

export function apiGetAutotraderStatus(options = {}) {
  return apiFetchJson('/api/strategy/autotrader/status', { method: 'GET', ...(options || {}) });
}

export function apiPrepareAutotraderLive(body, options = {}) {
  return apiFetchJson('/api/strategy/autotrader/prepare', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiGetPools(options = {}) {
  return apiFetchJson('/api/pools', { method: 'GET', ...(options || {}) });
}

export function apiSwap(
  {
    from,
    to,
    amountIn,
    minAmountOut = 1,
    poolId = null,
    assetIn = null,
    assetOut = null,
    senderPubkey = null,
    recipient = null,
    deadline = null,
  },
  options = {},
) {
  const body = {
    from,
    to,
    amountIn,
    minAmountOut,
  };
  if (poolId) body.poolId = poolId;
  if (assetIn) body.assetIn = assetIn;
  if (assetOut) body.assetOut = assetOut;
  if (senderPubkey) body.senderPubkey = senderPubkey;
  if (recipient) body.recipient = recipient;
  if (deadline) body.deadline = deadline;
  return apiFetchJson('/api/swap', {
    method: 'POST',
    body: JSON.stringify(body),
    ...(options || {}),
  });
}

export function apiDexImpactPreview(
  {
    reserveIn,
    reserveOut,
    amountIn,
    feeBps,
    pendingVolumeSameDirection = 0,
    confidenceBps = 9500,
  },
  options = {},
) {
  return apiFetchJson('/api/dex/impact_preview', {
    method: 'POST',
    body: JSON.stringify({
      reserve_in: reserveIn,
      reserve_out: reserveOut,
      amount_in: amountIn,
      fee_bps: feeBps,
      pending_volume_same_direction: pendingVolumeSameDirection,
      confidence_bps: confidenceBps,
      pools: [],
    }),
    ...(options || {}),
  });
}

export function apiDexSlippageAdvice(
  {
    reserveIn,
    reserveOut,
    amountIn,
    feeBps,
    pendingVolumeSameDirection = 0,
    confidenceBps = 9500,
    slippageOptionsBps = null,
    maxAttackerAmountIn = 5000,
    userSlippageBps = null,
  },
  options = {},
) {
  return apiFetchJson('/api/dex/slippage_advice', {
    method: 'POST',
    body: JSON.stringify({
      reserve_in: reserveIn,
      reserve_out: reserveOut,
      amount_in: amountIn,
      fee_bps: feeBps,
      pending_volume_same_direction: pendingVolumeSameDirection,
      confidence_bps: confidenceBps,
      slippage_options_bps: slippageOptionsBps,
      max_attacker_amount_in: maxAttackerAmountIn,
      user_slippage_bps: userSlippageBps,
      pools: [],
    }),
    ...(options || {}),
  });
}

export function apiDexPokayokeSwapSuggest(
  {
    reserveIn,
    reserveOut,
    amountIn,
    feeBps,
    pendingVolumeSameDirection = 0,
    confidenceBps = 9500,
    slippageOptionsBps = null,
    userSlippageBps = null,
  },
  options = {},
) {
  return apiFetchJson('/api/dex/pokayoke_swap_suggest', {
    method: 'POST',
    body: JSON.stringify({
      reserve_in: reserveIn,
      reserve_out: reserveOut,
      amount_in: amountIn,
      fee_bps: feeBps,
      pending_volume_same_direction: pendingVolumeSameDirection,
      confidence_bps: confidenceBps,
      slippage_options_bps: slippageOptionsBps,
      user_slippage_bps: userSlippageBps,
      pools: [],
    }),
    ...(options || {}),
  });
}

export function apiDexPokayokeSwapSuggestHeavy(
  {
    reserveIn,
    reserveOut,
    amountIn,
    feeBps,
    pendingVolumeSameDirection = 0,
    confidenceBps = 9500,
    slippageOptionsBps = null,
    userSlippageBps,
    maxAttackerAmountIn = 2000,
    maxEvals = 16,
    targetActions = ['confirm', 'allow'],
  },
  options = {},
) {
  return apiFetchJson('/api/dex/pokayoke_swap_suggest_heavy', {
    method: 'POST',
    body: JSON.stringify({
      reserve_in: reserveIn,
      reserve_out: reserveOut,
      amount_in: amountIn,
      fee_bps: feeBps,
      pending_volume_same_direction: pendingVolumeSameDirection,
      confidence_bps: confidenceBps,
      slippage_options_bps: slippageOptionsBps,
      user_slippage_bps: userSlippageBps,
      max_attacker_amount_in: maxAttackerAmountIn,
      max_evals: maxEvals,
      target_actions: targetActions,
      pools: [],
    }),
    ...(options || {}),
  });
}
