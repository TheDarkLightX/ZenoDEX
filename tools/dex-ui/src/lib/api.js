const DEFAULT_API_BASE = '';
const DEFAULT_TIMEOUT_MS = 15_000;

function getRuntimeConfig() {
  if (typeof window === 'undefined') {
    return {};
  }
  const cfg = window.__ZENODEX_CONFIG__;
  return cfg && typeof cfg === 'object' ? cfg : {};
}

function normalizeApiBase(raw) {
  const value = (raw ?? '').toString().trim();
  if (!value) {
    return '';
  }
  return value.endsWith('/') ? value.slice(0, -1) : value;
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

export function getApiToken() {
  const v = (import.meta?.env?.VITE_API_TOKEN ?? '').toString().trim();
  return v || '';
}

export async function apiFetchJson(path, options = {}) {
  const base = getApiBase();
  const url = `${base}${path}`;
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
