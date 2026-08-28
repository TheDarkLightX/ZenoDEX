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

const CURRENT_PROFILE_QUARANTINED_VALUE_ROUTES_V1 = Object.freeze({
  perpsWalletEnabled: false,
  zusdTauWalletEnabled: false,
  zusdMonetaryWalletEnabled: false,
});

export function getRuntimeValueRoutePresentationV1(runtimeConfig = getRuntimeConfig()) {
  // The current profile has no browser-selectable value-route admission.
  // Future activation requires a new release-backed profile and helper.
  void runtimeConfig;
  return CURRENT_PROFILE_QUARANTINED_VALUE_ROUTES_V1;
}

export function isLocalTestnetDeployment(runtimeConfig = getRuntimeConfig()) {
  const deployment = String(runtimeConfig?.deployment || '').toLowerCase();
  return deployment === 'local-testnet' || deployment === 'localtest';
}

export function readLocalSmokeFragmentSecret(names) {
  if (!isLocalTestnetDeployment() || typeof window === 'undefined') {
    return '';
  }
  const fragment = String(window.location.hash || '').replace(/^#/, '');
  if (!fragment) {
    return '';
  }
  const fragmentParams = new URLSearchParams(fragment);
  for (const name of Array.isArray(names) ? names : [names]) {
    const value = fragmentParams.get(name);
    if (value) {
      return value;
    }
  }
  return '';
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
  const runtimeConfig = getRuntimeConfig();
  const hasRuntimeOracleBase = Object.prototype.hasOwnProperty.call(runtimeConfig, 'zenoOracleApiBase');
  const runtimeBase = normalizeApiBase(runtimeConfig.zenoOracleApiBase);
  if (runtimeBase) {
    return runtimeBase;
  }
  const v = normalizeApiBase(import.meta?.env?.VITE_ZENO_ORACLE_API_URL ?? '');
  if (v) {
    return v;
  }
  if (hasRuntimeOracleBase) {
    return '';
  }
  return DEFAULT_ZENO_ORACLE_API_BASE;
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

function shouldAttachApiToken(url, { pathIsAbsolute }) {
  if (!pathIsAbsolute) {
    return true;
  }
  if (typeof window === 'undefined' || !window.location) {
    return false;
  }
  try {
    return new URL(url).origin === window.location.origin;
  } catch {
    return false;
  }
}

export async function apiFetchJson(path, options = {}) {
  const base = getApiBase();
  const pathText = String(path || '');
  const pathIsAbsolute = /^https?:\/\//i.test(pathText);
  const url = pathIsAbsolute ? pathText : `${base}${pathText}`;
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
  if (token && shouldAttachApiToken(url, { pathIsAbsolute }) && !hasHeader('authorization')) {
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

export function apiGetTokenomicsStatus(options = {}) {
  return apiFetchJson('/api/tokenomics/status', { method: 'GET', ...(options || {}) });
}

export function apiClaimTokenomicsActiveParticipantReward(body, options = {}) {
  return apiFetchJson('/api/tokenomics/active-participant/claim', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiGetConfidentialStatus(options = {}) {
  return apiFetchJson('/api/confidential/status', { method: 'GET', ...(options || {}) });
}

export function apiVerifyConfidentialAttestation(body, options = {}) {
  return apiFetchJson('/api/confidential/attestation/verify', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiAdmitConfidentialAttestation(body, options = {}) {
  return apiFetchJson('/api/confidential/attestation/admit', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiExecuteConfidentialAttestation(body, options = {}) {
  return apiFetchJson('/api/confidential/attestation/execute', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiGetConfidentialSealedBidStatus(options = {}) {
  return apiFetchJson('/api/confidential/sealed-bid/status', { method: 'GET', ...(options || {}) });
}

export function apiResetConfidentialSealedBid(body, options = {}) {
  return apiFetchJson('/api/confidential/sealed-bid/reset', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiCommitConfidentialSealedBid(body, options = {}) {
  return apiFetchJson('/api/confidential/sealed-bid/commit', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiOpenRevealConfidentialSealedBid(body, options = {}) {
  return apiFetchJson('/api/confidential/sealed-bid/open-reveal', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiRevealConfidentialSealedBid(body, options = {}) {
  return apiFetchJson('/api/confidential/sealed-bid/reveal', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiSettleConfidentialSealedBid(body, options = {}) {
  return apiFetchJson('/api/confidential/sealed-bid/se' + 'ttle', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
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

export function apiMintTestnetFaucet(body, options = {}) {
  return apiFetchJson('/api/testnet/faucet', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiMintPerpsWalletTestnetFaucet(body, options = {}) {
  return apiFetchJson('/api/perps/wallet/testnet-faucet', {
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

export function apiEvaluatePerpsRecovery(body, options = {}) {
  return apiFetchJson('/api/perps/wallet/recovery/evaluate', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiEvaluatePerpsRotation(body, options = {}) {
  return apiFetchJson('/api/perps/wallet/rotation/evaluate', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiEvaluatePerpsDeviceApproval(body, options = {}) {
  return apiFetchJson('/api/perps/wallet/device-approval/evaluate', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiEvaluatePerpsSignerDevice(body, options = {}) {
  return apiFetchJson('/api/perps/wallet/signer-device/evaluate', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiEvaluatePerpsSignerPromptCapture(body, options = {}) {
  return apiFetchJson('/api/perps/wallet/signer-prompt-capture/evaluate', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiEvaluatePerpsSignerExecution(body, options = {}) {
  return apiFetchJson('/api/perps/wallet/signer-execution/evaluate', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiEvaluatePerpsSignerCeremony(body, options = {}) {
  return apiFetchJson('/api/perps/wallet/signer-ceremony/evaluate', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiEvaluatePerpsHardwareCustody(body, options = {}) {
  return apiFetchJson('/api/perps/wallet/hardware-cus' + 'tody/evaluate', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiEvaluatePerpsEncryptedSssBackup(body, options = {}) {
  return apiFetchJson('/api/perps/wallet/encrypted-sss-backup/evaluate', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiDeliverPerpsEncryptedSssBackup(body, options = {}) {
  return apiFetchJson('/api/perps/wallet/encrypted-sss-backup/deliver', {
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

export function apiSubmitAutotraderLive(body, options = {}) {
  return apiFetchJson('/api/strategy/autotrader/submit', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiExecuteAutotraderLiveOnce(body, options = {}) {
  return apiFetchJson('/api/strategy/autotrader/execute-once', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiPreflightAutotraderSupervisor(body, options = {}) {
  return apiFetchJson('/api/strategy/autotrader/supervisor/preflight', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiExecuteAutotraderSupervisor(body, options = {}) {
  return apiFetchJson('/api/strategy/autotrader/supervisor/execute', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiGetPools(options = {}) {
  const { account = '', ...fetchOptions } = options || {};
  const accountText = String(account || '').trim();
  const path = accountText ? `/api/pools?account=${encodeURIComponent(accountText)}` : '/api/pools';
  return apiFetchJson(path, { method: 'GET', ...fetchOptions });
}

function isSwapExactOutRequest({ kind, amountOut, maxAmountIn }) {
  if (typeof kind === 'string' && kind.trim().toUpperCase() === 'SWAP_EXACT_OUT') {
    return true;
  }
  return amountOut != null || maxAmountIn != null;
}

export function apiSwap(
  {
    from,
    to,
    amountIn,
    minAmountOut = 1,
    amountOut = null,
    maxAmountIn = null,
    kind = null,
    poolId = null,
    assetIn = null,
    assetOut = null,
    senderPubkey = null,
    recipient = null,
    deadline = null,
    signature = null,
    nonce = null,
    timeMs = null,
    txId = null,
  },
  options = {},
) {
  const exactOut = isSwapExactOutRequest({ kind, amountOut, maxAmountIn });
  const body = { from, to };
  if (exactOut) {
    body.kind = 'SWAP_EXACT_OUT';
    body.amountOut = amountOut;
    body.maxAmountIn = maxAmountIn;
  } else {
    body.amountIn = amountIn;
    body.minAmountOut = minAmountOut;
  }
  if (kind && !exactOut) body.kind = kind;
  if (poolId) body.poolId = poolId;
  if (assetIn) body.assetIn = assetIn;
  if (assetOut) body.assetOut = assetOut;
  if (senderPubkey) body.senderPubkey = senderPubkey;
  if (recipient) body.recipient = recipient;
  if (deadline) body.deadline = deadline;
  if (signature) body.signature = signature;
  if (nonce != null) body.nonce = nonce;
  if (timeMs != null) body.time_ms = timeMs;
  if (txId) body.tx_id = txId;
  return apiFetchJson('/api/swap', {
    method: 'POST',
    body: JSON.stringify(body),
    ...(options || {}),
  });
}

export function apiRoute(
  {
    quoteReceipt,
    kind,
    legIndices = null,
    totalAmountIn = null,
    totalMinAmountOut = null,
    totalAmountOut = null,
    totalMaxAmountIn = null,
    senderPubkey = null,
    recipient = null,
    deadline = null,
    nonce = null,
    signature = null,
    timeMs = null,
    txId = null,
  },
  options = {},
) {
  const body = { quoteReceipt, kind };
  if (legIndices != null) body.legIndices = legIndices;
  if (totalAmountIn != null) body.totalAmountIn = totalAmountIn;
  if (totalMinAmountOut != null) body.totalMinAmountOut = totalMinAmountOut;
  if (totalAmountOut != null) body.totalAmountOut = totalAmountOut;
  if (totalMaxAmountIn != null) body.totalMaxAmountIn = totalMaxAmountIn;
  if (senderPubkey) body.senderPubkey = senderPubkey;
  if (recipient) body.recipient = recipient;
  if (deadline) body.deadline = deadline;
  if (nonce != null) body.nonce = nonce;
  if (signature) body.signature = signature;
  if (timeMs != null) body.time_ms = timeMs;
  if (txId) body.tx_id = txId;
  return apiFetchJson('/api/route', {
    method: 'POST',
    body: JSON.stringify(body),
    ...(options || {}),
  });
}

export function apiDexQuote(
  {
    kind,
    from,
    to,
    amountIn = null,
    amountOut = null,
    routingMode = null,
    fastTopkMax = null,
    quoteEpoch = null,
  },
  options = {},
) {
  const body = { kind, asset_in: from, asset_out: to };
  if (amountIn != null) body.amount_in = amountIn;
  if (amountOut != null) body.amount_out = amountOut;
  if (routingMode) body.routing_mode = routingMode;
  if (fastTopkMax != null) body.fast_topk_max = fastTopkMax;
  if (quoteEpoch != null) body.quote_epoch = quoteEpoch;
  return apiFetchJson('/api/dex/quote', {
    method: 'POST',
    body: JSON.stringify(body),
    ...(options || {}),
  });
}

export function apiAddLiquidity(
  {
    poolId,
    asset0 = null,
    asset1 = null,
    amount0Desired,
    amount1Desired,
    amount0Min = 0,
    amount1Min = 0,
    senderPubkey = null,
    recipient = null,
    deadline = null,
    signature = null,
    nonce = null,
    timeMs = null,
    txId = null,
  },
  options = {},
) {
  const body = {
    poolId,
    amount0Desired,
    amount1Desired,
    amount0Min,
    amount1Min,
  };
  if (asset0) body.asset0 = asset0;
  if (asset1) body.asset1 = asset1;
  if (senderPubkey) body.senderPubkey = senderPubkey;
  if (recipient) body.recipient = recipient;
  if (deadline) body.deadline = deadline;
  if (signature) body.signature = signature;
  if (nonce != null) body.nonce = nonce;
  if (timeMs != null) body.time_ms = timeMs;
  if (txId) body.tx_id = txId;
  return apiFetchJson('/api/liquidity/add', {
    method: 'POST',
    body: JSON.stringify(body),
    ...(options || {}),
  });
}

export function apiCreateLiquidityPool(
  {
    asset0,
    asset1,
    amount0,
    amount1,
    feeBps = 30,
    senderPubkey = null,
    deadline = null,
    signature = null,
    nonce = null,
    createdAt = null,
    timeMs = null,
    txId = null,
  },
  options = {},
) {
  const body = {
    asset0,
    asset1,
    amount0,
    amount1,
    feeBps,
  };
  if (senderPubkey) body.senderPubkey = senderPubkey;
  if (deadline) body.deadline = deadline;
  if (signature) body.signature = signature;
  if (nonce != null) body.nonce = nonce;
  if (createdAt != null) body.createdAt = createdAt;
  if (timeMs != null) body.time_ms = timeMs;
  if (txId) body.tx_id = txId;
  return apiFetchJson('/api/liquidity/create', {
    method: 'POST',
    body: JSON.stringify(body),
    ...(options || {}),
  });
}

export function apiRemoveLiquidity(
  {
    poolId,
    lpAmount,
    amount0Min = 0,
    amount1Min = 0,
    senderPubkey = null,
    recipient = null,
    deadline = null,
    signature = null,
    nonce = null,
    timeMs = null,
    txId = null,
  },
  options = {},
) {
  const body = {
    poolId,
    lpAmount,
    amount0Min,
    amount1Min,
  };
  if (senderPubkey) body.senderPubkey = senderPubkey;
  if (recipient) body.recipient = recipient;
  if (deadline) body.deadline = deadline;
  if (signature) body.signature = signature;
  if (nonce != null) body.nonce = nonce;
  if (timeMs != null) body.time_ms = timeMs;
  if (txId) body.tx_id = txId;
  return apiFetchJson('/api/liquidity/remove', {
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

export function apiCheckProofMiningStatus(body, options = {}) {
  return apiFetchJson('/api/dex/proof_mining_status', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiBuildProofMiningPayoutTemplate(body, options = {}) {
  return apiFetchJson('/api/dex/proof_mining_payout_template', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}

export function apiSubmitLedgerTransaction(body, options = {}) {
  return apiFetchJson('/tx', {
    method: 'POST',
    body: JSON.stringify(body || {}),
    ...(options || {}),
  });
}
