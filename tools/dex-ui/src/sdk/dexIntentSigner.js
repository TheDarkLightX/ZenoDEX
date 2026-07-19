import { hashV0, stableStringify } from './zenoProofClient.js';

const COMMON_INTENT_KEYS = new Set([
  'module',
  'version',
  'kind',
  'intent_id',
  'sender_pubkey',
  'deadline',
  'salt',
  'fields',
  'quote_receipt',
]);

function asInt(value, name) {
  const n = Number(value);
  if (!Number.isSafeInteger(n) || n < 0) {
    throw new Error(`${name}_must_be_safe_nonnegative_int`);
  }
  return n;
}

function canonicalAssetId(value, name) {
  const text = String(value || '').trim();
  const body = text.startsWith('0x') || text.startsWith('0X') ? text.slice(2) : text;
  if (!/^[0-9a-fA-F]{64}$/.test(body)) {
    throw new Error(`${name}_must_be_32_byte_asset_id`);
  }
  return `0x${body.toLowerCase()}`;
}

function toSafeNumber(value, name) {
  if (value > BigInt(Number.MAX_SAFE_INTEGER)) {
    throw new Error(`${name}_exceeds_safe_integer`);
  }
  return Number(value);
}

function divFloor(a, b) {
  if (b <= 0n) {
    throw new Error('division_by_zero');
  }
  return a / b;
}

function bpsMulFloor(value, bps, name) {
  return toSafeNumber((BigInt(value) * BigInt(bps)) / 10_000n, name);
}

function bpsMulCeil(value, bps, name) {
  return toSafeNumber((BigInt(value) * BigInt(bps) + 9_999n) / 10_000n, name);
}

export function encodeTauOperationsForWire(operations) {
  if (!operations || typeof operations !== 'object' || Array.isArray(operations)) {
    throw new Error('operations_must_be_object');
  }
  const encoded = {};
  for (const [key, value] of Object.entries(operations)) {
    if (key === '0' || key === '1') {
      encoded[key] = value;
    } else if (typeof value === 'boolean') {
      throw new Error(`operation stream ${key}: bool values are not allowed`);
    } else if (typeof value === 'string' || typeof value === 'number') {
      encoded[key] = value;
    } else {
      encoded[key] = stableStringify(value);
    }
  }
  return encoded;
}

const PERP_SIGNED_FIELD_KEYS = {
  init_market_2p: ['quote_asset', 'account_a_pubkey', 'account_b_pubkey', 'deadline'],
  init_market_3p: ['quote_asset', 'account_a_pubkey', 'account_b_pubkey', 'account_c_pubkey', 'deadline'],
  set_position_pair: ['account_a_pubkey', 'account_b_pubkey', 'new_position_base_a', 'new_position_base_b', 'deadline'],
  set_position_triplet: [
    'account_a_pubkey',
    'account_b_pubkey',
    'account_c_pubkey',
    'new_position_base_a',
    'new_position_base_b',
    'new_position_base_c',
    'deadline',
  ],
  publish_clearing_price: ['price_e8', 'deadline'],
};

export function buildPerpOpAuthSigningDictV1(op, { signerPubkey, signer_pubkey, nonce }) {
  if (!op || typeof op !== 'object' || Array.isArray(op)) {
    throw new Error('perp_op_must_be_object');
  }
  const signer = String(signer_pubkey ?? signerPubkey ?? '').trim();
  if (!signer) {
    throw new Error('signer_pubkey_required');
  }
  const keys = PERP_SIGNED_FIELD_KEYS[op.action];
  if (!keys) {
    throw new Error(`unsupported signed action: ${op.action}`);
  }
  for (const key of ['module', 'version', 'market_id', 'action']) {
    if (typeof op[key] !== 'string' || !op[key]) {
      throw new Error(`signing dict missing ${key}`);
    }
  }
  const fields = {};
  for (const key of keys) {
    if (!(key in op)) {
      throw new Error(`signing dict missing field: ${key}`);
    }
    fields[key] = op[key];
  }
  return {
    module: op.module,
    version: op.version,
    market_id: op.market_id,
    action: op.action,
    signer_pubkey: signer,
    nonce: asInt(nonce, 'nonce'),
    fields,
  };
}

export function buildDexIntentSigningDictV1(intent) {
  if (!intent || typeof intent !== 'object' || Array.isArray(intent)) {
    throw new Error('intent must be an object');
  }
  const explicitFields = intent.fields;
  const fields = explicitFields && typeof explicitFields === 'object' && !Array.isArray(explicitFields)
    ? { ...explicitFields }
    : Object.fromEntries(
      Object.entries(intent).filter(([key]) => !COMMON_INTENT_KEYS.has(key) && key !== 'signature'),
    );
  const signingDict = {
    module: intent.module,
    version: intent.version,
    kind: intent.kind,
    intent_id: intent.intent_id,
    sender_pubkey: intent.sender_pubkey,
    deadline: intent.deadline,
    fields,
  };
  if (intent.salt !== undefined && intent.salt !== null) {
    signingDict.salt = intent.salt;
  }
  return signingDict;
}

async function signDexIntentWithAvailableSigner(intent, { chainId, signDexIntent }) {
  if (typeof signDexIntent !== 'function') {
    throw new Error('external_dex_intent_signer_required');
  }
  return signDexIntent(intent, { chainId });
}

function liquidityMath({ kind, pool, payload }) {
  const reserve0 = BigInt(asInt(pool.reserve0 ?? pool.reserve_0, 'reserve0'));
  const reserve1 = BigInt(asInt(pool.reserve1 ?? pool.reserve_1, 'reserve1'));
  const lpSupply = BigInt(asInt(pool.lpSupply ?? pool.lp_supply, 'lp_supply'));
  const amount0Min = BigInt(asInt(payload.amount0Min ?? payload.amount0_min ?? 0, 'amount0_min'));
  const amount1Min = BigInt(asInt(payload.amount1Min ?? payload.amount1_min ?? 0, 'amount1_min'));
  if (kind === 'ADD_LIQUIDITY') {
    const amount0Desired = BigInt(asInt(payload.amount0Desired ?? payload.amount0_desired, 'amount0_desired'));
    const amount1Desired = BigInt(asInt(payload.amount1Desired ?? payload.amount1_desired, 'amount1_desired'));
    const lhs = amount0Desired * reserve1;
    const rhs = amount1Desired * reserve0;
    let amount0Used;
    let amount1Used;
    if (lhs <= rhs) {
      amount0Used = amount0Desired;
      amount1Used = divFloor(amount0Desired * reserve1, reserve0);
    } else {
      amount0Used = divFloor(amount1Desired * reserve0, reserve1);
      amount1Used = amount1Desired;
    }
    if (amount0Used < amount0Min || amount1Used < amount1Min) {
      throw new Error('liquidity_minimum_not_satisfied');
    }
    const lp0 = divFloor(amount0Used * lpSupply, reserve0);
    const lp1 = divFloor(amount1Used * lpSupply, reserve1);
    const lpMinted = lp0 < lp1 ? lp0 : lp1;
    if (lpMinted <= 0n) {
      throw new Error('lp_minted_zero');
    }
    return {
      amount0_desired: toSafeNumber(amount0Desired, 'amount0_desired'),
      amount1_desired: toSafeNumber(amount1Desired, 'amount1_desired'),
      amount0_used: toSafeNumber(amount0Used, 'amount0_used'),
      amount1_used: toSafeNumber(amount1Used, 'amount1_used'),
      lp_minted: toSafeNumber(lpMinted, 'lp_minted'),
    };
  }
  const lpAmount = BigInt(asInt(payload.lpAmount ?? payload.lp_amount, 'lp_amount'));
  const amount0Out = divFloor(lpAmount * reserve0, lpSupply);
  const amount1Out = divFloor(lpAmount * reserve1, lpSupply);
  if (amount0Out < amount0Min || amount1Out < amount1Min) {
    throw new Error('remove_liquidity_minimum_not_satisfied');
  }
  return {
    lp_amount: toSafeNumber(lpAmount, 'lp_amount'),
    amount0_out: toSafeNumber(amount0Out, 'amount0_out'),
    amount1_out: toSafeNumber(amount1Out, 'amount1_out'),
  };
}

export async function buildAndSignLiquidityIntent({
  kind,
  pool,
  payload,
  signDexIntent,
  chainId = '',
}) {
  if (kind !== 'ADD_LIQUIDITY' && kind !== 'REMOVE_LIQUIDITY') {
    throw new Error('unsupported_liquidity_kind');
  }
  const sender = String(payload.senderPubkey || payload.sender_pubkey || '').trim();
  const recipient = String(payload.recipient || sender).trim();
  const poolId = String(payload.poolId || payload.pool_id || pool.poolId || pool.pool_id || '').trim();
  const deadline = asInt(payload.deadline ?? 1_999_999_999, 'deadline');
  const nonce = asInt(payload.nonce, 'nonce');
  const amount0Min = asInt(payload.amount0Min ?? payload.amount0_min ?? 0, 'amount0_min');
  const amount1Min = asInt(payload.amount1Min ?? payload.amount1_min ?? 0, 'amount1_min');
  const math = liquidityMath({ kind, pool, payload });
  const intentPayload = {
    sender_pubkey: sender,
    recipient,
    pool_id: poolId,
    amount0_min: amount0Min,
    amount1_min: amount1Min,
    ...math,
    nonce,
  };
  const prefix = kind === 'ADD_LIQUIDITY' ? 'ui-add-liquidity' : 'ui-remove-liquidity';
  const operation = {
    module: 'TauSwap',
    version: '0.1',
    kind,
    sender_pubkey: sender,
    deadline,
    pool_id: poolId,
    amount0_min: amount0Min,
    amount1_min: amount1Min,
    recipient,
    nonce,
    intent_id: await hashV0(`${prefix}_intent_v0`, intentPayload),
  };
  if (kind === 'ADD_LIQUIDITY') {
    operation.amount0_desired = math.amount0_desired;
    operation.amount1_desired = math.amount1_desired;
  } else {
    operation.lp_amount = math.lp_amount;
  }
  return {
    intent: operation,
    signature: await signDexIntentWithAvailableSigner(operation, { chainId, signDexIntent }),
  };
}

const NONCE_U32_MAX = 0xFFFFFFFF;

function pyGetShadow(obj, key, fallback) {
  if (Object.prototype.hasOwnProperty.call(obj, key)) {
    return obj[key];
  }
  return fallback;
}

function swapModeMarker(payload) {
  const modeRaw = pyGetShadow(payload, 'mode', payload.kind);
  if (typeof modeRaw === 'string') {
    const mode = modeRaw.trim().toLowerCase().replace(/-/g, '_');
    if (mode === 'swap_exact_out' || mode === 'exact_out' || mode === 'out') {
      return 'out';
    }
    if (mode === 'swap_exact_in' || mode === 'exact_in' || mode === 'in') {
      return 'in';
    }
  }
  return null;
}

export function isSwapExactOutPayload(payload) {
  if (!payload || typeof payload !== 'object') {
    return false;
  }
  const marker = swapModeMarker(payload);
  if (marker === 'out') {
    return true;
  }
  if (marker === 'in') {
    return false;
  }
  return payload.amountOut != null || payload.amount_out != null
    || payload.maxAmountIn != null || payload.max_amount_in != null;
}

function requireUnambiguousSwapPayload(payload) {
  const inPresent = payload.amountIn != null || payload.amount_in != null
    || payload.minAmountOut != null || payload.min_amount_out != null;
  const outPresent = payload.amountOut != null || payload.amount_out != null
    || payload.maxAmountIn != null || payload.max_amount_in != null;
  const marker = swapModeMarker(payload);
  const markerOut = marker === 'out';
  const markerIn = marker === 'in';
  if ((inPresent && outPresent) || (markerOut && inPresent) || (markerIn && outPresent)) {
    throw new Error('ambiguous_swap_intent_specify_exact_in_or_exact_out_not_both');
  }
}

export async function buildAndSignSwapIntent({
  pool,
  payload,
  signDexIntent,
  chainId = '',
}) {
  if (!pool || typeof pool !== 'object' || Array.isArray(pool)) {
    throw new Error('pool_must_be_object');
  }
  requireUnambiguousSwapPayload(payload);
  const sender = String(payload.senderPubkey || payload.sender_pubkey || '').trim();
  const recipient = String(payload.recipient || sender).trim();
  const poolId = String(payload.poolId || payload.pool_id || pool.poolId || pool.pool_id || '').trim();
  const deadline = asInt(payload.deadline ?? 1_999_999_999, 'deadline');
  const nonce = asInt(payload.nonce, 'nonce');
  if (nonce > NONCE_U32_MAX) {
    throw new Error('nonce_must_fit_u32');
  }
  const rawAssetIn = payload.assetIn ?? payload.asset_in;
  const rawAssetOut = payload.assetOut ?? payload.asset_out;
  const assetIn = canonicalAssetId(rawAssetIn, 'asset_in');
  const assetOut = canonicalAssetId(rawAssetOut, 'asset_out');
  if (assetIn === assetOut) {
    throw new Error('swap_assets_must_differ');
  }
  const exactOut = isSwapExactOutPayload(payload);
  let amountFields;
  let kind;
  if (exactOut) {
    const amountOut = asInt(payload.amountOut ?? payload.amount_out, 'amount_out');
    const maxAmountIn = asInt(payload.maxAmountIn ?? payload.max_amount_in, 'max_amount_in');
    amountFields = { amount_out: amountOut, max_amount_in: maxAmountIn };
    kind = 'SWAP_EXACT_OUT';
  } else {
    const amountIn = asInt(payload.amountIn ?? payload.amount_in, 'amount_in');
    const minAmountOut = asInt(payload.minAmountOut ?? payload.min_amount_out ?? 1, 'min_amount_out');
    amountFields = { amount_in: amountIn, min_amount_out: minAmountOut };
    kind = 'SWAP_EXACT_IN';
  }
  const intentPayload = {
    sender_pubkey: sender,
    recipient,
    pool_id: poolId,
    asset_in: assetIn,
    asset_out: assetOut,
    ...amountFields,
    nonce,
  };
  const operation = {
    module: 'TauSwap',
    version: '0.1',
    kind,
    intent_id: await hashV0('ui_swap_intent_v0', intentPayload),
    sender_pubkey: sender,
    deadline,
    nonce,
    pool_id: poolId,
    asset_in: assetIn,
    asset_out: assetOut,
    ...amountFields,
    recipient,
  };
  return {
    intent: operation,
    signature: await signDexIntentWithAvailableSigner(operation, { chainId, signDexIntent }),
  };
}

export async function buildAndSignRouteIntent({
  payload,
  signDexIntent,
  chainId = '',
}) {
  const sender = String(payload.senderPubkey || payload.sender_pubkey || '').trim();
  const recipient = String(payload.recipient || sender).trim();
  const deadline = asInt(payload.deadline ?? 1_999_999_999, 'deadline');
  const nonceStart = asInt(payload.nonce ?? payload.nonceStart ?? payload.nonce_start, 'nonce');
  if (nonceStart > NONCE_U32_MAX) {
    throw new Error('nonce_must_fit_u32');
  }
  const quoteReceipt = payload.quoteReceipt || payload.quote_receipt;
  if (!quoteReceipt || typeof quoteReceipt !== 'object') {
    throw new Error('quote_receipt_required');
  }
  const receiptBody = quoteReceipt.body;
  if (!receiptBody || typeof receiptBody !== 'object') {
    throw new Error('quote_receipt_body_required');
  }
  const receiptKind = String(receiptBody.kind || '').trim().toLowerCase();
  if (receiptKind !== 'exact_in' && receiptKind !== 'exact_out') {
    throw new Error('quote_receipt_kind_must_be_exact_in_or_exact_out');
  }
  const kindMarker = String(payload.kind || payload.routeKind || payload.mode || '').trim().toLowerCase().replace(/-/g, '_');
  if (kindMarker && kindMarker !== receiptKind
    && !(kindMarker === 'route_exact_in' && receiptKind === 'exact_in')
    && !(kindMarker === 'route_exact_out' && receiptKind === 'exact_out')) {
    throw new Error('route_kind_mismatch');
  }
  const assetIn = canonicalAssetId(receiptBody.asset_in, 'asset_in');
  const assetOut = canonicalAssetId(receiptBody.asset_out, 'asset_out');
  if (assetIn === assetOut) {
    throw new Error('swap_assets_must_differ');
  }
  const legs = receiptBody.legs;
  if (!Array.isArray(legs) || legs.length === 0) {
    throw new Error('quote_receipt_legs_required');
  }
  const hopRows = [];
  for (const [legIndex, leg] of legs.entries()) {
    if (!Array.isArray(leg.hops) || leg.hops.length !== 1) {
      throw new Error('route_multihop_unsupported');
    }
    const hop = leg.hops[0];
    if (!hop || typeof hop !== 'object') {
      throw new Error('quote_receipt_hop_required');
    }
    hopRows.push([legIndex, hop]);
  }
  const expectedLegIndices = Array.from({ length: legs.length }, (_, i) => i);
  const rawLegIndices = payload.legIndices ?? payload.leg_indices;
  if (rawLegIndices != null) {
    if (!Array.isArray(rawLegIndices) || rawLegIndices.length !== expectedLegIndices.length
      || !rawLegIndices.every((v, i) => v === i)) {
      throw new Error('leg_indices_must_cover_full_receipt');
    }
  }
  const legIndices = expectedLegIndices;
  const canonicalReceiptHash = String(quoteReceipt.receipt_hash || '').trim();
  if (!canonicalReceiptHash) {
    throw new Error('quote_receipt_hash_required');
  }
  const receiptPools = receiptBody.pools;
  if (!receiptPools || typeof receiptPools !== 'object' || Array.isArray(receiptPools)) {
    throw new Error('quote_receipt_pools_required');
  }
  const bodyAmountIn = asInt(receiptBody.amount_in, 'amount_in');
  const bodyAmountOut = asInt(receiptBody.amount_out, 'amount_out');
  const slippageBps = asInt(payload.slippageBps ?? payload.slippage_bps ?? 0, 'slippage_bps');
  if (slippageBps > 10_000) {
    throw new Error('slippage_bps_must_be_at_most_10000');
  }
  if (nonceStart + hopRows.length - 1 > NONCE_U32_MAX) {
    throw new Error('nonce_range_overflow');
  }
  if (receiptKind === 'exact_in') {
    const totalAmountIn = asInt(payload.totalAmountIn ?? payload.total_amount_in ?? bodyAmountIn, 'total_amount_in');
    const totalMinAmountOut = asInt(payload.totalMinAmountOut ?? payload.total_min_amount_out ?? bodyAmountOut, 'total_min_amount_out');
    if (totalAmountIn !== bodyAmountIn) {
      throw new Error('total_amount_in_must_match_receipt');
    }
    if (totalMinAmountOut > bodyAmountOut) {
      throw new Error('total_min_amount_out_exceeds_receipt');
    }
  } else {
    const totalAmountOut = asInt(payload.totalAmountOut ?? payload.total_amount_out ?? bodyAmountOut, 'total_amount_out');
    const totalMaxAmountIn = asInt(payload.totalMaxAmountIn ?? payload.total_max_amount_in ?? bodyAmountIn, 'total_max_amount_in');
    if (totalAmountOut !== bodyAmountOut) {
      throw new Error('total_amount_out_must_match_receipt');
    }
    if (totalMaxAmountIn < bodyAmountIn) {
      throw new Error('total_max_amount_in_below_receipt');
    }
  }

  hopRows.sort((a, b) => {
    const poolA = String(a[1].pool_id || '');
    const poolB = String(b[1].pool_id || '');
    return poolA.localeCompare(poolB) || a[0] - b[0];
  });

  const signedIntents = [];
  for (const [orderIndex, [legIndex, hop]] of hopRows.entries()) {
    const poolId = String(hop.pool_id || '').trim();
    const hopAssetIn = canonicalAssetId(hop.asset_in, `legs.${legIndex}.asset_in`);
    const hopAssetOut = canonicalAssetId(hop.asset_out, `legs.${legIndex}.asset_out`);
    if (!poolId || hopAssetIn !== assetIn || hopAssetOut !== assetOut) {
      throw new Error('unsupported_mixed_route_leg');
    }
    const quotePoolFingerprint = String(receiptPools[poolId] || '').trim();
    if (!quotePoolFingerprint) {
      throw new Error('quote_pool_fingerprint_required');
    }
    const legNonce = nonceStart + orderIndex;
    const commonFields = {
      pool_id: poolId,
      asset_in: hopAssetIn,
      asset_out: hopAssetOut,
      recipient,
      quote_receipt_hash: canonicalReceiptHash,
      quote_pool_fingerprint: quotePoolFingerprint,
      quote_receipt_leg_index: legIndex,
      nonce: legNonce,
    };
    let kind;
    let amountFields;
    if (receiptKind === 'exact_in') {
      const amountIn = asInt(hop.amount_in, `legs.${legIndex}.amount_in`);
      const quotedAmountOut = asInt(hop.amount_out, `legs.${legIndex}.amount_out`);
      if (amountIn <= 0 || quotedAmountOut <= 0) {
        throw new Error('invalid_quote_receipt_amounts');
      }
      const minAmountOut = bpsMulFloor(
        quotedAmountOut,
        10_000 - slippageBps,
        `legs.${legIndex}.min_amount_out`,
      );
      kind = 'SWAP_EXACT_IN';
      amountFields = {
        amount_in: amountIn,
        min_amount_out: minAmountOut,
      };
    } else {
      const quotedAmountIn = asInt(hop.amount_in, `legs.${legIndex}.amount_in`);
      const amountOut = asInt(hop.amount_out, `legs.${legIndex}.amount_out`);
      if (quotedAmountIn <= 0 || amountOut <= 0) {
        throw new Error('invalid_quote_receipt_amounts');
      }
      const maxAmountIn = bpsMulCeil(
        quotedAmountIn,
        10_000 + slippageBps,
        `legs.${legIndex}.max_amount_in`,
      );
      kind = 'SWAP_EXACT_OUT';
      amountFields = {
        amount_out: amountOut,
        max_amount_in: maxAmountIn,
      };
    }
    const intentPayload = {
      sender_pubkey: sender,
      ...commonFields,
      ...amountFields,
    };
    const operation = {
      module: 'TauSwap',
      version: '0.1',
      kind,
      intent_id: await hashV0('ui_route_leg_intent_v0', intentPayload),
      sender_pubkey: sender,
      deadline,
      ...commonFields,
      ...amountFields,
      quote_receipt: quoteReceipt,
    };
    signedIntents.push({
      intent: operation,
      signature: await signDexIntentWithAvailableSigner(operation, { chainId, signDexIntent }),
    });
  }
  const first = signedIntents[0];
  return {
    intent: first.intent,
    signature: first.signature,
    intents: signedIntents.map((entry) => entry.intent),
    signatures: signedIntents.map((entry) => entry.signature),
    signedIntents,
    leg_indices: legIndices,
  };
}

export async function buildAndSignCreatePoolIntent({
  payload,
  signDexIntent,
  chainId = '',
}) {
  const sender = String(payload.senderPubkey || payload.sender_pubkey || '').trim();
  const deadline = asInt(payload.deadline ?? 1_999_999_999, 'deadline');
  const nonce = asInt(payload.nonce, 'nonce');
  const feeBps = asInt(payload.feeBps ?? payload.fee_bps ?? 30, 'fee_bps');
  if (feeBps > 10_000) {
    throw new Error('fee_bps_must_be_at_most_10000');
  }
  const createdAt = asInt(payload.createdAt ?? payload.created_at ?? Math.floor(Date.now() / 1000), 'created_at');
  const rawAsset0 = canonicalAssetId(payload.asset0, 'asset0');
  const rawAsset1 = canonicalAssetId(payload.asset1, 'asset1');
  if (rawAsset0 === rawAsset1) {
    throw new Error('assets_must_differ');
  }
  const rawAmount0 = asInt(payload.amount0, 'amount0');
  const rawAmount1 = asInt(payload.amount1, 'amount1');
  if (Math.floor(Math.sqrt(rawAmount0 * rawAmount1)) <= 1000) {
    throw new Error('initial_liquidity_must_exceed_locked_minimum');
  }
  const [asset0, asset1, amount0, amount1] = rawAsset0 < rawAsset1
    ? [rawAsset0, rawAsset1, rawAmount0, rawAmount1]
    : [rawAsset1, rawAsset0, rawAmount1, rawAmount0];
  const intentPayload = {
    sender_pubkey: sender,
    asset0,
    asset1,
    fee_bps: feeBps,
    amount0,
    amount1,
    created_at: createdAt,
    nonce,
  };
  const operation = {
    module: 'TauSwap',
    version: '0.1',
    kind: 'CREATE_POOL',
    intent_id: await hashV0('ui-create-pool_intent_v0', intentPayload),
    sender_pubkey: sender,
    deadline,
    nonce,
    asset0,
    asset1,
    fee_bps: feeBps,
    amount0,
    amount1,
    created_at: createdAt,
  };
  return {
    intent: operation,
    signature: await signDexIntentWithAvailableSigner(operation, { chainId, signDexIntent }),
  };
}
