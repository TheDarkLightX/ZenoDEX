import { hashV0, stableStringify } from './zenoProofClient.js';

const textEncoder = new TextEncoder();
const COMMON_INTENT_KEYS = new Set([
  'module',
  'version',
  'kind',
  'intent_id',
  'sender_pubkey',
  'deadline',
  'salt',
  'fields',
]);

function bytesToHex(bytes) {
  return Array.from(bytes, (byte) => byte.toString(16).padStart(2, '0')).join('');
}

function hexToBytes(value, name = 'hex') {
  const s = String(value || '').trim();
  const body = s.startsWith('0x') ? s.slice(2) : s;
  if (!/^[0-9a-fA-F]+$/.test(body) || body.length % 2 !== 0) {
    throw new Error(`${name} must be even-length hex`);
  }
  return Uint8Array.from(body.match(/../g).map((part) => Number.parseInt(part, 16)));
}

async function sha256Bytes(bytes) {
  const digest = await globalThis.crypto.subtle.digest('SHA-256', bytes);
  return new Uint8Array(digest);
}

function concatBytes(parts) {
  const total = parts.reduce((sum, part) => sum + part.length, 0);
  const out = new Uint8Array(total);
  let offset = 0;
  for (const part of parts) {
    out.set(part, offset);
    offset += part.length;
  }
  return out;
}

function canonicalJsonBytes(value) {
  return textEncoder.encode(stableStringify(value));
}

function domainSepBytes(label, version = 1) {
  const cleanLabel = String(label || '');
  if (!cleanLabel || cleanLabel.includes('\0')) {
    throw new Error('domain_label_invalid');
  }
  if (!Number.isSafeInteger(version) || version <= 0) {
    throw new Error('domain_version_invalid');
  }
  return textEncoder.encode(`zenodex:${cleanLabel}:v${version}\0`);
}

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

async function getBls() {
  const mod = await import('@noble/curves/bls12-381');
  return mod.bls12_381;
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

export async function signTauTransactionPayload(payload, { privkey }) {
  const signingDict = {
    sender_pubkey: payload.sender_pubkey,
    sequence_number: asInt(payload.sequence_number, 'sequence_number'),
    expiration_time: asInt(payload.expiration_time, 'expiration_time'),
    operations: payload.operations,
    fee_limit: String(payload.fee_limit),
  };
  const digest = await sha256Bytes(canonicalJsonBytes(signingDict));
  const bls = await getBls();
  const signature = await bls.sign(digest, hexToBytes(privkey, 'privkey'));
  return bytesToHex(signature);
}

export async function buildSignedTauTransaction({
  privkey,
  sequenceNumber,
  sequence_number,
  expirationTime,
  expiration_time,
  operations,
  feeLimit = '0',
  fee_limit,
}) {
  const bls = await getBls();
  const payload = {
    sender_pubkey: bytesToHex(bls.getPublicKey(hexToBytes(privkey, 'privkey'))),
    sequence_number: asInt(sequence_number ?? sequenceNumber, 'sequence_number'),
    expiration_time: asInt(expiration_time ?? expirationTime, 'expiration_time'),
    operations: encodeTauOperationsForWire(operations || {}),
    fee_limit: String(fee_limit ?? feeLimit),
  };
  payload.signature = await signTauTransactionPayload(payload, { privkey });
  return payload;
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

export async function signPerpOpForEngine(op, {
  privkey,
  chainId,
  chain_id,
  signerPubkey,
  signer_pubkey,
  nonce,
}) {
  const chain = String(chain_id ?? chainId ?? '').trim();
  if (!chain) {
    throw new Error('chain_id_required');
  }
  const signer = String(signer_pubkey ?? signerPubkey ?? '').trim();
  const signingDict = buildPerpOpAuthSigningDictV1(op, { signerPubkey: signer, nonce });
  const message = concatBytes([
    domainSepBytes(`perp_op_sig:${chain}`, 1),
    canonicalJsonBytes(signingDict),
  ]);
  const digest = await sha256Bytes(message);
  const bls = await getBls();
  const signature = await bls.sign(digest, hexToBytes(privkey, 'privkey'));
  return `0x${bytesToHex(signature)}`;
}

export async function generateLocalTauWallet({ chainId = 'zeno-ledger-localtest-v0' } = {}) {
  const bls = await getBls();
  const privateKey = bls.utils.randomPrivateKey();
  const publicKey = bls.getPublicKey(privateKey);
  return {
    address: `0x${bytesToHex(publicKey)}`,
    privkey: `0x${bytesToHex(privateKey)}`,
    chainId,
    localTestnetGenerated: true,
    balance: {
      ZDEX: 0,
      zUSD: 0,
      TASSET0: 0,
      TASSET1: 0,
      TZENO: 0,
    },
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

export async function signDexIntentForEngine(intent, { privkey, chainId }) {
  const chain = String(chainId || '').trim();
  if (!chain) {
    throw new Error('chain_id_required');
  }
  const signingPayload = textEncoder.encode(stableStringify(buildDexIntentSigningDictV1(intent)));
  const prefix = textEncoder.encode(`zenodex:dex_intent_sig:${chain}:v1\0`);
  const digest = await sha256Bytes(concatBytes([prefix, signingPayload]));
  const bls = await getBls();
  const signature = await bls.sign(digest, hexToBytes(privkey, 'privkey'));
  return `0x${bytesToHex(signature)}`;
}

async function signDexIntentWithAvailableSigner(intent, { privkey, chainId, signDexIntent }) {
  if (typeof signDexIntent === 'function') {
    return signDexIntent(intent, { chainId });
  }
  if (!privkey) {
    throw new Error('dex_intent_signer_unavailable');
  }
  return signDexIntentForEngine(intent, { privkey, chainId });
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
  privkey,
  signDexIntent,
  chainId = 'zeno-ledger-localtest-v0',
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
    signature: await signDexIntentWithAvailableSigner(operation, { privkey, chainId, signDexIntent }),
  };
}

export async function buildAndSignSwapIntent({
  pool,
  payload,
  privkey,
  signDexIntent,
  chainId = 'zeno-ledger-localtest-v0',
}) {
  if (!pool || typeof pool !== 'object' || Array.isArray(pool)) {
    throw new Error('pool_must_be_object');
  }
  const sender = String(payload.senderPubkey || payload.sender_pubkey || '').trim();
  const recipient = String(payload.recipient || sender).trim();
  const poolId = String(payload.poolId || payload.pool_id || pool.poolId || pool.pool_id || '').trim();
  const deadline = asInt(payload.deadline ?? 1_999_999_999, 'deadline');
  const nonce = asInt(payload.nonce, 'nonce');
  const amountIn = asInt(payload.amountIn ?? payload.amount_in, 'amount_in');
  const minAmountOut = asInt(payload.minAmountOut ?? payload.min_amount_out ?? 1, 'min_amount_out');
  const rawAssetIn = payload.assetIn ?? payload.asset_in;
  const rawAssetOut = payload.assetOut ?? payload.asset_out;
  const assetIn = canonicalAssetId(rawAssetIn, 'asset_in');
  const assetOut = canonicalAssetId(rawAssetOut, 'asset_out');
  if (assetIn === assetOut) {
    throw new Error('swap_assets_must_differ');
  }
  const intentPayload = {
    sender_pubkey: sender,
    recipient,
    pool_id: poolId,
    asset_in: assetIn,
    asset_out: assetOut,
    amount_in: amountIn,
    min_amount_out: minAmountOut,
    nonce,
  };
  const operation = {
    module: 'TauSwap',
    version: '0.1',
    kind: 'SWAP_EXACT_IN',
    intent_id: await hashV0('ui_swap_intent_v0', intentPayload),
    sender_pubkey: sender,
    deadline,
    nonce,
    pool_id: poolId,
    asset_in: assetIn,
    asset_out: assetOut,
    amount_in: amountIn,
    min_amount_out: minAmountOut,
    recipient,
  };
  return {
    intent: operation,
    signature: await signDexIntentWithAvailableSigner(operation, { privkey, chainId, signDexIntent }),
  };
}

/**
 * Compute a route intent_id reproducing the Python agent signer
 * (src/agents/intent_signer.py::_generate_intent_id) BYTE-FOR-BYTE:
 *
 *   sha256( sender || str(deadline) || kind || canonical_json(fields) [|| salt] )
 *
 * NOTE: route intents use the raw-concat `_generate_intent_id` scheme (no domain
 * separation), NOT the `hashV0` scheme the swap/create-pool UI builders use —
 * because the route reference builder is the Python agent signer, which is what
 * the cross-language parity test pins. `canonical_json(fields)` is byte-identical
 * to `stableStringify(fields)` (verified in the parity test).
 */
async function routeIntentIdV0({ sender, deadline, kind, fields, salt }) {
  const parts = [
    textEncoder.encode(String(sender)),
    textEncoder.encode(String(asInt(deadline, 'deadline'))),
    textEncoder.encode(String(kind)),
    canonicalJsonBytes(fields),
  ];
  if (salt !== undefined && salt !== null && salt !== '') {
    parts.push(textEncoder.encode(String(salt)));
  }
  const digest = await sha256Bytes(concatBytes(parts));
  return `0x${bytesToHex(digest)}`;
}

function ceilDiv(a, b) {
  if (b <= 0n) {
    throw new Error('division_by_zero');
  }
  return (a + b - 1n) / b;
}

/**
 * Lightly read a verified route quote receipt body into the fields a route
 * intent binds. This is NOT the full receipt verifier (that stays server-side,
 * `verify_route_quote_receipt`); the UI only needs the endpoints, totals,
 * receipt hash and leg count to build + sign the intent, and the backend
 * re-verifies the receipt before settlement.
 *
 * v1 scope (mirrors resolve_route_binding_from_receipt): single-hop legs whose
 * endpoints span the receipt's (asset_in, asset_out).
 */
function readRouteReceipt(receipt) {
  if (!receipt || typeof receipt !== 'object' || Array.isArray(receipt)) {
    throw new Error('route_receipt_must_be_object');
  }
  const receiptHash = String(receipt.receipt_hash || '').trim();
  if (!/^0x[0-9a-fA-F]{64}$/.test(receiptHash)) {
    throw new Error('route_receipt_hash_invalid');
  }
  const body = receipt.body;
  if (!body || typeof body !== 'object' || Array.isArray(body)) {
    throw new Error('route_receipt_missing_body');
  }
  const kind = String(body.kind || '').trim().toLowerCase();
  if (kind !== 'exact_in' && kind !== 'exact_out') {
    throw new Error('route_receipt_bad_kind');
  }
  const assetIn = String(body.asset_in || '').trim();
  const assetOut = String(body.asset_out || '').trim();
  if (!assetIn || !assetOut || assetIn === assetOut) {
    throw new Error('route_receipt_bad_assets');
  }
  const totalAmountIn = asInt(body.amount_in, 'route_total_amount_in');
  const totalAmountOut = asInt(body.amount_out, 'route_total_amount_out');
  if (totalAmountIn <= 0 || totalAmountOut <= 0) {
    throw new Error('route_receipt_bad_totals');
  }
  const legs = body.legs;
  if (!Array.isArray(legs) || legs.length === 0) {
    throw new Error('route_receipt_bad_legs');
  }
  for (const leg of legs) {
    const hops = leg && typeof leg === 'object' ? leg.hops : undefined;
    if (!Array.isArray(hops) || hops.length !== 1) {
      throw new Error('route_multi_hop_leg_unsupported');
    }
  }
  return { receiptHash, kind, assetIn, assetOut, totalAmountIn, totalAmountOut, legCount: legs.length };
}

/**
 * Build and sign ONE atomic route intent from a verified route quote receipt,
 * reproducing src/agents/intent_signer.py::create_route_intent_from_quote_receipt.
 *
 * The whole route (all legs) is bound by a single signature; the engine settles
 * it atomically. Slippage derives the totals exactly as the Python signer does:
 *   exact_in:  total_min_amount_out = floor(total_out * (10000 - s) / 10000)
 *   exact_out: total_max_amount_in  = ceil(total_in  * (10000 + s) / 10000)
 */
export async function buildAndSignRouteIntent({
  receipt,
  payload,
  privkey,
  signDexIntent,
  chainId = 'zeno-ledger-localtest-v0',
}) {
  const parsed = readRouteReceipt(receipt);
  const sender = String(payload.senderPubkey || payload.sender_pubkey || '').trim();
  if (!sender) {
    throw new Error('sender_pubkey_required');
  }
  const recipient = String(payload.recipient || sender).trim();
  const deadline = asInt(payload.deadline ?? 1_999_999_999, 'deadline');
  const nonce = asInt(payload.nonce, 'nonce');
  const slippageBps = asInt(payload.slippageBps ?? payload.slippage_bps ?? 50, 'slippage_bps');
  if (slippageBps > 10_000) {
    throw new Error('slippage_bps_must_be_at_most_10000');
  }
  const salt = payload.salt ?? null;

  const legIndices = Array.from({ length: parsed.legCount }, (_unused, i) => i);
  let kind;
  let totalFields;
  if (parsed.kind === 'exact_in') {
    kind = 'ROUTE_EXACT_IN';
    const totalMinOut = divFloor(
      BigInt(parsed.totalAmountOut) * BigInt(10_000 - slippageBps),
      10_000n,
    );
    totalFields = {
      total_amount_in: parsed.totalAmountIn,
      total_min_amount_out: toSafeNumber(totalMinOut, 'total_min_amount_out'),
    };
  } else {
    kind = 'ROUTE_EXACT_OUT';
    const totalMaxIn = ceilDiv(
      BigInt(parsed.totalAmountIn) * BigInt(10_000 + slippageBps),
      10_000n,
    );
    totalFields = {
      total_amount_out: parsed.totalAmountOut,
      total_max_amount_in: toSafeNumber(totalMaxIn, 'total_max_amount_in'),
    };
  }

  // Field SET matches create_route_intent_from_quote_receipt exactly; canonical
  // JSON sorts keys so insertion order is irrelevant to the intent_id.
  const fields = {
    quote_receipt_hash: parsed.receiptHash,
    asset_in: parsed.assetIn,
    asset_out: parsed.assetOut,
    leg_indices: legIndices,
    recipient,
    ...totalFields,
    nonce,
  };

  const intentId = await routeIntentIdV0({ sender, deadline, kind, fields, salt });

  const operation = {
    module: 'TauSwap',
    version: '0.1',
    kind,
    intent_id: intentId,
    sender_pubkey: sender,
    deadline,
    quote_receipt_hash: parsed.receiptHash,
    asset_in: parsed.assetIn,
    asset_out: parsed.assetOut,
    leg_indices: legIndices,
    recipient,
    ...totalFields,
    nonce,
  };
  if (salt !== undefined && salt !== null && salt !== '') {
    operation.salt = salt;
  }

  return {
    intent: operation,
    signature: await signDexIntentWithAvailableSigner(operation, { privkey, chainId, signDexIntent }),
  };
}

export async function buildAndSignCreatePoolIntent({
  payload,
  privkey,
  signDexIntent,
  chainId = 'zeno-ledger-localtest-v0',
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
    signature: await signDexIntentWithAvailableSigner(operation, { privkey, chainId, signDexIntent }),
  };
}
