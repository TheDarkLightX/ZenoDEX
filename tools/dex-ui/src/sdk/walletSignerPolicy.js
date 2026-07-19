import { encodeTauOperationsForWire } from './dexIntentSigner.js';
import { hashV0, stableStringify } from './zenoProofClient.js';

const EXTERNAL_SIGNER_GLOBALS = ['zenodexSecureSigner', 'zenodexSigner'];
const EXTERNAL_SIGNER_PUBLIC_RECEIPT_SCHEMA_V1 = 'zenodex/external_signer/public_receipt/v1';
const RUNTIME_DEFAULT_EXTERNAL_SIGNER_SCHEMA_V1 = 'zenodex/dex-ui/runtime-default-external-signer/v1';
const EXTERNAL_SIGNER_SECURITY_PROFILE_V1 = 'external-signer-v1';
const SUPPORTED_EXTERNAL_SIGNER_SECURITY_PROFILES = new Set([
  EXTERNAL_SIGNER_SECURITY_PROFILE_V1,
]);
const REMOTE_HTTPS_EXTERNAL_SIGNER_SECURITY_PROFILES = new Set([
  EXTERNAL_SIGNER_SECURITY_PROFILE_V1,
]);

const PUBLIC_RECEIPT_KEYS_V1 = [
  'schema',
  'provider',
  'key_id',
  'public_key',
  'algorithm',
  'chain_id',
  'allowed_chain_ids',
  'issued_at_epoch',
  'approval_mode',
  'signer_user_approval_required',
  'bridge_auth_required',
  'browser_generated',
  'zenodex_custody',
  'receipt_hash',
];

function parseBooleanLike(raw) {
  if (raw === true || raw === 'true' || raw === '1' || raw === 1) {
    return true;
  }
  if (raw === false || raw === 'false' || raw === '0' || raw === 0) {
    return false;
  }
  return undefined;
}

function hasSecretField(value) {
  if (!value || typeof value !== 'object') {
    return false;
  }
  if (Array.isArray(value)) {
    return value.some((item) => hasSecretField(item));
  }
  for (const [key, item] of Object.entries(value)) {
    const normalized = String(key).toLowerCase().replace(/[^a-z0-9]/g, '');
    if (
      normalized === 'privkey'
      || normalized === 'privatekey'
      || normalized === 'privatekeyhex'
      || normalized === 'rawprivatekey'
      || normalized === 'mnemonic'
      || normalized === 'secret'
      || normalized === 'secretkey'
      || normalized === 'seed'
      || normalized === 'seedphrase'
    ) {
      return true;
    }
    if (hasSecretField(item)) {
      return true;
    }
  }
  return false;
}

function canonicalPubkey(value, name = 'address') {
  const text = String(value || '').trim();
  const body = text.startsWith('0x') || text.startsWith('0X') ? text.slice(2) : text;
  if (!/^[0-9a-fA-F]{96}$/.test(body)) {
    throw new Error(`${name}_must_be_canonical_bls_public_key`);
  }
  return `0x${body.toLowerCase()}`;
}

function canonicalRoot(value, name) {
  const text = String(value || '').trim();
  const body = text.startsWith('0x') || text.startsWith('0X') ? text.slice(2) : text;
  if (!/^[0-9a-fA-F]{64}$/.test(body)) {
    throw new Error(`${name}_must_be_canonical_root`);
  }
  return `0x${body.toLowerCase()}`;
}

function requireRecord(value, name) {
  if (!value || typeof value !== 'object' || Array.isArray(value)) {
    throw new Error(`${name}_must_be_json_object`);
  }
  return value;
}

function exactKeys(value, keys, name) {
  const actual = Object.keys(value).sort();
  const expected = [...keys].sort();
  if (actual.length !== expected.length || actual.some((key, index) => key !== expected[index])) {
    throw new Error(`${name}_keys_mismatch`);
  }
}

function bodyWithoutHash(value, hashKey) {
  const body = {};
  for (const [key, item] of Object.entries(value)) {
    if (key !== hashKey) {
      body[key] = item;
    }
  }
  return body;
}

function requireFalse(value, name) {
  if (value !== false) {
    throw new Error(`${name}_must_be_false`);
  }
}

function requireNonnegativeSafeInt(value, name) {
  if (!Number.isSafeInteger(value) || value < 0) {
    throw new Error(`${name}_must_be_nonnegative_safe_integer`);
  }
}

async function validateExternalSignerPublicReceipt(receipt, {
  address,
  chainId,
  provider,
  requireUserApproval = false,
}) {
  requireRecord(receipt, 'signer_bridge_public_receipt');
  exactKeys(receipt, PUBLIC_RECEIPT_KEYS_V1, 'signer_bridge_public_receipt');
  if (hasSecretField(receipt)) {
    throw new Error('signer_bridge_public_receipt_contains_private_key_material');
  }
  if (receipt.schema !== EXTERNAL_SIGNER_PUBLIC_RECEIPT_SCHEMA_V1) {
    throw new Error('signer_bridge_public_receipt_schema_mismatch');
  }
  if (!receipt.provider || String(receipt.provider) !== provider) {
    throw new Error('signer_bridge_public_receipt_provider_mismatch');
  }
  if (!String(receipt.key_id || '').trim()) {
    throw new Error('signer_bridge_public_receipt_key_id_required');
  }
  if (receipt.algorithm !== 'bls12-381-g2-basic-release-v0') {
    throw new Error('signer_bridge_public_receipt_algorithm_mismatch');
  }
  if (canonicalPubkey(receipt.public_key, 'signer_bridge_public_receipt_public_key') !== address) {
    throw new Error('signer_bridge_public_receipt_public_key_mismatch');
  }
  if (String(receipt.chain_id) !== chainId) {
    throw new Error('signer_bridge_public_receipt_chain_id_mismatch');
  }
  if (!Array.isArray(receipt.allowed_chain_ids)
    || receipt.allowed_chain_ids.some((allowed) => typeof allowed !== 'string')
    || !receipt.allowed_chain_ids.includes(chainId)) {
    throw new Error('signer_bridge_public_receipt_chain_not_allowed');
  }
  requireNonnegativeSafeInt(receipt.issued_at_epoch, 'signer_bridge_public_receipt_issued_at_epoch');
  if (!['offline-cli', 'prompt', 'unattended'].includes(receipt.approval_mode)) {
    throw new Error('signer_bridge_public_receipt_approval_mode_mismatch');
  }
  if (typeof receipt.signer_user_approval_required !== 'boolean') {
    throw new Error('signer_bridge_public_receipt_user_approval_required_mismatch');
  }
  if (typeof receipt.bridge_auth_required !== 'boolean') {
    throw new Error('signer_bridge_public_receipt_bridge_auth_required_mismatch');
  }
  if (receipt.signer_user_approval_required && receipt.approval_mode !== 'prompt') {
    throw new Error('signer_bridge_public_receipt_approval_posture_mismatch');
  }
  if (requireUserApproval) {
    if (receipt.approval_mode !== 'prompt' || receipt.signer_user_approval_required !== true) {
      throw new Error('signer_bridge_public_receipt_user_approval_required');
    }
    if (receipt.bridge_auth_required !== true) {
      throw new Error('signer_bridge_public_receipt_bridge_auth_required');
    }
  }
  requireFalse(receipt.browser_generated, 'signer_bridge_public_receipt_browser_generated');
  requireFalse(receipt.zenodex_custody, 'signer_bridge_public_receipt_zenodex_custody');
  const expectedReceiptHash = await hashV0(
    'external_signer_public_receipt_v1',
    bodyWithoutHash(receipt, 'receipt_hash'),
  );
  if (canonicalRoot(receipt.receipt_hash, 'signer_bridge_public_receipt_hash') !== expectedReceiptHash) {
    throw new Error('signer_bridge_public_receipt_hash_mismatch');
  }
  return receipt;
}

function findExternalSigner(globalObject) {
  if (!globalObject || typeof globalObject !== 'object') {
    return null;
  }
  for (const name of EXTERNAL_SIGNER_GLOBALS) {
    const candidate = globalObject[name];
    if (candidate && typeof candidate.connect === 'function') {
      return { name, signer: candidate };
    }
  }
  return null;
}

function runtimeDefaultExternalSignerAllowed({ runtimeConfig = {} } = {}) {
  return parseBooleanLike(runtimeConfig?.allowDefaultExternalSigner) === true;
}

function runtimeDefaultExternalSignerConfig(runtimeConfig = {}) {
  return runtimeConfig?.defaultExternalSigner
    || runtimeConfig?.defaultExternalWallet
    || runtimeConfig?.externalDefaultSigner
    || null;
}

function signerSecurityProfile(config) {
  const profile = String(
    config.signerSecurityProfile
    || config.signer_security_profile
    || config.securityProfile
    || config.providerProfile
    || '',
  ).trim();
  if (!profile) {
    throw new Error('runtime_default_external_signer_security_profile_required');
  }
  if (!SUPPORTED_EXTERNAL_SIGNER_SECURITY_PROFILES.has(profile)) {
    throw new Error('runtime_default_external_signer_security_profile_unsupported');
  }
  return profile;
}

function remoteHttpsAllowedForProfile(profile) {
  return REMOTE_HTTPS_EXTERNAL_SIGNER_SECURITY_PROFILES.has(profile);
}

function normalizeSignerEndpoint(raw, { allowRemoteHttps = false, name = 'external_signer_endpoint' } = {}) {
  if (raw == null || raw === '') {
    return '';
  }
  const text = String(raw).trim();
  if (!text) {
    return '';
  }
  if (text.startsWith('/')) {
    if (text.startsWith('//')) {
      throw new Error(`${name}_must_be_same_origin_or_explicit_https`);
    }
    return text;
  }
  let url;
  try {
    url = new URL(text);
  } catch {
    throw new Error(`${name}_must_be_valid_url`);
  }
  if (url.protocol === 'https:' && allowRemoteHttps) {
    return url.toString();
  }
  throw new Error(`${name}_must_be_same_origin_or_explicit_https`);
}

async function postSignerJson(endpoint, body, { globalObject = globalThis, operation, headers = {} }) {
  const fetchFn = globalObject?.fetch || globalThis.fetch;
  if (typeof fetchFn !== 'function') {
    throw new Error(`${operation}_fetch_unavailable`);
  }
  const response = await fetchFn(endpoint, {
    method: 'POST',
    headers: { 'content-type': 'application/json', ...headers },
    credentials: 'omit',
    body: JSON.stringify(body),
  });
  const text = typeof response?.text === 'function' ? await response.text() : '';
  let data = {};
  if (text) {
    try {
      data = JSON.parse(text);
    } catch {
      throw new Error(`${operation}_response_must_be_json`);
    }
  }
  if (!response?.ok) {
    throw new Error(data?.error || `${operation}_failed`);
  }
  if (!data || typeof data !== 'object' || Array.isArray(data)) {
    throw new Error(`${operation}_response_must_be_json_object`);
  }
  if (hasSecretField(data)) {
    throw new Error(`${operation}_response_contains_private_key_material`);
  }
  return data;
}

function tauTransactionPayloadFromRequest(request) {
  const value = requireRecord(request, 'tau_transaction_sign_request');
  return {
    sender_pubkey: String(value.sender_pubkey ?? value.senderPubkey ?? ''),
    sequence_number: value.sequence_number ?? value.sequenceNumber,
    expiration_time: value.expiration_time ?? value.expirationTime,
    operations: encodeTauOperationsForWire(value.operations || {}),
    fee_limit: String(value.fee_limit ?? value.feeLimit ?? '0'),
  };
}

function normalizedTauPubkey(value, name) {
  return canonicalPubkey(value, name).slice(2);
}

function safeNonnegativeIntLike(value, name) {
  const n = Number(value);
  if (!Number.isSafeInteger(n) || n < 0) {
    throw new Error(`${name}_must_be_nonnegative_safe_integer`);
  }
  return n;
}

function normalizedTauPayload(value, name) {
  const payload = requireRecord(value, name);
  return {
    sender_pubkey: normalizedTauPubkey(payload.sender_pubkey, `${name}_sender_pubkey`),
    sequence_number: safeNonnegativeIntLike(payload.sequence_number, `${name}_sequence_number`),
    expiration_time: safeNonnegativeIntLike(payload.expiration_time, `${name}_expiration_time`),
    operations: encodeTauOperationsForWire(payload.operations || {}),
    fee_limit: String(payload.fee_limit ?? '0'),
  };
}

function signedTauTransactionFromResponse(data, payload) {
  const signed = data.signed_tau_tx_payload || data.signedTauTxPayload || data.payload;
  let signature = '';
  if (signed && typeof signed === 'object' && !Array.isArray(signed)) {
    if (hasSecretField(signed)) {
      throw new Error('runtime_default_external_signer_signed_payload_contains_private_key_material');
    }
    const allowedKeys = new Set(['sender_pubkey', 'sequence_number', 'expiration_time', 'operations', 'fee_limit', 'signature']);
    for (const key of Object.keys(signed)) {
      if (!allowedKeys.has(key)) {
        throw new Error('runtime_default_external_signer_signed_payload_keys_mismatch');
      }
    }
    signature = String(signed.signature || '');
    const expected = normalizedTauPayload(payload, 'requested_tau_payload');
    const actual = normalizedTauPayload(signed, 'signed_tau_payload');
    if (stableStringify(actual) !== stableStringify(expected)) {
      throw new Error('runtime_default_external_signer_signed_payload_request_mismatch');
    }
    if (!signature) {
      throw new Error('runtime_default_external_signer_signed_payload_signature_missing');
    }
    return { ...expected, signature };
  }
  if (typeof data.signature === 'string' && data.signature) {
    signature = data.signature;
    return { ...normalizedTauPayload(payload, 'requested_tau_payload'), signature };
  }
  throw new Error('runtime_default_external_signer_signed_payload_missing');
}

function dexIntentSignatureFromResponse(data) {
  if (typeof data.signature === 'string' && data.signature) {
    return data.signature;
  }
  const receipt = data.signature_receipt || data.signatureReceipt || data.receipt;
  if (receipt && typeof receipt === 'object' && typeof receipt.signature === 'string' && receipt.signature) {
    return receipt.signature;
  }
  throw new Error('runtime_default_external_signer_signature_missing');
}

function buildRuntimeDefaultExternalSigner(raw, { chainId, globalObject, runtimeConfig }) {
  const config = requireRecord(raw, 'runtime_default_external_signer');
  if (hasSecretField(config)) {
    throw new Error('runtime_default_external_signer_contains_private_key_material');
  }
  if (config.schema !== RUNTIME_DEFAULT_EXTERNAL_SIGNER_SCHEMA_V1) {
    throw new Error('runtime_default_external_signer_schema_mismatch');
  }
  if (!runtimeDefaultExternalSignerAllowed({ runtimeConfig, chainId })) {
    throw new Error('runtime_default_external_signer_not_allowed');
  }
  const securityProfile = signerSecurityProfile(config);
  const requestedRemoteHttps = parseBooleanLike(config.allowRemoteHttpsEndpoint) === true
    || parseBooleanLike(runtimeConfig?.allowRemoteExternalSignerEndpoint) === true;
  const allowRemoteHttps = requestedRemoteHttps && remoteHttpsAllowedForProfile(securityProfile);
  if (requestedRemoteHttps && !allowRemoteHttps) {
    throw new Error('runtime_default_external_signer_remote_https_profile_not_allowed');
  }
  const connectUrl = normalizeSignerEndpoint(config.connectUrl || config.connect_url, {
    allowRemoteHttps,
    name: 'runtime_default_external_signer_connect_url',
  });
  const signTauUrl = normalizeSignerEndpoint(
    config.signTauTransactionPayloadUrl || config.signTauTransactionPayloadURL || config.signTauTransactionUrl,
    { allowRemoteHttps, name: 'runtime_default_external_signer_sign_tau_url' },
  );
  const signDexUrl = normalizeSignerEndpoint(
    config.signDexIntentForEngineUrl || config.signDexIntentUrl || config.signIntentUrl,
    { allowRemoteHttps, name: 'runtime_default_external_signer_sign_dex_url' },
  );
  const providerName = String(config.signerProvider || config.signer_provider || '').trim();
  if (!providerName) {
    throw new Error('runtime_default_external_signer_provider_required');
  }
  const baseWallet = {
    address: config.address ?? config.publicKey ?? config.public_key,
    chainId: String(config.chainId || config.chain_id || chainId),
    signerProvider: providerName,
    publicReceipt: config.publicReceipt || config.public_receipt,
    balance: config.balance,
    signerSecurityProfile: securityProfile,
  };
  let signerPairingToken = '';
  const signerAuthHeaders = () => (signerPairingToken ? { 'x-zenodex-signer-token': signerPairingToken } : {});
  const signer = {
    async connect() {
      if (connectUrl) {
        const data = await postSignerJson(connectUrl, { chainId }, {
          globalObject,
          operation: 'runtime_default_external_signer_connect',
        });
        const wallet = data.wallet || data;
        signerPairingToken = String(data.signerPairingToken || wallet.signerPairingToken || '');
        delete wallet.signerPairingToken;
        return {
          ...wallet,
          signerSecurityProfile: wallet.signerSecurityProfile || wallet.signer_security_profile || securityProfile,
        };
      }
      return baseWallet;
    },
  };
  if (signTauUrl) {
    signer.signTauTransactionPayload = async (request) => {
      const payload = tauTransactionPayloadFromRequest(request);
      const data = await postSignerJson(signTauUrl, {
        chainId: request?.chainId || request?.chain_id || chainId,
        payload,
      }, {
        globalObject,
        operation: 'runtime_default_external_signer_sign_tau',
        headers: signerAuthHeaders(),
      });
      return signedTauTransactionFromResponse(data, payload);
    };
  }
  if (signDexUrl) {
    signer.signDexIntentForEngine = async (intent, options = {}) => {
      const data = await postSignerJson(signDexUrl, {
        chainId: options?.chainId || options?.chain_id || chainId,
        intent,
      }, {
        globalObject,
        operation: 'runtime_default_external_signer_sign_dex',
        headers: signerAuthHeaders(),
      });
      return dexIntentSignatureFromResponse(data);
    };
    signer.signDexIntent = signer.signDexIntentForEngine;
  }
  return { name: providerName, signer };
}

const SIGNER_CALLBACK_KEYS = [
  'signDexIntent',
  'signDexIntentForEngine',
  'signTauTransactionPayload',
  'signTauTransaction',
  'signTauPayload',
  'signPerpOperation',
  'signPerpOp',
];

function strictRuntimeRequiresSignerApproval(runtimeConfig = {}) {
  const deployment = String(runtimeConfig?.deployment || '').toLowerCase();
  if (deployment === 'production' || deployment === 'public-testnet') {
    return true;
  }
  return parseBooleanLike(runtimeConfig?.signerUserApprovalRequired) === true;
}

async function normalizeExternalSignerWallet(raw, { chainId, providerName, signer, runtimeConfig = {} }) {
  if (!raw || typeof raw !== 'object' || Array.isArray(raw)) {
    throw new Error('signer_bridge_result_invalid');
  }
  if (hasSecretField(raw)) {
    throw new Error('signer_bridge_result_contains_private_key_material');
  }
  const wallet = {
    ...raw,
    address: canonicalPubkey(raw.address ?? raw.publicKey ?? raw.public_key, 'signer_bridge_address'),
    chainId: String(raw.chainId || raw.chain_id || chainId),
    signerProvider: String(raw.signerProvider || raw.signer_provider || providerName).trim(),
  };
  if (wallet.chainId !== chainId) {
    throw new Error('signer_bridge_chain_id_mismatch');
  }
  if (!wallet.signerProvider) {
    throw new Error('signer_bridge_provider_required');
  }
  const publicReceipt = raw.publicReceipt || raw.public_receipt;
  if (!publicReceipt) {
    throw new Error('signer_bridge_public_receipt_required');
  }
  wallet.publicReceipt = await validateExternalSignerPublicReceipt(publicReceipt, {
    address: wallet.address,
    chainId: wallet.chainId,
    provider: wallet.signerProvider,
    requireUserApproval: strictRuntimeRequiresSignerApproval(runtimeConfig),
  });
  for (const key of SIGNER_CALLBACK_KEYS) {
    if (typeof wallet[key] !== 'function' && typeof signer?.[key] === 'function') {
      wallet[key] = signer[key].bind(signer);
    }
  }
  return wallet;
}

export async function connectPreferredWallet({
  chainId = '',
  globalObject = globalThis,
  runtimeConfig = {},
} = {}) {
  const normalizedChainId = String(chainId || '').trim();
  if (!normalizedChainId) {
    throw new Error('chain_id_required');
  }
  const external = findExternalSigner(globalObject);
  if (external) {
    const raw = await external.signer.connect({ chainId: normalizedChainId });
    return normalizeExternalSignerWallet(raw, {
      chainId: normalizedChainId,
      providerName: external.name,
      signer: external.signer,
      runtimeConfig,
    });
  }

  const runtimeDefault = runtimeDefaultExternalSignerConfig(runtimeConfig);
  if (runtimeDefault) {
    const externalDefault = buildRuntimeDefaultExternalSigner(runtimeDefault, {
      chainId: normalizedChainId,
      globalObject,
      runtimeConfig,
    });
    const raw = await externalDefault.signer.connect({ chainId: normalizedChainId });
    return normalizeExternalSignerWallet(raw, {
      chainId: normalizedChainId,
      providerName: externalDefault.name,
      signer: externalDefault.signer,
      runtimeConfig,
    });
  }

  throw new Error('external_signer_unavailable');
}
