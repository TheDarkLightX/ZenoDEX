import { generateLocalTauWallet } from './dexIntentSigner.js';

const SECURE_SIGNER_GLOBALS = ['zenodexSecureSigner', 'zenodexSigner'];

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

export function browserKeyGenerationAllowed({
  locationSearch = '',
  runtimeConfig = {},
  env = {},
} = {}) {
  const params = new URLSearchParams(String(locationSearch || ''));
  const queryValue = params.has('zenodexAllowBrowserKeygen')
    ? parseBooleanLike(params.get('zenodexAllowBrowserKeygen'))
    : undefined;
  if (queryValue !== undefined) {
    return queryValue;
  }

  const runtimeValue = parseBooleanLike(runtimeConfig?.allowBrowserKeyGeneration);
  if (runtimeValue !== undefined) {
    return runtimeValue;
  }

  const envValue = parseBooleanLike(env?.VITE_ALLOW_BROWSER_KEYGEN);
  if (envValue !== undefined) {
    return envValue;
  }

  return false;
}

function findSecureSigner(globalObject) {
  if (!globalObject || typeof globalObject !== 'object') {
    return null;
  }
  for (const name of SECURE_SIGNER_GLOBALS) {
    const candidate = globalObject[name];
    if (candidate && typeof candidate.connect === 'function') {
      return { name, signer: candidate };
    }
  }
  return null;
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

function normalizeSecureSignerWallet(raw, { chainId, providerName, signer }) {
  if (!raw || typeof raw !== 'object' || Array.isArray(raw)) {
    throw new Error('secure_signer_result_invalid');
  }
  if (hasSecretField(raw)) {
    throw new Error('secure_signer_result_contains_private_key_material');
  }
  const wallet = {
    ...raw,
    address: canonicalPubkey(raw.address ?? raw.publicKey ?? raw.public_key, 'secure_signer_address'),
    chainId: String(raw.chainId || raw.chain_id || chainId),
    signerProvider: String(raw.signerProvider || raw.signer_provider || providerName),
    localTestnetGenerated: false,
  };
  for (const key of SIGNER_CALLBACK_KEYS) {
    if (typeof wallet[key] !== 'function' && typeof signer?.[key] === 'function') {
      wallet[key] = signer[key].bind(signer);
    }
  }
  return wallet;
}

export async function connectPreferredWallet({
  chainId = 'zeno-ledger-localtest-v0',
  globalObject = globalThis,
  allowBrowserFallback = false,
  generateLocalWallet = generateLocalTauWallet,
} = {}) {
  const secure = findSecureSigner(globalObject);
  if (secure) {
    const raw = await secure.signer.connect({ chainId });
    return normalizeSecureSignerWallet(raw, { chainId, providerName: secure.name, signer: secure.signer });
  }

  if (allowBrowserFallback) {
    const wallet = await generateLocalWallet({ chainId });
    return {
      ...wallet,
      signerProvider: 'browser-local-last-resort',
      browserLastResort: true,
      localTestnetGenerated: true,
    };
  }

  throw new Error('secure_signer_unavailable');
}
