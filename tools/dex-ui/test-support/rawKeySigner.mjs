/** Test-only raw-key signer support. Never import this module from production UI code. */
import { stableStringify } from '../src/sdk/zenoProofClient.js';
import {
  buildDexIntentSigningDictV1,
  buildPerpOpAuthSigningDictV1,
  encodeTauOperationsForWire,
} from '../src/sdk/dexIntentSigner.js';

const textEncoder = new TextEncoder();

function bytesToHex(bytes) {
  return Array.from(bytes, (byte) => byte.toString(16).padStart(2, '0')).join('');
}

function hexToBytes(value, name = 'hex') {
  const text = String(value || '').trim();
  const body = text.startsWith('0x') ? text.slice(2) : text;
  if (!/^[0-9a-fA-F]+$/.test(body) || body.length % 2 !== 0) {
    throw new Error(`${name} must be even-length hex`);
  }
  return Uint8Array.from(body.match(/../g).map((part) => Number.parseInt(part, 16)));
}

function asInt(value, name) {
  const number = Number(value);
  if (!Number.isSafeInteger(number) || number < 0) {
    throw new Error(`${name}_must_be_safe_nonnegative_int`);
  }
  return number;
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

function domainSepBytes(label, version = 1) {
  return textEncoder.encode(`zenodex:${label}:v${version}\0`);
}

async function getBls() {
  const module = await import('@noble/curves/bls12-381');
  return module.bls12_381;
}

export async function signTauTransactionPayload(payload, { privkey }) {
  const signingDict = {
    sender_pubkey: payload.sender_pubkey,
    sequence_number: asInt(payload.sequence_number, 'sequence_number'),
    expiration_time: asInt(payload.expiration_time, 'expiration_time'),
    operations: payload.operations,
    fee_limit: String(payload.fee_limit),
  };
  const digest = await sha256Bytes(textEncoder.encode(stableStringify(signingDict)));
  const bls = await getBls();
  return bytesToHex(await bls.sign(digest, hexToBytes(privkey, 'privkey')));
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

export async function signPerpOpForEngine(op, {
  privkey,
  chainId,
  chain_id,
  signerPubkey,
  signer_pubkey,
  nonce,
}) {
  const chain = String(chain_id ?? chainId ?? '').trim();
  if (!chain) throw new Error('chain_id_required');
  const signer = String(signer_pubkey ?? signerPubkey ?? '').trim();
  const signingDict = buildPerpOpAuthSigningDictV1(op, { signerPubkey: signer, nonce });
  const message = concatBytes([
    domainSepBytes(`perp_op_sig:${chain}`, 1),
    textEncoder.encode(stableStringify(signingDict)),
  ]);
  const bls = await getBls();
  const signature = await bls.sign(await sha256Bytes(message), hexToBytes(privkey, 'privkey'));
  return `0x${bytesToHex(signature)}`;
}

export async function signDexIntentForEngine(intent, { privkey, chainId }) {
  const chain = String(chainId || '').trim();
  if (!chain) throw new Error('chain_id_required');
  const signingPayload = textEncoder.encode(stableStringify(buildDexIntentSigningDictV1(intent)));
  const prefix = textEncoder.encode(`zenodex:dex_intent_sig:${chain}:v1\0`);
  const bls = await getBls();
  const signature = await bls.sign(
    await sha256Bytes(concatBytes([prefix, signingPayload])),
    hexToBytes(privkey, 'privkey'),
  );
  return `0x${bytesToHex(signature)}`;
}
