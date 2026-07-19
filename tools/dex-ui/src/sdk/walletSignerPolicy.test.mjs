import assert from 'node:assert/strict';
import { test } from 'node:test';
import { connectPreferredWallet } from './walletSignerPolicy.js';
import { hashV0 } from './zenoProofClient.js';

const CHAIN_ID = 'zeno-ledger-production-v1';
const PUBKEY = `0x${'11'.repeat(48)}`;
const PRIVKEY = `0x${'22'.repeat(32)}`;
const PROVIDER = 'independent-hardware-signer';
const RUNTIME_DEFAULT_SCHEMA = 'zenodex/dex-ui/runtime-default-external-signer/v1';
const SECURITY_PROFILE = 'external-signer-v1';

async function makePublicReceipt({
  publicKey = PUBKEY,
  chainId = CHAIN_ID,
  provider = PROVIDER,
  approvalMode = 'prompt',
  userApprovalRequired = true,
  bridgeAuthRequired = true,
} = {}) {
  const body = {
    schema: 'zenodex/external_signer/public_receipt/v1',
    provider,
    key_id: 'signing-key-7',
    public_key: publicKey,
    algorithm: 'bls12-381-g2-basic-release-v0',
    chain_id: chainId,
    allowed_chain_ids: [chainId],
    issued_at_epoch: 7,
    approval_mode: approvalMode,
    signer_user_approval_required: userApprovalRequired,
    bridge_auth_required: bridgeAuthRequired,
    browser_generated: false,
    zenodex_custody: false,
  };
  return {
    ...body,
    receipt_hash: await hashV0('external_signer_public_receipt_v1', body),
  };
}

function runtimeSignerConfig(publicReceipt, overrides = {}) {
  return {
    schema: RUNTIME_DEFAULT_SCHEMA,
    signerSecurityProfile: SECURITY_PROFILE,
    signerProvider: PROVIDER,
    address: PUBKEY,
    chainId: CHAIN_ID,
    publicReceipt,
    ...overrides,
  };
}

test('wallet policy accepts an injected generic signer with a verified public receipt', async () => {
  const signTauTransactionPayload = async () => ({ ok: true });
  const signDexIntentForEngine = async () => '0xsignature';
  const publicReceipt = await makePublicReceipt();
  const wallet = await connectPreferredWallet({
    chainId: CHAIN_ID,
    globalObject: {
      zenodexSigner: {
        signTauTransactionPayload,
        signDexIntentForEngine,
        connect: async ({ chainId }) => ({
          address: PUBKEY,
          chainId,
          signerProvider: PROVIDER,
          publicReceipt,
        }),
      },
    },
  });

  assert.equal(wallet.address, PUBKEY);
  assert.equal(wallet.chainId, CHAIN_ID);
  assert.equal(wallet.signerProvider, PROVIDER);
  assert.deepEqual(wallet.publicReceipt, publicReceipt);
  assert.equal(Object.hasOwn(wallet, 'privkey'), false);
  assert.equal(typeof wallet.signTauTransactionPayload, 'function');
  assert.equal(typeof wallet.signDexIntentForEngine, 'function');
  assert.deepEqual(await wallet.signTauTransactionPayload(), { ok: true });
  assert.equal(await wallet.signDexIntentForEngine(), '0xsignature');
});

test('wallet policy rejects any secret material returned by an external signer', async () => {
  await assert.rejects(
    connectPreferredWallet({
      chainId: CHAIN_ID,
      globalObject: {
        zenodexSecureSigner: {
          connect: async () => ({
            address: PUBKEY,
            signerProvider: PROVIDER,
            publicReceipt: await makePublicReceipt(),
            private_key_hex: PRIVKEY,
          }),
        },
      },
    }),
    /private_key_material/,
  );
});

test('wallet policy requires a receipt and binds it to key, chain, and provider', async () => {
  await assert.rejects(
    connectPreferredWallet({
      chainId: CHAIN_ID,
      globalObject: {
        zenodexSigner: {
          connect: async () => ({ address: PUBKEY, chainId: CHAIN_ID, signerProvider: PROVIDER }),
        },
      },
    }),
    /public_receipt_required/,
  );

  const forged = await makePublicReceipt();
  forged.public_key = `0x${'12'.repeat(48)}`;
  await assert.rejects(
    connectPreferredWallet({
      chainId: CHAIN_ID,
      globalObject: {
        zenodexSigner: {
          connect: async () => ({
            address: PUBKEY,
            chainId: CHAIN_ID,
            signerProvider: PROVIDER,
            publicReceipt: forged,
          }),
        },
      },
    }),
    /public_key_mismatch|receipt_hash_mismatch/,
  );
});

test('wallet policy rejects a wallet for a different requested chain', async () => {
  const otherChain = 'another-production-chain';
  await assert.rejects(
    connectPreferredWallet({
      chainId: CHAIN_ID,
      globalObject: {
        zenodexSigner: {
          connect: async () => ({
            address: PUBKEY,
            chainId: otherChain,
            signerProvider: PROVIDER,
            publicReceipt: await makePublicReceipt({ chainId: otherChain }),
          }),
        },
      },
    }),
    /chain_id_mismatch/,
  );
});

test('strict deployments require prompt approval and authenticated bridge pairing', async () => {
  const unattendedReceipt = await makePublicReceipt({
    approvalMode: 'unattended',
    userApprovalRequired: false,
  });
  await assert.rejects(
    connectPreferredWallet({
      chainId: CHAIN_ID,
      globalObject: {},
      runtimeConfig: {
        deployment: 'production',
        allowDefaultExternalSigner: true,
        defaultExternalSigner: runtimeSignerConfig(unattendedReceipt),
      },
    }),
    /user_approval_required/,
  );

  const unauthenticatedReceipt = await makePublicReceipt({ bridgeAuthRequired: false });
  await assert.rejects(
    connectPreferredWallet({
      chainId: CHAIN_ID,
      globalObject: {},
      runtimeConfig: {
        deployment: 'production',
        allowDefaultExternalSigner: true,
        defaultExternalSigner: runtimeSignerConfig(unauthenticatedReceipt),
      },
    }),
    /bridge_auth_required/,
  );
});

test('wallet policy accepts an explicitly enabled generic runtime signer', async () => {
  const publicReceipt = await makePublicReceipt();
  const wallet = await connectPreferredWallet({
    chainId: CHAIN_ID,
    globalObject: {},
    runtimeConfig: {
      deployment: 'production',
      allowDefaultExternalSigner: true,
      defaultExternalSigner: runtimeSignerConfig(publicReceipt),
    },
  });

  assert.equal(wallet.address, PUBKEY);
  assert.equal(wallet.signerProvider, PROVIDER);
  assert.equal(wallet.signerSecurityProfile, SECURITY_PROFILE);
  assert.equal(Object.hasOwn(wallet, 'privkey'), false);
});

test('wallet policy rejects a runtime signer unless it is explicitly enabled', async () => {
  await assert.rejects(
    connectPreferredWallet({
      chainId: CHAIN_ID,
      globalObject: {},
      runtimeConfig: {
        deployment: 'production',
        defaultExternalSigner: runtimeSignerConfig(await makePublicReceipt()),
      },
    }),
    /runtime_default_external_signer_not_allowed/,
  );
});

test('wallet policy rejects unsupported or implicit runtime security profiles', async () => {
  const publicReceipt = await makePublicReceipt();
  await assert.rejects(
    connectPreferredWallet({
      chainId: CHAIN_ID,
      globalObject: {},
      runtimeConfig: {
        allowDefaultExternalSigner: true,
        defaultExternalSigner: runtimeSignerConfig(publicReceipt, { signerSecurityProfile: undefined }),
      },
    }),
    /security_profile_required/,
  );
  await assert.rejects(
    connectPreferredWallet({
      chainId: CHAIN_ID,
      globalObject: {},
      runtimeConfig: {
        allowDefaultExternalSigner: true,
        defaultExternalSigner: runtimeSignerConfig(publicReceipt, { signerSecurityProfile: 'opaque-custody-v0' }),
      },
    }),
    /security_profile_unsupported/,
  );
});

test('wallet policy signs through same-origin generic endpoints without browser keys', async () => {
  const publicReceipt = await makePublicReceipt();
  const txSignature = '33'.repeat(96);
  const dexSignature = `0x${'44'.repeat(96)}`;
  const seen = [];
  const wallet = await connectPreferredWallet({
    chainId: CHAIN_ID,
    globalObject: {
      fetch: async (url, options) => {
        seen.push({ url, body: JSON.parse(options.body) });
        return {
          ok: true,
          text: async () => JSON.stringify({
            signature: url.includes('tau') ? txSignature : dexSignature,
          }),
        };
      },
    },
    runtimeConfig: {
      deployment: 'production',
      allowDefaultExternalSigner: true,
      defaultExternalSigner: runtimeSignerConfig(publicReceipt, {
        signTauTransactionPayloadUrl: '/api/external-signer/sign-tau',
        signDexIntentForEngineUrl: '/api/external-signer/sign-intent',
      }),
    },
  });

  const signedTauTx = await wallet.signTauTransactionPayload({
    chainId: CHAIN_ID,
    senderPubkey: PUBKEY,
    sequenceNumber: 7,
    expirationTime: 99,
    operations: { 8: { action: 'set-position' } },
    feeLimit: '0',
  });
  const signedDexIntent = await wallet.signDexIntentForEngine(
    { sender_pubkey: PUBKEY },
    { chainId: CHAIN_ID },
  );

  assert.equal(signedTauTx.sender_pubkey, PUBKEY.slice(2));
  assert.equal(signedTauTx.sequence_number, 7);
  assert.equal(signedTauTx.signature, txSignature);
  assert.equal(signedDexIntent, dexSignature);
  assert.deepEqual(seen.map((item) => item.url), [
    '/api/external-signer/sign-tau',
    '/api/external-signer/sign-intent',
  ]);
});

test('wallet policy rejects any mutation of a requested Tau transaction', async () => {
  const wallet = await connectPreferredWallet({
    chainId: CHAIN_ID,
    globalObject: {
      fetch: async () => ({
        ok: true,
        text: async () => JSON.stringify({
          signed_tau_tx_payload: {
            sender_pubkey: PUBKEY.slice(2),
            sequence_number: 8,
            expiration_time: 99,
            operations: { 8: JSON.stringify({ action: 'mutated' }) },
            fee_limit: '0',
            signature: '33'.repeat(96),
          },
        }),
      }),
    },
    runtimeConfig: {
      deployment: 'production',
      allowDefaultExternalSigner: true,
      defaultExternalSigner: runtimeSignerConfig(await makePublicReceipt(), {
        signTauTransactionPayloadUrl: '/api/external-signer/sign-tau',
      }),
    },
  });

  await assert.rejects(
    wallet.signTauTransactionPayload({
      chainId: CHAIN_ID,
      senderPubkey: PUBKEY,
      sequenceNumber: 7,
      expirationTime: 99,
      operations: { 8: { action: 'original' } },
      feeLimit: '0',
    }),
    /signed_payload_request_mismatch/,
  );
});

test('wallet policy keeps pairing tokens out of the wallet and sends them only on signing', async () => {
  const publicReceipt = await makePublicReceipt();
  const seen = [];
  const wallet = await connectPreferredWallet({
    chainId: CHAIN_ID,
    globalObject: {
      fetch: async (url, options) => {
        seen.push({ url, headers: options.headers });
        if (url.includes('connect')) {
          return {
            ok: true,
            text: async () => JSON.stringify({
              signerPairingToken: 'pairing-token-for-test',
              wallet: {
                address: PUBKEY,
                chainId: CHAIN_ID,
                signerProvider: PROVIDER,
                publicReceipt,
              },
            }),
          };
        }
        return {
          ok: true,
          text: async () => JSON.stringify({ signature: '55'.repeat(96) }),
        };
      },
    },
    runtimeConfig: {
      deployment: 'production',
      allowDefaultExternalSigner: true,
      defaultExternalSigner: runtimeSignerConfig(publicReceipt, {
        connectUrl: '/api/external-signer/connect',
        signTauTransactionPayloadUrl: '/api/external-signer/sign-tau',
      }),
    },
  });

  assert.equal(Object.hasOwn(wallet, 'signerPairingToken'), false);
  await wallet.signTauTransactionPayload({
    chainId: CHAIN_ID,
    senderPubkey: PUBKEY,
    sequenceNumber: 7,
    expirationTime: 99,
    operations: {},
    feeLimit: '0',
  });
  assert.equal(seen[0].headers['x-zenodex-signer-token'], undefined);
  assert.equal(seen[1].headers['x-zenodex-signer-token'], 'pairing-token-for-test');
});

test('wallet policy rejects HTTP and allows explicit HTTPS signer endpoints', async () => {
  const publicReceipt = await makePublicReceipt();
  await assert.rejects(
    connectPreferredWallet({
      chainId: CHAIN_ID,
      globalObject: {},
      runtimeConfig: {
        allowDefaultExternalSigner: true,
        defaultExternalSigner: runtimeSignerConfig(publicReceipt, {
          signTauTransactionPayloadUrl: 'http://signer.example/sign',
        }),
      },
    }),
    /same_origin_or_explicit_https/,
  );

  const wallet = await connectPreferredWallet({
    chainId: CHAIN_ID,
    globalObject: {},
    runtimeConfig: {
      deployment: 'production',
      allowDefaultExternalSigner: true,
      allowRemoteExternalSignerEndpoint: true,
      defaultExternalSigner: runtimeSignerConfig(publicReceipt, {
        signTauTransactionPayloadUrl: 'https://signer.example/sign',
      }),
    },
  });
  assert.equal(wallet.signerSecurityProfile, SECURITY_PROFILE);
});

test('wallet policy has no browser key generation fallback', async () => {
  await assert.rejects(
    connectPreferredWallet({ chainId: CHAIN_ID, globalObject: {} }),
    /external_signer_unavailable/,
  );
});

test('wallet policy requires an explicit chain id', async () => {
  await assert.rejects(
    connectPreferredWallet({ chainId: '', globalObject: {} }),
    /chain_id_required/,
  );
});
