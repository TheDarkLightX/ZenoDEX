import assert from 'node:assert/strict';
import { test } from 'node:test';
import { browserKeyGenerationAllowed, connectPreferredWallet } from './walletSignerPolicy.js';
import { hashV0 } from './zenoProofClient.js';

const CHAIN_ID = 'zeno-ledger-localtest-v0';
const PUBKEY = `0x${'11'.repeat(48)}`;
const PRIVKEY = `0x${'22'.repeat(32)}`;
const ROOT = `0x${'aa'.repeat(32)}`;
const RUNTIME_DEFAULT_SCHEMA = 'zenodex/dex-ui/runtime-default-external-signer/v0';

async function makePublicReceipt({ publicKey = PUBKEY, chainId = CHAIN_ID } = {}) {
  const vault = {
    schema: 'zenodex/local_signer/vault/v0',
    version: 1,
    provider: 'zenodex-local-signer-v0',
    key_id: 'ui-test-local-signer',
    public_key: publicKey,
    algorithm: 'bls12-381-g2-basic-release-v0',
    chain_id: chainId,
    allowed_chain_ids: [chainId],
    created_at_epoch: 1,
    keygen_method: 'tau-testnet-console-wallet-py-ecc-g2basic-keygen-v0',
    storage_backend: 'encrypted-local-vault-scrypt-aesgcm-v0',
    browser_generated: false,
    zenodex_custody: false,
    encrypted_payload_hash: ROOT,
  };
  const vault_hash = await hashV0('local_signer_public_vault_v0', vault);
  const body = {
    schema: 'zenodex/local_signer/public_receipt/v0',
    provider: 'zenodex-local-signer-v0',
    vault_hash,
    vault,
    approval_mode: 'prompt',
    signer_user_approval_required: true,
    browser_bridge_auth_required: true,
    browser_generated: false,
    zenodex_custody: false,
  };
  return {
    ...body,
    receipt_hash: await hashV0('local_signer_public_receipt_v0', body),
  };
}

test('wallet policy prefers external signer bridge with a verified public receipt', async () => {
  const signTauTransactionPayload = async () => ({ ok: true });
  const signDexIntentForEngine = async () => '0xsignature';
  const publicReceipt = await makePublicReceipt();
  const wallet = await connectPreferredWallet({
    chainId: CHAIN_ID,
    globalObject: {
      zenodexLocalSigner: {
        signTauTransactionPayload,
        signDexIntentForEngine,
        connect: async ({ chainId }) => ({
          address: PUBKEY,
          chainId,
          signerProvider: 'zenodex-local-signer-v0',
          publicReceipt,
        }),
      },
    },
  });

  assert.equal(wallet.address, PUBKEY);
  assert.equal(wallet.chainId, CHAIN_ID);
  assert.equal(wallet.signerProvider, 'zenodex-local-signer-v0');
  assert.equal(wallet.localTestnetGenerated, false);
  assert.deepEqual(wallet.publicReceipt, publicReceipt);
  assert.equal(Object.hasOwn(wallet, 'privkey'), false);
  assert.equal(typeof wallet.signTauTransactionPayload, 'function');
  assert.equal(typeof wallet.signDexIntentForEngine, 'function');
  assert.deepEqual(await wallet.signTauTransactionPayload(), { ok: true });
  assert.equal(await wallet.signDexIntentForEngine(), '0xsignature');
});

test('wallet policy rejects external signer bridge that returns private key material', async () => {
  await assert.rejects(
    connectPreferredWallet({
      chainId: CHAIN_ID,
      globalObject: {
        zenodexSecureSigner: {
          connect: async () => ({
            address: PUBKEY,
            publicReceipt: await makePublicReceipt(),
            private_key_hex: PRIVKEY,
          }),
        },
      },
    }),
    /private_key_material/,
  );
});

test('wallet policy rejects external signer bridge without public receipt', async () => {
  await assert.rejects(
    connectPreferredWallet({
      chainId: CHAIN_ID,
      globalObject: {
        zenodexLocalSigner: {
          connect: async () => ({
            address: PUBKEY,
            chainId: CHAIN_ID,
          }),
        },
      },
    }),
    /public_receipt_required/,
  );
});

test('wallet policy rejects forged local signer public receipt', async () => {
  const publicReceipt = await makePublicReceipt();
  publicReceipt.vault.public_key = `0x${'12'.repeat(48)}`;

  await assert.rejects(
    connectPreferredWallet({
      chainId: CHAIN_ID,
      globalObject: {
        zenodexLocalSigner: {
          connect: async () => ({
            address: PUBKEY,
            chainId: CHAIN_ID,
            publicReceipt,
          }),
        },
      },
    }),
    /public_key_mismatch|vault_hash_mismatch|receipt_hash_mismatch/,
  );
});

test('wallet policy rejects unattended signer receipt in strict deployment', async () => {
  const publicReceipt = await makePublicReceipt();
  const body = { ...publicReceipt };
  delete body.receipt_hash;
  body.approval_mode = 'unattended';
  body.signer_user_approval_required = false;
  body.browser_bridge_auth_required = true;
  publicReceipt.approval_mode = body.approval_mode;
  publicReceipt.signer_user_approval_required = body.signer_user_approval_required;
  publicReceipt.browser_bridge_auth_required = body.browser_bridge_auth_required;
  publicReceipt.receipt_hash = await hashV0('local_signer_public_receipt_v0', body);

  await assert.rejects(
    connectPreferredWallet({
      chainId: CHAIN_ID,
      globalObject: {},
      runtimeConfig: {
        deployment: 'production',
        allowDefaultExternalSigner: true,
        defaultExternalSigner: {
          schema: RUNTIME_DEFAULT_SCHEMA,
          signerSecurityProfile: 'native-desktop-loopback-signer-v0',
          address: PUBKEY,
          chainId: CHAIN_ID,
          publicReceipt,
        },
      },
    }),
    /user_approval_required/,
  );
});

test('wallet policy accepts local-testnet runtime default external signer with public receipt', async () => {
  const publicReceipt = await makePublicReceipt();
  const wallet = await connectPreferredWallet({
    chainId: CHAIN_ID,
    globalObject: {},
    runtimeConfig: {
      deployment: 'local-testnet',
      defaultExternalSigner: {
        schema: RUNTIME_DEFAULT_SCHEMA,
        signerSecurityProfile: 'native-desktop-loopback-signer-v0',
        address: PUBKEY,
        chainId: CHAIN_ID,
        signerProvider: 'zenodex-local-signer-v0',
        publicReceipt,
      },
    },
  });

  assert.equal(wallet.address, PUBKEY);
  assert.equal(wallet.chainId, CHAIN_ID);
  assert.equal(wallet.signerProvider, 'zenodex-local-signer-v0');
  assert.equal(wallet.signerSecurityProfile, 'native-desktop-loopback-signer-v0');
  assert.equal(wallet.localTestnetGenerated, false);
  assert.equal(Object.hasOwn(wallet, 'privkey'), false);
  assert.deepEqual(wallet.publicReceipt, publicReceipt);
});

test('wallet policy rejects runtime default external signer outside allowed deployment', async () => {
  await assert.rejects(
    connectPreferredWallet({
      chainId: CHAIN_ID,
      globalObject: {},
      runtimeConfig: {
        deployment: 'production',
        defaultExternalSigner: {
          schema: RUNTIME_DEFAULT_SCHEMA,
          signerSecurityProfile: 'native-desktop-loopback-signer-v0',
          address: PUBKEY,
          chainId: CHAIN_ID,
          publicReceipt: await makePublicReceipt(),
        },
      },
    }),
    /runtime_default_external_signer_not_allowed/,
  );
});

test('wallet policy rejects runtime default external signer private key material', async () => {
  await assert.rejects(
    connectPreferredWallet({
      chainId: CHAIN_ID,
      globalObject: {},
      runtimeConfig: {
        deployment: 'local-testnet',
        defaultExternalSigner: {
          schema: RUNTIME_DEFAULT_SCHEMA,
          signerSecurityProfile: 'native-desktop-loopback-signer-v0',
          address: PUBKEY,
          chainId: CHAIN_ID,
          publicReceipt: await makePublicReceipt(),
          private_key_hex: PRIVKEY,
        },
      },
    }),
    /private_key_material/,
  );
});

test('wallet policy wires local runtime default signer endpoint without browser private key', async () => {
  const publicReceipt = await makePublicReceipt();
  const txSignature = '33'.repeat(96);
  const dexSignature = `0x${'44'.repeat(96)}`;
  const seen = [];
  const wallet = await connectPreferredWallet({
    chainId: CHAIN_ID,
    globalObject: {
      fetch: async (url, options) => {
        const body = JSON.parse(options.body);
        seen.push({ url, body });
        const payload = url.includes('tau')
          ? { signature: txSignature }
          : { signature: dexSignature };
        return {
          ok: true,
          text: async () => JSON.stringify(payload),
        };
      },
    },
    runtimeConfig: {
      deployment: 'local-testnet',
      defaultExternalSigner: {
        schema: RUNTIME_DEFAULT_SCHEMA,
        signerSecurityProfile: 'native-desktop-loopback-signer-v0',
        address: PUBKEY,
        chainId: CHAIN_ID,
        publicReceipt,
        signTauTransactionPayloadUrl: 'http://127.0.0.1:8799/sign-tau-transaction-payload',
        signDexIntentForEngineUrl: '/api/local-signer/sign-dex-intent',
      },
    },
  });

  const signedTauTx = await wallet.signTauTransactionPayload({
    chainId: CHAIN_ID,
    senderPubkey: PUBKEY.slice(2),
    sequenceNumber: 7,
    expirationTime: 99,
    operations: { 8: { action: 'local-testnet-check' } },
    feeLimit: '0',
  });
  const signedDexIntent = await wallet.signDexIntentForEngine({ sender_pubkey: PUBKEY }, { chainId: CHAIN_ID });

  assert.equal(signedTauTx.sender_pubkey, PUBKEY.slice(2));
  assert.equal(signedTauTx.sequence_number, 7);
  assert.equal(signedTauTx.signature, txSignature);
  assert.deepEqual(seen[1].body, {
    chainId: CHAIN_ID,
    intent: { sender_pubkey: PUBKEY },
  });
  assert.equal(signedDexIntent, dexSignature);
  assert.deepEqual(seen.map((item) => item.url), [
    'http://127.0.0.1:8799/sign-tau-transaction-payload',
    '/api/local-signer/sign-dex-intent',
  ]);
  assert.equal(Object.hasOwn(wallet, 'privkey'), false);
});

test('wallet policy rejects runtime signer Tau payload mutation', async () => {
  const publicReceipt = await makePublicReceipt();
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
      deployment: 'local-testnet',
      defaultExternalSigner: {
        schema: RUNTIME_DEFAULT_SCHEMA,
        signerSecurityProfile: 'native-desktop-loopback-signer-v0',
        address: PUBKEY,
        chainId: CHAIN_ID,
        publicReceipt,
        signTauTransactionPayloadUrl: 'http://127.0.0.1:8799/sign-tau-transaction-payload',
      },
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

test('wallet policy can load runtime default signer wallet through loopback connect URL', async () => {
  const publicReceipt = await makePublicReceipt();
  const seen = [];
  const wallet = await connectPreferredWallet({
    chainId: CHAIN_ID,
    globalObject: {
      fetch: async (url, options) => {
        seen.push({ url, body: JSON.parse(options.body) });
        return {
          ok: true,
          text: async () => JSON.stringify({
            ok: true,
            wallet: {
              address: PUBKEY,
              chainId: CHAIN_ID,
              signerProvider: 'zenodex-local-signer-v0',
              publicReceipt,
            },
          }),
        };
      },
    },
    runtimeConfig: {
      deployment: 'local-testnet',
      defaultExternalSigner: {
        schema: RUNTIME_DEFAULT_SCHEMA,
        signerSecurityProfile: 'native-desktop-loopback-signer-v0',
        connectUrl: 'http://127.0.0.1:8799/public-receipt',
      },
    },
  });

  assert.equal(wallet.address, PUBKEY);
  assert.equal(wallet.signerProvider, 'zenodex-local-signer-v0');
  assert.deepEqual(seen, [{
    url: 'http://127.0.0.1:8799/public-receipt',
    body: { chainId: CHAIN_ID },
  }]);
});

test('wallet policy falls back to browser keygen when local-testnet default signer is unreachable', async () => {
  const wallet = await connectPreferredWallet({
    chainId: CHAIN_ID,
    allowBrowserFallback: true,
    generateLocalWallet: async ({ chainId }) => ({
      address: PUBKEY,
      chainId,
      privkey: PRIVKEY,
      balance: {},
    }),
    globalObject: {
      fetch: async () => {
        throw new TypeError('Failed to fetch');
      },
    },
    runtimeConfig: {
      deployment: 'local-testnet',
      allowBrowserKeyGeneration: true,
      defaultExternalSigner: {
        schema: RUNTIME_DEFAULT_SCHEMA,
        signerSecurityProfile: 'native-desktop-loopback-signer-v0',
        connectUrl: 'http://127.0.0.1:8799/public-receipt',
      },
    },
  });

  assert.equal(wallet.address, PUBKEY);
  assert.equal(wallet.signerProvider, 'browser-local-last-resort');
  assert.equal(wallet.browserLastResort, true);
  assert.equal(wallet.localTestnetGenerated, true);
  assert.equal(wallet.privkey, PRIVKEY);
});

test('wallet policy does not browser-fallback around signer validation failures', async () => {
  await assert.rejects(
    connectPreferredWallet({
      chainId: CHAIN_ID,
      allowBrowserFallback: true,
      generateLocalWallet: async () => ({
        address: PUBKEY,
        privkey: PRIVKEY,
      }),
      globalObject: {},
      runtimeConfig: {
        deployment: 'local-testnet',
        allowBrowserKeyGeneration: true,
        defaultExternalSigner: {
          schema: RUNTIME_DEFAULT_SCHEMA,
          signerSecurityProfile: 'native-desktop-loopback-signer-v0',
          address: PUBKEY,
          chainId: CHAIN_ID,
        },
      },
    }),
    /public_receipt_required/,
  );
});

test('wallet policy forwards signer pairing token only as a signing header', async () => {
  const publicReceipt = await makePublicReceipt();
  const seen = [];
  const wallet = await connectPreferredWallet({
    chainId: CHAIN_ID,
    globalObject: {
      fetch: async (url, options) => {
        seen.push({ url, headers: options.headers, body: JSON.parse(options.body) });
        if (url.includes('public-receipt')) {
          return {
            ok: true,
            text: async () => JSON.stringify({
              ok: true,
              signerPairingToken: 'pairing-token-for-test',
              wallet: {
                address: PUBKEY,
                chainId: CHAIN_ID,
                signerProvider: 'zenodex-local-signer-v0',
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
      deployment: 'local-testnet',
      defaultExternalSigner: {
        schema: RUNTIME_DEFAULT_SCHEMA,
        signerSecurityProfile: 'native-desktop-loopback-signer-v0',
        connectUrl: 'http://127.0.0.1:8799/public-receipt',
        signTauTransactionPayloadUrl: 'http://127.0.0.1:8799/sign-tau-transaction-payload',
      },
    },
  });

  assert.equal(Object.hasOwn(wallet, 'signerPairingToken'), false);
  assert.equal(Object.hasOwn(wallet, 'localSignerPairingToken'), false);
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

test('wallet policy rejects non-loopback runtime default signer endpoint by default', async () => {
  await assert.rejects(
    connectPreferredWallet({
      chainId: CHAIN_ID,
      globalObject: {},
      runtimeConfig: {
        deployment: 'local-testnet',
        defaultExternalSigner: {
          schema: RUNTIME_DEFAULT_SCHEMA,
          signerSecurityProfile: 'native-desktop-loopback-signer-v0',
          address: PUBKEY,
          chainId: CHAIN_ID,
          publicReceipt: await makePublicReceipt(),
          signTauTransactionPayloadUrl: 'http://example.com/sign',
        },
      },
    }),
    /same_origin_or_loopback/,
  );
});

test('wallet policy allows explicit production external signer profile', async () => {
  const publicReceipt = await makePublicReceipt();
  const wallet = await connectPreferredWallet({
    chainId: CHAIN_ID,
    globalObject: {},
    runtimeConfig: {
      deployment: 'production',
      allowDefaultExternalSigner: true,
      defaultExternalSigner: {
        schema: RUNTIME_DEFAULT_SCHEMA,
        signerSecurityProfile: 'native-desktop-loopback-signer-v0',
        address: PUBKEY,
        chainId: CHAIN_ID,
        publicReceipt,
      },
    },
  });

  assert.equal(wallet.address, PUBKEY);
  assert.equal(wallet.signerSecurityProfile, 'native-desktop-loopback-signer-v0');
  assert.equal(Object.hasOwn(wallet, 'privkey'), false);
});

test('wallet policy rejects unsupported production external signer profile', async () => {
  await assert.rejects(
    connectPreferredWallet({
      chainId: CHAIN_ID,
      globalObject: {},
      runtimeConfig: {
        deployment: 'production',
        allowDefaultExternalSigner: true,
        defaultExternalSigner: {
          schema: RUNTIME_DEFAULT_SCHEMA,
          signerSecurityProfile: 'opaque-remote-custody-v0',
          address: PUBKEY,
          chainId: CHAIN_ID,
          publicReceipt: await makePublicReceipt(),
        },
      },
    }),
    /security_profile_unsupported/,
  );
});

test('wallet policy rejects remote HTTPS endpoint for native desktop profile', async () => {
  await assert.rejects(
    connectPreferredWallet({
      chainId: CHAIN_ID,
      globalObject: {},
      runtimeConfig: {
        deployment: 'production',
        allowDefaultExternalSigner: true,
        allowRemoteExternalSignerEndpoint: true,
        defaultExternalSigner: {
          schema: RUNTIME_DEFAULT_SCHEMA,
          signerSecurityProfile: 'native-desktop-loopback-signer-v0',
          connectUrl: 'https://signer.example/public-receipt',
        },
      },
    }),
    /remote_https_profile_not_allowed/,
  );
});

test('wallet policy rejects threshold signer profile until its receipt schema is wired', async () => {
  await assert.rejects(
    connectPreferredWallet({
    chainId: CHAIN_ID,
    globalObject: {
      fetch: async () => ({
        ok: true,
        text: async () => JSON.stringify({
          wallet: {
            address: PUBKEY,
            chainId: CHAIN_ID,
            signerProvider: 'zenodex-local-signer-v0',
            publicReceipt,
          },
        }),
      }),
    },
    runtimeConfig: {
      deployment: 'production',
      allowDefaultExternalSigner: true,
      allowRemoteExternalSignerEndpoint: true,
      defaultExternalSigner: {
        schema: RUNTIME_DEFAULT_SCHEMA,
        signerSecurityProfile: 'threshold-signer-v0',
        connectUrl: 'https://threshold-signer.example/public-receipt',
      },
    },
    }),
    /security_profile_unsupported/,
  );
});

test('wallet policy blocks browser key generation unless explicit fallback is enabled', async () => {
  await assert.rejects(
    connectPreferredWallet({
      chainId: CHAIN_ID,
      globalObject: {},
      generateLocalWallet: async () => ({ address: PUBKEY, privkey: PRIVKEY }),
    }),
    /external_signer_unavailable/,
  );

  const wallet = await connectPreferredWallet({
    chainId: CHAIN_ID,
    globalObject: {},
    allowBrowserFallback: true,
    generateLocalWallet: async ({ chainId }) => ({ address: PUBKEY, privkey: PRIVKEY, chainId }),
  });

  assert.equal(wallet.address, PUBKEY);
  assert.equal(wallet.privkey, PRIVKEY);
  assert.equal(wallet.browserLastResort, true);
  assert.equal(wallet.signerProvider, 'browser-local-last-resort');
});

test('browser key generation flag is opt-in only for explicit local deployments', () => {
  assert.equal(browserKeyGenerationAllowed(), false);
  assert.equal(
    browserKeyGenerationAllowed({
      locationSearch: '?zenodexAllowBrowserKeygen=1',
      runtimeConfig: { deployment: 'local-testnet' },
    }),
    true,
  );
  assert.equal(
    browserKeyGenerationAllowed({
      locationSearch: '?zenodexAllowBrowserKeygen=0',
      runtimeConfig: { deployment: 'local-testnet' },
    }),
    false,
  );
  assert.equal(
    browserKeyGenerationAllowed({
      runtimeConfig: { deployment: 'local-testnet', allowBrowserKeyGeneration: true },
    }),
    true,
  );
  assert.equal(
    browserKeyGenerationAllowed({
      runtimeConfig: { deployment: 'local-testnet' },
      env: { VITE_ALLOW_BROWSER_KEYGEN: 'true' },
    }),
    true,
  );
  assert.equal(
    browserKeyGenerationAllowed({
      locationSearch: '?zenodexAllowBrowserKeygen=1',
      runtimeConfig: { deployment: 'local-testent', allowBrowserKeyGeneration: true },
      env: { VITE_ALLOW_BROWSER_KEYGEN: 'true' },
    }),
    false,
  );
  assert.equal(
    browserKeyGenerationAllowed({
      locationSearch: '?zenodexAllowBrowserKeygen=1',
      runtimeConfig: { deployment: 'local-testnet', allowBrowserKeyGeneration: false },
    }),
    false,
  );
});

test('browser key generation is hard-disabled for public testnet and production', () => {
  for (const deployment of ['public-testnet', 'production']) {
    assert.equal(
      browserKeyGenerationAllowed({
        locationSearch: '?zenodexAllowBrowserKeygen=1',
        runtimeConfig: { deployment, allowBrowserKeyGeneration: true },
        env: { VITE_ALLOW_BROWSER_KEYGEN: 'true' },
      }),
      false,
    );
  }
});
