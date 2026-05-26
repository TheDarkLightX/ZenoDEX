import assert from 'node:assert/strict';
import { test } from 'node:test';
import { browserKeyGenerationAllowed, connectPreferredWallet } from './walletSignerPolicy.js';

const CHAIN_ID = 'zeno-ledger-localtest-v0';
const PUBKEY = `0x${'11'.repeat(48)}`;
const PRIVKEY = `0x${'22'.repeat(32)}`;

test('wallet policy prefers secure signer bridge without private key material', async () => {
  const signTauTransactionPayload = async () => ({ ok: true });
  const signDexIntentForEngine = async () => '0xsignature';
  const wallet = await connectPreferredWallet({
    chainId: CHAIN_ID,
    globalObject: {
      zenodexSecureSigner: {
        signTauTransactionPayload,
        signDexIntentForEngine,
        connect: async ({ chainId }) => ({
          address: PUBKEY,
          chainId,
          signerProvider: 'tee-attested-signer',
          hardwareBacked: true,
        }),
      },
    },
  });

  assert.equal(wallet.address, PUBKEY);
  assert.equal(wallet.chainId, CHAIN_ID);
  assert.equal(wallet.signerProvider, 'tee-attested-signer');
  assert.equal(wallet.localTestnetGenerated, false);
  assert.equal(Object.hasOwn(wallet, 'privkey'), false);
  assert.equal(typeof wallet.signTauTransactionPayload, 'function');
  assert.equal(typeof wallet.signDexIntentForEngine, 'function');
  assert.deepEqual(await wallet.signTauTransactionPayload(), { ok: true });
  assert.equal(await wallet.signDexIntentForEngine(), '0xsignature');
});

test('wallet policy rejects secure signer bridge that returns private key material', async () => {
  await assert.rejects(
    connectPreferredWallet({
      chainId: CHAIN_ID,
      globalObject: {
        zenodexSecureSigner: {
          connect: async () => ({
            address: PUBKEY,
            private_key_hex: PRIVKEY,
          }),
        },
      },
    }),
    /private_key_material/,
  );
});

test('wallet policy blocks browser key generation unless explicit fallback is enabled', async () => {
  await assert.rejects(
    connectPreferredWallet({
      chainId: CHAIN_ID,
      globalObject: {},
      generateLocalWallet: async () => ({ address: PUBKEY, privkey: PRIVKEY }),
    }),
    /secure_signer_unavailable/,
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

test('browser key generation flag is opt-in through query, runtime config, or env', () => {
  assert.equal(browserKeyGenerationAllowed(), false);
  assert.equal(browserKeyGenerationAllowed({ locationSearch: '?zenodexAllowBrowserKeygen=1' }), true);
  assert.equal(browserKeyGenerationAllowed({ locationSearch: '?zenodexAllowBrowserKeygen=0' }), false);
  assert.equal(browserKeyGenerationAllowed({ runtimeConfig: { allowBrowserKeyGeneration: true } }), true);
  assert.equal(browserKeyGenerationAllowed({ env: { VITE_ALLOW_BROWSER_KEYGEN: 'true' } }), true);
});
