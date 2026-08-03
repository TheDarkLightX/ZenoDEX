import assert from 'node:assert/strict';
import { test } from 'node:test';
import { readFileSync } from 'node:fs';

// Source-contract regression for the community report "I got 50k of both but it
// only shows at LP Pool, not swap or perps" — the zUSD half. The api.js layer is
// covered by apiAccountForwarding.test.mjs; this test locks the COMPONENT wiring
// that makes the connected wallet actually drive the zUSD account-aware status
// query (Codex flagged that App rendered <ZUSDWorkbench/> with no wallet, and the
// surfaces never rendered status.account_view). It is a static guard, not a DOM
// render test: it asserts the wiring is present so it cannot silently regress.

function src(rel) {
  return readFileSync(new URL(rel, import.meta.url), 'utf8');
}

const app = src('../App.jsx');
const workbench = src('../components/ZUSDWorkbench.jsx');
const monetary = src('../components/ZUSDMonetarySurface.jsx');
const tau = src('../components/ZUSDTauWalletSurface.jsx');

test('App passes the connected wallet to ZUSDWorkbench (like Swap/Pools/Perps)', () => {
  assert.match(app, /<ZUSDWorkbench\s+wallet=\{wallet\}/);
});

test('ZUSDWorkbench accepts wallet and threads it to surfaces + MintPanel', () => {
  assert.match(workbench, /function ZUSDWorkbench\(\{\s*wallet/);
  assert.match(workbench, /<ZUSDMonetarySurface\s+wallet=\{wallet\}/);
  assert.match(workbench, /<ZUSDTauWalletSurface\s+wallet=\{wallet\}/);
  // Both MintPanel render sites (live smoke + demo panel) get the wallet. Match
  // each full self-closing tag (it may contain `=>` arrows, so don't use [^>]).
  const mintPanelTags = workbench.match(/<MintPanel\b[\s\S]*?\/>/g) || [];
  assert.ok(mintPanelTags.length >= 2, 'expected at least two MintPanel render sites');
  for (const tag of mintPanelTags) {
    assert.ok(tag.includes('wallet={wallet}'), `MintPanel site missing wallet prop: ${tag}`);
  }
});

test('ZUSDMonetarySurface binds the connected account and renders account_view', () => {
  assert.match(monetary, /function ZUSDMonetarySurface\(\{\s*wallet/);
  // The connected wallet seeds/rebinds the account-aware query field.
  assert.match(monetary, /connectedAccount\s*=\s*\(wallet\?\.address/);
  assert.match(monetary, /actor_pubkey:\s*connectedAccount/);
  // The connected account's balance is actually shown.
  assert.match(monetary, /status\.account_view\.zusd_balance/);
  // On disconnect, the auto-bound field is cleared only when it still equals the
  // prior wallet (manual edits survive) — no stale account_view after disconnect.
  assert.match(monetary, /curr\.actor_pubkey === previous/);
});

test('ZUSDTauWalletSurface binds the connected account and renders account_view', () => {
  assert.match(tau, /function ZUSDTauWalletSurface\(\{\s*wallet/);
  assert.match(tau, /connectedAccount\s*=\s*\(wallet\?\.address/);
  assert.match(tau, /sender_pubkey:\s*connectedAccount/);
  assert.match(tau, /status\.account_view\.balance/);
  assert.match(tau, /curr\.sender_pubkey === previous/);
});

test('ZUSDTauWalletSurface exposes transfer only and ignores supply-action query input', () => {
  assert.match(tau, /action:\s*'transfer'/);
  assert.doesNotMatch(tau, /params\.get\('zusdAction'\)/);
  assert.doesNotMatch(tau, /<option\s+value="mint"/);
  assert.doesNotMatch(tau, /<option\s+value="burn"/);
  assert.doesNotMatch(tau, /id="zusd-operator"/);
});

test('MintPanel clears the auto-bound owner only on a matching disconnect', () => {
  // prevWalletRef + clear-if-equals-previous guard (manual edits preserved).
  assert.match(workbench, /curr === previous \? '' : curr/);
});

test('vault-owner prefill is suppressed once a wallet has driven the field', () => {
  // Codex catch: after disconnect, the global vault_owner_pubkey prefill must NOT
  // rehydrate the disconnected account (which also poisoned the re-connect rebind).
  // Both monetary paths gate the prefill on !walletEverConnectedRef.current.
  assert.match(workbench, /vault_owner_pubkey && !walletEverConnectedRef\.current/);
  assert.match(monetary, /vault_owner_pubkey && !walletEverConnectedRef\.current/);
});
