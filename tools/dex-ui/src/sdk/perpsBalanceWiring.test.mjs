import assert from 'node:assert/strict';
import { test } from 'node:test';
import { readFileSync } from 'node:fs';

// Source-contract regression (Codex F4) — the perps half of the community
// "I got 50k of both but it only shows at LP Pool" bug. In PerpProvider.jsx,
// derivePositionFromWalletMarket's 2p-clearinghouse branch must copy the matched
// slot's always-present account_{a,b}_quote_balance into position.quoteBalance.
// Without it the 2p branch left quoteBalance undefined, and PerpCollateralModal
// (which reads position.quoteBalance before falling back to wallet.balance[asset],
// an asset-id key the wallet usually lacks) showed a funded connected account a
// zero/unavailable perps balance. A behavioral import isn't possible (PerpProvider
// is a JSX/React module node:test can't load), so this locks the wiring at source.

const src = readFileSync(new URL('../lib/PerpProvider.jsx', import.meta.url), 'utf8');

test('2p branch copies account_a_quote_balance into quoteBalance (slot A)', () => {
  assert.match(src, /quoteBalance = Number\(walletMarket\.account_a_quote_balance \?\? 0\)/);
});

test('2p branch copies account_b_quote_balance into quoteBalance (slot B)', () => {
  assert.match(src, /quoteBalance = Number\(walletMarket\.account_b_quote_balance \?\? 0\)/);
});

test('the 2p-derived position object exposes quoteBalance', () => {
  // The returned object must surface quoteBalance (the accounts-list branch
  // already did via account.quote_balance; the 2p branch now matches it).
  assert.ok(
    /collateralQuote,[\s\S]*?\bquoteBalance,/.test(src),
    'derived 2p position must include quoteBalance in its returned object',
  );
});
