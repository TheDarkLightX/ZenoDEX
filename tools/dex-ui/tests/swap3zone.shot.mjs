// One-off screenshot capture for the Swap 3-zone instrument (dev server).
// Stubs runtime posture (enforced vs advisory) + a realistic ZDEX/zUSD pool
// feed so the Market rail + Execution-proof envelope render with data.
// Run: node tests/swap3zone.shot.mjs   (vite dev on :5180)
import { chromium } from '@playwright/test';
import { mkdirSync } from 'node:fs';

const BASE = process.env.PW_BASE_URL || 'http://127.0.0.1:5180';
const OUT = 'test-results/screens';
mkdirSync(OUT, { recursive: true });

const POOLS = {
  pools: [
    { token0: 'ZDEX', token1: 'zUSD', asset0: 'ZDEX', asset1: 'zUSD', reserve0: 1_850_000, reserve1: 4_625_000, feeBps: 30, poolId: 'zdex-zusd' },
    { token0: 'TASSET0', token1: 'TASSET1', asset0: 'TASSET0', asset1: 'TASSET1', reserve0: 1_000_000, reserve1: 1_000_000, feeBps: 30, poolId: 't0-t1' },
  ],
  tokens: [
    { symbol: 'ZDEX', name: 'ZenoDEX', decimals: 18 },
    { symbol: 'zUSD', name: 'ZenoUSD', decimals: 18 },
    { symbol: 'TASSET0', name: 'Test Asset 0', decimals: 18 },
    { symbol: 'TASSET1', name: 'Test Asset 1', decimals: 18 },
  ],
};

const VARIANTS = {
  enforced: {
    deployment: 'local-testnet', chainId: 'zeno-ledger-localtest-v0', apiBase: '', demoMode: false,
    expectedZkPosture: {
      ok: true, production_security_claim: false, proof_verifier_kind: 'subprocess',
      zk_fallback_reason: null, zk_mode_effective: 'strict', zk_mode_requested: 'strict', zk_required: true,
    },
  },
  advisory: {
    deployment: 'local-testnet', chainId: 'zeno-ledger-localtest-v0', apiBase: '', demoMode: false,
    expectedZkPosture: {
      ok: true, production_security_claim: false, proof_verifier_kind: 'disabled',
      zk_fallback_reason: 'proof verifier command unavailable', zk_mode_effective: 'open',
      zk_mode_requested: 'auto-strict', zk_required: false,
    },
  },
};

const browser = await chromium.launch();
for (const [name, cfg] of Object.entries(VARIANTS)) {
  const ctx = await browser.newContext({ viewport: { width: 1440, height: 1000 }, deviceScaleFactor: 2, colorScheme: 'dark' });
  const page = await ctx.newPage();
  await page.route('**/zenodex-config.json', (r) => r.fulfill({ status: 200, contentType: 'application/json', body: JSON.stringify(cfg) }));
  let poolHits = 0;
  await page.route('**/api/pools**', (r) => { poolHits += 1; r.fulfill({ status: 200, contentType: 'application/json', body: JSON.stringify(POOLS) }); });
  const errs = [];
  page.on('pageerror', (e) => errs.push(String(e)));
  page.on('console', (m) => { if (m.type() === 'error') errs.push('console:' + m.text()); });
  page.on('requestfinished', (req) => { if (req.url().includes('/api/pools')) console.log(`  req ${req.url()}`); });
  await page.goto(`${BASE}?theme=dark`, { waitUntil: 'networkidle' });
  await page.waitForSelector('.swap-instrument', { timeout: 8000 });
  // Empty-amount state first
  await page.screenshot({ path: `${OUT}/swap-AFTER-${name}-empty.png`, fullPage: true });
  // Select the all-uppercase TASSET0 -> TASSET1 pair (matches the stub key).
  const selectToken = async (which, symbol) => {
    const sel = page.locator('.token-selector').nth(which);
    await sel.click();
    await page.locator('.token-list-item:not(.excluded)', { hasText: symbol }).first().click();
    await page.waitForTimeout(150);
  };
  await selectToken(0, 'TASSET0');
  await selectToken(1, 'TASSET1');
  // Fill an amount so the envelope + impact render
  const input = page.locator('.swap-amount-input').first();
  await input.fill('120000');
  await page.waitForTimeout(900);
  await page.screenshot({ path: `${OUT}/swap-AFTER-${name}.png`, fullPage: true });
  const railText = await page.locator('.swap-market').first().innerText().catch(() => '(no rail)');
  console.log(`[${name}] poolHits=${poolHits} pageerrors=${errs.length}${errs.length ? ' :: ' + errs.slice(0, 3).join(' | ') : ''}`);
  console.log(`  rail: ${railText.replace(/\n/g, ' / ').slice(0, 160)}`);
  await ctx.close();
}
await browser.close();
console.log('done');
