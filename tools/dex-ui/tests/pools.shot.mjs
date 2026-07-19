// One-off screenshot capture for the Pools surface (dev server, dark theme).
// Stubs /api/pools with a realistic live-shaped feed (varied reserves so the
// composition bars differ; one FROZEN pool to exercise the unverified dot).
// Run: node tests/pools.shot.mjs
import { chromium } from '@playwright/test';
import { mkdirSync } from 'node:fs';

const BASE = process.env.PW_BASE_URL || 'http://127.0.0.1:5180';
const OUT = 'test-results/screens';
mkdirSync(OUT, { recursive: true });

const POOLS = {
  pools: [
    { poolId: 'zdex-zusd', token0: 'ZDEX', token1: 'zUSD', asset0: 'ZDEX', asset1: 'zUSD', reserve0: 1_850_000, reserve1: 4_625_000, feeBps: 30, lpSupply: 2_900_000, status: 'ACTIVE', inputVolume0_24h: 142_000, fee0_24h: 426 },
    { poolId: 't0-t1', token0: 'TASSET0', token1: 'TASSET1', asset0: 'TASSET0', asset1: 'TASSET1', reserve0: 1_000_000, reserve1: 1_000_000, feeBps: 30, lpSupply: 1_000_000, status: 'ACTIVE' },
    { poolId: 't1-tzeno', token0: 'TASSET1', token1: 'TZENO', asset0: 'TASSET1', asset1: 'TZENO', reserve0: 320_000, reserve1: 5_400_000, feeBps: 30, lpSupply: 1_300_000, status: 'ACTIVE' },
    { poolId: 'zdex-tzeno', token0: 'ZDEX', token1: 'TZENO', asset0: 'ZDEX', asset1: 'TZENO', reserve0: 90_000, reserve1: 60_000, feeBps: 50, lpSupply: 73_000, status: 'FROZEN' },
  ],
  tokens: [
    { symbol: 'ZDEX', name: 'ZenoDEX', decimals: 18 },
    { symbol: 'zUSD', name: 'ZenoUSD', decimals: 18 },
    { symbol: 'TASSET0', name: 'Test Asset 0', decimals: 18 },
    { symbol: 'TASSET1', name: 'Test Asset 1', decimals: 18 },
    { symbol: 'TZENO', name: 'Test Zeno', decimals: 18 },
  ],
};
const CFG = {
  deployment: 'local-testnet', chainId: 'zeno-ledger-localtest-v0', apiBase: '',
  demoMode: false, allowDemoMode: false,
  expectedZkPosture: { zk_mode_effective: 'strict', zk_required: true, proof_verifier_kind: 'subprocess' },
};

const browser = await chromium.launch();
const ctx = await browser.newContext({ viewport: { width: 1440, height: 1100 }, deviceScaleFactor: 2, colorScheme: 'dark' });
const page = await ctx.newPage();
const errs = [];
page.on('pageerror', (e) => errs.push(String(e)));
page.on('console', (m) => { if (m.type() === 'error') errs.push('console:' + m.text()); });
await page.route('**/zenodex-config.json', (r) => r.fulfill({ status: 200, contentType: 'application/json', body: JSON.stringify(CFG) }));
await page.route('**/api/pools**', (r) => r.fulfill({ status: 200, contentType: 'application/json', body: JSON.stringify(POOLS) }));

await page.goto(`${BASE}?theme=dark`, { waitUntil: 'networkidle' });
await page.getByRole('button', { name: 'Pools' }).first().click().catch(() => {});
await page.waitForSelector('.pool-table', { timeout: 8000 });
await page.waitForTimeout(800);
await page.screenshot({ path: `${OUT}/pools-AFTER.png`, fullPage: true });
await page.locator('.pool-stats').screenshot({ path: `${OUT}/pools-crop-stats.png` }).catch(() => {});
await page.locator('.pool-table').screenshot({ path: `${OUT}/pools-crop-table.png` }).catch(() => {});

const rows = await page.locator('.pool-table tbody tr').count();
const compBars = await page.locator('.pool-comp-bar').count();
const verifyChips = await page.locator('.pool-verify').count();
const verified = await page.locator('.pool-verify.is-verified').count();
const unverified = await page.locator('.pool-verify.is-unverified').count();
const verifiedTile = await page.locator('.pool-stat-verified .stat-value').innerText().catch(() => '?');
console.log(`rows=${rows} compBars=${compBars} verifyChips=${verifyChips} (verified=${verified} unverified=${unverified}) verifiedTile="${verifiedTile}" pageerrors=${errs.length}`);
if (errs.length) console.log('  errs:', errs.slice(0, 4).join(' | '));
await browser.close();
