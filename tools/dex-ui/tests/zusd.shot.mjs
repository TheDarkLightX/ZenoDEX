// One-off screenshot capture for the LIVE zUSD surface (dev server).
// Stubs demoMode:false config + the REAL captured monetary status so the
// enriched live surface (stat tiles · risk params · Formal Proofs panel)
// renders against authentic node data. Run: node tests/zusd.shot.mjs
import { chromium } from '@playwright/test';
import { mkdirSync, readFileSync } from 'node:fs';

const BASE = process.env.PW_BASE_URL || 'http://127.0.0.1:5180';
const OUT = 'test-results/screens';
mkdirSync(OUT, { recursive: true });

const STATUS = JSON.parse(readFileSync('test-results/zusd-status-live.json', 'utf8'));
const CFG = {
  deployment: 'local-testnet', chainId: 'zeno-ledger-localtest-v0', apiBase: '',
  demoMode: false, allowDemoMode: false,
  expectedZkPosture: { zk_mode_effective: 'strict', zk_required: true, proof_verifier_kind: 'subprocess' },
};

const browser = await chromium.launch();
const ctx = await browser.newContext({ viewport: { width: 1440, height: 1200 }, deviceScaleFactor: 2, colorScheme: 'dark' });
const page = await ctx.newPage();
const errs = [];
page.on('pageerror', (e) => errs.push(String(e)));
page.on('console', (m) => { if (m.type() === 'error') errs.push('console:' + m.text()); });
await page.route('**/zenodex-config.json', (r) => r.fulfill({ status: 200, contentType: 'application/json', body: JSON.stringify(CFG) }));
await page.route('**/api/zusd/monetary/status**', (r) => r.fulfill({ status: 200, contentType: 'application/json', body: JSON.stringify(STATUS) }));
// Other zUSD endpoints (tau wallet surface) — return benign empty so nothing hangs.
await page.route('**/api/zusd/**', (r) => {
  if (r.request().url().includes('/monetary/status')) return r.fallback();
  return r.fulfill({ status: 200, contentType: 'application/json', body: JSON.stringify({ ok: true }) });
});

await page.goto(`${BASE}?theme=dark`, { waitUntil: 'networkidle' });
// Navigate to the zUSD tab.
await page.locator('button.nav-tab, .nav-tab, nav button', { hasText: 'zUSD' }).first().click().catch(async () => {
  await page.getByText('zUSD', { exact: true }).first().click();
});
await page.waitForSelector('.zusd-wallet-surface', { timeout: 8000 });
await page.waitForSelector('.zusd-assurance-grid', { timeout: 8000 });
await page.waitForTimeout(900);
await page.screenshot({ path: `${OUT}/zusd-AFTER.png`, fullPage: true });
await page.locator('.zusd-stat-tiles').screenshot({ path: `${OUT}/zusd-crop-tiles.png` }).catch(() => {});
await page.locator('.zusd-assurance-grid').screenshot({ path: `${OUT}/zusd-crop-assurance.png` }).catch(() => {});

const tiles = await page.locator('.zusd-stat-tile').count();
const proofs = await page.locator('.zusd-fp-row').count();
const riskRows = await page.locator('.zusd-rp-table tr').count();
const profile = await page.locator('.zusd-proof-profile').count();
console.log(`tiles=${tiles} leanProofs=${proofs} riskRows=${riskRows} proofProfile=${profile} pageerrors=${errs.length}`);
if (errs.length) console.log('  errs:', errs.slice(0, 4).join(' | '));
await browser.close();
