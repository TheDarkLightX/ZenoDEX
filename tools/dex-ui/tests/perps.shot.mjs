// Screenshot the Perps tab (dev server, dark theme) against the REAL captured
// wallet-status (1 clearinghouse_2p_v1 market). No wallet connected → trader
// surface renders read-real market data + epoch. Run: node tests/perps.shot.mjs
import { chromium } from '@playwright/test';
import { mkdirSync, readFileSync } from 'node:fs';

const BASE = process.env.PW_BASE_URL || 'http://127.0.0.1:5180';
const OUT = 'test-results/screens';
mkdirSync(OUT, { recursive: true });

const STATUS = JSON.parse(readFileSync('test-results/perps-wallet-status-live.json', 'utf8'));
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
await page.route('**/api/perps/wallet/status**', (r) => r.fulfill({ status: 200, contentType: 'application/json', body: JSON.stringify(STATUS) }));
await page.route('**/api/perps/**', (r) => {
  if (r.request().url().includes('/wallet/status')) return r.fallback();
  return r.fulfill({ status: 200, contentType: 'application/json', body: JSON.stringify({ ok: true }) });
});

await page.goto(`${BASE}?theme=dark`, { waitUntil: 'networkidle' });
await page.getByRole('button', { name: 'Perpetuals' }).first().click().catch(() => {});
await page.waitForSelector('.perp-grid', { timeout: 9000 }).catch(() => {});
await page.waitForTimeout(1000);
await page.screenshot({ path: `${OUT}/perps-AFTER.png`, fullPage: true });

const grid = await page.locator('.perp-grid').count();
const epochStep = await page.locator('[class*="epoch"], [class*="step"]').count();
console.log(`perpGrid=${grid} epochEls=${epochStep} pageerrors=${errs.length}`);
if (errs.length) console.log('  errs:', errs.slice(0, 5).join(' | '));
await browser.close();
