// Capture the four reworked surfaces from the LIVE strict stack (:18081, real
// data, proof-enforced posture, dark theme). Deploy verification + review ref.
import { chromium } from '@playwright/test';
import { mkdirSync } from 'node:fs';

const BASE = process.env.PW_BASE_URL || 'http://127.0.0.1:18081';
const OUT = 'test-results/live';
mkdirSync(OUT, { recursive: true });

const TABS = [
  ['Swap', 'swap', '.swap-instrument'],
  ['Pools', 'pools', '.pool-table'],
  ['zUSD', 'zusd', '.zusd-wallet-surface'],
  ['Perpetuals', 'perps', '.perp-grid'],
];

const browser = await chromium.launch();
const ctx = await browser.newContext({ viewport: { width: 1440, height: 1200 }, deviceScaleFactor: 2, colorScheme: 'dark' });
const page = await ctx.newPage();
const errs = [];
page.on('pageerror', (e) => errs.push(String(e)));
page.on('console', (m) => { if (m.type() === 'error') errs.push('console:' + m.text().slice(0, 120)); });

await page.goto(`${BASE}/?theme=dark`, { waitUntil: 'networkidle' });
for (const [label, slug, sel] of TABS) {
  await page.getByRole('button', { name: label }).first().click().catch(() => {});
  await page.waitForSelector(sel, { timeout: 9000 }).catch(() => {});
  await page.waitForTimeout(1100);
  await page.screenshot({ path: `${OUT}/live-${slug}.png`, fullPage: true });
  const present = await page.locator(sel).count();
  console.log(`[${label}] selector=${present} (${sel})`);
}
console.log(`pageerrors=${errs.length}${errs.length ? ' :: ' + errs.slice(0, 4).join(' | ') : ''}`);
await browser.close();
