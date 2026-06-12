import { chromium } from '@playwright/test';
import { mkdirSync } from 'node:fs';
const BASE = process.env.PW_BASE_URL || 'http://127.0.0.1:18081';
const OUT = 'test-results/live'; mkdirSync(OUT, { recursive: true });
const TABS = [
  ['ZDEX Stats', 'stats'],
  ['Oracle', 'oracle'],
  ['Confidential', 'confidential'],
  ['Keys', 'keys'],
];
const browser = await chromium.launch();
const ctx = await browser.newContext({ viewport: { width: 1440, height: 1300 }, deviceScaleFactor: 2, colorScheme: 'dark' });
const page = await ctx.newPage();
const errs = []; page.on('pageerror', e => errs.push(String(e))); page.on('console', m => { if (m.type()==='error') errs.push('c:'+m.text().slice(0,100)); });
await page.goto(`${BASE}/?theme=dark`, { waitUntil: 'networkidle' });
for (const [label, slug] of TABS) {
  await page.getByRole('button', { name: label }).first().click().catch(()=>{});
  await page.waitForTimeout(1400);
  await page.screenshot({ path: `${OUT}/live-${slug}.png`, fullPage: true });
  console.log(`[${label}] captured`);
}
console.log(`pageerrors=${errs.length}${errs.length?' :: '+errs.slice(0,5).join(' | '):''}`);
await browser.close();
