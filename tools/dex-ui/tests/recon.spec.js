// Evidence capture across every surface of the LIVE local-testnet GUI.
//
// Sandbox reality: only the orchestrator can reach loopback :18080; analysis
// subagents cannot. So this spec drives the real GUI and captures rich,
// reviewable evidence to test-results/evidence/ — screenshot, full console log
// (all levels), every network request with status + (for /api/) response body,
// nav/paint timing, and visible text — one JSON per surface. Role-based
// analysis agents then reason over this real captured behavior plus the
// component code, instead of touching the network themselves.
import { test } from '@playwright/test';
import fs from 'node:fs';

const EV = 'test-results/evidence';
fs.mkdirSync(EV, { recursive: true });

const TABS = [
  ['swap', 'Swap'],
  ['pools', 'Pools'],
  ['stats', 'ZDEX Stats'],
  ['perps', 'Perpetuals'],
  ['strategy', 'Strategy'],
  ['zusd', 'zUSD'],
  ['oracle', 'Oracle'],
  ['confidential', 'Confidential'],
  ['keys', 'Keys'],
];

for (const [slug, label] of TABS) {
  test(`recon: ${label}`, async ({ page }) => {
    const ev = {
      surface: label,
      slug,
      console: [], // {type, text}
      network: [], // {method, url, status, ms, apiBody?}
      perf: {},
      visibleTextSample: '',
      ts: new Date().toISOString(),
    };
    const reqStart = new Map();
    page.on('console', (m) => ev.console.push({ type: m.type(), text: m.text().slice(0, 600) }));
    page.on('pageerror', (e) => ev.console.push({ type: 'pageerror', text: String(e).slice(0, 800) }));
    page.on('request', (r) => reqStart.set(r, Date.now()));
    page.on('response', async (res) => {
      const req = res.request();
      const url = res.url();
      const rec = {
        method: req.method(),
        url: url.replace('http://127.0.0.1:18080', ''),
        status: res.status(),
        ms: reqStart.has(req) ? Date.now() - reqStart.get(req) : null,
      };
      if (url.includes('/api/') && req.method() !== 'OPTIONS') {
        try {
          const body = await res.text();
          rec.apiBody = body.slice(0, 1500);
        } catch { /* streamed/aborted */ }
      }
      ev.network.push(rec);
    });

    await page.goto('/', { waitUntil: 'domcontentloaded' });
    await page.waitForLoadState('networkidle').catch(() => {});

    // Switch to the surface.
    const byRole = page.getByRole('button', { name: label, exact: true });
    if (await byRole.count()) await byRole.first().click();
    else await page.getByText(label, { exact: true }).first().click();
    await page.waitForTimeout(1200);
    await page.waitForLoadState('networkidle').catch(() => {});

    await page.screenshot({ path: `${EV}/${slug}.png`, fullPage: true });
    ev.visibleTextSample = (await page.locator('main, #root, body').first().innerText().catch(() => ''))
      .replace(/\n{2,}/g, '\n')
      .slice(0, 4000);
    ev.perf = await page.evaluate(() => {
      const nav = performance.getEntriesByType('navigation')[0] || {};
      const paints = Object.fromEntries(
        performance.getEntriesByType('paint').map((p) => [p.name, Math.round(p.startTime)]),
      );
      return {
        domContentLoaded: Math.round(nav.domContentLoadedEventEnd || 0),
        loadEvent: Math.round(nav.loadEventEnd || 0),
        ...paints,
        resourceCount: performance.getEntriesByType('resource').length,
      };
    });

    fs.writeFileSync(`${EV}/${slug}.json`, JSON.stringify(ev, null, 2));
  });
}
