// Live-GUI smoke + visual capture across all top-level surfaces.
//
// Drives the real local-testnet bundle on :18080: loads the app, walks every
// nav tab, screenshots each, and records browser console errors / failed
// network requests. Screenshots land in test-results/screens/ for the analysis
// agents to review. This is the de-risking proof that browser automation works
// end-to-end against the live stack before fanning out role-based agents.
import { test, expect } from '@playwright/test';

const TABS = [
  'Swap',
  'Pools',
  'ZDEX Stats',
  'Perpetuals',
  'Strategy',
  'zUSD',
  'Oracle',
  'Confidential',
  'Keys',
];

// Console/network noise we don't want to fail the smoke on (favicon etc.).
const IGNORE = [/favicon/i, /\/branding\//i];

function collectErrors(page, sink) {
  page.on('console', (msg) => {
    if (msg.type() === 'error') sink.console.push(msg.text());
  });
  page.on('pageerror', (err) => sink.page.push(String(err)));
  page.on('requestfailed', (req) => {
    const url = req.url();
    if (IGNORE.some((re) => re.test(url))) return;
    sink.requests.push(`${req.failure()?.errorText || 'failed'} ${url}`);
  });
  page.on('response', (res) => {
    if (res.status() >= 500) sink.requests.push(`HTTP ${res.status()} ${res.url()}`);
  });
}

test('app shell loads and is not a blank/error page', async ({ page }) => {
  const errors = { console: [], page: [], requests: [] };
  collectErrors(page, errors);
  await page.goto('/', { waitUntil: 'domcontentloaded' });
  // The SPA should hydrate something visible, not a blank body.
  await expect(page.locator('body')).not.toBeEmpty();
  await page.waitForLoadState('networkidle').catch(() => {});
  await page.screenshot({ path: 'test-results/screens/00-landing.png', fullPage: true });
  // A hard crash (uncaught pageerror) is a smoke failure; console errors are
  // reported but tolerated here (agents triage them).
  expect(errors.page, `uncaught page errors:\n${errors.page.join('\n')}`).toEqual([]);
});

for (const [i, tab] of TABS.entries()) {
  test(`tab renders: ${tab}`, async ({ page }) => {
    const errors = { console: [], page: [], requests: [] };
    collectErrors(page, errors);
    await page.goto('/', { waitUntil: 'domcontentloaded' });
    await page.waitForLoadState('networkidle').catch(() => {});

    // Click the nav control whose accessible name / text matches the tab.
    const byRole = page.getByRole('button', { name: tab, exact: true });
    const byText = page.getByText(tab, { exact: true }).first();
    if (await byRole.count()) {
      await byRole.first().click();
    } else {
      await byText.click();
    }
    await page.waitForTimeout(800); // allow surface mount + first fetch
    await page.waitForLoadState('networkidle').catch(() => {});

    const idx = String(i + 1).padStart(2, '0');
    const slug = tab.toLowerCase().replace(/[^a-z0-9]+/g, '-');
    await page.screenshot({ path: `test-results/screens/${idx}-${slug}.png`, fullPage: true });

    // The surface mounted without an uncaught crash or a 5xx from its API.
    expect(errors.page, `uncaught error on ${tab}:\n${errors.page.join('\n')}`).toEqual([]);
    const fivexx = errors.requests.filter((r) => r.startsWith('HTTP 5'));
    expect(fivexx, `5xx on ${tab}:\n${fivexx.join('\n')}`).toEqual([]);
  });
}

test('design DNA: tabular numerics are globally enforced', async ({ page }) => {
  await page.goto('/', { waitUntil: 'domcontentloaded' });
  const fvn = await page.evaluate(
    () => getComputedStyle(document.body).fontVariantNumeric,
  );
  // The skill mandates lining-nums tabular-nums on body so digits don't shift.
  expect(fvn).toContain('tabular-nums');
});
