// Design-DNA regression checks (skill section 8). Run against the live bundle
// or, for unreleased fixes, a dev/preview server via PW_BASE_URL.
import { test, expect } from '@playwright/test';

async function entranceDurationMs(page) {
  const animated = page.locator('.animate-fade-in, .animate-slide-up, .animate-scale-in').first();
  await expect(animated).toBeVisible();
  return animated.evaluate((el) => {
    const d = getComputedStyle(el).animationDuration; // "0.25s" | "1e-05s" | "..ms"
    return parseFloat(d) * (d.trim().endsWith('ms') ? 1 : 1000);
  });
}

test('animations collapse to ~instant when reduced motion is requested', async ({ page }) => {
  // emulateMedia is the reliable lever (test.use({reducedMotion}) did not apply
  // here). The global @media (prefers-reduced-motion: reduce) guard forces
  // animation-duration to 0.01ms.
  await page.emulateMedia({ reducedMotion: 'reduce' });
  await page.goto('/', { waitUntil: 'domcontentloaded' });
  await page.waitForLoadState('networkidle').catch(() => {});
  expect(await entranceDurationMs(page)).toBeLessThan(5);
});

test('entrance animations actually play (non-zero) without a reduced-motion request', async ({ page }) => {
  // Guards the malformed-shorthand regression: the .animate-* rules previously
  // expanded to "fadeIn 250ms ease ease-out" (two timing functions = invalid),
  // silently disabling the entrance motion. They must be a valid ~250ms+.
  await page.emulateMedia({ reducedMotion: 'no-preference' });
  await page.goto('/', { waitUntil: 'domcontentloaded' });
  expect(await entranceDurationMs(page)).toBeGreaterThan(50);
});
