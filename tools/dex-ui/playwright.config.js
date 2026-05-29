// Playwright config for driving the LIVE local-testnet GUI.
//
// This is the browser-automation harness the zenodex-frontend skill assumes
// exists (it did not, until now). It points at the real local-testnet stack
// served by nginx on 127.0.0.1:18080 (brought up via
// `python3 tools/zenoctl.py testnet local up`), NOT a vite dev server — so the
// tests exercise the production-built bundle the same way a real user would.
//
// Override the target with PW_BASE_URL when pointing at a different stack.
import { defineConfig, devices } from '@playwright/test';

const BASE_URL = process.env.PW_BASE_URL || 'http://127.0.0.1:18080';

export default defineConfig({
  testDir: './tests',
  // The shared live stack is stateful; keep cross-file isolation but allow
  // in-file sequencing. One worker by default avoids ledger contention between
  // specs; raise with PW_WORKERS for read-only/visual suites.
  workers: Number(process.env.PW_WORKERS || 1),
  fullyParallel: false,
  forbidOnly: !!process.env.CI,
  retries: process.env.CI ? 1 : 0,
  timeout: 45_000,
  expect: { timeout: 10_000 },
  reporter: [
    ['list'],
    ['json', { outputFile: 'test-results/results.json' }],
  ],
  outputDir: 'test-results/artifacts',
  use: {
    baseURL: BASE_URL,
    headless: true,
    screenshot: 'only-on-failure',
    trace: 'retain-on-failure',
    video: 'off',
    // chromium-headless-shell is what `npx playwright install chromium` fetched.
    channel: undefined,
  },
  projects: [
    {
      name: 'chromium',
      use: { ...devices['Desktop Chrome'] },
    },
  ],
});
