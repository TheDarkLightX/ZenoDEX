import { test, expect } from '@playwright/test';

test('nested liquidity confirmation closes top dialog first and keeps body locked', async ({ page }) => {
  await page.route('**/zenodex-config.json', async (route) => {
    await route.fulfill({
      status: 200,
      contentType: 'application/json',
      body: JSON.stringify({
        deployment: 'local-testnet',
        chainId: 'zeno-ledger-localtest-v0',
        apiBase: '',
        demoMode: true,
        allowDemoMode: true,
      }),
    });
  });
  const walletAddress = '0x'.concat('a'.repeat(96));
  await page.goto(`/?demo=true&tab=pools&walletAddress=${walletAddress}`, { waitUntil: 'domcontentloaded' });
  await page.waitForLoadState('networkidle').catch(() => {});

  await expect(page.getByRole('heading', { name: 'Liquidity Pools' })).toBeVisible();
  await page.getByRole('button', { name: 'Add Liquidity' }).first().click();

  const parentDialog = page.getByRole('dialog', { name: 'Add Liquidity' });
  await expect(parentDialog).toBeVisible();
  await expect(page.locator('body')).toHaveClass(/modal-open/);

  await parentDialog.getByRole('button', { name: /Balanced/ }).click();
  const amountInputs = parentDialog.locator('input.input-amount');
  await amountInputs.nth(0).fill('10');
  await amountInputs.nth(1).fill('1');
  await parentDialog.getByRole('button', { name: 'Add Liquidity' }).click();

  const childDialog = page.getByRole('dialog').filter({ hasText: 'Imbalanced Liquidity' });
  await expect(childDialog).toBeVisible();
  await expect(page.getByRole('dialog')).toHaveCount(2);

  await page.keyboard.press('Escape');
  await expect(childDialog).toHaveCount(0);
  await expect(parentDialog).toBeVisible();
  await expect(page.locator('body')).toHaveClass(/modal-open/);

  await page.keyboard.press('Escape');
  await expect(page.getByRole('dialog')).toHaveCount(0);
  await expect(page.locator('body')).not.toHaveClass(/modal-open/);
});
