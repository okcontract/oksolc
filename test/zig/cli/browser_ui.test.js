// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

// Optional real-browser check using the documented Vault/Math fixture. The
// Playwright package and Chrome are supplied by the caller, never by the app.
import assert from 'node:assert/strict';
import { browserTest, browserOptions, browserAssets, startArchive } from './browser-test.js';

browserTest('archive navigation, complete source buffers, artifacts and responsive layouts', async () => {
  const { binary, chromium, chrome, screenshots } = await browserOptions('browser_ui_smoke');
  const archive = await startArchive(binary);
  const url = archive.url;
  const browser = await chromium.launch({ executablePath: chrome, headless: true });
  try {
    const page = await browser.newPage({ viewport: { width: 1440, height: 950 }, colorScheme: 'light' });
    await browserAssets(page);
    const errors = [];
    page.on('pageerror', (error) => errors.push(error.message));
    await page.goto(`${url}/#source=src%2FVault.sol`);
    await page.locator('.code-line').first().waitFor();
    assert.equal(await page.locator('#filename').innerText(), 'Vault.sol');
    assert.ok(await page.locator('.token-keyword').count() > 10);
    assert.equal(await page.evaluate(() => window.sourceExecuted), undefined);
    assert.equal(await page.locator('.topbar #filename').count(), 1);
    assert.equal(await page.locator('.source-toolbar').count(), 0);
    assert.ok((await page.locator('.code-line').first().boundingBox()).y < 150);
    const filteredDiagnostics = await (await page.request.get(`${url}/api/diagnostics?hide_libraries=1`)).json();
    const allDiagnostics = await (await page.request.get(`${url}/api/diagnostics`)).json();
    assert.ok(filteredDiagnostics.length < allDiagnostics.length);
    await page.locator('#diagnostics-summary').click();
    const libraryFilter = page.getByRole('checkbox', { name: 'Hide library diagnostics' });
    assert.equal(await libraryFilter.isChecked(), true);
    await page.locator('#details .card').first().waitFor();
    assert.equal(await page.locator('#details .card').count(), filteredDiagnostics.length);
    assert.equal(await page.locator('#diagnostics-summary').innerText(), `${filteredDiagnostics.length} diagnostics`);
    await libraryFilter.uncheck();
    await page.getByText('Showing diagnostics from all sources', { exact: true }).waitFor();
    assert.equal(await page.locator('#details .card').count(), allDiagnostics.length);
    assert.equal(await page.locator('#diagnostics-summary').innerText(), `${allDiagnostics.length} diagnostics`);
    await libraryFilter.check();
    await page.getByText(`${allDiagnostics.length - filteredDiagnostics.length} library diagnostics hidden`, { exact: true }).waitFor();
    await page.screenshot({ path: `${screenshots}/browser-diagnostics-filter.png` });
    await page.getByRole('button', { name: 'Outline', exact: true }).click();
    await page.screenshot({ path: `${screenshots}/browser-desktop.png` });
    await page.getByRole('link', { name: 'twice', exact: true }).click();
    await page.waitForFunction(() => document.getElementById('filename').textContent === 'Math.sol');
    await page.locator('.code-line.active').waitFor();
    assert.ok((await page.locator('.code-line.active').innerText()).includes('function twice'));
    await page.locator('#details a').first().waitFor();
    assert.ok((await page.locator('#details').innerText()).includes('src/Vault.sol'));
    await page.goBack();
    await page.waitForFunction(() => document.getElementById('filename').textContent === 'Vault.sol');
    await page.locator('.code-line').first().waitFor();
    const source = await (await page.request.get(`${url}/api/source?source=src%2FVault.sol`)).json();
    const lines = source.content.split('\n').map((line) => line.replace(/\r$/, ''));
    assert.ok(lines.length > 250);
    assert.deepEqual(await page.locator('.code-line code').allTextContents(), lines);
    assert.equal(await page.getByRole('button', { name: /Previous|Next/ }).count(), 0);
    await page.locator('.code-line').last().scrollIntoViewIfNeeded();
    assert.ok(await page.locator('#content').evaluate((node) => node.scrollTop > 0));
    // The complete buffer stays selectable across the former page boundary.
    assert.equal(await page.evaluate(() => {
      const selection = getSelection(), range = document.createRange();
      range.setStartBefore(document.querySelector('#L250 code'));
      range.setEndAfter(document.querySelector('#L251 code'));
      selection.removeAllRanges(); selection.addRange(range);
      const text = selection.toString(); selection.removeAllRanges();
      return text.includes(document.querySelector('#L250 code').textContent)
        && text.includes(document.querySelector('#L251 code').textContent);
    }), true);
    assert.equal(await page.evaluate(() => window.sourceExecuted), undefined);
    const selectedLine = await page.locator('.code-line.active').getAttribute('id');
    await page.getByRole('button', { name: 'Go to line', exact: true }).click();
    const jump = page.getByRole('spinbutton', { name: 'Go to line' });
    assert.equal(await jump.evaluate((node) => node === document.activeElement), true);
    await jump.fill('251'); await jump.press('Escape');
    await page.locator('#line-jump').waitFor({ state: 'hidden' });
    assert.equal(await page.locator('#line-position').evaluate((node) => node === document.activeElement), true);
    await page.getByRole('button', { name: 'Go to line', exact: true }).click();
    await jump.fill(String(lines.length + 1)); await jump.press('Enter');
    assert.equal(await page.locator('#line-jump:popover-open').count(), 1);
    assert.equal(await page.locator('.code-line.active').getAttribute('id'), selectedLine);
    await page.getByRole('spinbutton', { name: 'Go to line' }).fill('251');
    await page.getByRole('spinbutton', { name: 'Go to line' }).press('Enter');
    await page.locator('#L251.active').waitFor();
    assert.equal(await page.locator('.code-line').count(), lines.length);
    assert.equal(await page.locator('#L251').evaluate((node) => {
      const row = node.getBoundingClientRect(), view = document.getElementById('content').getBoundingClientRect();
      return row.top >= view.top && row.bottom <= view.bottom;
    }), true);
    await page.getByRole('button', { name: 'Go to line', exact: true }).click();
    await page.getByRole('spinbutton', { name: 'Go to line' }).fill('1');
    await page.getByRole('spinbutton', { name: 'Go to line' }).press('Enter');
    await page.locator('#L1.active').waitFor();
    assert.equal(await page.locator('#content').evaluate((node) => node.scrollTop), 0);
    await page.getByRole('button', { name: 'ABI', exact: true }).click();
    await page.locator('.abi-entry').first().waitFor();
    assert.ok((await page.locator('#content').innerText()).includes('ABI'));
    await page.getByRole('button', { name: 'Bytecode', exact: true }).click();
    await page.getByText('Creation bytecode', { exact: true }).waitFor();
    await page.getByRole('button', { name: 'Artifacts', exact: true }).click();
    await page.getByRole('button', { name: 'Browse complete compiler output' }).click();
    await page.getByText('Complete compiler output', { exact: true }).waitFor();
    await page.keyboard.press('/');
    await page.getByRole('searchbox').fill('twice');
    await page.locator('.search-hit').first().waitFor();
    assert.ok((await page.locator('#search-results').innerText()).includes('lib/Math.sol'));
    await page.keyboard.press('Escape');
    assert.equal(await page.locator('#tree').isVisible(), true);
    await page.getByRole('button', { name: 'Source', exact: true }).click();
    await page.locator('.code-line').first().waitFor();
    await page.emulateMedia({ colorScheme: 'dark' });
    await page.screenshot({ path: `${screenshots}/browser-dark.png` });
    await page.setViewportSize({ width: 390, height: 844 });
    await page.emulateMedia({ colorScheme: 'light' });
    await page.screenshot({ path: `${screenshots}/browser-mobile.png` });
    assert.equal(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth), true);
    await page.getByRole('button', { name: 'Toggle project navigation' }).click();
    assert.equal(await page.locator('#navigation').isVisible(), true);
    await page.locator('.file-link[data-source="lib/Math.sol"]').click();
    await page.waitForFunction(() => document.getElementById('filename').textContent === 'Math.sol');
    assert.equal(await page.locator('#navigation').isVisible(), false);
    // Exercise the reported filename and large-count boundary without compiling
    // a large diagnostic corpus just to check header layout.
    await page.route('**/api/summary?*', async (route) => {
      const response = await route.fetch();
      await route.fulfill({ response, json: [{ kind: 'diagnostic', status: 'warning', total: 36000, hidden: 0 }] });
    });
    await page.reload(); await page.locator('.code-line').first().waitFor();
    assert.equal(await page.locator('#diagnostics-summary').innerText(), '36K diagnostics');
    for (const width of [1440, 1024, 768, 390]) {
      await page.setViewportSize({ width, height: 950 });
      await page.locator('#filename').evaluate((node) => { node.textContent = 'PagedIndex.sol'; });
      assert.equal(await page.locator('#filename').evaluate((node) => {
        const range = document.createRange(); range.selectNodeContents(node);
        return new Set([...range.getClientRects()].map((rect) => rect.y)).size;
      }), 1);
      for (const control of ['#filename', '#diagnostics-summary', '#compilation', '#download-output']) {
        const bounds = await page.locator(control).boundingBox();
        assert.ok(bounds && bounds.x >= 0 && bounds.x + bounds.width <= width, `${width}: ${control} ${JSON.stringify(bounds)}`);
      }
      assert.equal(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth), true);
      await page.screenshot({ path: `${screenshots}/browser-layout-${width}.png` });
      await page.keyboard.press('Escape');
    }
    assert.deepEqual(errors, []);
    assert.equal(await page.locator('#toast').isVisible(), false);
    console.log('browser UI: definitions, references, history, full source scrolling/selection, line jumps, artifacts, search, XSS text handling, and responsive layouts passed');
  } finally { await browser.close(); await archive.close(); }
}, 180_000);
