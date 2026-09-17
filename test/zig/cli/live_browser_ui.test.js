// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

// Optional browser acceptance: use caller-supplied Playwright/Chrome.
import assert from 'node:assert/strict';
import { readFile, writeFile, mkdir, mkdtemp, rm, rename } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join, resolve, dirname } from 'node:path';
import { spawn } from 'node:child_process';
import { once } from 'node:events';
import net from 'node:net';
import { browserTest, browserOptions, browserAssets } from './browser-test.js';

browserTest('live compilation, source refresh, progress, history and recovery', async () => {
  const { binary, chromium, chrome, screenshots } = await browserOptions('live_browser_ui_smoke');
  const directory = await mkdtemp(join(tmpdir(), 'oksolc-live-ui-'));
  const fixture = JSON.parse(await readFile(new URL('./browser-ui.json', import.meta.url), 'utf8'));
  for (const [name, source] of Object.entries(fixture.sources)) {
    await mkdir(dirname(join(directory, name)), { recursive: true });
    await writeFile(join(directory, name), source.content);
  }
  await mkdir(join(directory, '.git'));
  const socket = net.createServer();
  socket.listen(0, '127.0.0.1'); await once(socket, 'listening');
  const port = socket.address().port;
  await new Promise((resolve) => socket.close(resolve));
  const service = spawn(resolve(binary), ['serve', '--browse', '--no-cache', '--database', ':memory:', '--port', String(port), '--poll-ms', '50'], { cwd: directory });
  let log = '';
  service.stderr.on('data', (bytes) => { log += bytes; });
  service.stdout.resume();
  const browser = await chromium.launch({ executablePath: chrome, headless: true });
  try {
    const url = `http://127.0.0.1:${port}`;
    for (let attempt = 0; ; attempt++) {
      try { if ((await fetch(`${url}/api/status`)).ok) break; } catch {}
      assert.ok(attempt < 600 && service.exitCode === null, log);
      await Bun.sleep(50);
    }
    const page = await browser.newPage({ viewport: { width: 1440, height: 950 } });
    page.setDefaultTimeout(15000);
    await browserAssets(page);
    const errors = [];
    page.on('pageerror', (error) => errors.push(error.message));
    // Hold only the presentation state at an initial compile. Source browsing
    // still reads the real connection-local workspace. The Zig blocked-compiler
    // test separately verifies the actual backend's pending state and progress.
    let pending = true, progress = { stage: 'generating_contracts', completed_items: 1, total_items: 3, item_name: 'src/Vault.sol:Vault' };
    await page.route('**/api/status?*', async (route) => {
      const response = await route.fetch();
      const status = await response.json();
      await route.fulfill({ response, json: pending ? { ...status, latest: null, current: null, phase: 'compiling', failure: null, progress: { ...status.progress, ...progress } } : status });
    });
    await page.route('**/api/compilations?*', async (route) => {
      if (pending) await route.fulfill({ json: [] });
      else await route.continue();
    });
    await page.goto(url);
    await page.locator('.code-line').first().waitFor();
    assert.equal(await page.locator('#compilation').inputValue(), '0');
    assert.equal(await page.locator('#live-progress').getAttribute('value'), '1');
    assert.equal(await page.locator('#live-progress').getAttribute('max'), '3');
    assert.equal(await page.locator('#progress-count').innerText(), '1 / 3');
    assert.equal(await page.locator('#download-output').isVisible(), false);
    assert.equal(await page.locator('#download-request').isVisible(), false);
    assert.ok(await page.locator('.token-keyword').count() > 10);
    await page.getByRole('button', { name: 'ABI', exact: true }).click();
    await page.getByText('Available after compilation', { exact: true }).waitFor();
    await page.getByRole('button', { name: 'Source', exact: true }).click();
    await page.locator('.code-line').first().waitFor();
    await mkdir(screenshots, { recursive: true });
    await page.screenshot({ path: join(screenshots, 'live-browser-compiling.png') });
    assert.equal(await page.locator('.code-line').count(), fixture.sources['src/Vault.sol'].content.split('\n').length);
    assert.equal(await page.getByRole('button', { name: /Previous|Next/ }).count(), 0);
    await page.getByRole('button', { name: 'Go to line', exact: true }).click();
    await page.getByRole('spinbutton', { name: 'Go to line' }).fill('251');
    await page.getByRole('spinbutton', { name: 'Go to line' }).press('Enter');
    await page.locator('#L251.active').waitFor();
    progress = { stage: 'analyzing_sources', completed_items: 0, total_items: 0, item_name: '' };
    await page.waitForFunction(() => !document.getElementById('live-progress').hasAttribute('value'));
    assert.equal(await page.locator('#progress-count').innerText(), '');
    await page.emulateMedia({ reducedMotion: 'reduce' });
    assert.equal(await page.locator('#live-progress').evaluate((node) => getComputedStyle(node).animationName), 'none');
    await page.locator('#search').fill('NewSource');
    await writeFile(join(directory, 'src/NewSource.sol'), 'pragma solidity >=0.0.0; contract NewSource {}');
    await page.locator('#search-results a').filter({ hasText: 'src/NewSource.sol' }).first().waitFor();
    await page.locator('#L251.active').waitFor();
    assert.equal(await page.locator('#search').inputValue(), 'NewSource');
    await page.locator('#search-results a').filter({ hasText: 'src/NewSource.sol' }).first().click();
    await page.waitForFunction(() => document.getElementById('filename').textContent === 'NewSource.sol');
    await page.locator('#search').fill('');
    await page.locator('#tree a[data-source="src/Vault.sol"]').click();
    await page.locator('#L251').waitFor();
    await page.getByRole('button', { name: 'Go to line', exact: true }).click();
    await page.getByRole('spinbutton', { name: 'Go to line' }).fill('251');
    await page.getByRole('spinbutton', { name: 'Go to line' }).press('Enter');
    await page.locator('#L251.active').waitFor();
    await page.setViewportSize({ width: 390, height: 844 });
    progress = { stage: 'generating_contracts', completed_items: 2, total_items: 3, item_name: 'src/Vault.sol:Vault' };
    await page.getByText('2 / 3', { exact: true }).waitFor();
    assert.ok(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth));
    await page.screenshot({ path: join(screenshots, 'live-browser-compiling-mobile.png') });
    await page.setViewportSize({ width: 1440, height: 950 });
    // Reopening an automatically written workspace URL must still follow its
    // completed output, including when the user is waiting on an artifact tab.
    await page.getByRole('button', { name: 'ABI', exact: true }).click();
    await page.getByText('Available after compilation', { exact: true }).waitFor();
    await page.reload();
    await page.getByText('Available after compilation', { exact: true }).waitFor();
    assert.equal(await page.locator('#compilation').inputValue(), '0');
    for (let attempt = 0; ; attempt++) {
      const status = await (await fetch(`${url}/api/status`)).json();
      if (status.phase === 'watching') break;
      assert.ok(attempt < 600, log);
      await Bun.sleep(50);
    }
    pending = false;
    await page.getByText('Watching src · following latest', { exact: true }).waitFor();
    assert.equal(await page.getByText('Available after compilation', { exact: true }).count(), 0);
    assert.equal(await page.locator('[data-tab="abi"]').getAttribute('aria-current'), 'page');
    await page.getByRole('button', { name: 'Bytecode', exact: true }).click();
    await page.getByRole('heading', { name: 'Creation bytecode', exact: true }).waitFor();
    await page.getByRole('button', { name: 'Source', exact: true }).click();
    await page.locator('#L251.active').waitFor();
    assert.equal(await page.locator('#compilation-progress').isVisible(), false);
    assert.equal(await page.locator('#download-output').isVisible(), true);
    assert.equal(await page.locator('#toast').isVisible(), false);
    await page.locator('.code-line').first().waitFor();
    assert.equal(await page.locator('#filename').innerText(), 'Vault.sol');
    const withAddition = await page.locator('#compilation').inputValue();
    await rm(join(directory, 'src/NewSource.sol'));
    await page.waitForFunction((previous) => document.getElementById('compilation').value !== previous, withAddition);
    await page.locator('#L251.active').waitFor();
    const first = await page.locator('#compilation').inputValue();
    pending = true;
    await page.waitForFunction(() => document.getElementById('live-bar').dataset.phase === 'compiling');
    await page.locator('#compilation').selectOption('0');
    await page.waitForFunction(() => document.getElementById('compilation').value === '0');
    assert.equal(await page.locator('#compilation').inputValue(), '0');
    await page.locator('#L251.active').waitFor();
    pending = false;
    await page.getByText('Watching src · following latest', { exact: true }).waitFor();
    await page.waitForFunction((first) => document.getElementById('compilation').value === first, first);
    const math = join(directory, 'lib/Math.sol');
    await writeFile(math, fixture.sources['lib/Math.sol'].content.replace('value * 2', 'value * 3'));
    await page.waitForFunction((first) => document.getElementById('compilation').value !== first, first);
    await page.locator('#L251.active').waitFor();
    assert.equal(await page.locator('#filename').innerText(), 'Vault.sol');
    assert.equal(new URLSearchParams(new URL(page.url()).hash.slice(1)).get('symbol'), null);
    const second = await page.locator('#compilation').inputValue();
    await page.locator('#compilation').selectOption(first);
    await page.getByText(`Watching src · viewing snapshot #${first}`, { exact: true }).waitFor();
    await page.locator('#L251.active').waitFor();
    await writeFile(math, fixture.sources['lib/Math.sol'].content.replace('value * 2', 'value * 4'));
    await page.waitForFunction((second) => [...document.querySelectorAll('#compilation option')].some((option) => Number(option.value) > Number(second)), second);
    assert.equal(await page.locator('#compilation').inputValue(), first);
    await page.getByRole('button', { name: 'Follow latest', exact: true }).click();
    await page.getByText('Watching src · following latest', { exact: true }).waitFor();
    await page.getByRole('button', { name: 'ABI', exact: true }).click();
    await page.locator('.abi-entry').first().waitFor();
    await mkdir(screenshots, { recursive: true });
    await page.screenshot({ path: join(screenshots, 'live-browser-output.png') });
    await rename(join(directory, 'src'), join(directory, 'src-away'));
    await page.waitForFunction(() => document.getElementById('live-bar').dataset.phase === 'stale');
    assert.match(await page.locator('#live-status').innerText(), /Output is stale/);
    await page.screenshot({ path: join(screenshots, 'live-browser-stale.png') });
    await rename(join(directory, 'src-away'), join(directory, 'src'));
    await page.getByText('Watching src · following latest', { exact: true }).waitFor();
    // Deleting the selected file must choose an available source in the new view.
    await page.getByRole('button', { name: 'Source', exact: true }).click();
    await writeFile(join(directory, 'src/Other.sol'), 'pragma solidity >=0.0.0; contract Other {}');
    await rm(join(directory, 'src/Vault.sol'));
    await page.waitForFunction(() => document.getElementById('filename').textContent === 'Other.sol');
    await page.locator('.code-line').first().waitFor();
    await page.setViewportSize({ width: 390, height: 844 });
    assert.ok(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth));
    await page.screenshot({ path: join(screenshots, 'live-browser-mobile.png') });
    assert.deepEqual(errors, []);
    console.log('live UI: pending workspace, stage progress, indeterminate/reduced-motion states, live search, source location, completion, pinned history, stale/recovery, deletion fallback and mobile layout passed');
  } finally {
    await browser.close();
    service.kill('SIGTERM');
    if (service.exitCode === null) await once(service, 'exit');
    await rm(directory, { recursive: true, force: true });
  }
}, 180_000);
