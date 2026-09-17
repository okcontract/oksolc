// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

// Actual compiler ABI/objects, browser clipboard/downloads and native layout.
import assert from 'node:assert/strict';
import { readFile, writeFile, mkdir, mkdtemp, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { spawn, spawnSync } from 'node:child_process';
import { once } from 'node:events';
import net from 'node:net';
import { browserTest, browserOptions, browserAssets } from './browser-test.js';

browserTest('ABI inspection, bytecode, exports, compiler parity and live edits', async () => {
  const { binary, chromium, chrome, screenshots } = await browserOptions('artifact_ui_smoke');
  const directory = await mkdtemp(join(tmpdir(), 'oksolc-artifact-ui-'));
  await mkdir(join(directory, '.git')); await mkdir(join(directory, 'src'));
  await writeFile(join(directory, 'src/Types.sol'), `// Copyright (C) 2026 OKcontract Pte. Ltd.
pragma solidity >=0.0.0;
/// @title Typed orders
/// @notice Inspect an order before submitting it.
contract Types {
  struct Order { address owner; uint256[] amounts; }
  address public immutable owner;
  /// @notice An order was sent.
  event Sent(address indexed sender, bytes data);
  /// @notice The owner is not valid.
  error Refused(uint256 reason);
  /// @notice Create an order book.
  /// @param initialOwner The owner of this instance.
  constructor(address initialOwner) { if (initialOwner == address(0)) revert Refused(0); owner = initialOwner; }
  /// @notice Submit <b>an order</b> without changing it.
  /// @dev The order is returned verbatim.
  /// @param order The owner and requested amounts.
  /// @return Unchanged order.
  function submit(Order calldata order) external pure returns (Order memory) { return order; }
  /// @notice Submit a single value.
  function submit(uint256 value) external pure returns (uint256) { return value; }
  receive() external payable {}
  fallback() external payable {}
}
library External { function value() public pure returns (uint256) { return 1; } }
contract Linked { function value() external pure returns (uint256) { return External.value(); } }
interface Empty {}
`);
  const socket = net.createServer(); socket.listen(0, '127.0.0.1'); await once(socket, 'listening');
  const port = socket.address().port; await new Promise((resolve) => socket.close(resolve));
  const service = spawn(resolve(binary), ['serve', '--browse', '--no-cache', '--database', ':memory:', '--port', String(port)], { cwd: directory });
  let log = ''; service.stderr.on('data', (bytes) => { log += bytes; }); service.stdout.resume();
  const browser = await chromium.launch({ executablePath: chrome, headless: true });
  try {
    const url = `http://127.0.0.1:${port}`;
    for (let attempt = 0; ; attempt++) {
      try { if ((await (await fetch(`${url}/api/status`)).json()).phase === 'watching') break; } catch {}
      assert.ok(attempt < 600 && service.exitCode === null, log);
      await Bun.sleep(50);
    }
    const output = await (await fetch(`${url}/api/output`)).json();
    assert.ok(!output.errors?.some((error) => error.severity === 'error'), JSON.stringify(output.errors));
    const contracts = output.contracts['src/Types.sol'], data = contracts.Types;
    // Inspection fields must not change ABI, metadata or either bytecode object.
    const request = await (await fetch(`${url}/api/request`)).json();
    request.settings.outputSelection = { '*': { '*': ['abi', 'metadata', 'evm.bytecode.object', 'evm.deployedBytecode.object'] } };
    const ordinary = spawnSync(resolve(binary), ['standard-json', '--no-cache'], { input: JSON.stringify(request), encoding: 'utf8', timeout: 120000, maxBuffer: 16 * 1024 * 1024 });
    assert.equal(ordinary.status, 0, ordinary.stderr);
    const plain = JSON.parse(ordinary.stdout);
    assert.ok(!plain.errors?.some((error) => error.severity === 'error'), ordinary.stdout);
    for (const [name, contract] of Object.entries(contracts)) {
      const original = plain.contracts['src/Types.sol'][name];
      assert.deepEqual(contract.abi, original.abi);
      assert.equal(contract.metadata, original.metadata);
      assert.equal(contract.evm.bytecode.object, original.evm.bytecode.object);
      assert.equal(contract.evm.deployedBytecode.object, original.evm.deployedBytecode.object);
    }
    const page = await browser.newPage({ viewport: { width: 1440, height: 950 } });
    await browserAssets(page);
    await page.context().grantPermissions(['clipboard-read', 'clipboard-write'], { origin: url });
    await mkdir(screenshots, { recursive: true });
    const errors = []; page.on('pageerror', (error) => errors.push(error.message));
    await page.goto(`${url}/#source=src%2FTypes.sol&tab=abi&contract=Types`);
    await page.locator('.abi-entry').first().waitFor();
    assert.equal(await page.locator('.abi-entry').count(), data.abi.length);
    assert.equal(await page.locator('.inspector').isVisible(), false);
    await page.getByText('Typed orders', { exact: true }).waitFor();
    const search = page.getByRole('searchbox', { name: 'Search ABI', exact: true });
    const selector = data.evm.methodIdentifiers['submit((address,uint256[]))'];
    assert.match(selector, /^[0-9a-f]{8}$/);
    await search.fill(selector);
    assert.equal(await page.locator('.abi-entry').count(), 1);
    assert.equal(await page.locator('.abi-selector').innerText(), `0x${selector}`);
    await search.fill('returned verbatim');
    assert.equal(await page.locator('.abi-entry').count(), 1);
    await search.fill('requested amounts');
    assert.equal(await page.locator('.abi-entry').count(), 1);
    await search.fill('submit');
    assert.equal(await page.locator('.abi-entry').count(), 2);
    const tuple = page.locator('.abi-entry').filter({ hasText: 'submit((address,uint256[]))' });
    await tuple.locator('summary').first().click();
    await tuple.getByText('Submit <b>an order</b> without changing it.', { exact: true }).waitFor();
    assert.equal(await tuple.locator('.artifact-description b').count(), 0);
    await tuple.getByText('The owner and requested amounts.', { exact: true }).waitFor();
    await tuple.getByText('Unchanged order.', { exact: true }).waitFor();
    await tuple.getByRole('button', { name: 'Copy selector', exact: true }).click();
    await tuple.getByRole('button', { name: 'Copied', exact: true }).waitFor();
    assert.equal(await page.evaluate(() => navigator.clipboard.readText()), `0x${selector}`);
    await tuple.getByRole('button', { name: 'Copy selector', exact: true }).waitFor();
    await tuple.getByRole('button', { name: 'Copy signature', exact: true }).click();
    await tuple.getByRole('button', { name: 'Copied', exact: true }).waitFor();
    assert.equal(await page.evaluate(() => navigator.clipboard.readText()), 'submit((address,uint256[]))');
    await tuple.locator('.abi-components > summary').first().click();
    assert.match(await tuple.innerText(), /owner/);
    assert.match(await tuple.innerText(), /amounts/);
    await page.screenshot({ path: join(screenshots, 'abi-documentation.png') });
    await search.fill('');
    await page.getByRole('combobox', { name: 'ABI kind', exact: true }).selectOption('event');
    assert.equal(await page.locator('.abi-entry').count(), 1);
    await page.locator('.abi-entry > summary').click();
    await page.getByText('indexed', { exact: true }).waitFor();
    await page.getByText('An order was sent.', { exact: true }).waitFor();
    assert.equal(await page.locator('.abi-selector').count(), 0);
    await page.getByRole('combobox', { name: 'ABI kind', exact: true }).selectOption('error');
    await page.locator('.abi-entry > summary').click();
    await page.getByText('The owner is not valid.', { exact: true }).waitFor();
    await page.getByRole('combobox', { name: 'ABI kind', exact: true }).selectOption('constructor');
    await page.locator('.abi-entry > summary').click();
    await page.getByText('Create an order book.', { exact: true }).waitFor();
    await page.getByText('The owner of this instance.', { exact: true }).waitFor();
    await page.getByRole('combobox', { name: 'ABI kind', exact: true }).selectOption('');
    await page.getByRole('button', { name: 'Copy ABI', exact: true }).click();
    await page.getByRole('button', { name: 'Copied', exact: true }).waitFor();
    assert.deepEqual(JSON.parse(await page.evaluate(() => navigator.clipboard.readText())), data.abi);
    const abiDownload = page.waitForEvent('download');
    await page.getByRole('button', { name: 'Download ABI', exact: true }).click();
    assert.deepEqual(JSON.parse(await readFile(await (await abiDownload).path(), 'utf8')), data.abi);
    await page.screenshot({ path: join(screenshots, 'abi-desktop.png') });
    await search.fill('no-such-function');
    await page.getByText('No ABI entries match these filters.', { exact: true }).waitFor();
    await search.fill('');
    await page.getByRole('button', { name: 'Bytecode', exact: true }).click();
    await page.locator('.bytecode-panel').first().waitFor();
    for (const [index, object] of [data.evm.bytecode.object, data.evm.deployedBytecode.object].entries()) {
      const panel = page.locator('.bytecode-panel').nth(index);
      assert.equal(await panel.locator('.bytecode-size strong').innerText(), (object.length / 2).toLocaleString());
      await panel.getByRole('button', { name: 'Copy bytecode', exact: true }).click();
      await panel.getByRole('button', { name: 'Copied', exact: true }).waitFor();
      assert.equal(await page.evaluate(() => navigator.clipboard.readText()), `0x${object}`);
      const file = page.waitForEvent('download');
      await panel.getByRole('button', { name: 'Download .bin', exact: true }).click();
      assert.equal(await readFile(await (await file).path(), 'utf8'), object);
    }
    await page.screenshot({ path: join(screenshots, 'bytecode-desktop.png') });
    const runtime = page.locator('.bytecode-panel').nth(1);
    await runtime.getByText('Immutable patch locations', { exact: true }).click();
    await runtime.locator('.bytecode-references tbody tr').first().waitFor();
    const locations = Object.entries(data.evm.deployedBytecode.immutableReferences).flatMap(([id, sites]) => sites.map((site) => [id, site.start.toLocaleString(), site.length.toLocaleString()]));
    assert.ok(locations.length);
    assert.deepEqual(await runtime.locator('.bytecode-references tbody tr').evaluateAll((rows) => rows.map((row) => [...row.cells].map((cell) => cell.textContent))), locations);
    await page.setViewportSize({ width: 390, height: 844 });
    assert.ok(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth));
    assert.ok(await page.locator('.bytecode-panel').first().evaluate((node) => node.scrollWidth <= node.clientWidth));
    await page.screenshot({ path: join(screenshots, 'bytecode-mobile.png') });
    await page.getByRole('combobox', { name: 'Contract', exact: true }).selectOption('Linked');
    await page.getByText('Unlinked bytecode · library addresses are required.', { exact: true }).first().waitFor();
    for (const [index, code] of [contracts.Linked.evm.bytecode, contracts.Linked.evm.deployedBytecode].entries()) {
      const panel = page.locator('.bytecode-panel').nth(index);
      await panel.getByText('Library link locations', { exact: true }).click();
      await panel.locator('.bytecode-references tbody tr').first().waitFor();
      const expected = Object.entries(code.linkReferences).flatMap(([source, libraries]) => Object.entries(libraries).flatMap(([name, sites]) => sites.map((site) => [`${source}:${name}`, site.start.toLocaleString(), site.length.toLocaleString()])));
      assert.ok(expected.length);
      assert.deepEqual(await panel.locator('.bytecode-references tbody tr').evaluateAll((rows) => rows.map((row) => [...row.cells].map((cell) => cell.textContent))), expected);
    }
    assert.ok(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth));
    await page.screenshot({ path: join(screenshots, 'bytecode-linking-mobile.png') });
    await page.getByRole('combobox', { name: 'Contract', exact: true }).selectOption('Empty');
    await page.getByText('No executable bytecode was emitted.', { exact: true }).first().waitFor();
    await page.getByRole('button', { name: 'ABI', exact: true }).click();
    await page.getByText('This contract has an empty ABI.', { exact: true }).waitFor();
    await page.getByRole('combobox', { name: 'Contract', exact: true }).selectOption('Types');
    await page.locator('.abi-entry').first().waitFor();
    const previous = await page.locator('#compilation').inputValue();
    await search.fill('submit');
    await writeFile(join(directory, 'src/Types.sol'), await readFile(join(directory, 'src/Types.sol'), 'utf8') + '\n// live edit\n');
    await page.waitForFunction((id) => document.getElementById('compilation').value !== id, previous);
    assert.equal(await search.inputValue(), 'submit');
    assert.equal(await page.locator('.abi-entry').count(), 2);
    await search.fill('');
    assert.ok(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth));
    await page.screenshot({ path: join(screenshots, 'abi-mobile.png') });
    await page.setViewportSize({ width: 1440, height: 950 });
    await page.emulateMedia({ colorScheme: 'dark' });
    await page.screenshot({ path: join(screenshots, 'abi-dark.png') });
    await page.locator('#summary button').first().click();
    await page.locator('.inspector').waitFor({ state: 'visible' });
    assert.equal(await page.locator('[data-panel="diagnostics"]').getAttribute('aria-pressed'), 'true');
    assert.deepEqual(errors, []);
    assert.equal(await page.locator('#toast').isVisible(), false);
    console.log('artifact UI: real documented/overloaded ABI, selector search/copy, literal NatSpec, compiler output parity, exact exports, immutable/library byte locations, live edits and light/dark/mobile layout passed');
  } finally {
    await browser.close(); service.kill('SIGTERM');
    if (service.exitCode === null) await once(service, 'exit');
    await rm(directory, { recursive: true, force: true });
  }
}, 180_000);
