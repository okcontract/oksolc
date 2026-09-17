// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

import { test } from 'bun:test';
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import { once } from 'node:events';
import { mkdir, readFile } from 'node:fs/promises';
import { join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import net from 'node:net';

// Browser dependencies are caller-supplied; the default Bun run reports these
// integration cases as skipped. Opting in requires an actual Playwright module.
export const browserTest = test.skipIf(Bun.env.OKSOLC_BROWSER_TESTS !== '1');

export async function browserOptions(name) {
  assert.ok(Bun.env.OKSOLC_PLAYWRIGHT, 'Set OKSOLC_PLAYWRIGHT to the installed Playwright index.mjs');
  const { chromium } = await import(pathToFileURL(resolve(Bun.env.OKSOLC_PLAYWRIGHT)).href);
  const binary = resolve(Bun.env.OKSOLC_BINARY || fileURLToPath(new URL('../../../zig-out/bin/oksolc', import.meta.url)));
  const screenshots = resolve(Bun.env.OKSOLC_SCREENSHOTS || 'zig-out/browser-tests', name);
  await mkdir(screenshots, { recursive: true });
  return { binary, chromium, chrome: Bun.env.OKSOLC_CHROME, screenshots };
}

export async function browserAssets(page) {
  const directory = Bun.env.OKSOLC_UI_ASSETS;
  if (!directory) return;
  for (const [path, name, contentType] of [['/', 'index.html', 'text/html'], ['/app.js', 'app.js', 'text/javascript'], ['/style.css', 'style.css', 'text/css']]) {
    await page.route((url) => url.pathname === path, async (route) => route.fulfill({ contentType, body: await readFile(join(directory, name)) }));
  }
}

export async function startArchive(binary) {
  const socket = net.createServer();
  socket.listen(0, '127.0.0.1'); await once(socket, 'listening');
  const port = socket.address().port;
  await new Promise((resolve) => socket.close(resolve));
  const service = spawn(binary, ['browse', '--no-cache', '--database', ':memory:', '--request', fileURLToPath(new URL('./browser-ui.json', import.meta.url)), '--port', String(port)]);
  let log = '';
  service.stderr.on('data', (data) => { log += data; }); service.stdout.resume();
  const close = async () => {
    if (service.exitCode === null && service.signalCode === null) { service.kill('SIGTERM'); await once(service, 'exit'); }
  };
  const url = `http://127.0.0.1:${port}`;
  try {
    for (let attempt = 0; ; attempt++) {
      try { if ((await fetch(url + '/api/status')).ok) break; } catch {}
      assert.ok(attempt < 600 && service.exitCode === null, log);
      await Bun.sleep(50);
    }
    return { url, close };
  } catch (error) { await close(); throw error; }
}
