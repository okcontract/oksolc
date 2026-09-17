// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

// Exercise the real frontend build helper in a small, isolated Zig project.
// This checks failure propagation and cache invalidation without recompiling Solidity.
import { test } from 'bun:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { cp, mkdir, mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
test('browser build enforces strict types, cache invalidation, deterministic embedding and tool versions', async () => {
  const zig = Bun.env.ZIG || 'zig';
  const root = fileURLToPath(new URL('../../../', import.meta.url));
  const directory = await mkdtemp(join(tmpdir(), 'oksolc-browser-build-'));
  const sources = join(directory, 'src/cli/browser');
  async function build(args = [], success = true) {
    const result = spawnSync(zig, ['build', ...args, '-j4', '--summary', 'all'], { cwd: directory, encoding: 'utf8', timeout: 120000 });
    if (result.error) throw result.error;
    const log = result.stdout + result.stderr;
    if (success) assert.equal(result.status, 0, log);
    else { assert.notEqual(result.status, 0, log); assert.ok(log.includes('tsc') || log.includes('bun'), log); }
    return log;
  }
  try {
    await mkdir(join(directory, 'build_support'), { recursive: true });
    await cp(join(root, 'build_support/browser.zig'), join(directory, 'build_support/browser.zig'));
    await cp(join(root, 'src/cli/browser'), sources, { recursive: true });
    const config = JSON.parse(await readFile(join(sources, 'tsconfig.json'), 'utf8'));
    for (const flag of ['strict', 'noUncheckedIndexedAccess', 'exactOptionalPropertyTypes', 'noEmitOnError', 'noEmit', 'allowImportingTsExtensions'])
      assert.equal(config.compilerOptions[flag], true, `${flag} must remain enabled`);
    await writeFile(join(directory, 'build.zig'), `// Copyright (C) 2026 OKcontract Pte. Ltd.
const std = @import("std");
pub fn build(b: *std.Build) void {
    const module = b.createModule(.{ .root_source_file = b.path("main.zig"), .target = b.standardTargetOptions(.{}), .optimize = .ReleaseSafe });
    @import("build_support/browser.zig").build(b, module);
    b.installArtifact(b.addExecutable(.{ .name = "embed-check", .root_module = module }));
}
`);
    await writeFile(join(directory, 'main.zig'), `// Copyright (C) 2026 OKcontract Pte. Ltd.
pub fn main() u8 { return if (@embedFile("browser_app").len > 0) 0 else 1; }
`);
    await build(['build-browser']);
    const bundlePath = join(directory, 'zig-out/browser/app.js');
    const originalBundle = await readFile(bundlePath, 'utf8');
    assert.ok(originalBundle.includes('Compiler diagnostics'));
    assert.ok(!/from ["']\.\//.test(originalBundle), 'The app must be a self-contained bundle');
    await build();

    const notesPath = join(sources, 'summary.ts');
    const notes = await readFile(notesPath, 'utf8');
    await writeFile(notesPath, notes + '\nconst invalid: string = 1;\n');
    assert.match(await build([], false), /not assignable/);
    assert.equal(await readFile(bundlePath, 'utf8'), originalBundle);
    await writeFile(notesPath, notes.replace('Compiler diagnostics across this compilation', 'Frontend cache invalidation marker.'));
    await build(['build-browser']);
    assert.ok((await readFile(bundlePath, 'utf8')).includes('Frontend cache invalidation marker.'));
    await writeFile(notesPath, notes);

    await mkdir(join(sources, 'nested'));
    const added = join(sources, 'nested/new-module.ts');
    await writeFile(added, `// Copyright (C) 2026 OKcontract Pte. Ltd.
export function implicit(value) { return value; }
export const nullable: string = null;
const items: string[] = [];
export const indexed: string = items[0];
export const optional: { value?: string } = { value: undefined };
`);
    const strictErrors = await build([], false);
    assert.match(strictErrors, /new-module/);
    assert.match(strictErrors, /TS7006/);
    assert.match(strictErrors, /TS2375/);
    assert.ok((strictErrors.match(/TS2322/g) || []).length >= 2);
    await rm(added);
    await build(['build-browser']);
    assert.equal(await readFile(bundlePath, 'utf8'), originalBundle);

    const wrong = join(directory, 'wrong-version');
    await writeFile(wrong, '#!/bin/sh\nprintf "Version 0.0.0\\n"\n', { mode: 0o755 });
    assert.match(await build(['build-browser', '-Dtsc=' + wrong], false), /0\.0\.0/);
    assert.match(await build(['build-browser', '-Dbun=' + wrong], false), /0\.0\.0/);
    console.log('browser build: required strict checking before embedding, edits/additions invalidate cache, deterministic bundle and tool version gates passed');
  } finally { await rm(directory, { recursive: true, force: true }); }
}, 300_000);
