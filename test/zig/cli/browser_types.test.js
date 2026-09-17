// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

// Bun loads the exact TypeScript modules checked by the frontend build step.
import { test } from 'bun:test';
import assert from 'node:assert/strict';
import { array, object, optional, parse, string } from '../../../src/cli/browser/decode.ts';
import { decodeResponse } from '../../../src/cli/browser/model.ts';

test('decoders preserve unknown fields without mutation and reject invalid values', () => {
  const original = JSON.parse('{"name":"C","extra":{"__proto__":"kept","value":[1,null,false]}}');
  const decoded = object({ name: string, absent: optional(string) })(original);
  assert.deepEqual(decoded, original);
  assert.equal(Object.hasOwn(decoded, 'absent'), false);
  assert.notEqual(decoded, original);
  assert.throws(() => object({ name: string })(Object.create({ name: 'inherited' })), /name/);
  assert.deepEqual(array((value) => string(value).toUpperCase())(['a', 'b']), ['A', 'B']);
  assert.throws(() => array(string)(['valid', 7, 'also valid']), /string/);
  assert.throws(() => parse('{', string), SyntaxError);
});

test('API responses validate consumed fields and unavailable source buffers', () => {
  assert.deepEqual(decodeResponse('source', { content: null, tokens: [], highlight_warning: null }), { content: null, tokens: [], highlight_warning: null });
  assert.deepEqual(decodeResponse('source', { content: '', tokens: [], highlight_warning: null }).tokens, []);
  assert.throws(() => decodeResponse('source', { content: 7, tokens: [], highlight_warning: null }), /content/);
  assert.throws(() => decodeResponse('source', { content: 'uint', tokens: [{ start: '0', end: 4, kind: 'type' }], highlight_warning: null }), /start/);
  assert.throws(() => decodeResponse('source', { content: 'uint', tokens: [{ start: 0, end: NaN, kind: 'type' }], highlight_warning: null }), /finite/);
  assert.throws(() => decodeResponse('project', [{ name: 'C.sol', diagnostics: 0 }, { name: 'D.sol' }]), /diagnostics/);
  assert.throws(() => decodeResponse('compilations', {}), /array/);
  const imported = { src: '0:20:0', name_src: null, reference: null, import_path: 'lib/Math.sol', target_source: null, target_src: null, target_name: null };
  assert.deepEqual(decodeResponse('links', [imported]), [imported]);
});

test('compiler artifacts retain unknown output fields', () => {
  const output = { contracts: { 'C.sol': { C: { abi: null, evm: { bytecode: { object: 'unlinked' } } } } }, future: ['untouched'] };
  assert.deepEqual(decodeResponse('output', output), output);
});
