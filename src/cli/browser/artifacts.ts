// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

import { errorMessage, isObject } from './decode.ts';
import type { UI } from './ui.ts';

type RecordValue = Record<string, unknown>;
interface Documentation { user?: RecordValue[]; dev?: RecordValue[] }
interface Entry { raw: unknown; entry: RecordValue; signature: string; docs: Documentation; selector: string; search: string }
interface Preferences { search: string; kind: string; open: Set<string>; bytecode: Set<string> }
const recordValue = (value: unknown): RecordValue => isObject(value) ? value : {};
const stringValue = (value: unknown): string => typeof value === 'string' ? value : '';

// Read-only artifact views. Display formatting never changes exported values.
export function createArtifactBrowser({ element, button, jsonTree }: Pick<UI, 'element' | 'button' | 'jsonTree'>) {
  const views = new Map<string, Preferences>();
  function preferences(source: string, contract: string): Preferences {
    const key = `${source}\0${contract}`;
    let view = views.get(key);
    if (!view) {
      if (views.size >= 16) { const oldest = views.keys().next(); if (!oldest.done) views.delete(oldest.value); }
      view = { search: '', kind: '', open: new Set(), bytecode: new Set() };
      views.set(key, view);
    }
    return view;
  }
  const parameters = (value: unknown): RecordValue[] => Array.isArray(value) ? value.map(recordValue) : [];
  const type = (parameter: RecordValue): string => {
    const name = typeof parameter?.type === 'string' ? parameter.type : '?';
    return name.startsWith('tuple') && Array.isArray(parameter.components)
      ? `(${parameters(parameter.components).map(type).join(',')})${name.slice(5)}` : name;
  };
  const signature = (entry: RecordValue) => `${entry?.name || entry?.type || '?'}(${parameters(entry?.inputs).map(type).join(',')})`;
  const object = isObject;
  const member = (value: unknown, key: string): unknown => object(value) && Object.hasOwn(value, key) ? value[key] : undefined;
  function documentation(data: RecordValue, entry?: RecordValue, signature = ''): Documentation {
    const result: Documentation = {};
    if (entry !== undefined && !object(entry)) return result;
    for (const kind of ['user', 'dev'] as const) {
      const doc = recordValue(data[`${kind}doc`]);
      if (doc?.version !== 1 || doc.kind !== kind) continue;
      const table = entry?.type === 'event' ? 'events' : entry?.type === 'error' ? 'errors' : 'methods';
      const selected = entry ? member(doc[table], entry.type === 'constructor' ? 'constructor' : signature) : doc;
      result[kind] = (Array.isArray(selected) ? selected : [selected]).filter(object);
    }
    return result;
  }
  function description(docs: Documentation) {
    const box = element('div', 'artifact-description'), seen = new Set();
    for (const key of ['title', 'notice', 'details']) {
      for (const doc of [...(docs.user || []), ...(docs.dev || [])]) {
        if (typeof doc[key] !== 'string' || !doc[key] || seen.has(doc[key])) continue;
        seen.add(doc[key]); box.append(element('p', key === 'title' ? 'doc-title' : '', doc[key]));
      }
    }
    return box;
  }

  function copy(label: string, text: string) {
    return button(label, async (control) => {
      try {
        await navigator.clipboard.writeText(text);
        control.textContent = 'Copied';
      } catch (error) {
        control.textContent = 'Copy unavailable'; control.title = errorMessage(error);
      }
      setTimeout(() => { control.textContent = label; }, 1800);
    }, 'button');
  }
  function download(label: string, text: string, filename: string, mime = 'text/plain') {
    return button(label, () => {
      const url = URL.createObjectURL(new Blob([text], { type: mime }));
      const link = element('a'); link.href = url; link.download = filename;
      document.body.append(link); link.click(); link.remove();
      setTimeout(() => URL.revokeObjectURL(url), 1000);
    }, 'button');
  }
  function parameterList(values: RecordValue[], label: string, docs?: unknown, returns = false): HTMLElement {
    const section = element('section', 'abi-parameters');
    section.append(element('h3', 'section-label', label));
    if (!values.length) section.append(element('p', 'muted', 'None'));
    for (const [index, value] of values.entries()) {
      const row = element('div', 'abi-parameter');
      row.append(element('code', '', type(value)), element('span', '', value?.name || 'unnamed'));
      if (value?.indexed) row.append(element('small', 'muted', 'indexed'));
      const text = member(docs, stringValue(value.name) || (returns ? `_${index}` : ''));
      if (typeof text === 'string' && text) row.append(element('p', 'parameter-description', text));
      if (Array.isArray(value?.components)) {
        const detail = element('details', 'abi-components');
        detail.append(element('summary', '', value.internalType || 'Tuple components'), parameterList(parameters(value.components), 'Components'));
        row.append(detail);
      }
      section.append(row);
    }
    return section;
  }

  function abi(data: RecordValue, contract: string, source: string) {
    const view = preferences(source, contract);
    const box = element('div', 'artifact abi-view');
    const heading = element('div', 'artifact-heading');
    heading.append(element('h2', '', 'Application binary interface'));
    box.append(heading);
    if (!Array.isArray(data.abi)) {
      box.append(element('p', 'muted', data.abi === undefined ? 'ABI was not requested for this contract.' : 'The stored ABI is not an array.'), jsonTree(data.abi ?? null, 'Recorded ABI'));
      return box;
    }
    const json = JSON.stringify(data.abi, null, 2), actions = element('div', 'artifact-actions');
    actions.append(copy('Copy ABI', json), download('Download ABI', json, `${contract}.abi.json`, 'application/json'));
    heading.append(actions);
    box.append(description(documentation(data)));
    const entries: Entry[] = data.abi.map((raw: unknown) => {
      const entry = recordValue(raw);
      const name = signature(entry), docs = documentation(data, entry, name);
      const identifier = entry?.type === 'function' ? member(recordValue(data.evm).methodIdentifiers, name) : null;
      const selector = typeof identifier === 'string' && /^[0-9a-f]{8}$/i.test(identifier) ? `0x${identifier}` : '';
      const text = [...(docs.user || []), ...(docs.dev || [])].flatMap((doc) => [
        doc.notice, doc.details,
        ...Object.values(object(doc.params) ? doc.params : {}),
        ...Object.values(object(doc.returns) ? doc.returns : {}),
      ]).filter((value) => typeof value === 'string');
      const search = [name, selector, ...parameters(entry?.inputs).map((value) => value?.name || ''), ...parameters(entry?.outputs).flatMap((value) => [type(value), value?.name || '']), ...text].join(' ').toLowerCase();
      return { raw, entry, signature: name, docs, selector, search };
    });
    const kinds = [...new Set(entries.map(({ entry }) => stringValue(entry.type) || 'unknown'))];
    const recordKey = (value: Pick<Entry, 'entry' | 'signature'>) => `${value.entry?.type}:${value.signature}`;
    const available = new Set(entries.map(recordKey));
    for (const key of view.open) if (!available.has(key)) view.open.delete(key);
    const filters = element('div', 'artifact-filters');
    const search = element('input'); search.type = 'search'; search.placeholder = 'Find a signature, selector or documentation…'; search.setAttribute('aria-label', 'Search ABI');
    search.value = view.search;
    const kind = element('select'); kind.setAttribute('aria-label', 'ABI kind');
    for (const value of ['', ...kinds]) {
      const option = element('option', '', value || 'All kinds'); option.value = value; kind.append(option);
    }
    kind.value = kinds.includes(view.kind) ? view.kind : '';
    const count = element('span', 'muted'); count.setAttribute('role', 'status');
    filters.append(search, kind, count);
    const list = element('div', 'abi-list');
    box.append(filters, list);
    function record({ raw, entry, signature, docs, selector }: Entry) {
      const detail = element('details', 'abi-entry'), summary = element('summary');
      const key = recordKey({ entry, signature });
      detail.open = view.open.has(key);
      summary.append(element('span', 'abi-kind', entry?.type || 'unknown'), element('code', 'abi-signature', signature));
      if (entry?.stateMutability) summary.append(element('span', 'badge', entry.stateMutability));
      if (entry?.anonymous) summary.append(element('span', 'badge', 'anonymous'));
      if (selector) summary.append(element('code', 'abi-selector', selector));
      detail.append(summary);
      let loaded = false;
      detail.addEventListener('toggle', () => {
        if (detail.open) view.open.add(key); else view.open.delete(key);
        if (!detail.open || loaded) return;
        loaded = true;
        const body = element('div', 'abi-body'), controls = element('div', 'artifact-actions');
        controls.append(copy('Copy signature', signature));
        if (selector) controls.append(copy('Copy selector', selector));
        const dev = docs.dev?.length === 1 ? docs.dev[0] : null;
        body.append(description(docs), controls, parameterList(parameters(entry?.inputs), 'Inputs', dev?.params));
        if (entry?.type === 'function') body.append(parameterList(parameters(entry.outputs), 'Returns', dev?.returns, true));
        body.append(jsonTree(raw, 'ABI entry'));
        if (docs.user?.length || docs.dev?.length) body.append(jsonTree(docs, 'Recorded NatSpec'));
        detail.append(body);
      });
      return detail;
    }
    function refresh() {
      view.search = search.value; view.kind = kind.value;
      const term = search.value.trim().toLowerCase();
      const matches = entries.filter((value) => (!kind.value || (value.entry?.type || 'unknown') === kind.value) && value.search.includes(term));
      count.textContent = `${matches.length} / ${entries.length} entries`;
      list.replaceChildren();
      if (!matches.length) { list.append(element('p', 'empty', entries.length ? 'No ABI entries match these filters.' : 'This contract has an empty ABI.')); return; }
      let cursor = 0;
      const more = button('Show more entries', append, 'more');
      function append() {
        more.remove();
        const end = Math.min(cursor + 200, matches.length);
        for (const entry of matches.slice(cursor, end)) list.append(record(entry));
        cursor = end;
        if (cursor < matches.length) list.append(more);
      }
      append();
    }
    search.addEventListener('input', refresh); kind.addEventListener('change', refresh);
    refresh();
    box.append(jsonTree(data.abi, 'Full ABI JSON'));
    return box;
  }

  // Compiler offsets are byte locations in the recorded object. These are
  // patch sites, not deployed addresses or immutable values. Expand lazily.
  function references(values: unknown, label: string, libraries = false) {
    if (!object(values) || !Object.keys(values).length) return null;
    const detail = element('details', 'bytecode-references');
    detail.append(element('summary', '', label));
    let loaded = false;
    detail.addEventListener('toggle', () => {
      if (!detail.open || loaded) return;
      loaded = true;
      function* rows(): Generator<(string | number)[]> {
        for (const [name, value] of Object.entries(recordValue(values))) {
          for (const [key, sites] of libraries && object(value) ? Object.entries(value) : [[null, value] as const]) {
            const identity = libraries && key !== null ? `${name}:${key}` : name;
            if (!Array.isArray(sites)) { yield [identity, 'Invalid locations', '—']; continue; }
            for (const site of sites) yield [identity, ...['start', 'length'].map((field) => {
              const position = recordValue(site)[field];
              return typeof position === 'number' && Number.isSafeInteger(position) && position >= 0 ? position.toLocaleString() : 'Invalid';
            })];
          }
        }
      }
      const table = element('table'), head = element('thead'), header = element('tr'), body = element('tbody');
      for (const title of [libraries ? 'Library' : 'Declaration ID', 'Byte offset', 'Bytes']) {
        const cell = element('th', '', title); cell.scope = 'col'; header.append(cell);
      }
      head.append(header); table.append(head, body); detail.append(table);
      const iterator = rows(), more = button('Show more locations', append, 'more');
      let next = iterator.next();
      function append() {
        more.remove();
        for (let i = 0; i < 200 && !next.done; i++, next = iterator.next()) {
          const row = element('tr');
          for (const text of next.value) row.append(element('td', '', text));
          body.append(row);
        }
        if (!next.done) detail.append(more);
      }
      append();
    });
    return detail;
  }

  function bytecode(data: RecordValue, contract: string, source: string) {
    const view = preferences(source, contract);
    const box = element('div', 'artifact bytecode-grid');
    const evm = recordValue(data.evm);
    for (const [label, value, suffix] of [['Creation bytecode', evm.bytecode, 'creation'], ['Runtime bytecode', evm.deployedBytecode, 'runtime']] as const) {
      const code = recordValue(value);
      const panel = element('section', 'bytecode-panel');
      panel.append(element('h2', '', label));
      box.append(panel);
      if (typeof code?.object !== 'string') { panel.append(element('p', 'muted', 'Not present in this compiler output.')); continue; }
      const object = code.object, hex = object.replace(/^0x/i, '');
      const unlinked = /__\$[0-9a-f]{34}\$__/i.test(hex);
      const validHex = /^[0-9a-f]*$/i.test(hex.replace(/__\$[0-9a-f]{34}\$__/gi, '0'.repeat(40))) && hex.length % 2 === 0;
      const size = element('div', 'bytecode-size');
      size.append(element('strong', '', validHex ? (hex.length / 2).toLocaleString() : '—'), element('span', 'muted', 'bytes'));
      panel.append(size);
      if (!hex.length) panel.append(element('p', 'muted', 'No executable bytecode was emitted.'));
      else if (unlinked && validHex) panel.append(element('p', 'artifact-caution', 'Unlinked bytecode · library addresses are required.'));
      else if (!validHex) panel.append(element('p', 'artifact-caution', 'The stored object contains non-hex data or has an odd length.'));
      const actions = element('div', 'artifact-actions');
      actions.append(copy('Copy bytecode', hex ? `0x${hex}` : '0x'), download('Download .bin', object, `${contract}.${suffix}.bin`));
      panel.append(actions);
      const links = references(code.linkReferences, 'Library link locations', true);
      const immutables = references(code.immutableReferences, 'Immutable patch locations');
      if (links) panel.append(links);
      if (immutables) panel.append(immutables);
      if (hex.length) {
        const preview = element('pre', 'bytecode-preview', view.bytecode.has(suffix) ? hex : hex.slice(0, 1024).match(/.{1,64}/g)?.join('\n') || '');
        preview.tabIndex = 0; preview.setAttribute('aria-label', `${label} preview`);
        panel.append(preview);
        if (hex.length > 1024 && !view.bytecode.has(suffix)) {
          panel.append(element('p', 'muted', `Preview · first ${validHex ? `512 of ${(hex.length / 2).toLocaleString()} bytes` : '1,024 characters'}. Copy and download include the full object.`));
          panel.append(button('Show full bytecode', (control) => { view.bytecode.add(suffix); preview.textContent = hex; control.remove(); }));
        }
      }
      panel.append(jsonTree(code, 'Compiler bytecode record'));
    }
    return box;
  }
  return { abi, bytecode };
}
