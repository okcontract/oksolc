// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

import { createArtifactBrowser } from './artifacts.ts';
import { createSourcePosition } from './source-position.ts';
import { createSummary } from './summary.ts';
import { $, element, button, badge } from './ui.ts';
import { errorMessage, isObject, objectValue, parse } from './decode.ts';
import { choice, decodeResponse, panels, parseDiagnostic, queryString, tabs } from './model.ts';
import type { CompilationRow, ContractRow, FileData, FileRow, LinkedSpan, ListRoute, LiveStatus, Navigation, Params, Response, Route, Row } from './model.ts';

// All displayed compiler/source data enters through text nodes. Solidity source
// locations are UTF-8 byte offsets; JavaScript string indices are never used for them.
const empty = (node: HTMLElement, title: string, message = '') => {
  const box = element('div', 'empty');
  box.append(element('h2', '', title), element('p', '', message));
  node.replaceChildren(box);
};
const encoder = new TextEncoder();
const decoder = new TextDecoder();
function range(src: string | null): [number, number, number] {
  const [start = 0, length = 0, file = -1] = (src || '0:0:-1').split(':').map(Number);
  return [start, length, file];
}
const state: Navigation = { compilation: null, source: '', tab: 'source', start: 0, contract: '', symbol: '', panel: 'outline' };
let compilations: CompilationRow[] = [], files: FileRow[] = [], contracts: ContractRow[] = [];
let generation = 0, panelGeneration = 0, searchGeneration = 0;
let navigationAbort = new AbortController();
let panelAbort = new AbortController();
let compilationOffset = 0, compilationGeneration = 0;
let workspaceRevision: number | null | undefined = null;
let live: LiveStatus | null = null;
let followLatest = !(Number(new URLSearchParams(location.hash.slice(1)).get('compilation')) > 0);
const sourceCache = new Map<string, FileData>();
const artifacts = createArtifactBrowser({ element, button, jsonTree });
let hideLibraries = true, summaryGeneration = 0;
let summaryRows: Row<'summary'>[] = [];
const sourcePosition = createSourcePosition((start) => navigate({ start }));
const summary = createSummary(() => {
  state.panel = 'diagnostics';
  if (['abi', 'bytecode', 'artifacts'].includes(state.tab)) navigate({ tab: 'source' });
  else renderPanel().catch(report);
});
function renderSummary() { summary(summaryRows, (state.compilation ?? 0) > 0); }

function apiUrl(route: Route, params: Params = {}) {
  const query = queryString({ ...(state.compilation === null ? {} : { compilation: state.compilation }), ...params });
  return `/api/${route}?${query}`;
}
async function api<R extends Route>(route: R, params: Params = {}, signal = navigationAbort.signal): Promise<Response<R>> {
  const response = await fetch(apiUrl(route, params), { signal });
  const data: unknown = await response.json();
  if (!response.ok) throw new Error(isObject(data) && typeof data.error === 'string' ? data.error : `HTTP ${response.status}`);
  try { return decodeResponse(route, data); }
  catch (error) { throw new Error(`Invalid ${route} response: ${errorMessage(error)}`); }
}
function report(error: unknown) {
  if (error instanceof Error && error.name === 'AbortError') return;
  $('toast').textContent = errorMessage(error);
  $('toast').hidden = false;
}
function hash(changes: Partial<Navigation> = {}) {
  const next = { ...state, ...changes };
  const query = new URLSearchParams();
  for (const key of ['compilation', 'source', 'tab', 'start', 'contract', 'symbol', 'panel'] as const) {
    if (next[key] !== '' && next[key] != null) query.set(key, String(next[key]));
  }
  return `#${query}`;
}
function navigate(changes: Partial<Navigation>) { location.hash = hash(changes); }
function sourceLink(source: string, start = 0, symbol: string | number = '', text: string | number = source, className = '') {
  const link = element('a', className, text);
  link.href = hash({ source, start: Math.max(0, Number(start) || 0), tab: 'source', symbol: String(symbol), contract: '' });
  return link;
}

// Lazy expansion bounds DOM work even for large compiler artifacts.
function jsonTree(value: unknown, label = 'value'): HTMLDivElement {
  const box = element('div', 'json-tree');
  if (value === null || typeof value !== 'object') {
    box.append(element('span', 'json-key', `${label}: `));
    const text = typeof value === 'string' ? value : JSON.stringify(value) ?? 'undefined';
    const display = element('span', 'json-value', text.length > 4000 ? `${text.slice(0, 4000)}…` : text);
    box.append(display);
    if (text.length > 4000) box.append(button(`Show all ${text.length.toLocaleString()} characters`, (control) => {
      display.textContent = text;
      control.remove();
    }));
    return box;
  }
  const entries: [string, unknown][] = Object.entries(value);
  const detail = element('details');
  detail.append(element('summary', '', `${label} ${Array.isArray(value) ? '[' : '{'}${entries.length}${Array.isArray(value) ? ']' : '}'}`));
  let cursor = 0;
  const more = button('Show more fields', () => appendFields(), 'more');
  function appendFields() {
    more.remove();
    const end = Math.min(cursor + 100, entries.length);
    for (const [key, item] of entries.slice(cursor, end)) detail.append(jsonTree(item, key));
    cursor = end;
    if (cursor < entries.length) detail.append(more);
  }
  detail.addEventListener('toggle', () => { if (detail.open && cursor === 0) appendFields(); });
  box.append(detail);
  return box;
}

async function loadCompilations(offset = 0) {
  const epoch = ++compilationGeneration;
  const rows = await api('compilations', { offset }, AbortSignal.timeout(15000));
  if (epoch !== compilationGeneration) return;
  const pinned = compilations.find((row) => row.id === state.compilation);
  if (offset === 0) compilations = [];
  for (const row of rows.slice(0, 200)) {
    if (!compilations.some((existing) => existing.id === row.id)) compilations.push(row);
  }
  compilationOffset = offset + Math.min(rows.length, 200);
  // Keep the selected historical snapshot visible even outside the latest page.
  if (pinned && !compilations.some((row) => row.id === pinned.id)) compilations.push(pinned);
  compilations.sort((a, b) => b.id - a.id);
  $('compilation').replaceChildren(...compilations.map((row) => {
    const option = element('option', '', `#${row.id} · ${row.label}`);
    option.value = String(row.id);
    return option;
  }));
  if (live?.live) {
    const workspace = element('option', '', 'Workspace');
    workspace.value = '0';
    $('compilation').prepend(workspace);
  }
  $('compilation').value = String(state.compilation ?? '');
  $('older').hidden = rows.length <= 200;
}

const progressStages: Record<string, string> = {
  starting: 'Opening workspace', reading: 'Reading sources', checking: 'Checking for changes',
  parsing_sources: 'Parsing sources', analyzing_sources: 'Analyzing sources',
  generating_contracts: 'Generating contracts',
  compiling_yul: 'Compiling Yul', writing_output: 'Writing compiler output', publishing: 'Saving compilation',
};
function renderLive() {
  $('live-bar').hidden = !live?.live;
  if (!live?.live) return;
  const busy = ['starting', 'reading', 'checking', 'compiling', 'publishing'].includes(live.phase);
  const stage = progressStages[live.progress.stage] || 'Compiling project';
  const scope = live.source_path;
  $('live-bar').dataset.phase = live.phase;
  const message = live.failure
    ? `${state.compilation === 0 ? 'Compilation paused' : 'Output is stale'} · ${live.failure}${live.phase === 'stopped' ? ' · restart serve' : ' · retrying'}`
    : busy ? `${stage} · ${scope}${(state.compilation ?? 0) > 0 ? ` · viewing snapshot #${state.compilation}` : ''}`
    : followLatest ? `Watching ${live.source_path} · following latest`
    : state.compilation === 0 ? `Watching ${live.source_path} · browsing workspace`
    : `Watching ${live.source_path} · viewing snapshot #${state.compilation}`;
  if ($('live-status').textContent !== message) $('live-status').textContent = message;
  $('follow-live').hidden = followLatest;
  $('workspace-live').hidden = !busy || state.compilation === 0;
  $('compilation-progress').hidden = !busy;
  const progress = $('live-progress'), completed = live.progress?.completed_items || 0, total = live.progress?.total_items || 0;
  progress.setAttribute('aria-label', stage);
  if (total > 0) { progress.max = total; progress.value = Math.min(completed, total); }
  else progress.removeAttribute('value');
  $('progress-count').textContent = total > 0 ? `${completed.toLocaleString()} / ${total.toLocaleString()}` : '';
  const item = live.progress?.item_name;
  $('progress-item').textContent = item || (live.phase === 'checking' ? 'Checking source contents and used imports' : 'You can browse your sources while compilation continues');
  $('progress-item').title = item || '';
}
async function followLive() {
  const current = live?.current ?? live?.latest;
  if (!current) return;
  followLatest = true;
  // AST IDs belong to one compilation. Retain the file/tab/offset, discard IDs.
  state.panel = state.panel === 'references' ? 'outline' : state.panel;
  history.replaceState(null, '', hash({ compilation: current, symbol: '' }));
  const source = state.source, scroll = $('content').scrollTop;
  await navigateFromHash();
  if (state.source === source) $('content').scrollTop = scroll;
  renderLive();
}
async function pollLive() {
  try {
    const selection = `${state.compilation}:${state.source}:${state.tab}`, epoch = generation;
    const status = await api('status', { source: state.source }, AbortSignal.timeout(15000));
    if (epoch !== generation || selection !== `${state.compilation}:${state.source}:${state.tab}`) return;
    live = status;
    if (!live.live) return;
    if (live.latest !== (compilations[0]?.id ?? null)) {
      await loadCompilations();
    }
    // Navigation to history always pins it, including browser back/forward.
    const query = new URLSearchParams(location.hash.slice(1));
    const selected = query.has('compilation') ? Number(query.get('compilation')) : state.compilation;
    if (followLatest && live.current != null && selected === state.compilation && state.compilation !== live.current) await followLive();
    else if (state.compilation === 0 && workspaceRevision !== live.workspace_revision) {
      const source = state.source, scroll = $('content').scrollTop;
      await navigateFromHash();
      if (state.source === source) $('content').scrollTop = scroll;
    }
    renderLive();
  } catch (error) {
    if (live?.live) {
      live = { ...live, phase: 'stopped', failure: `Live updates unavailable: ${errorMessage(error)}` };
      renderLive();
    }
  } finally {
    if (live?.live !== false) setTimeout(pollLive, 750);
  }
}

function renderTree() {
  const expanded = new Map([...$('tree').querySelectorAll<HTMLDetailsElement>('details[data-path]')].map((node) => [node.dataset.path, node.open]));
  interface Folder { folders: Map<string, Folder>; files: (FileRow & { label: string })[] }
  const root: Folder = { folders: new Map(), files: [] };
  for (const file of files) {
    const parts = file.name.split('/');
    const name = parts.pop() ?? '';
    let folder = root;
    for (const part of parts) {
      let child = folder.folders.get(part);
      if (!child) { child = { folders: new Map(), files: [] }; folder.folders.set(part, child); }
      folder = child;
    }
    folder.files.push({ ...file, label: name });
  }
  function fill(parent: HTMLElement, folder: Folder, prefix = '') {
    for (const [name, child] of folder.folders) {
      const path = `${prefix}${name}/`;
      const detail = element('details', 'folder');
      detail.dataset.path = path;
      detail.open = expanded.get(path) ?? (state.source.startsWith(path) || folder === root);
      const contents = element('div', 'folder-body');
      detail.append(element('summary', '', name || '/'), contents);
      fill(contents, child, path);
      parent.append(detail);
    }
    for (const file of folder.files) {
      const link = sourceLink(file.name, 0, '', '', 'file-link');
      link.title = file.name;
      link.dataset.source = file.name;
      if (file.name === state.source) link.setAttribute('aria-current', 'page');
      link.append(element('span', 'file-icon', file.name.endsWith('.yul') ? 'Y' : 'S'), element('span', 'file-label', file.label));
      if (file.diagnostics) link.append(element('span', 'file-count', file.diagnostics));
      parent.append(link);
    }
  }
  $('tree').replaceChildren();
  fill($('tree'), root);
  $('file-count').textContent = String(files.length);
}
function updateTree() {
  for (const link of $('tree').querySelectorAll<HTMLAnchorElement>('[data-source]')) {
    if (link.dataset.source === state.source) {
      link.setAttribute('aria-current', 'page');
      for (let parent = link.parentElement; parent && parent !== $('tree'); parent = parent.parentElement) {
        if (parent instanceof HTMLDetailsElement) parent.open = true;
      }
    } else link.removeAttribute('aria-current');
  }
}

async function navigateFromHash() {
  sourcePosition.clear();
  const epoch = ++generation;
  navigationAbort.abort();
  navigationAbort = new AbortController();
  $('toast').hidden = true;
  const query = new URLSearchParams(location.hash.slice(1));
  const compilation = query.has('compilation') ? Number(query.get('compilation')) : live?.live ? live.current ?? 0 : compilations[0]?.id;
  if (compilation == null) return empty($('content'), 'No compilations', 'Import or compile a project with oksolc browse.');
  // Workspace is a transient view of the current sources, including after a
  // reload or a dropdown selection. Only a completed snapshot can pin history.
  if (live?.live && compilation === 0) followLatest = true;
  else if (live?.live && state.compilation !== null && compilation !== state.compilation && compilation !== live.current) followLatest = false;
  const revision = live?.workspace_revision;
  const changedCompilation = compilation !== state.compilation;
  const changed = changedCompilation || (compilation === 0 && workspaceRevision !== revision);
  const oldSymbol = state.symbol;
  const nextState: Navigation = { ...state,
    compilation, source: query.get('source') || '', start: Math.max(0, Number(query.get('start')) || 0),
    tab: choice(tabs, query.get('tab'), 'source'),
    contract: query.get('contract') || '', symbol: query.get('symbol') || '',
    panel: choice(panels, query.get('panel'), state.panel),
  };
  Object.assign(state, nextState);
  const observation = await api('status', { source: state.source });
  if (epoch !== generation) return;
  live = observation;
  $('content').replaceChildren();
  if (state.symbol && state.symbol !== oldSymbol) state.panel = 'references';
  document.body.classList.remove('menu-open');
  $('menu-toggle').setAttribute('aria-expanded', 'false');
  $('view-status').textContent = compilation === 0 ? 'Loading workspace…' : 'Loading snapshot…';
  if (changed) {
    sourceCache.clear();
    ++searchGeneration;
    if (changedCompilation) {
      $('search').value = '';
      $('search-results').hidden = true;
      $('tree').hidden = false;
    }
    await loadProject(epoch);
    if (compilation === 0) workspaceRevision = revision;
  }
  const removedSource = changed && state.source && !files.some((file) => file.name === state.source);
  if (!state.source || removedSource) {
    const label = compilations.find((row) => row.id === compilation)?.label;
    state.source = files.find((file) => file.name === label || file.name.startsWith(`${label}/`))?.name || files[0]?.name || '';
  }
  if (removedSource) {
    state.start = 0; state.symbol = ''; state.contract = '';
    history.replaceState(null, '', hash());
  }
  if (changed) renderTree(); else updateTree();
  if (changed && $('search').value) searchProject().catch(report);
  $('compilation').value = String(compilation);
  const snapshot = compilations.find((row) => row.id === compilation);
  $('snapshot-origin').textContent = compilation === 0 ? 'workspace' : snapshot?.origin || 'snapshot';
  $('timestamp').textContent = snapshot?.created_at || '';
  $('download-output').href = apiUrl('output');
  $('download-request').href = apiUrl('request');
  $('download-output').hidden = compilation === 0;
  $('download-request').parentElement?.toggleAttribute('hidden', compilation === 0);
  const parts = state.source.split('/');
  const filename = parts.pop();
  $('filename').textContent = filename || (compilation === 0 ? 'Your workspace' : 'Compilation');
  $('filename').title = state.source || $('filename').textContent;
  $('directory').textContent = parts.join(' / ') || 'PROJECT';
  $('directory').title = $('directory').textContent;
  renderSummary();
  document.title = `${state.source || 'Workspace'} · oksolc`;
  for (const tab of document.querySelectorAll<HTMLElement>('[data-tab]')) {
    if (tab.dataset.tab === state.tab) tab.setAttribute('aria-current', 'page'); else tab.removeAttribute('aria-current');
  }
  document.body.classList.toggle('artifact-view', ['abi', 'bytecode', 'artifacts'].includes(state.tab));
  const selectedContracts = contracts.filter((row) => row.source === state.source);
  if (!selectedContracts.some((row) => row.name === state.contract)) state.contract = selectedContracts[0]?.name || '';
  $('contract').replaceChildren(...selectedContracts.map((row) => {
    const option = element('option', '', row.name); option.value = row.name; return option;
  }));
  $('contract').value = state.contract;
  $('contract').hidden = !['abi', 'bytecode', 'artifacts'].includes(state.tab) || !selectedContracts.length;
  $('view-status').textContent = '';
  sourcePosition.clear(`${files.length} source files · ${compilation === 0 ? 'workspace' : `snapshot #${compilation}`}`);
  $('content').replaceChildren();
  await Promise.all([renderContent(epoch), renderPanel()]);
  renderLive();
}

async function loadProject(epoch: number) {
  const [nextFiles, nextContracts] = await Promise.all([api('project'), api('contracts'), loadSummary(epoch)]);
  if (epoch !== generation) return;
  files = nextFiles; contracts = nextContracts;
}

async function loadSummary(epoch = generation) {
  const request = ++summaryGeneration;
  const rows = await api('summary', { hide_libraries: Number(hideLibraries) });
  if (epoch !== generation || request !== summaryGeneration) return;
  summaryRows = rows; renderSummary();
}

async function fileData(source: string): Promise<FileData> {
  const key = `${state.compilation}:${source}`;
  const cached = sourceCache.get(key);
  if (cached) return cached;
  let linkWarning: string | null = null;
  const [file, links] = await Promise.all([api('source', { source }), api('links', { source }).catch((error: unknown) => {
    if (error instanceof Error && error.name === 'AbortError') throw error;
    linkWarning = `Definition links unavailable: ${errorMessage(error)}`;
    return [];
  })]);
  let result: FileData;
  if (file.content === null) result = { ...file, content: null, link_warning: linkWarning };
  else {
    const bytes = encoder.encode(file.content), lines = [0];
    for (let i = 0; i < bytes.length; i++) if (bytes[i] === 10) lines.push(i + 1);
    const spans = links.map((link) => {
      const [start, length] = range(link.name_src || link.src);
      return { ...link, start, end: start + length };
    }).filter((link) => link.start >= 0 && link.end > link.start).sort((a, b) => a.start - b.start || a.end - b.end);
    result = { ...file, content: file.content, bytes, lines, links: spans, link_warning: linkWarning };
  }
  if (sourceCache.size >= 2) { const oldest = sourceCache.keys().next(); if (!oldest.done) sourceCache.delete(oldest.value); }
  sourceCache.set(key, result);
  return result;
}
function lineAt(lines: readonly number[], offset: number) {
  let low = 0, high = lines.length;
  while (low + 1 < high) { const mid = (low + high) >>> 1; if ((lines[mid] ?? 0) <= offset) low = mid; else high = mid; }
  return low;
}
async function renderSource(epoch: number) {
  if (!state.source && state.compilation === 0) return empty($('content'), 'Opening your workspace', `Solidity sources in ${live?.source_path || 'src'} will appear here as they are read.`);
  if (!state.source) return empty($('content'), 'No source files', 'The snapshot still contains the complete compiler output.');
  const file = await fileData(state.source);
  if (epoch !== generation) return;
  if (file.content === null) return empty($('content'), 'Source bytes unavailable', 'This imported output did not include source content. AST and compiler artifacts remain available.');
  if (file.highlight_warning) $('view-status').textContent = `Plain source display: ${file.highlight_warning}. Compiler output is unchanged.`;
  if (file.link_warning) $('view-status').textContent += ` ${file.link_warning}`;
  const activeLine = lineAt(file.lines, state.start);
  const code = element('div', 'code');
  let tokenIndex = 0, linkIndex = 0;
  let activeLinks: LinkedSpan[] = [];
  for (const [line, start] of file.lines.entries()) {
    const nextStart = file.lines[line + 1];
    let end = nextStart === undefined ? file.bytes.length : nextStart - 1;
    if (file.bytes[end - 1] === 13) end--;
    const row = element('div', `code-line${line === activeLine ? ' active' : ''}`); row.id = `L${line + 1}`;
    const lineLink = sourceLink(state.source, start, '', line + 1, 'line-number');
    row.append(lineLink);
    const body = element('code');
    let cursor = start;
    while (cursor < end) {
      while (tokenIndex < file.tokens.length && (file.tokens[tokenIndex]?.end ?? Infinity) <= cursor) tokenIndex++;
      const token = file.tokens[tokenIndex];
      const boundary = token ? Math.min(end, token.start > cursor ? token.start : token.end) : end;
      const kind = token && token.start <= cursor ? token.kind : '';
      let link = file.links[linkIndex];
      while (link && link.start <= cursor) { activeLinks.push(link); link = file.links[++linkIndex]; }
      activeLinks = activeLinks.filter((link) => link.end > cursor);
      const target = (kind === 'identifier' || kind === 'type' || kind === 'string') && activeLinks
        .filter((link) => link.end >= boundary && (link.target_source || link.import_path))
        .reduce<LinkedSpan | null>((best, link) => !best || link.end - link.start < best.end - best.start ? link : best, null);
      const text = decoder.decode(file.bytes.subarray(cursor, boundary));
      const span = target ? sourceLink(target.target_source || target.import_path || '', range(target.target_src)[0], target.reference !== null && target.reference >= 0 ? target.reference : '', text, `code-link token-${kind}`) : element('span', `token-${kind}`, text);
      if (target) span.title = `Go to ${target.target_name || target.import_path || target.target_source}`;
      body.append(span); cursor = boundary;
    }
    row.append(body); code.append(row);
  }
  $('content').replaceChildren(code);
  sourcePosition.show(file.lines, activeLine, file.bytes.length);
  // Finish the jump before live refreshes restore the user's scroll position.
  if (activeLine > 0) document.getElementById(`L${activeLine + 1}`)?.scrollIntoView({ block: 'center' });
  else $('content').scrollTop = 0;
}

async function renderContent(epoch: number) {
  if (state.tab === 'source') return renderSource(epoch);
  if (state.compilation === 0) return empty($('content'), 'Available after compilation', 'You can browse source files while the compiler prepares these results.');
  if (!state.contract && state.tab !== 'artifacts') return empty($('content'), 'No contract artifact', 'This source has no contract in the selected compiler output.');
  const rows = await api('contract', { source: state.source, name: state.contract });
  if (epoch !== generation) return;
  const data = rows[0] ? parse(rows[0].data, objectValue) : {};
  if (state.tab === 'abi' || state.tab === 'bytecode') {
    $('content').replaceChildren(artifacts[state.tab](data, state.contract, state.source));
    return;
  }
  const box = element('div', 'artifact');
  box.append(element('h2', '', `${state.contract} · contract artifacts`));
  const tree = jsonTree(data, 'Contract'); box.append(tree); tree.querySelector('details')?.setAttribute('open', '');
  box.append(button('Browse complete compiler output', async (control) => {
    control.disabled = true;
    try {
      const output = await api('output');
      if (epoch !== generation) return;
      const full = jsonTree(output, 'Compiler output');
      box.replaceChildren(element('h2', '', 'Complete compiler output'), full);
      full.querySelector('details')?.setAttribute('open', '');
    } catch (error) { control.disabled = false; report(error); }
  }, 'button'));
  $('content').replaceChildren(box);
}

// Every paginated endpoint returns one extra row as an explicit continuation.
// Failures retain an error message; they never turn a partial list into completeness.
async function paged<R extends ListRoute>(container: HTMLElement, route: R, params: Params, render: (row: Row<R>) => Node, current: () => boolean, offset = 0): Promise<void> {
  const rows = await api(route, { ...params, offset });
  if (!current()) return;
  if (offset === 0) container.replaceChildren();
  for (const row of rows.slice(0, 200)) container.append(render(row));
  if (rows.length === 0 && offset === 0) container.append(element('p', 'muted', 'No records in this view.'));
  if (rows.length > 200) container.append(button('Load more', async (node) => {
    node.disabled = true;
    try { await paged(container, route, params, render, current, offset + 200); node.remove(); }
    catch (error) { node.disabled = false; report(error); }
  }, 'more'));
}
async function renderPanel() {
  panelAbort.abort(); panelAbort = new AbortController();
  const epoch = generation, panelEpoch = ++panelGeneration;
  const current = () => epoch === generation && panelEpoch === panelGeneration;
  for (const button of document.querySelectorAll<HTMLElement>('[data-panel]')) button.setAttribute('aria-pressed', String(button.dataset.panel === state.panel));
  if (['abi', 'bytecode', 'artifacts'].includes(state.tab)) { $('details').replaceChildren(); return; }
  if (state.compilation === 0) return empty($('details'), 'Workspace sources', 'The outline, diagnostics and references are available in completed compilations.');
  $('details').replaceChildren(element('p', 'muted', 'Loading…'));
  if (state.panel === 'references') {
    if (!state.symbol) return empty($('details'), 'Find references', 'Choose a declaration in the outline or follow a source link.');
    return paged($('details'), 'references', { symbol: state.symbol }, (row) => sourceLink(row.source, range(row.name_src || row.src)[0], state.symbol, `${row.source} · ${row.kind}`, 'outline-item'), current);
  }
  if (state.panel === 'diagnostics') {
    const filter = element('label', 'diagnostics-filter');
    const toggle = element('input'); toggle.type = 'checkbox'; toggle.checked = hideLibraries;
    filter.append(toggle, element('span', '', 'Hide library diagnostics'));
    filter.title = 'Library paths: lib/, node_modules/, vendor/, and scoped packages. Other project imports remain visible.';
    const hidden = summaryRows.reduce((sum, row) => sum + (row.kind === 'diagnostic' ? row.hidden : 0), 0);
    const note = element('p', 'diagnostics-note muted', hideLibraries ? `${hidden.toLocaleString()} library diagnostics hidden` : 'Showing diagnostics from all sources');
    const cards = element('div');
    $('details').replaceChildren(filter, note, cards);
    toggle.addEventListener('change', async () => {
      hideLibraries = toggle.checked; toggle.disabled = true;
      try {
        await loadSummary(); await renderPanel();
        $('details').querySelector<HTMLInputElement>('.diagnostics-filter input')?.focus({ preventScroll: true });
      }
      catch (error) { toggle.disabled = false; report(error); }
    });
    // Filter in SQL before pagination; diagnostics without a location stay visible.
    return paged(cards, 'diagnostics', { hide_libraries: Number(hideLibraries) }, (row) => {
      const data = parseDiagnostic(row.data), card = element('article', 'card');
      card.append(badge(row.severity, row.severity), element('p', '', data.message || data.formattedMessage || 'Compiler diagnostic'));
      if (row.source) card.append(sourceLink(row.source, data.sourceLocation?.start, '', row.source, 'card-location'));
      card.append(jsonTree(data, 'Details')); return card;
    }, current);
  }
  return paged($('details'), 'symbols', { source: state.source }, (row) => {
    const link = sourceLink(row.source, range(row.name_src || row.src)[0], row.id, '', 'outline-item');
    const text = element('span', '', row.name || row.kind);
    text.append(element('small', '', row.kind));
    link.append(element('span', 'symbol-icon', row.kind.replace('Definition', '').slice(0, 1)), text);
    link.title = 'Go to definition and find references'; return link;
  }, current);
}

let searchTimer: ReturnType<typeof setTimeout> | undefined, searchAbort: AbortController | undefined;
async function searchProject() {
  const term = $('search').value.trim(), epoch = ++searchGeneration;
  searchAbort?.abort(); searchAbort = new AbortController();
  $('tree').hidden = !!term; $('search-results').hidden = !term;
  if (!term) return;
  const node = $('search-results'); node.replaceChildren(element('p', 'muted', 'Searching…'));
  const [hits, symbols] = await Promise.all([api('search', { q: term }, searchAbort.signal), api('symbols', { q: term }, searchAbort.signal)]);
  if (epoch !== searchGeneration) return;
  node.replaceChildren();
  function results<R extends ListRoute>(label: string, route: R, rows: Row<R>[], render: (row: Row<R>) => Node) {
    node.append(element('h3', 'section-label', label));
    const list = element('div'); node.append(list);
    rows.slice(0, 200).forEach((row) => list.append(render(row)));
    if (!rows.length) list.append(element('p', 'muted', 'No matches.'));
    if (rows.length > 200) list.append(button('Load more', async (control) => {
      try { await paged(list, route, { q: term }, render, () => epoch === searchGeneration, 200); control.remove(); }
      catch (error) { report(error); }
    }, 'more'));
  }
  results('Files & code · first match per file', 'search', hits, (row) => {
    const link = sourceLink(row.name, row.start, '', row.name, 'search-hit');
    if (row.snippet) link.append(element('pre', '', row.snippet)); return link;
  });
  results('Symbols', 'symbols', symbols, (row) => sourceLink(row.source, range(row.name_src || row.src)[0], row.id, `${row.name} · ${row.source}`, 'search-hit'));

}

$('compilation').addEventListener('change', () => {
  followLatest = Number($('compilation').value) === 0 || Number($('compilation').value) === live?.latest;
  // Source paths and contract names survive snapshots; AST symbol IDs do not.
  // navigateFromHash already falls back when a file or contract is absent.
  state.panel = state.panel === 'references' ? 'outline' : state.panel;
  navigate({ compilation: Number($('compilation').value), symbol: '' });
  renderLive();
});
$('follow-live').addEventListener('click', () => followLive().catch(report));
$('workspace-live').addEventListener('click', async () => {
  history.replaceState(null, '', hash({ compilation: 0, symbol: '', tab: 'source' }));
  try { await navigateFromHash(); followLatest = true; renderLive(); } catch (error) { report(error); }
});
$('older').addEventListener('click', () => loadCompilations(compilationOffset).catch(report));
$('contract').addEventListener('change', () => navigate({ contract: $('contract').value }));
for (const node of document.querySelectorAll<HTMLElement>('[data-tab]')) node.addEventListener('click', () => navigate({ tab: choice(tabs, node.dataset.tab, 'source') }));
for (const node of document.querySelectorAll<HTMLElement>('[data-panel]')) node.addEventListener('click', () => {
  state.panel = choice(panels, node.dataset.panel, 'outline');
  history.replaceState(null, '', hash());
  renderPanel().catch(report);
});
$('search').addEventListener('input', () => { clearTimeout(searchTimer); searchTimer = setTimeout(() => searchProject().catch(report), 180); });
$('menu-toggle').addEventListener('click', () => $('menu-toggle').setAttribute('aria-expanded', String(document.body.classList.toggle('menu-open'))));
$('toast').addEventListener('click', () => { $('toast').hidden = true; });
document.addEventListener('keydown', (event) => {
  if (event.key === '/' && !['INPUT', 'TEXTAREA', 'SELECT'].includes(document.activeElement?.tagName ?? '')) {
    event.preventDefault(); document.body.classList.add('menu-open'); $('menu-toggle').setAttribute('aria-expanded', 'true'); $('search').focus();
  }
  if (event.key === 'Escape') {
    $('search').value = ''; searchProject().catch(report); $('search').blur();
    document.body.classList.remove('menu-open'); $('menu-toggle').setAttribute('aria-expanded', 'false');
  }
});
window.addEventListener('hashchange', () => navigateFromHash().catch((error) => { if (!(error instanceof Error && error.name === 'AbortError')) $('view-status').textContent = `Could not load this view: ${errorMessage(error)}`; report(error); }));
try { live = await api('status', {}, AbortSignal.timeout(15000)); await loadCompilations(); await navigateFromHash(); }
catch (error) { empty($('content'), 'Snapshot unavailable', errorMessage(error)); report(error); }

pollLive();
