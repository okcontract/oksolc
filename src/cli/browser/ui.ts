// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

import type { Api, Navigation, Paged } from './model.ts';

// The static page owns these IDs and tags. Check the DOM before borrowing it.
const tags = {
  'menu-toggle': 'button',
  'compilation': 'select',
  'older': 'button',
  'download-output': 'a',
  'navigation': 'aside',
  'file-count': 'span',
  'search': 'input',
  'tree': 'nav',
  'search-results': 'div',
  'snapshot-origin': 'span',
  'main': 'main',
  'directory': 'div',
  'filename': 'h1',
  'summary': 'div',
  'diagnostics-summary': 'button',
  'contract': 'select',
  'view-status': 'div',
  'live-bar': 'div',
  'live-status': 'span',
  'workspace-live': 'button',
  'follow-live': 'button',
  'compilation-progress': 'div',
  'live-progress': 'progress',
  'progress-item': 'span',
  'progress-count': 'span',
  'content': 'div',
  'position': 'span',
  'line-position': 'button',
  'line-jump': 'form',
  'line-jump-close': 'button',
  'line-number': 'input',
  'line-range': 'span',
  'download-request': 'a',
  'timestamp': 'span',
  'details': 'div',
  'toast': 'div',
} as const;
export function $<K extends keyof typeof tags>(id: K): HTMLElementTagNameMap[(typeof tags)[K]] {
  const node = document.getElementById(id);
  if (!node || node.localName !== tags[id]) throw new Error(`Missing or invalid page element: ${id}`);
  // The HTML tag was checked against the exact ID/tag mapping above.
  return node as HTMLElementTagNameMap[(typeof tags)[K]];
}
export function element<K extends keyof HTMLElementTagNameMap>(tag: K, className = '', text: unknown = ''): HTMLElementTagNameMap[K] {
  const node = document.createElement(tag);
  node.className = className;
  node.textContent = text == null ? '' : String(text);
  return node;
}
export function button(text: string, action: (control: HTMLButtonElement) => unknown, className = 'quiet'): HTMLButtonElement {
  const node = element('button', className, text);
  node.addEventListener('click', () => { action(node); });
  return node;
}
const statuses = new Set(['error', 'warning']);
export function badge<K extends 'span' | 'button' = 'span'>(text: unknown, status: string | null | undefined, tag?: K): HTMLElementTagNameMap[K | 'span'] {
  return element(tag ?? 'span', `badge ${status && statuses.has(status) ? status : ''}`, text);
}
export type JsonTree = (value: unknown, label?: string) => HTMLDivElement;
export type SourceLink = (source: string, start?: number, symbol?: string | number, text?: string | number, className?: string) => HTMLAnchorElement;
export interface UI {
  element: typeof element;
  button: typeof button;
  badge: typeof badge;
  jsonTree: JsonTree;
  sourceLink: SourceLink;
  navigate: (changes: Partial<Navigation>) => void;
  hash: (changes?: Partial<Navigation>) => string;
  api: Api;
  paged: Paged;
}
