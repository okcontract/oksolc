// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

import { array, boolean, nullable, number, object, objectValue, oneOf, optional, parse, string } from './decode.ts';
import type { Decoded, Decoder } from './decode.ts';

// Wire projections are owned by server.zig. Unknown artifact fields remain
// available in the full record.
const text = optional(string), integerOrNull = nullable(number), textOrNull = nullable(string);
export const tabs = ['source', 'abi', 'bytecode', 'artifacts'] as const;
export const panels = ['outline', 'references', 'diagnostics'] as const;
export function choice<const T extends readonly string[]>(values: T, value: string | null | undefined, fallback: T[number]): T[number] {
  return values.find((candidate) => candidate === value) ?? fallback;
}
export interface Navigation {
  compilation: number | null;
  source: string;
  tab: typeof tabs[number];
  start: number;
  contract: string;
  symbol: string;
  panel: typeof panels[number];
}
export type Params = Record<string, string | number | boolean>;
export function queryString(params: Params): URLSearchParams {
  return new URLSearchParams(Object.entries(params).map(([key, value]) => [key, String(value)]));
}

export const parseDiagnostic = (value: string) => parse(value, object({
  message: text, formattedMessage: text,
  sourceLocation: optional(object({ start: number })),
}));
const compilationRow = object({ id: number, label: string, origin: string, created_at: string });
export type CompilationRow = Decoded<typeof compilationRow>;
const fileRow = object({ name: string, diagnostics: number });
export type FileRow = Decoded<typeof fileRow>;
const contractRow = object({ source: string, name: string });
export type ContractRow = Decoded<typeof contractRow>;
const symbolRow = object({ id: number, source: string, kind: string, name: string, src: string, name_src: textOrNull });
export type SymbolRow = Decoded<typeof symbolRow>;
const linkRow = object({ src: string, name_src: textOrNull, reference: integerOrNull, import_path: textOrNull, target_source: textOrNull, target_src: textOrNull, target_name: textOrNull });
export type LinkRow = Decoded<typeof linkRow>;
const source = object({
  content: textOrNull, highlight_warning: textOrNull,
  tokens: array(object({ start: number, end: number, kind: oneOf('keyword', 'type', 'number', 'string', 'comment', 'identifier', 'punctuation', 'invalid') })),
});
export type Source = Decoded<typeof source>;
export type LinkedSpan = LinkRow & { start: number; end: number };
export type FileData = Source & ({ content: null } | { content: string; bytes: Uint8Array; lines: number[]; links: LinkedSpan[] }) & { link_warning: string | null };
const liveStatus = object({
  live: boolean, phase: oneOf('starting', 'reading', 'checking', 'watching', 'compiling', 'publishing', 'stale', 'stopped'),
  failure: textOrNull, source_path: textOrNull, latest: integerOrNull, current: integerOrNull, workspace_revision: number,
  progress: object({ stage: string, completed_items: number, total_items: number, item_name: string }),
});
export type LiveStatus = Decoded<typeof liveStatus>;
const searchRow = object({ name: string, start: number, snippet: textOrNull });
export type SearchRow = Decoded<typeof searchRow>;

export const responses = {
  status: liveStatus,
  compilations: array(compilationRow), project: array(fileRow), contracts: array(contractRow),
  summary: array(object({ kind: oneOf('diagnostic'), status: string, total: number, hidden: number })),
  source, links: array(linkRow), symbols: array(symbolRow),
  references: array(object({ source: string, kind: string, src: string, name_src: textOrNull })),
  search: array(searchRow), contract: array(object({ data: string })),
  diagnostics: array(object({ severity: string, source: textOrNull, data: string })),
  output: objectValue, request: objectValue,
};
export type Route = keyof typeof responses;
type Responses = { [R in Route]: Decoded<typeof responses[R]> };
export type Response<R extends Route> = Responses[R];
export type ListRoute = { [R in Route]: Response<R> extends unknown[] ? R : never }[Route];
export type Row<R extends ListRoute> = Response<R>[number];
export type Api = <R extends Route>(route: R, params?: Params, signal?: AbortSignal) => Promise<Response<R>>;
export type Paged = <R extends ListRoute>(container: HTMLElement, route: R, params: Params, render: (row: Row<R>) => Node, current: () => boolean, offset?: number) => Promise<void>;
// The mapped table preserves the route/result relationship across generic calls.
const decoders: { [R in Route]: Decoder<Response<R>> } = responses;
export function decodeResponse<R extends Route>(route: R, value: unknown): Response<R> {
  return decoders[route](value);
}
