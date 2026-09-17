// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

import { $ } from './ui.ts';
import type { Row } from './model.ts';

const compact = (value: number) => value.toLocaleString(undefined, { notation: 'compact', maximumFractionDigits: 1 });

export function createSummary(openDiagnostics: () => void) {
  const diagnostics = $('diagnostics-summary');
  diagnostics.addEventListener('click', openDiagnostics);
  return (rows: Row<'summary'>[], compiled: boolean) => {
    const diagnosticRows = rows.filter((row) => row.kind === 'diagnostic');
    const diagnosticCount = diagnosticRows.reduce((sum, row) => sum + row.total, 0);
    const hidden = diagnosticRows.reduce((sum, row) => sum + row.hidden, 0);
    diagnostics.hidden = !compiled;
    diagnostics.textContent = `${compact(diagnosticCount)} diagnostics`;
    diagnostics.title = ['Compiler diagnostics across this compilation', ...diagnosticRows.map((row) => `${row.total.toLocaleString()} ${row.status}`), ...(hidden ? [`${hidden.toLocaleString()} library diagnostics hidden`] : [])].join('\n');
    diagnostics.classList.toggle('warning', diagnosticRows.some((row) => row.status === 'warning' && row.total > 0));
    diagnostics.classList.toggle('error', diagnosticRows.some((row) => row.status === 'error' && row.total > 0));
  };
}
