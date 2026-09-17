// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

import { $ } from './ui.ts';

// Line offsets belong to the currently displayed buffer. Drop them before a
// navigation can expose a different file or snapshot to the jump control.
export function createSourcePosition(navigate: (start: number) => void) {
  let lines: readonly number[] = [], activeLine = 0;
  const form = $('line-jump'), input = $('line-number'), control = $('line-position');
  function close() { if (form.matches(':popover-open')) form.hidePopover(); }
  $('line-jump-close').addEventListener('click', close);
  form.addEventListener('beforetoggle', (event) => {
    if (event.newState !== 'open') return;
    input.value = String(activeLine + 1);
  });
  form.addEventListener('toggle', (event) => { if (event.newState === 'open') input.select(); });
  form.addEventListener('submit', (event) => {
    event.preventDefault();
    if (!form.reportValidity()) return;
    const start = lines[input.valueAsNumber - 1];
    if (start === undefined) return;
    close(); navigate(start);
  });
  return {
    clear(message = 'Ready') {
      close(); lines = []; control.hidden = true; $('position').textContent = message;
    },
    show(offsets: readonly number[], line: number, bytes: number) {
      lines = offsets; activeLine = line;
      input.max = String(lines.length);
      $('line-range').textContent = `(1–${lines.length.toLocaleString()})`;
      control.textContent = `Ln ${(line + 1).toLocaleString()} / ${lines.length.toLocaleString()}`;
      control.hidden = false;
      $('position').textContent = `UTF-8 · ${bytes.toLocaleString()} bytes`;
    },
  };
}
