// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

export fn fill(p: [*]u32, length: usize, value: u32) void {
    @setRuntimeSafety(false);
    var index: usize = 0;
    while (index < length) : (index += 1) {
        p[index] = value;
    }
}

// Forward copy deliberately permits overlapping source and destination views.
export fn copy_forward(destination: [*]u32, source: [*]const u32, length: usize) void {
    @setRuntimeSafety(false);
    var index: usize = 0;
    while (index < length) : (index += 1) {
        destination[index] = source[index];
    }
}

export fn nested_continue(p: [*]u32, rows: usize, columns: usize, stop: usize, value: u32) void {
    @setRuntimeSafety(false);
    var row: usize = 0;
    var column: usize = 0;
    outer: while (row < rows) : (row += 1) {
        column = 0;
        while (column < columns) : (column += 1) {
            if (column == stop) continue :outer;
            p[row * columns + column] = value;
        }
    }
}
