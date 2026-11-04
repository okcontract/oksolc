// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
export fn slice_element(pointer: [*]u32, length: usize, index: usize) *u32 {
    @setRuntimeSafety(false);
    const view = pointer[0..length];
    return &view[index];
}
