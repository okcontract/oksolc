#!/usr/bin/env python3
"""Admit a direct AssemblyItem member and its reviewed owned-field shape.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from extract_storage import function, struct_member


def member_body(data, name, signature):
    function(data, 'const std =').expect('@import("std");')
    function(data, 'const VerbatimBytecode =').expect(
        'struct { arguments: usize, return_variables: usize, data: []u8, };')
    return struct_member(data, 'const AssemblyItem =',
        'item_type: AssemblyItemType, instruction_value: ?InstructionModule.Instruction = null,'
        ' data_value: u256 = 0, verbatim: ?VerbatimBytecode = null, debug_data: DebugData = .{},'
        ' jump_type: JumpType = .Ordinary, pushed_value: ?u256 = null,'
        ' immutable_occurrences: ?usize = null, modifier_depth: usize = 0,', name, signature)
