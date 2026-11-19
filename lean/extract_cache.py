#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Extract actual key fields, equality tests and normalization decisions. The
parser and identification of memcpy/sort/container primitives remain trusted.
"""
import argparse
import hashlib
from pathlib import Path
import re

from extract_compiler import Unsupported
from extract_storage import function, lex

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'src/libevmasm/expression_classes.zig'
SEMANTICS = ROOT / 'src/libevmasm/semantic_information.zig'
ITEMS = ROOT / 'src/libevmasm/assembly_item.zig'
OPCODES = ROOT / 'src/libevmasm/instruction.zig'
OUTPUT = ROOT / 'lean/Compiler/Extraction/CacheProgram.lean'


def scalar(p, expected):
    if p.peek() == expected.split('.')[0]:
        p.expect(expected)
        return '.input'
    token = p.pop()
    if not re.fullmatch(r'[0-9]+', token):
        raise Unsupported('unmodeled key scalar')
    return '(.literal ' + token + ')'


def condition(p):
    p.expect('item.item_type')
    op = p.pop()
    if op not in ('==', '!='):
        raise Unsupported('unmodeled item-kind comparison')
    p.expect('.Operation')
    return '.operation' if op == '==' else '.notOperation'


def opcode_values(data):
    """Admit the actual enum, excluding comments and unrelated declarations."""
    p = function(data, 'pub const Instruction = enum(u8)')
    p.expect('{')
    result = {}
    while not p.take('}'):
        name = p.ident()
        if name == '_':
            p.expect(',')
            continue
        p.expect('=')
        value = p.pop()
        if name in result or not re.fullmatch(r'0x[0-9a-fA-F]+|[0-9]+', value):
            raise Unsupported('unmodeled or duplicate opcode binding')
        number = int(value, 16 if value.startswith('0x') else 10)
        if not 0 <= number < 256:
            raise Unsupported('opcode exceeds u8')
        p.expect(',')
        result[name] = number
    p.expect(';')
    return result


def comparison(p):
    value = p.pop()
    names = {'<': 'lt', '<=': 'le', '>': 'gt', '>=': 'ge'}
    if value not in names:
        raise Unsupported('unmodeled normalization length comparison')
    return names[value]


def extract(data, semantics, items, opcodes):
    # Key item-kind numbers are source-bound c_int values, with no C ABI layout
    # proof claimed. Refuse a reorder or new explicit ordinal here.
    p = function(items, 'pub const AssemblyItemType = enum(c_int)')
    p.expect('{ UndefinedItem, Operation, Push, PushTag, PushSub, PushSubSize, PushProgramSize, Tag,'
             ' PushData, PushLibraryAddress, PushDeployTimeAddress, PushImmutable, AssignImmutable, VerbatimBytecode, };')
    tokens, binding = lex(data.decode()), lex('pub const Id = u32;')
    if sum(tokens[i:i+len(binding)] == binding for i in range(len(tokens))) != 1:
        raise Unsupported('cache ID width changed')
    p = function(data, 'const ExpressionKey = struct')
    p.expect('{ item_type: AssemblyItemType, instruction: u8, data: u256, arguments: []const Id, sequence_number: u32, };')
    p = function(data, 'fn makeKey(item: *const AssemblyItem, arguments: []const Id, sequence_number: u32) ExpressionKey')
    p.expect('{ return .{ .item_type =')
    kind = scalar(p, 'item.item_type')
    p.expect(', .instruction = if (')
    instruction_test = condition(p)
    p.expect(') @backingInt(item.instruction_value.?) else 0, .data = if (')
    data_test = condition(p)
    p.expect(')')
    yes = scalar(p, 'item.data_value')
    p.expect('else')
    no = scalar(p, 'item.data_value')
    p.expect(', .arguments = arguments, .sequence_number =')
    sequence = scalar(p, 'sequence_number')
    p.expect(', }; }')
    p = function(data, 'pub fn eql(_: @This(), left: ExpressionKey, right: ExpressionKey) bool')
    p.expect('{ return')
    fields = []
    names = {'item_type': 'kind', 'instruction': 'instruction', 'data': 'data', 'sequence_number': 'sequence'}
    while True:
        if p.take('std'):
            p.expect('.mem.eql(Id, left.arguments, right.arguments)')
            fields.append('.arguments')
        else:
            p.expect('left.')
            field = p.pop()
            if field not in names:
                raise Unsupported('unknown key field')
            p.expect('== right.' + field)
            fields.append('.' + names[field])
        if not p.take('and'):
            break
    p.expect('; }')
    p = function(semantics, 'pub fn isCommutativeOperation(item: *const AssemblyItemModule.AssemblyItem) bool')
    p.expect('{ if (item.item_type')
    rejected = p.pop()
    if rejected not in ('==', '!='):
        raise Unsupported('unmodeled commutativity discriminator')
    p.expect('.Operation) return false; return switch (item.instruction_value.?) {')
    commutes = []
    bindings = opcode_values(opcodes)
    while p.take('.'):
        name = p.pop()
        if name not in bindings:
            raise Unsupported('unknown commutative opcode')
        commutes.append(str(bindings[name]))
        if not p.take(','):
            break
    p.expect('=> true, else => false, }; }')
    layout = function(data, 'const NormalizedArguments = struct')
    layout.expect('{ items: []const Id, owned: ?[]Id = null, fn init')
    p = function(data, 'fn init(allocator: std.mem.Allocator, item: *const AssemblyItem, arguments: []const Id, buffer: []Id) !NormalizedArguments')
    p.expect('{ if (!SemanticInformation.isCommutativeOperation(item) or arguments.len <')
    threshold = p.pop()
    if not re.fullmatch(r'[0-9]+', threshold):
        raise Unsupported('unmodeled normalization threshold')
    p.expect(') return .{ .items = arguments }; const normalized = if (arguments.len')
    scratch = comparison(p)
    p.expect('buffer.len) buffer[0..arguments.len] else try allocator.alloc(Id, arguments.len);'
             ' @memcpy(normalized, arguments); std.sort.insertion(Id, normalized, {}, std.sort.asc(Id));'
             ' return .{ .items = normalized, .owned = if (arguments.len')
    owned = comparison(p)
    p.expect('buffer.len) normalized else null, }; }')
    p = function(data, 'fn deinit(self: *NormalizedArguments, allocator: std.mem.Allocator) void')
    p.expect('{')
    frees = p.take('if')
    if frees:
        p.expect('(self.owned) |owned| allocator.free(owned);')
    p.expect('self.* = undefined; }')
    p = function(data, 'fn takeOwned(self: *NormalizedArguments, allocator: std.mem.Allocator) ![]Id')
    p.expect('{ if (self.owned) |owned| {')
    clears = p.take('self')
    if clears:
        p.expect('.owned = null;')
    p.expect('return owned; } return allocator.dupe(Id, self.items); }')
    hashes = '\n'.join('-- ' + label + ' SHA-256: ' + hashlib.sha256(value).hexdigest()
                       for label, value in [('Expression classes',data),('Semantic information',semantics),('Item kinds',items),('Opcodes',opcodes)])
    return ('/-\n// SPDX-License-Identifier: GPL-3.0\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n-/\n'
        'import Compiler.Extraction.NormalizationOwnership\n\nnamespace Compiler.Extraction.Cache\n\n' + hashes + '\n'
        'def keyCode : KeyCode := { kind := ' + kind + ', instructionTest := ' + instruction_test +
        ', dataTest := ' + data_test + ', operationData := ' + yes + ', otherData := ' + no + ', sequence := ' + sequence + ' }\n'
        'def equalityFields : List Field := [' + ', '.join(fields) + ']\n'
        'def normalizeCode : NormalizeCode := { commutative := [' + ', '.join(commutes) + '], guard := ' +
        ('.operation' if rejected == '!=' else '.notOperation') + ', threshold := ' + threshold + ' }\n'
        'def normalizationOwnershipCode : NormalizationOwnership.Code := { threshold := ' + threshold +
        ', useScratch := .' + scratch + ', ownTemporary := .' + owned +
        ', clearOnTake := ' + str(clears).lower() + ', freeOnDeinit := ' + str(frees).lower() + ' }\n\n'
        'end Compiler.Extraction.Cache\n').encode()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--check', action='store_true')
    args = p.parse_args()
    output = extract(SOURCE.read_bytes(), SEMANTICS.read_bytes(), ITEMS.read_bytes(), OPCODES.read_bytes())
    if args.check:
        if OUTPUT.read_bytes() != output:
            p.error('cache extraction is stale; review source and proofs')
    else:
        OUTPUT.write_bytes(output)


if __name__ == '__main__':
    main()
