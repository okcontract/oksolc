#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Extract actual constant/operation wrappers and their AssemblyItem constructors.
This semantic projection frames debug metadata and binds all observed defaults.
"""
import argparse
import hashlib
import re
from pathlib import Path
from extract_compiler import Unsupported
from extract_storage import function
from extract_cache import opcode_values
from extract_assembly_item import member_body

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'src/libevmasm/expression_classes.zig'
ITEMS = ROOT / 'src/libevmasm/assembly_item.zig'
OPCODES = ROOT / 'src/libevmasm/instruction.zig'
OUTPUT = ROOT / 'lean/Compiler/Extraction/ConstructorProgram.lean'


def integer(p, bits):
    token = p.pop()
    if not re.fullmatch(r'[0-9]+', token) or int(token) >= 2**bits:
        raise Unsupported('unsupported constructor integer')
    return token


def extract(data, items, opcodes):
    bindings = opcode_values(opcodes)
    function(data, 'pub const Id = u32').expect(';')
    p = function(items, 'pub const AssemblyItemType = enum(c_int)')
    p.expect('{ UndefinedItem, Operation, Push, PushTag, PushSub, PushSubSize, PushProgramSize, Tag,'
             ' PushData, PushLibraryAddress, PushDeployTimeAddress, PushImmutable, AssignImmutable, VerbatimBytecode, };')
    # Reuse complete member/field admission, including declarations after
    # methods. A matching field prefix alone does not describe the whole item.
    for name, signature, body in (
        ('initPush', 'pub fn initPush(value: u256, debug_data: DebugData) AssemblyItem',
         'return initType(.Push, value, debug_data);'),
        ('initType', 'pub fn initType(item_type: AssemblyItemType, value: u256, debug_data: DebugData,) AssemblyItem',
         'return if (item_type == .Operation) initInstruction(@fromBackingInt(@intCast(@as(u8, @truncate(value)))), debug_data)'
         ' else .{ .item_type = item_type, .data_value = value, .debug_data = debug_data, };'),
        ('initInstruction', 'pub fn initInstruction(opcode: InstructionModule.Instruction, debug_data: DebugData,) AssemblyItem',
         'return .{ .item_type = .Operation, .instruction_value = opcode, .debug_data = debug_data, };')):
        p = member_body(items, name, signature)
        p.expect(body)
        if p.pos != len(p.items):
            raise Unsupported('unreviewed AssemblyItem initializer suffix: ' + name)
    p = function(data, 'pub fn findDefault(self: *ExpressionClasses, item: *const AssemblyItem, arguments: []const Id,) ExpressionError!Id')
    p.expect('{ return self.find(item, arguments, true,')
    sequence = integer(p, 32)
    p.expect('); }')
    p = function(data, 'pub fn makeConstant(self: *ExpressionClasses, value: u256, debug_data: DebugData,) ExpressionError!Id')
    p.expect('{ const item = AssemblyItem.initPush(')
    constant = '.input' if p.take('value') else '(.literal ' + integer(p, 256) + ')'
    p.expect(', debug_data); return self.findDefault(&item, &.{}); }')
    p = function(data, 'pub fn makeOperation(self: *ExpressionClasses, instruction: Instruction, arguments: []const Id, debug_data: DebugData,) ExpressionError!Id')
    p.expect('{ const item = AssemblyItem.initInstruction(')
    if p.take('instruction'):
        instruction = '.input'
    else:
        p.expect('.')
        name = p.ident()
        if name not in bindings:
            raise Unsupported('unknown constructor opcode')
        instruction = '(.literal ' + str(bindings[name]) + ')'
    p.expect(', debug_data); return self.findDefault(&item, arguments); }')
    if any(name not in bindings for name in ['NOT', 'SUB', 'ISZERO']):
        raise Unsupported('missing constructor opcode')
    codes = '\n'.join('  | .' + name + ' => ' + str(bindings[name]) for name in ['NOT', 'SUB', 'ISZERO'])
    hashes = '\n'.join('-- ' + name + ' SHA-256: ' + hashlib.sha256(value).hexdigest()
                       for name, value in [('Constructors', data), ('AssemblyItem', items), ('Opcodes', opcodes)])
    return ('/-\n// SPDX-License-Identifier: GPL-3.0\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n-/\n'
        'import Compiler.Extraction.Constructor\n\nnamespace Compiler.Extraction.Interner\n'
        'open Compiler.Algebraic Compiler.Extraction.Cache\n\n' + hashes + '\n'
        'def constructorCode : ConstructorCode := { constant := ' + constant + ', instruction := ' + instruction +
        ', sequence := ' + sequence + ' }\n\ndef buildOpcode : BuildOp → Opcode\n' + codes +
        '\n\nend Compiler.Extraction.Interner\n').encode()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--check', action='store_true')
    args = p.parse_args()
    output = extract(SOURCE.read_bytes(), ITEMS.read_bytes(), OPCODES.read_bytes())
    if args.check:
        if OUTPUT.read_bytes() != output:
            p.error('constructor extraction is stale; review source and proofs')
    else:
        OUTPUT.write_bytes(output)


if __name__ == '__main__':
    main()
