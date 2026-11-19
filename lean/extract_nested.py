#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Closed admission of complete native nested-matching helper bodies.
The fixed length guards and dominated accesses become list patterns; callback
order, first capture, nullable results and optional equality dispatch are kept.
"""
import argparse
import hashlib
from pathlib import Path
from extract_storage import function, lex
from extract_compiler import Unsupported
from extract_cache import opcode_values

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'src/libevmasm/rule_list.zig'
OPCODES = ROOT / 'src/libevmasm/instruction.zig'
STORAGE = ROOT / 'src/libevmasm/expression_classes.zig'
OUTPUT = ROOT / 'lean/Compiler/Extraction/NestedProgram.lean'

HELPERS = [
    ('fn sameExpression(classes: anytype, left: ExpressionId, right: ExpressionId) bool', '''{
        if (@hasDecl(@TypeOf(classes.*), "sameExpression")) return classes.sameExpression(left, right);
        return left == right; }''', '''
def sameExpression (reads : Reads) (left right : NodeId) : Bool :=
  match reads.overrideEquality with
  | some equal => equal left right
  | none => left == right
'''),
    ('fn splitConstant(classes: anytype, arguments: []const ExpressionId) ?ConstantOperand', '''{
        if (arguments.len != 2) return null;
        if (classes.knownConstantValue(arguments[1])) |value|
            return .{ .expression = arguments[0], .constant_expression = arguments[1], .value = value };
        if (classes.knownConstantValue(arguments[0])) |value|
            return .{ .expression = arguments[1], .constant_expression = arguments[0], .value = value };
        return null; }''', '''
def splitConstant (reads : Reads) (arguments : List NodeId) : Except ReadError (Option ConstantOperand) := do
  match arguments with
  | [left, right] =>
    if let some value ← reads.constant right then return some ⟨left, right, value⟩
    if let some value ← reads.constant left then return some ⟨right, left, value⟩
    return none
  | _ => return none
'''),
    ('fn cancelNestedBinary(classes: anytype, instruction: Instruction, single: ExpressionId, nested_id: ExpressionId,) !?ExpressionId', '''{
        const nested = classes.operationArguments(nested_id, instruction) orelse return null;
        if (nested.len != 2) return null;
        if (sameExpression(classes, nested[0], single)) return nested[1];
        if (sameExpression(classes, nested[1], single)) return nested[0];
        return null; }''', '''
def cancelNestedBinary (reads : Reads) (instruction : Opcode) (single nestedId : NodeId) :
    Except ReadError (Option NodeId) := do
  let some nested ← reads.operation nestedId instruction | return none
  match nested.items with
  | [left, right] =>
    if sameExpression reads left single then return some right
    if sameExpression reads right single then return some left
    return none
  | _ => return none
'''),
    ('fn absorbedOccurrence(classes: anytype, single: ExpressionId, nested_id: ExpressionId, nested_instruction: Instruction) ?ExpressionId', '''{
        const nested = classes.operationArguments(nested_id, nested_instruction) orelse return null;
        if (nested.len != 2) return null;
        for (nested) |operand| if (sameExpression(classes, operand, single)) return operand;
        return null; }''', '''
def absorbedOccurrence (reads : Reads) (single nestedId : NodeId) (instruction : Opcode) :
    Except ReadError (Option NodeId) := do
  let some nested ← reads.operation nestedId instruction | return none
  match nested.items with
  | [left, right] =>
    if sameExpression reads left single then return some left
    if sameExpression reads right single then return some right
    return none
  | _ => return none
'''),
    ('fn isNegation(classes: anytype, value: ExpressionId, possible_not: ExpressionId) bool', '''{
        const arguments = classes.operationArguments(possible_not, .NOT) orelse return false;
        return arguments.len == 1 and sameExpression(classes, arguments[0], value); }''', '''
def isNegation (reads : Reads) (value possibleNot : NodeId) : Except ReadError Bool := do
  let some arguments ← reads.operation possibleNot nestedNotOpcode | return false
  match arguments.items with
  | [operand] => return sameExpression reads operand value
  | _ => return false
'''),
]


def extract(data, opcodes, storage):
    # The concrete specialization uses ID equality only while this class has
    # no override. Reject any occurrence outside trivia, including new aliases
    # or declarations; do not silently retain the old @hasDecl result.
    if 'sameExpression' in lex(storage.decode('utf-8')):
        raise Unsupported('expression classes now expose or refer to equality override')
    function(storage, 'const RuleList =').expect('@import("rule_list.zig");')
    function(storage, 'pub const ExpressionClasses = struct').expect(
        '{ allocator: std.mem.Allocator, representatives: std.ArrayList(Expression) = .empty,'
        ' expressions: ExpressionMap = .empty,')
    function(data, 'const Instruction =').expect('@import("instruction.zig").Instruction;')
    function(data, 'pub const ExpressionId =').expect('u32;')
    function(data, 'const ConstantOperand = struct').expect(
        '{ expression: ExpressionId, constant_expression: ExpressionId, value: u256, };')
    bindings = opcode_values(opcodes)
    definitions = []
    for header, body, lean in HELPERS:
        function(data, header).expect(body)
        definitions.append(lean)
    return ('/-\n// SPDX-License-Identifier: GPL-3.0\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n-/\n'
            'import Compiler.Extraction.Nested\n\nnamespace Compiler.Extraction.Nested\n'
            'open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul\n\n'
            '-- Source SHA-256: ' + hashlib.sha256(data).hexdigest() + '\n'
            '-- Opcodes SHA-256: ' + hashlib.sha256(opcodes).hexdigest() + '\n'
            '-- Expression classes SHA-256: ' + hashlib.sha256(storage).hexdigest() + '\n'
            'def nestedNotOpcode : Opcode := ' + str(bindings['NOT']) + '\n' + ''.join(definitions) +
            '\nend Compiler.Extraction.Nested\n').encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    generated = extract(SOURCE.read_bytes(), OPCODES.read_bytes(), STORAGE.read_bytes())
    if args.check:
        if OUTPUT.read_bytes() != generated:
            parser.error('nested-helper extraction is stale; review source and proofs')
    else:
        OUTPUT.write_bytes(generated)


if __name__ == '__main__':
    main()
