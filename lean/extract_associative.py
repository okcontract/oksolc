#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Complete source admission for associative selection, combination and construction.
Native unreachable stays a modeled safety fault, never a missing rewrite.
"""
import argparse
import hashlib
from extract_storage import function
from extract_cache import opcode_values
import extract_nested as nested

OUTPUT = nested.ROOT / 'lean/Compiler/Extraction/AssociativeProgram.lean'

def extract(data, opcodes, storage):
    nested.extract(data, opcodes, storage)
    function(data, 'fn isAssociative(instruction: Instruction) bool').expect('''{
        return switch (instruction) { .ADD, .MUL, .AND, .OR, .XOR => true, else => false, }; }''')
    function(data, 'fn combineConstants(instruction: Instruction, left: u256, right: u256) u256').expect('''{
        return switch (instruction) { .ADD => left +% right, .MUL => left *% right,
        .AND => left & right, .OR => left | right, .XOR => left ^ right, else => unreachable, }; }''')
    function(storage, 'pub fn materializeConstant(self: *ExpressionClasses, _: Id, value: u256, debug_data: DebugData,) ExpressionError!Id').expect('''{
        return self.makeConstant(value, debug_data); }''')
    function(data, 'fn reassociate(classes: anytype, instruction: Instruction, nested_id: ExpressionId, other: ExpressionId, nested_is_right: bool, debug_data: DebugData,) !?ExpressionId').expect('''{
        const nested = classes.operationArguments(nested_id, instruction) orelse return null;
        const parts = splitConstant(classes, nested) orelse return null;
        if (classes.knownConstantValue(other)) |other_constant|
            return try classes.makeOperation(instruction,
                &.{ parts.expression, try classes.makeConstant(combineConstants(instruction, parts.value, other_constant), debug_data), },
                debug_data,);
        const inner = if (nested_is_right)
            try classes.makeOperation(instruction, &.{ other, parts.expression }, debug_data)
        else
            try classes.makeOperation(instruction, &.{ parts.expression, other }, debug_data);
        return try classes.makeOperation(instruction,
            &.{ inner, try classes.materializeConstant(parts.constant_expression, parts.value, debug_data) },
            debug_data,);
    }''')
    bindings = opcode_values(opcodes)
    codes = ', '.join(str(bindings[name]) for name in ['ADD', 'MUL', 'AND', 'OR', 'XOR'])
    branches = '\n'.join('  if instruction == ' + str(bindings[name]) + ' then .ok (left ' + operator + ' right) else'
                         for name, operator in [('ADD', '+'), ('MUL', '*'), ('AND', '&&&'), ('OR', '|||'), ('XOR', '^^^')])
    return ('/-\n// SPDX-License-Identifier: GPL-3.0\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n-/\n'
        'import Compiler.Extraction.ConstructorPair\n\nnamespace Compiler.Extraction.Associative\n'
        'open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage\n'
        'open Compiler.Extraction.Interner Compiler.Extraction.Nested Contract.Yul\n\n'
        'variable {m : Type → Type} [Monad m] [MonadLift (Except Interner.Error) m]\n\n'
        '-- Source SHA-256: ' + hashlib.sha256(data).hexdigest() + '\n'
        '-- Opcodes SHA-256: ' + hashlib.sha256(opcodes).hexdigest() + '\n'
        '-- Expression classes SHA-256: ' + hashlib.sha256(storage).hexdigest() + '\n'
        'def isAssociative (instruction : Opcode) : Bool := [' + codes + '].contains instruction\n\n'
        'def combineConstants (instruction : Opcode) (left right : Word) : Except ReadError Word :=\n' + branches +
        '\n  .error .safetyFault\n' + '''
def materializeConstant (make : Word → Debug → m NodeId) (_ : NodeId) (value : Word) (debug : Debug) : m NodeId :=
  make value debug

def reassociate (reads : Reads) (constructors : Constructors Debug m) (instruction : Opcode)
    (nestedId other : NodeId) (nestedIsRight : Bool) (debug : Debug)
    (query : QueryRead m := fun action => readAction (action reads)) : m (Option NodeId) := do
  let some nested ← query (fun reads => reads.operation nestedId instruction) | return none
  let some parts ← query (fun reads => splitConstant reads nested.items) | return none
  if let some otherConstant ← query (fun reads => reads.constant other) then
    let combined ← readAction (combineConstants instruction parts.value otherConstant)
    let constant ← constructors.constant combined debug
    return some (← ConstructorPair.scalars constructors instruction parts.expression constant debug)
  let inner ← if nestedIsRight then
    ConstructorPair.scalars constructors instruction other parts.expression debug
  else
    ConstructorPair.scalars constructors instruction parts.expression other debug
  let constant ← constructors.materialize parts.constantExpression parts.value debug
  return some (← ConstructorPair.scalars constructors instruction inner constant debug)

end Compiler.Extraction.Associative
''').encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    emitted = extract(nested.SOURCE.read_bytes(), nested.OPCODES.read_bytes(), nested.STORAGE.read_bytes())
    if args.check:
        if OUTPUT.read_bytes() != emitted:
            raise SystemExit('stale associative extraction')
    else:
        OUTPUT.write_bytes(emitted)


if __name__ == '__main__':
    main()
