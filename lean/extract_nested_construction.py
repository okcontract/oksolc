#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Admit complete node-producing nested helpers, preserving calls and capture order.
The read-only prefix is factored from its constructor continuation. Native array
accesses and update are dominated by the exact two-element length guard.
"""
import argparse
import hashlib
from extract_storage import function
from extract_cache import opcode_values
import extract_nested as nested

OUTPUT = nested.ROOT / 'lean/Compiler/Extraction/NestedConstructionProgram.lean'

HELPERS = [
    ('fn doubleIsZero(classes: anytype, value: ExpressionId, debug_data: DebugData) !ExpressionId', '''{
        const inner = try classes.makeOperation(.ISZERO, &.{value}, debug_data);
        return classes.makeOperation(.ISZERO, &.{inner}, debug_data);
    }''', '''
def doubleIsZero (build : OperationBuilder Debug m) (value : NodeId) (debug : Debug) : m NodeId := do
  let inner ← build nestedIszeroOpcode [value] debug
  build nestedIszeroOpcode [inner] debug
'''),
    ('fn dropRepeatedNested(classes: anytype, instruction: Instruction, nested_id: ExpressionId, repeated: ExpressionId, repeated_is_first: bool, debug_data: DebugData,) !?ExpressionId', '''{
        const nested = classes.operationArguments(nested_id, instruction) orelse return null;
        if (nested.len != 2) return null;
        const repeated_index: usize = if (sameExpression(classes, nested[1], repeated)) 1 else if (sameExpression(classes, nested[0], repeated)) 0 else return null;
        var operands = [2]ExpressionId{ nested[0], nested[1] };
        if (repeated_is_first) operands[repeated_index] = repeated;
        return try classes.makeOperation(instruction, &operands, debug_data);
    }''', '''
def repeatedIndex (reads : Reads) (left right repeated : NodeId) : Option Nat :=
  if sameExpression reads right repeated then some 1
  else if sameExpression reads left repeated then some 0
  else none

def repeatedOperands (reads : Reads) (left right repeated : NodeId) (repeatedIsFirst : Bool) : Option (List NodeId) :=
  (repeatedIndex reads left right repeated).map
    (fun selected => localArguments ⟨0, [left, right]⟩ selected repeated repeatedIsFirst)

def dropRepeatedLocal (reads : Reads) (localBuild : LocalOperationBuilder Debug m) (instruction : Opcode)
    (nestedId repeated : NodeId) (repeatedIsFirst : Bool) (debug : Debug)
    (query : QueryRead m := fun action => readAction (action reads)) : m (Option NodeId) := do
  let some nested ← query (fun reads => reads.operation nestedId instruction) | return none
  match nested.items with
  | [left, right] =>
    let some selected := repeatedIndex reads left right repeated | return none
    return some (← localBuild instruction nested selected repeated repeatedIsFirst debug)
  | _ => return none

/-- Storage-erasing specialization for existing logical clients. Both entries
execute the same admitted query/selection body above. -/
def dropRepeatedNested (reads : Reads) (build : OperationBuilder Debug m) (instruction : Opcode)
    (nestedId repeated : NodeId) (repeatedIsFirst : Bool) (debug : Debug) : m (Option NodeId) :=
  dropRepeatedLocal reads (localBuilder build) instruction nestedId repeated repeatedIsFirst debug

'''),
]


def extract(data, opcodes, storage):
    # Bind the shared class/equality specialization and helper dependencies.
    nested.extract(data, opcodes, storage)
    definitions = []
    for header, body, lean in HELPERS:
        function(data, header).expect(body)
        definitions.append(lean)
    return ('/-\n// SPDX-License-Identifier: GPL-3.0\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n-/\n'
            'import Compiler.Extraction.NestedConstruction\n\nnamespace Compiler.Extraction.Nested\n'
            'open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner Contract.Yul\n\n'
            'variable {m : Type → Type} [Monad m] [MonadLift (Except Interner.Error) m]\n\n'
            '-- Source SHA-256: ' + hashlib.sha256(data).hexdigest() + '\n'
            '-- Opcodes SHA-256: ' + hashlib.sha256(opcodes).hexdigest() + '\n'
            '-- Expression classes SHA-256: ' + hashlib.sha256(storage).hexdigest() + '\n'
            'def nestedIszeroOpcode : Opcode := ' + str(opcode_values(opcodes)['ISZERO']) + '\n' +
            ''.join(definitions) + '\nend Compiler.Extraction.Nested\n').encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    emitted = extract(nested.SOURCE.read_bytes(), nested.OPCODES.read_bytes(), nested.STORAGE.read_bytes())
    if args.check:
        if OUTPUT.read_bytes() != emitted:
            raise SystemExit('stale nested construction extraction')
    else:
        OUTPUT.write_bytes(emitted)


if __name__ == '__main__':
    main()
