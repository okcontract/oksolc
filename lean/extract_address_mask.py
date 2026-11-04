#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Admit the complete native addressInstruction helper, retaining ordered probes,
the exact 160-bit mask, zero arity and short-circuit read faults.
"""
import argparse
import hashlib
from extract_storage import function
from extract_cache import opcode_values
import extract_nested as nested

OUTPUT = nested.ROOT / 'lean/Compiler/Extraction/AddressMaskProgram.lean'


def extract(data, opcodes, storage):
    nested.extract(data, opcodes, storage)
    function(data, 'fn addressInstruction(classes: anytype, operation_id: ExpressionId, mask_id: ExpressionId) ?Instruction').expect('''{
        if (classes.knownConstantValue(mask_id) != ((@as(u256, 1) << 160) - 1)) return null;
        inline for ([_]Instruction{ .ADDRESS, .CALLER, .ORIGIN, .COINBASE }) |instruction| {
            if (classes.operationArguments(operation_id, instruction)) |arguments|
                if (arguments.len == 0) return instruction;
        }
        return null;
    }''')
    bindings = opcode_values(opcodes)
    return ('/-\n// SPDX-License-Identifier: GPL-3.0\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n-/\n'
        'import Compiler.Extraction.AddressMask\n\nnamespace Compiler.Extraction.AddressMask\n'
        'open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage\n'
        'open Compiler.Extraction.Nested Contract.Yul\n\n'
        '-- Source SHA-256: ' + hashlib.sha256(data).hexdigest() + '\n'
        '-- Opcodes SHA-256: ' + hashlib.sha256(opcodes).hexdigest() + '\n'
        '-- Expression classes SHA-256: ' + hashlib.sha256(storage).hexdigest() + '\n'
        'def addressOpcodes : List Opcode := [' + ', '.join(str(bindings[name]) for name in
            ['ADDRESS', 'CALLER', 'ORIGIN', 'COINBASE']) + ']\n' + '''
-- A closed compile-time expression; its non-wrapping subtraction is proved safe.
def nativeMask : Word := ((1 : Word) <<< 160) - 1

def search (reads : Reads) (operationId : NodeId) : List Opcode → Except ReadError (Option Opcode)
  | [] => .ok none
  | instruction :: rest => do
    if let some arguments ← reads.operation operationId instruction then
      if arguments.items.isEmpty then return some instruction
    search reads operationId rest

def addressInstruction (reads : Reads) (operationId maskId : NodeId) : Except ReadError (Option Opcode) := do
  if (← reads.constant maskId) != some nativeMask then return none
  search reads operationId addressOpcodes

end Compiler.Extraction.AddressMask
''').encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    emitted = extract(nested.SOURCE.read_bytes(), nested.OPCODES.read_bytes(), nested.STORAGE.read_bytes())
    if args.check:
        if OUTPUT.read_bytes() != emitted:
            raise SystemExit('stale address-mask extraction')
    else:
        OUTPUT.write_bytes(emitted)


if __name__ == '__main__':
    main()
