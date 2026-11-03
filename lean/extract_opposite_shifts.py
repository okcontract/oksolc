#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Admit the complete opposite-shift helper. Integer casts and non-wrapping
subtraction retain safety faults; callers must establish their native bounds.
"""
import argparse
import hashlib
from extract_storage import function
from extract_cache import opcode_values
import extract_nested as nested

OUTPUT = nested.ROOT / 'lean/Compiler/Extraction/OppositeShiftsProgram.lean'


def extract(data, opcodes, storage):
    nested.extract(data, opcodes, storage)
    function(data, 'const max_word =').expect('~@as(u256, 0);')
    function(data, 'fn combineOppositeShifts(classes: anytype, outer_instruction: Instruction, outer_shift: u256, inner_shift: u256, value: ExpressionId, debug_data: DebugData,) !ExpressionId').expect('''{
        const mask = if (outer_instruction == .SHR)
            (max_word << @intCast(inner_shift)) >> @intCast(outer_shift)
        else (max_word >> @intCast(inner_shift)) << @intCast(outer_shift);
        const shifted = if (inner_shift > outer_shift)
            try classes.makeOperation(if (outer_instruction == .SHR) .SHL else .SHR,
                &.{ try classes.makeConstant(inner_shift - outer_shift, debug_data), value }, debug_data,)
        else if (outer_shift > inner_shift)
            try classes.makeOperation(outer_instruction,
                &.{ try classes.makeConstant(outer_shift - inner_shift, debug_data), value }, debug_data,)
        else value;
        return classes.makeOperation(.AND,
            &.{ shifted, try classes.makeConstant(mask, debug_data) }, debug_data,);
    }''')
    bindings = opcode_values(opcodes)
    return ('/-\n// SPDX-License-Identifier: GPL-3.0\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n-/\n'
        'import Compiler.Extraction.OppositeShifts\n\nnamespace Compiler.Extraction.OppositeShifts\n'
        'open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage\n'
        'open Compiler.Extraction.Interner Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul\n\n'
        'variable {m : Type → Type} [Monad m] [MonadLift (Except Interner.Error) m]\n\n'
        '-- Source SHA-256: ' + hashlib.sha256(data).hexdigest() + '\n'
        '-- Opcodes SHA-256: ' + hashlib.sha256(opcodes).hexdigest() + '\n'
        '-- Expression classes SHA-256: ' + hashlib.sha256(storage).hexdigest() + '\n' +
        ''.join('def ' + name.lower() + 'Opcode : Opcode := ' + str(bindings[name]) + '\n'
                for name in ['SHL', 'SHR', 'AND']) + '''
def oppositeOpcode (opcode : Opcode) : Opcode := if opcode == shrOpcode then shlOpcode else shrOpcode

def nativeMask (opcode : Opcode) (outer inner : Word) : Except ReadError Word :=
  if inner.toNat < 256 then
    if outer.toNat < 256 then
      if opcode == shrOpcode then .ok ((BitVec.allOnes 256 <<< inner.toNat) >>> outer.toNat)
      else .ok ((BitVec.allOnes 256 >>> inner.toNat) <<< outer.toNat)
    else .error .safetyFault
  else .error .safetyFault

def checkedDifference (left right : Word) : Except ReadError Word :=
  if right.toNat ≤ left.toNat then .ok (left - right) else .error .safetyFault

def buildNet (constructors : Constructors Debug m) (opcode : Opcode)
    (outer inner : Word) (value : NodeId) (debug : Debug) : m NodeId := do
  if inner.toNat > outer.toNat then
    let difference ← readAction (checkedDifference inner outer)
    let amount ← constructors.constant difference debug
    ConstructorPair.scalars constructors (oppositeOpcode opcode) amount value debug
  else if outer.toNat > inner.toNat then
    let difference ← readAction (checkedDifference outer inner)
    let amount ← constructors.constant difference debug
    ConstructorPair.scalars constructors opcode amount value debug
  else return value

def combineOppositeShifts (constructors : Constructors Debug m) (opcode : Opcode)
    (outer inner : Word) (value : NodeId) (debug : Debug) : m NodeId := do
  let mask ← readAction (nativeMask opcode outer inner)
  let shifted ← buildNet constructors opcode outer inner value debug
  let maskId ← constructors.constant mask debug
  ConstructorPair.scalars constructors andOpcode shifted maskId debug

end Compiler.Extraction.OppositeShifts
''').encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    emitted = extract(nested.SOURCE.read_bytes(), nested.OPCODES.read_bytes(), nested.STORAGE.read_bytes())
    if args.check:
        if OUTPUT.read_bytes() != emitted:
            raise SystemExit('stale opposite-shift extraction')
    else:
        OUTPUT.write_bytes(emitted)


if __name__ == '__main__':
    main()
