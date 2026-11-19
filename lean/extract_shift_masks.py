#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Admit complete shift-product and covered-mask helper bodies.
The native u8 shift-count cast remains an explicit fault outside its guard.
"""
import argparse
import hashlib
from extract_storage import function
from extract_cache import opcode_values
import extract_nested as nested

OUTPUT = nested.ROOT / 'lean/Compiler/Extraction/ShiftMasksProgram.lean'


def extract(data, opcodes, storage):
    nested.extract(data, opcodes, storage)
    function(data, 'const max_word =').expect('~@as(u256, 0);')
    function(data, 'fn removeCoveredShiftMask(classes: anytype, mask_id: ExpressionId, shifted_id: ExpressionId, debug_data: DebugData,) !?ExpressionId').expect('''{
        const mask = classes.knownConstantValue(mask_id) orelse return null;
        const shifted = classes.operationArguments(shifted_id, .SHR) orelse return null;
        if (shifted.len != 2) return null;
        const amount = classes.knownConstantValue(shifted[0]) orelse return null;
        if (amount > 256) return null;
        const coverage = if (amount == 256) @as(u256, 0) else max_word >> @intCast(amount);
        return if ((mask & coverage) == coverage)
            try classes.makeOperation(.SHR, shifted, debug_data)
        else null;
    }''')
    function(data, 'fn powerOfTwoShiftProduct(classes: anytype, value: ExpressionId, shift_id: ExpressionId, debug_data: DebugData,) !?ExpressionId').expect('''{
        const shift = classes.operationArguments(shift_id, .SHL) orelse return null;
        if (shift.len != 2 or classes.knownConstantValue(shift[1]) != 1) return null;
        return try classes.makeOperation(.SHL, &.{ shift[0], value }, debug_data);
    }''')
    bindings = opcode_values(opcodes)
    return ('/-\n// SPDX-License-Identifier: GPL-3.0\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n-/\n'
        'import Compiler.Extraction.ShiftMasks\n\nnamespace Compiler.Extraction.ShiftMasks\n'
        'open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage\n'
        'open Compiler.Extraction.Interner Compiler.Extraction.Nested Contract.Yul\n\n'
        'variable {m : Type → Type} [Monad m] [MonadLift (Except Interner.Error) m]\n\n'
        '-- Source SHA-256: ' + hashlib.sha256(data).hexdigest() + '\n'
        '-- Opcodes SHA-256: ' + hashlib.sha256(opcodes).hexdigest() + '\n'
        '-- Expression classes SHA-256: ' + hashlib.sha256(storage).hexdigest() + '\n'
        'def shlOpcode : Opcode := ' + str(bindings['SHL']) + '\n'
        'def shrOpcode : Opcode := ' + str(bindings['SHR']) + '\n' + '''
def shiftedCoverage (amount : Word) : Except ReadError Word :=
  if amount.toNat == 256 then .ok 0 else
  if amount.toNat < 256 then .ok (BitVec.allOnes 256 >>> amount.toNat) else .error .safetyFault

def removeCoveredShiftMask (reads : Reads) (constructors : Compiler.Extraction.Associative.Constructors Debug m)
    (maskId shiftedId : NodeId) (debug : Debug)
    (query : QueryRead m := fun action => readAction (action reads)) : m (Option NodeId) := do
  let some mask ← query (fun reads => reads.constant maskId) | return none
  let some shifted ← query (fun reads => reads.operation shiftedId shrOpcode) | return none
  match shifted.items with
  | [amountId, _] =>
    let some amount ← query (fun reads => reads.constant amountId) | return none
    if amount.toNat > 256 then return none
    let coverage ← readAction (shiftedCoverage amount)
    if mask &&& coverage == coverage then
      return some (← constructors.borrowedOperation shifted.address shrOpcode shifted.items debug)
    return none
  | _ => return none

@[reducible] def powerOfTwoShiftProductWithInputs (reads : Reads) (build : OperationBuilder Debug m)
    (value shiftId : NodeId) (debug : Debug)
    (operand : OperandRead m := logicalOperand)
    (query : QueryRead m := fun action => readAction (action reads)) : m (Option NodeId) := do
  let some shift ← query (fun reads => reads.operation shiftId shlOpcode) | return none
  match shift.items with
  | [amountId, baseId] =>
    if (← query (fun reads => reads.constant baseId)) != some 1 then return none
    return some (← build shlOpcode [← operand shift 0 amountId, value] debug)
  | _ => return none


/-- Logical projection of the same source body. -/
def powerOfTwoShiftProduct (reads : Reads) (build : OperationBuilder Debug m)
    (value shiftId : NodeId) (debug : Debug) : m (Option NodeId) :=
  powerOfTwoShiftProductWithInputs reads build value shiftId debug

end Compiler.Extraction.ShiftMasks
''').encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    emitted = extract(nested.SOURCE.read_bytes(), nested.OPCODES.read_bytes(), nested.STORAGE.read_bytes())
    if args.check:
        if OUTPUT.read_bytes() != emitted:
            raise SystemExit('stale shift-mask extraction')
    else:
        OUTPUT.write_bytes(emitted)


if __name__ == '__main__':
    main()
