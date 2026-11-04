#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Admit the complete native sign-extension mask-removal helper.
Reuse the checked Zig arithmetic model; retain faults before construction.
"""
import argparse
import hashlib
from extract_storage import function
from extract_cache import opcode_values
import extract_nested as nested

OUTPUT = nested.ROOT / 'lean/Compiler/Extraction/SignExtendMaskProgram.lean'


def extract(data, opcodes, storage):
    nested.extract(data, opcodes, storage)
    function(data, 'fn stripRedundantSignExtendMask(classes: anytype, constant_id: ExpressionId, sign_extend_id: ExpressionId, debug_data: DebugData,) !?ExpressionId').expect('''{
        const mask = classes.knownConstantValue(constant_id) orelse return null;
        const sign_extend = classes.operationArguments(sign_extend_id, .SIGNEXTEND) orelse return null;
        if (sign_extend.len != 2) return null;
        const byte_index = classes.knownConstantValue(sign_extend[0]) orelse return null;
        if (byte_index >= 31) return null;
        const bit_count: u8 = @intCast((byte_index + 1) * 8);
        const low_mask = (@as(u256, 1) << bit_count) - 1;
        if ((mask & low_mask) != mask) return null;
        const materialized_mask = try classes.materializeConstant(constant_id, mask, debug_data);
        return try classes.makeOperation(.AND, &.{ materialized_mask, sign_extend[1] }, debug_data);
    }''')
    bindings = opcode_values(opcodes)
    return ('/-\n// SPDX-License-Identifier: GPL-3.0\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n-/\n'
        'import Compiler.Extraction.SignExtendMask\n\nnamespace Compiler.Extraction.SignExtendMask\n'
        'open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage\n'
        'open Compiler.Extraction.Interner Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul\n\n'
        'variable {m : Type → Type} [Monad m] [MonadLift (Except Interner.Error) m]\n\n'
        '-- Source SHA-256: ' + hashlib.sha256(data).hexdigest() + '\n'
        '-- Opcodes SHA-256: ' + hashlib.sha256(opcodes).hexdigest() + '\n'
        '-- Expression classes SHA-256: ' + hashlib.sha256(storage).hexdigest() + '\n'
        'def signextendOpcode : Opcode := ' + str(bindings['SIGNEXTEND']) + '\n'
        'def andOpcode : Opcode := ' + str(bindings['AND']) + '\n' + '''
def nativeLowMask (index : Word) : Folding.Result := do
  let incremented ← Folding.Zig.checkedAdd 256 index.toNat 1
  let product ← Folding.Zig.checkedMul 256 incremented 8
  let count ← Folding.Zig.narrow 8 product
  let high : Word := (1 : Word) <<< count
  let low ← Folding.Zig.checkedSub high.toNat 1
  return BitVec.ofNat 256 low

def lowMaskRead (index : Word) : Except ReadError Word :=
  match nativeLowMask index with
  | .ok mask => .ok mask
  | .error _ => .error .safetyFault

@[reducible] def stripRedundantSignExtendMaskWithInputs (reads : Reads) (constructors : Constructors Debug m)
    (constantId signExtendId : NodeId) (debug : Debug)
    (operand : OperandRead m := logicalOperand)
    (query : QueryRead m := fun action => readAction (action reads)) : m (Option NodeId) := do
  let some mask ← query (fun reads => reads.constant constantId) | return none
  let some extended ← query (fun reads => reads.operation signExtendId signextendOpcode) | return none
  match extended.items with
  | [indexId, valueId] =>
    let some index ← query (fun reads => reads.constant indexId) | return none
    if index.toNat ≥ 31 then return none
    let low ← readAction (lowMaskRead index)
    if mask &&& low != mask then return none
    let materialized ← constructors.materialize constantId mask debug
    return some (← constructors.operation andOpcode [materialized, ← operand extended 1 valueId] debug)
  | _ => return none


/-- Logical projection of the same source body. -/
def stripRedundantSignExtendMask (reads : Reads) (constructors : Constructors Debug m)
    (constantId signExtendId : NodeId) (debug : Debug) : m (Option NodeId) :=
  stripRedundantSignExtendMaskWithInputs reads constructors constantId signExtendId debug

end Compiler.Extraction.SignExtendMask
''').encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    emitted = extract(nested.SOURCE.read_bytes(), nested.OPCODES.read_bytes(), nested.STORAGE.read_bytes())
    if args.check:
        if OUTPUT.read_bytes() != emitted:
            raise SystemExit('stale sign-extension mask extraction')
    else:
        OUTPUT.write_bytes(emitted)


if __name__ == '__main__':
    main()
