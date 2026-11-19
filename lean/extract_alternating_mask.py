#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Closed admission of all eight distribution candidates and five constructors.
"""
import argparse
import hashlib
from extract_storage import function
from extract_cache import opcode_values
import extract_nested as nested

OUTPUT = nested.ROOT / 'lean/Compiler/Extraction/AlternatingMaskProgram.lean'


def extract(data, opcodes, storage):
    nested.extract(data, opcodes, storage)
    function(data, '''fn distributeAlternatingMask(
        classes: anytype, outer_left: ExpressionId, outer_right: ExpressionId,
        debug_data: DebugData,
    ) !?ExpressionId''').expect('''{
    const outer_arguments = [2]ExpressionId{ outer_left, outer_right };

    // Preserve the exact nested-loop order in RuleList.h. Both alternatives
    // can themselves be ANDs with constants, so collapsing the commutative
    // variants into splitConstant() changes which alternative is captured as
    // X. That operand order remains observable after stack allocation.
    for ([_]bool{ false, true }) |constant_first| {
        for (0..2) |inner_index| {
            for (0..2) |second_index| {
                const second_id = outer_arguments[second_index];
                const outer_mask_id = outer_arguments[1 - second_index];
                const outer_mask = classes.knownConstantValue(outer_mask_id) orelse continue;
                const alternatives = classes.operationArguments(second_id, .OR) orelse continue;
                if (alternatives.len != 2) continue;
                const inner = classes.operationArguments(alternatives[inner_index], .AND) orelse continue;
                if (inner.len != 2) continue;
                const constant_index: usize = @intFromBool(constant_first == false);
                const expression_index = 1 - constant_index;
                const inner_mask = classes.knownConstantValue(inner[constant_index]) orelse continue;

                const left = try classes.makeOperation(
                    .AND,
                    &.{ inner[expression_index], try classes.makeConstant(inner_mask & outer_mask, debug_data) },
                    debug_data,
                );
                // A Constant pattern captures the resolved literal rather
                // than the SSA identifier through which it was discovered.
                const materialized_outer_mask = try classes.materializeConstant(
                    outer_mask_id,
                    outer_mask,
                    debug_data,
                );
                const right = try classes.makeOperation(
                    .AND,
                    &.{ alternatives[1 - inner_index], materialized_outer_mask },
                    debug_data,
                );
                return try classes.makeOperation(.OR, &.{ left, right }, debug_data);
            }
        }
    }
    return null;
}''')
    bindings = opcode_values(opcodes)
    return ('/-\n// SPDX-License-Identifier: GPL-3.0\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n-/\n'
        'import Compiler.Extraction.AlternatingMask\n\nnamespace Compiler.Extraction.AlternatingMask\n'
        'open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage\n'
        'open Compiler.Extraction.Interner Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul\n\n'
        'variable {m : Type → Type} [Monad m] [MonadLift (Except Interner.Error) m]\n\n'
        '-- Source SHA-256: ' + hashlib.sha256(data).hexdigest() + '\n'
        '-- Opcodes SHA-256: ' + hashlib.sha256(opcodes).hexdigest() + '\n'
        '-- Expression classes SHA-256: ' + hashlib.sha256(storage).hexdigest() + '\n'
        'def andOpcode : Opcode := ' + str(bindings['AND']) + '\n'
        'def orOpcode : Opcode := ' + str(bindings['OR']) + '\n' + '''
def choices : List Choice :=
  [⟨false, false, false⟩, ⟨false, false, true⟩,
   ⟨false, true, false⟩, ⟨false, true, true⟩,
   ⟨true, false, false⟩, ⟨true, false, true⟩,
   ⟨true, true, false⟩, ⟨true, true, true⟩]

def matchCandidate (reads : Reads) (choice : Choice) (outerLeft outerRight : NodeId) :
    Except ReadError (Option Capture) := do
  let secondId := pick choice.outerSecond outerLeft outerRight
  let outerMaskId := pick choice.outerSecond outerRight outerLeft
  let some outerMask ← reads.constant outerMaskId | return none
  let some alternatives ← reads.operation secondId orOpcode | return none
  let [altLeft, altRight] := alternatives.items | return none
  let some inner ← reads.operation (pick choice.innerSecond altLeft altRight) andOpcode | return none
  let [innerLeft, innerRight] := inner.items | return none
  let some innerMask ← reads.constant (pick choice.constantFirst innerRight innerLeft) | return none
  return some ⟨pick choice.constantFirst innerLeft innerRight,
    pick choice.innerSecond altRight altLeft, outerMaskId, innerMask, outerMask,
    inner, alternatives, if choice.constantFirst then 1 else 0, if choice.innerSecond then 0 else 1⟩

@[reducible] def buildCandidateWithInputs (constructors : Constructors Debug m) (capture : Capture) (debug : Debug) (operand : OperandRead m := logicalOperand) : m NodeId := do
  let expression ← operand capture.inner capture.expressionIndex capture.expression
  let constant ← constructors.constant (capture.innerMask &&& capture.outerMask) debug
  let left ← constructors.operation andOpcode [expression, constant] debug
  let materialized ← constructors.materialize capture.outerMaskId capture.outerMask debug
  let right ← constructors.operation andOpcode [← operand capture.alternatives capture.otherIndex capture.otherExpression, materialized] debug
  ConstructorPair.scalars constructors orOpcode left right debug


/-- Logical projection of the same source body. -/
def buildCandidate (constructors : Constructors Debug m) (capture : Capture) (debug : Debug) : m NodeId :=
  buildCandidateWithInputs constructors capture debug

@[reducible] def searchWithInputs (reads : Reads) (constructors : Constructors Debug m) (outerLeft outerRight : NodeId)
    (debug : Debug) (candidates : List Choice) (operand : OperandRead m := logicalOperand)
    (query : QueryRead m := fun action => readAction (action reads)) : m (Option NodeId) :=
  match candidates with
  | [] => pure none
  | choice :: rest => do
    let some capture ← query (fun reads => matchCandidate reads choice outerLeft outerRight) |
      searchWithInputs reads constructors outerLeft outerRight debug rest operand query
    return some (← buildCandidateWithInputs constructors capture debug operand)


/-- Logical projection of the same source body. -/
def search (reads : Reads) (constructors : Constructors Debug m) (outerLeft outerRight : NodeId)
    (debug : Debug) (candidates : List Choice) : m (Option NodeId) :=
  searchWithInputs reads constructors outerLeft outerRight debug candidates

@[reducible] def distributeAlternatingMaskWithInputs (reads : Reads) (constructors : Constructors Debug m)
    (outerLeft outerRight : NodeId) (debug : Debug)
    (operand : OperandRead m := logicalOperand)
    (query : QueryRead m := fun action => readAction (action reads)) : m (Option NodeId) :=
  searchWithInputs reads constructors outerLeft outerRight debug choices operand query


/-- Logical projection of the same source body. -/
def distributeAlternatingMask (reads : Reads) (constructors : Constructors Debug m)
    (outerLeft outerRight : NodeId) (debug : Debug) : m (Option NodeId) :=
  distributeAlternatingMaskWithInputs reads constructors outerLeft outerRight debug

end Compiler.Extraction.AlternatingMask
''').encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    emitted = extract(nested.SOURCE.read_bytes(), nested.OPCODES.read_bytes(), nested.STORAGE.read_bytes())
    if args.check:
        if OUTPUT.read_bytes() != emitted:
            raise SystemExit('stale alternating-mask extraction')
    else:
        OUTPUT.write_bytes(emitted)


if __name__ == '__main__':
    main()
