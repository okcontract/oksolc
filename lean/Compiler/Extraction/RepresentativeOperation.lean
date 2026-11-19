/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeArray
import Compiler.Extraction.AssemblyItemFields

namespace Compiler.Extraction.RepresentativeArray.Operation
open Compiler.ZigAir.Memory Compiler.Algebraic

/-- The native return copies the descriptor and removes write permission. It
does not dereference, validate, sort or copy the independently owned operands. -/
def borrowed (address : Address) (length : Nat) : Value :=
  .slice (.slice false Expression.idType) address length

def arguments (state : State) (descriptor : Address) : Except Fault Value := do
  let .slice type address length ← Expression.readField state false descriptor Expression.argumentsOffset
    | .error .malformed
  if type ≠ Expression.argumentsType then .error .malformed else .ok (borrowed address length)

/-- Follow the admitted operationArguments body in its source read order.
Memory rejection and the invalid optional unwrap remain distinct from null.
Alternative source return forms need their own pointer-identity admission. -/
def read (state : State) (descriptor : Address) (opcode : BitVec 8) :
    Except Fault (Except Storage.ReadError (Option Value)) := do
  let .pointer type item ← Expression.readField state false descriptor Expression.itemOffset
    | .error .malformed
  if type ≠ Expression.itemType then .error .malformed else do
  let kind ← AssemblyItem.Fields.kind state item
  if (kind == 1) == Storage.operationProgram.rejectOnOperation then return .ok none else do
  let instruction ← AssemblyItem.Fields.instruction state item
  let some instruction := instruction | return .error .invalidOptional
  if (instruction == opcode) == Storage.operationProgram.rejectOnEqualOpcode then return .ok none else
  match Storage.operationProgram.arguments with
  | .stored => return .ok (some (← arguments state descriptor))
  | .empty => .error .unsupported

def run (state : State) (header : Address) (id : NodeId) (opcode : BitVec 8) :
    Except Fault (Except Storage.ReadError (Option Value)) := do
  let selected ← representative state header id
  match selected with
  | .error .invalidId => return .ok none
  | .error fault => return .error fault
  | .ok (.pointer type descriptor) =>
    if type ≠ .pointer false false Expression.allocationType then .error .malformed
    else read state descriptor opcode
  | .ok _ => .error .malformed

theorem arguments_from_field (state : State) (descriptor address : Address) (length : Nat)
    (loaded : Expression.readField state false descriptor Expression.argumentsOffset =
      .ok (.slice Expression.argumentsType address length)) :
    arguments state descriptor = .ok (borrowed address length) := by
  simp only [arguments, loaded, bind, Except.bind, ne_self_iff_false, ↓reduceIte]

/-- Invalid IDs return before any representative or item storage is read. -/
theorem invalid_id (state : State) (header data : Address) (length : Nat) (id : NodeId) (opcode : BitVec 8)
    (loaded : readItems state header = .ok (.slice itemsType data length)) (outside : length ≤ id.toNat) :
    run state header id opcode = .ok (.ok none) := by
  simp only [run, invalid_from_loaded_header state header data length id loaded outside,
    bind, Except.bind, pure, Except.pure]

end Compiler.Extraction.RepresentativeArray.Operation
