/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerQueryProgram
import Compiler.Extraction.InternerCallerMemory

namespace Compiler.Extraction.Interner.Queries
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.Extraction.Memory.Arguments.Normalization
open Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall

/-- The native caller's closed query specialization. The private capacity
projection is used only after `admit` establishes a representative observation;
an absent graph is rejected before any capacity/cache/ownership operation. -/
def queries : Caller.Queries where
  atCapacity := fun heap => decide ((heap.representatives.getD []).length ≥ 2^32 - 1)
  deterministic := determinismCode.run
  validate := fun id heap => match heap.representatives with
    | none => .error .safetyFault
    | some cells => (representativeProgram.run cells id).mapError (fun
        | .invalidId => .invalidId | .invalidOptional => .invalidOptional | .safetyFault => .safetyFault) |>.map (fun _ => ())

/-- This is model admission, not an added check in the production compiler.
It refuses an absent native graph projection without running an abstract cache
or inventing a capacity/OOM result. Rejection preserves the exact reached state. -/
def admit (action : OwnedCall.Action σ α) : OwnedCall.Action σ α := fun before =>
  if before.world.graph.representatives.isSome then action before
  else (.error (.language .safetyFault), before)

theorem absent_rejected (action : OwnedCall.Action σ α) (before : OwnedCall.State σ)
    (absent : before.world.graph.representatives = none) :
    admit action before = (.error (.language .safetyFault), before) := by simp [admit, absent]

theorem present_execution (action : OwnedCall.Action σ α) (before : OwnedCall.State σ)
    (present : before.world.graph.representatives.isSome = true) :
    admit action before = action before := by simp [admit, present]

theorem capacity_exact (heap : Heap) (cells : List Cell) (present : heap.representatives = some cells) :
    queries.atCapacity heap = decide (2^32 - 1 ≤ cells.length) := by simp [queries, present]

theorem validation_exact (heap : Heap) (cells : List Cell) (present : heap.representatives = some cells) (id : NodeId) :
    queries.validate id heap = if id.toNat < cells.length then .ok () else .error .invalidId := by
  simp only [queries, present]
  rw [representative_correct]
  cases found : cells[id.toNat]? with
  | none => simp [Nat.not_lt.mpr (List.getElem?_eq_none_iff.mp found), Except.map, Except.mapError]
  | some cell => simp [(List.getElem?_eq_some_iff.mp found).1, Except.map, Except.mapError]

/-- Exact ordinary classification, including the early VerbatimBytecode error.
Malformed item/optional combinations violate hasInstruction's assertion and
remain safety faults even when the native build erases its dynamic check. -/
def classification (item : Item) : Except Error Bool :=
  if item.kind = 13 then .error .assemblyException else
  if item.kind = 1 then match item.instruction with
    | none => .error .safetyFault
    | some opcode => .ok (if opcode ∈ ([0xf1, 0xf2, 0xf4, 0xfa, 0xf0, 0xf5, 0x5a, 0x58,
        0x59, 0x31, 0x47, 0x3b, 0x3f, 0x3e, 0x3d] : List Opcode) then false else true)
  else if item.instruction.isSome then .error .safetyFault else .ok true

theorem deterministic_exact (item : Item) : queries.deterministic item = classification item := by
  by_cases verbatim : item.kind = 13#32 <;> by_cases operation : item.kind = 1#32 <;>
    cases instruction : item.instruction <;>
    simp [queries, Determinism.run, determinismCode, Test.run, classification, verbatim, operation, instruction]

/-- Every source-classified nondeterministic item bypasses sorting. This ties
the retained-operand insertion path to the actual closed opcode classifier. -/
theorem nondeterministic_noncommutative (item : Item)
    (classified : queries.deterministic item = .ok false) :
    Interner.Scoped.commutative item = .ok false := by
  rw [deterministic_exact] at classified
  by_cases verbatim : item.kind = 13
  · rw [classification, if_pos verbatim] at classified
    contradiction
  by_cases operation : item.kind = 1
  · cases instruction : item.instruction with
    | none =>
      rw [classification, if_neg verbatim, if_pos operation, instruction] at classified
      contradiction
    | some opcode =>
      rw [classification, if_neg verbatim, if_pos operation, instruction] at classified
      dsimp only at classified
      split at classified
      · rename_i member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [Interner.Scoped.commutative, normalizeCode, Test.run, operation, instruction]
      · simp at classified
  · rw [classification, if_neg verbatim, if_neg operation] at classified
    split at classified <;> simp at classified

theorem assembly_error_ordinary : ordinary (Except.error (.language .assemblyException) : Except Fault NodeId) = true := rfl
theorem malformed_rejected : ordinary (Except.error (.language .safetyFault) : Except Fault NodeId) = false := rfl

end Compiler.Extraction.Interner.Queries
