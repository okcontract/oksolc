/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeComparisonDispatch
import Compiler.Extraction.InternerNativePrefixTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeComparisonTests
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul
open NativeAlgebraicTests

/-- Reuse the algebraic fixture's zero constant. Operation probes must not run
for comparison dispatch, whether or not the constant is exposed. -/
def reads (knownZero : Bool) : Nested.Reads where
  constant := fun id => .ok (if knownZero = true ∧ id = 0 then some 0 else none)
  operation := fun _ _ => .error .invalidOptional

theorem reads_sound (meaning : Meaning) (memory : Session Nat) (value : Word) (knownZero : Bool) :
    Nested.Sound meaning (fixture memory value).graph.read (reads knownZero) := by
  constructor
  · intro id word found
    by_cases selected : knownZero = true ∧ id = 0
    · have zero := selected.2
      subst id
      have same : (0 : Word) = word := by
        simpa [reads, selected.1] using found
      exact same ▸ rfl
    · simp only [reads, selected, ↓reduceIte] at found
      cases found
  · intro id opcode slice found
    cases found
  · intro left right a b equal lhs rhs
    simp only [Nested.sameExpression, reads, beq_iff_eq] at equal
    subst right
    exact Option.some.inj (lhs.symm.trans rhs)

/-- Unknown equal operands use the equality table or signed fallback; known
zero operands fold first. Both keep the actual child outcome and effect. -/
theorem equal_outcome (before : World Nat) (literal : Bool) (op : Folding.Op)
    (comparison : Dispatch.BooleanOperation op) :
    (Dispatch.simplifyWithInputs (reads literal) children 64 op.opcode
      [if literal then 0 else 4, if literal then 0 else 4] () NativeUnaryTests.loading 0) before =
      ((match op with | .eq => .error (.language .outOfMemory) | _ => .ok (some 0)), before.mapEffects Nat.succ) := by
  cases literal <;> rcases comparison with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem unequal_miss (before : World Nat) (op : Folding.Op) (comparison : Dispatch.BooleanOperation op) :
    (Dispatch.simplifyWithInputs (reads false) children 64 op.opcode [4, 0] () NativeUnaryTests.loading 0) before =
      (.ok none, before) := by
  rcases comparison with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The constant table's Boolean construction can fail at its first operation.
Its failure must not fall through to a miss or lose the child effect. -/
theorem constant_table_oom (before : World Nat) :
    (Dispatch.simplifyWithInputs (reads true) children 64 17 [4, 0] () NativeUnaryTests.loading 0) before =
      (.error (.language .outOfMemory), before.mapEffects Nat.succ) := rfl

def rightFailure (error : Storage.ReadError) : Nested.Reads where
  constant := fun id => if id = 4 then .ok none else .error error
  operation := fun _ _ => .error .invalidOptional

/-- The fold stops at its unknown left operand. The binary stage then reaches
its second read and must propagate that error exactly. -/
theorem second_read_failure (before : World Nat) (error : Storage.ReadError)
    (op : Folding.Op) (comparison : Dispatch.BooleanOperation op) :
    (Dispatch.simplifyWithInputs (rightFailure error) children 64 op.opcode [4, 0] () NativeUnaryTests.loading 0) before =
      (.error (.language (match error with | .invalidId => .invalidId | .invalidOptional => .invalidOptional | .safetyFault => .safetyFault)), before) := by
  cases error <;> rcases comparison with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- One derived fixture instance exercises all comparison opcodes and the
known/unknown, equal/unequal cases without assuming an execution outcome. -/
theorem preserved (other : Meaning) (memory : Session Nat) (value : Word) (op : Folding.Op)
    (comparison : Dispatch.BooleanOperation op) (knownZero leftZero sameIds : Bool) :
    let before := fixture memory value
    let left := if leftZero then 0 else 4
    let right := if sameIds then left else 0
    let a := if leftZero then 0 else value
    let b := if sameIds then a else 0
    let ran := (Dispatch.simplifyWithInputs (reads knownZero) children 64 op.opcode [left, right] () NativeUnaryTests.loading 0) before
    (ordinary ran.1 = true → ready ran.2) ∧
    Semantic.Ensures (Folding.wordMeaning other) before.graph ran.1 ran.2.graph
      (fun found after => ∀ id, found = some id → after.read id = some (op.value a b 0)) := by
  dsimp only
  apply NativeRecursion.comparison_dispatch_verified other (reads knownZero) children 64 op comparison _ _ ()
    (fixture memory value) ready rfl (fixture_valid _ memory value) (rules _)
    (reads_sound _ memory value knownZero) (if leftZero then 0 else value) (if sameIds then (if leftZero then 0 else value) else 0)
  · cases leftZero <;> rfl
  · cases leftZero <;> cases sameIds <;> rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeComparisonTests
