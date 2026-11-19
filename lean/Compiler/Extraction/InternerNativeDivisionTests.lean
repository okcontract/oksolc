/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeDivisionDispatch
import Compiler.Extraction.InternerNativeComparisonTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeDivisionTests
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul
open NativeAlgebraicTests

/-- A distinct DIV obligation: a queried SHL slice supplies the initializer.
The existing callbacks and state-changing load exercise its reached state. -/
def reads (base : Word) (items : List NodeId := [1, 2]) : Nested.Reads where
  constant := fun id => .ok (if id = 2 then some base else none)
  operation := fun id opcode => .ok (if id = 3 ∧ opcode = Dispatch.opSHL then some ⟨17, items⟩ else none)

def fixture (memory : Session Nat) (amount base numerator : Word) : World Nat :=
  ⟨{ read := fun id => some (if id = 1 then amount else if id = 2 then base
      else if id = 3 then Folding.Op.shl.value amount base 0 else if id = 4 then numerator else 0),
     table := fun _ => none }, memory⟩

theorem fixture_valid (meaning : Meaning) (memory : Session Nat) (amount base numerator : Word) :
    Interner.Invariant meaning (fixture memory amount base numerator).graph := by
  constructor
  · intro key id found
    cases found
  · trivial

theorem reads_sound (other : Meaning) (memory : Session Nat) (amount base numerator : Word) :
    Nested.Sound (Folding.wordMeaning other) (fixture memory amount base numerator).graph.read (reads base) := by
  constructor
  · intro id word found
    by_cases selected : id = 2
    · subst id
      have same : base = word := by simpa [reads] using found
      exact same ▸ rfl
    · simp only [reads, selected, ↓reduceIte] at found
      cases found
  · intro id opcode slice found
    by_cases selected : id = 3 ∧ opcode = Dispatch.opSHL
    · obtain ⟨rfl, rfl⟩ := selected
      have same : (⟨17, [1, 2]⟩ : Storage.ArgumentSlice) = slice := by simpa [reads] using found
      subst slice
      exact ⟨0, [amount, base], Folding.Op.shl.value amount base 0, rfl, rfl,
        Folding.word_meaning_operation other .shl 0 [amount, base]⟩
    · simp only [reads, selected, ↓reduceIte] at found
      cases found
  · intro left right a b equal lhs rhs
    simp only [Nested.sameExpression, reads, beq_iff_eq] at equal
    subst right
    exact Option.some.inj (lhs.symm.trans rhs)

/-- Failure at the initializer retains its own effect and prevents the child. -/
def loading (fail : Bool) : Nested.OperandRead (GraphAction Nat) :=
  if fail then fun _ _ _ before => (.error (.language .outOfMemory), before.mapEffects Nat.succ)
  else NativeUnaryTests.loading

theorem inputs (meaning : Meaning) (before : World Nat) (base : Word) (fail : Bool)
    (valid : ready before ∧ Interner.Invariant meaning before.graph) :
    Dispatch.UnaryPreservation.Inputs (Semantic.builderLogic meaning ready) (reads base) (loading fail) before := by
  intro id opcode source found index annotation item
  cases fail <;> exact fun _ => ⟨valid.1, valid.2, fun _ _ same => same, by trivial⟩

theorem shift_rule (meaning : Meaning) :
    Dispatch.Preservation.OperationRule (Semantic.builderLogic meaning ready) children () .shr := by
  intro ids values value before valid actual evaluated
  exact fun _ => ⟨valid.1, valid.2, fun _ _ same => same, trivial⟩

theorem initializer_outcome (before : World Nat) (fail : Bool) :
    (Dispatch.simplifyWithInputs (reads 1) children 64 Dispatch.opDIV [4, 3] () (loading fail) 0) before =
      (.error (.language .outOfMemory), if fail then before.mapEffects Nat.succ
        else (before.mapEffects Nat.succ).mapEffects Nat.succ) := by
  cases fail <;> rfl

theorem wrong_base_miss (before : World Nat) :
    (Dispatch.simplifyWithInputs (reads 2) children 64 Dispatch.opDIV [4, 3] () (loading true) 0) before =
      (.ok none, before) := rfl

theorem wrong_arity_miss (before : World Nat) :
    (Dispatch.simplifyWithInputs (reads 1 [1]) children 64 Dispatch.opDIV [4, 3] () (loading true) 0) before =
      (.ok none, before) := rfl

def baseFailure (error : Storage.ReadError) : Nested.Reads :=
  { reads 1 with constant := fun id => if id = 2 then .error error else .ok none }

theorem base_read_failure (before : World Nat) (error : Storage.ReadError) :
    (Dispatch.simplifyWithInputs (baseFailure error) children 64 Dispatch.opDIV [4, 3] () (loading false) 0) before =
      (.error (.language (match error with | .invalidId => .invalidId | .invalidOptional => .invalidOptional | .safetyFault => .safetyFault)), before) := by
  cases error <;> rfl

/-- An exact forwarding probe checks the source address/index and SHR operand
order. Its callback is only a probe; preservation below uses derived contracts. -/
theorem forwarded (before : World Nat) :
    (Dispatch.simplifyWithInputs (reads 1)
      { children with operation := fun opcode ids _ world =>
          (if opcode = Dispatch.opSHR ∧ ids = [1, 4] then .ok 0 else .error .missingHandle, world.mapEffects Nat.succ) }
      64 Dispatch.opDIV [4, 3] ()
      (fun source index annotation world =>
        if source.address = 17 ∧ index = 0 ∧ annotation = 1 then NativeUnaryTests.loading source index annotation world
        else (.error .missingHandle, world)) 0) before =
      (.ok (some 0), (before.mapEffects Nat.succ).mapEffects Nat.succ) := rfl

/-- Arbitrary word amounts include oversized shifts: the existing divisor
identity handles the resulting zero divisor with EVM's zero result. -/
theorem preserved (other : Meaning) (memory : Session Nat) (amount base numerator : Word) (fail : Bool) :
    let before := fixture memory amount base numerator
    let ran := (Dispatch.simplifyWithInputs (reads base) children 64 Dispatch.opDIV [4, 3] () (loading fail) 0) before
    (ordinary ran.1 = true → ready ran.2) ∧
    Semantic.Ensures (Folding.wordMeaning other) before.graph ran.1 ran.2.graph
      (fun found after => ∀ id, found = some id → after.read id = some (numerator / Folding.Op.shl.value amount base 0)) := by
  exact NativeRecursion.division_dispatch_verified other (reads base) children 64 4 3 ()
    (fixture memory amount base numerator) ready rfl (fixture_valid _ memory amount base numerator)
    (rules _) (shift_rule _) (reads_sound other memory amount base numerator) numerator _ rfl rfl
    (loading fail) 0 (inputs _ _ base fail ⟨rfl, fixture_valid _ memory amount base numerator⟩)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeDivisionTests
