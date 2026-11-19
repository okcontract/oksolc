/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeUnaryDispatch
import Compiler.Extraction.InternerNativeAlgebraicTests
import Compiler.Extraction.DispatchUnaryTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeUnaryTests
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul
open Dispatch.UnaryPreservation

/-- Reuse the earlier effect callbacks: every operation refuses allocation
and retains its private-state update. This is not a physical allocator model. -/
abbrev children := NativeAlgebraicTests.children

def ready (_ : World Nat) : Prop := True

theorem rules (meaning : Meaning) (reads : Nested.Reads) :
    Children (Semantic.builderLogic meaning ready) reads children () := by
  constructor
  · intro op ids values value before valid _ _
    exact fun _ => ⟨valid.1, valid.2, fun _ _ found => found, trivial⟩
  · intro id queried source found op values value before valid _ _
    exact fun _ => ⟨valid.1, valid.2, fun _ _ found => found, trivial⟩

def reads : Nested.Reads where
  constant := fun _ => .ok none
  operation := fun id opcode => .ok (if opcode = 21 then
    if id = 2 then some ⟨17, [1]⟩ else if id = 1 then some ⟨29, [0]⟩ else none else none)

def fixture (memory : Session Nat) : World Nat :=
  ⟨{ read := fun id => some (if id = 1 then 1 else 0), table := fun _ => none }, memory⟩

theorem fixture_valid (meaning : Meaning) (memory : Session Nat) :
    Interner.Invariant meaning (fixture memory).graph := by
  constructor
  · intro key id found
    cases found
  · trivial

theorem reads_sound (other : Meaning) (memory : Session Nat) :
    Nested.Sound (Folding.wordMeaning other) (fixture memory).graph.read reads := by
  constructor
  · intro id word found
    cases found
  · intro id opcode slice found
    by_cases operation : opcode = 21
    · subst opcode
      by_cases outer : id = 2
      · subst id
        have same : (⟨17, [1]⟩ : Storage.ArgumentSlice) = slice := by simpa only [reads, ↓reduceIte, Except.ok.injEq, Option.some.injEq] using found
        subst slice
        refine ⟨0, [1], 0, rfl, rfl, ?_⟩
        exact Folding.word_meaning_operation other .iszero 0 [1]
      · by_cases inner : id = 1
        · subst id
          have same : (⟨29, [0]⟩ : Storage.ArgumentSlice) = slice := by simpa only [reads, outer, ↓reduceIte, Except.ok.injEq, Option.some.injEq] using found
          subst slice
          refine ⟨0, [0], 1, rfl, rfl, ?_⟩
          exact Folding.word_meaning_operation other .iszero 0 [0]
        · simp only [reads, outer, inner, ↓reduceIte] at found
          cases found
    · simp only [reads, operation, ↓reduceIte] at found
      cases found
  · intro left right a b equal lhs rhs
    simp only [Nested.sameExpression, reads, beq_iff_eq] at equal
    subst right
    exact Option.some.inj (lhs.symm.trans rhs)

/-- A state-changing initializer exercises the shared bind proof before the
child. Native production instead derives its load from NativeGraph.Facts. -/
def loading : Nested.OperandRead (GraphAction Nat) := fun _ _ annotation before =>
  (.ok annotation, before.mapEffects Nat.succ)

theorem inputs (meaning : Meaning) (before : World Nat) (valid : Interner.Invariant meaning before.graph) :
    Inputs (Semantic.builderLogic meaning ready) reads loading before := by
  intro id opcode source found index annotation item
  exact fun _ => ⟨trivial, valid, fun _ _ same => same, rfl⟩

theorem initializer_then_oom (before : World Nat) :
    (Dispatch.simplifyWithInputs reads children 64 21 [2] () loading 0) before =
      (.error (.language .outOfMemory), (before.mapEffects Nat.succ).mapEffects Nat.succ) := by
  rw [NativeRecursion.unary_dispatch_result reads children 64 21 2 () before rfl loading 0]
  rfl

theorem preserved (other : Meaning) (memory : Session Nat) :
    let before := fixture memory
    let ran := (Dispatch.simplifyWithInputs reads children 64 21 [2] () loading 0) before
    (ordinary ran.1 = true → ready ran.2) ∧
    Semantic.Ensures (Folding.wordMeaning other) before.graph ran.1 ran.2.graph
      (fun found after => ∀ id, found = some id → after.read id = some 1) := by
  exact NativeRecursion.unary_dispatch_verified other reads children 64 21 2 () (fixture memory) ready trivial
    (fixture_valid _ memory) (rules _ reads) (reads_sound other memory) 0 1 0 rfl
    (Folding.word_meaning_operation other .iszero 0 [0]) (by intro values _ _ collected; cases collected) loading 0 (inputs _ _ (fixture_valid _ memory))

def faultReads (error : Storage.ReadError) : Nested.Reads :=
  { Dispatch.UnaryTests.faultReads error with constant := fun _ => .ok none }

theorem read_failure (before : World Nat) (error : Storage.ReadError) :
    (Dispatch.simplifyWithInputs (faultReads error) children 64 25 [0] () loading 0) before =
      (.error (.language (match error with | .invalidId => .invalidId | .invalidOptional => .invalidOptional | .safetyFault => .safetyFault)), before) := by
  cases error <;> rfl

theorem unknown_miss (before : World Nat) :
    (Dispatch.simplifyWithInputs (faultReads .safetyFault) children 64 1 [0] () loading 0) before = (.ok none, before) := rfl

/-- Reuse the ordered-probe fixture. A borrowed hit must forward its address,
opcode and complete items, and stop before the deliberately failing next query. -/
def borrowing : Associative.Constructors Unit (GraphAction Nat) := { children with
  borrowedOperation := fun address opcode ids _ before =>
    if address = 0 ∧ opcode = 20 ∧ ids = [0, 0] then (.ok 0, before.mapEffects Nat.succ)
    else (.error .missingHandle, before) }

theorem borrowed_stops (before : World Nat) :
    (Dispatch.simplifyWithInputs Dispatch.UnaryTests.firstComparison borrowing 64 21 [2] () loading 0) before =
      (.ok (some 0), before.mapEffects Nat.succ) := rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeUnaryTests
