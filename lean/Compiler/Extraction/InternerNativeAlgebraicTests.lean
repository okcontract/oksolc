/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeAlgebraicDispatch
import Compiler.Extraction.InternerNativeAllocationAdmissionTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeAlgebraicTests
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul

/-- Effect-level callbacks, not physical allocator fixtures. Constant zero is
an interned hit; every call advances private state. The operation then refuses
allocation, exercising failure after a successful, state-changing child. -/
def children : Associative.Constructors Unit (GraphAction Nat) where
  constant := fun value _ before =>
    (if value = 0 then .ok 0 else .error (.language .outOfMemory), before.mapEffects Nat.succ)
  operation := fun _ _ _ before => (.error (.language .outOfMemory), before.mapEffects Nat.succ)
  materialize := fun _ _ _ before => (.error (.language .outOfMemory), before.mapEffects Nat.succ)

def ready (world : World Nat) : Prop := world.graph.read 0 = some 0

theorem rules (meaning : Meaning) :
    BuilderRules (Semantic.builderLogic meaning ready) (Dispatch.algebraicBuilder children) () := by
  constructor
  · intro value before valid
    change ready before ∧ Interner.Invariant meaning before.graph at valid
    by_cases zero : value = 0
    · subst value
      exact fun _ => ⟨valid.1, valid.2, fun _ _ found => found, valid.1⟩
    · intro ordinary
      simp only [Dispatch.algebraicBuilder, children, zero, ↓reduceIte] at ordinary ⊢
      exact ⟨valid.1, valid.2, fun _ _ found => found, trivial⟩
  · intro op ids values value before valid _ _
    change ready before ∧ Interner.Invariant meaning before.graph at valid
    exact fun _ => ⟨valid.1, valid.2, fun _ _ found => found, trivial⟩

theorem sequential_oom (before : World Nat) (left right : NodeId) :
    zigApply .neg_right (Dispatch.algebraicBuilder children) left right () before =
      (.error (.language .outOfMemory), (before.mapEffects Nat.succ).mapEffects Nat.succ) := rfl

theorem first_oom (before : World Nat) :
    zigApply .one (Dispatch.algebraicBuilder children) 0 4 () before =
      (.error (.language .outOfMemory), before.mapEffects Nat.succ) := rfl

def reads : Nested.Reads where
  constant := fun id => .ok (if id = 1 then some (BitVec.allOnes 256) else none)
  operation := fun _ _ => .ok none

/-- Exercise the full extracted dispatcher, including the unsuccessful first
fold stage, table selection and both sequential children. -/
theorem dispatch_oom (before : World Nat) :
    (Dispatch.simplifyWithInputs reads children 64 2 [1, 4] ()) before =
      (.error (.language .outOfMemory), (before.mapEffects Nat.succ).mapEffects Nat.succ) := by
  simpa only [sequential_oom] using NativeRecursion.algebraic_dispatch_result reads children 64 2 1 4 () before
    (some (BitVec.allOnes 256)) none .neg_right rfl rfl rfl (by decide)

def fixture (memory : Session Nat) (value : Word) : World Nat :=
  ⟨{ read := fun id => if id = 0 then some 0 else if id = 1 then some (BitVec.allOnes 256)
        else if id = 4 then some value else none, table := fun _ => none }, memory⟩

theorem fixture_valid (meaning : Meaning) (memory : Session Nat) (value : Word) :
    Interner.Invariant meaning (fixture memory value).graph := by
  constructor
  · intro key id found
    cases found
  · trivial

/-- The preservation premise is inhabited and derived for the callbacks. It
does not assume a native result, final invariant or constant allocation success. -/
theorem sequential_preserved (meaning : Meaning) (memory : Session Nat) (value : Word) :
    Semantic.NativeSafe meaning ready (zigApply .neg_right (Dispatch.algebraicBuilder children) 1 4 ())
      (fixture memory value) (fun id after => after.graph.read id = some (0 - value)) := by
  rw [zigApply_eq]
  exact (rules meaning).replacement (fixture memory value) ⟨rfl, fixture_valid meaning memory value⟩
    .neg_right 1 4 (BitVec.allOnes 256) value rfl rfl

theorem oracle_sound (meaning : Meaning) (memory : Session Nat) (value : Word) :
    Nested.Sound meaning (fixture memory value).graph.read reads := by
  constructor
  · intro id word found
    by_cases selected : id = 1
    · subst id
      have same : BitVec.allOnes 256 = word := by simpa only [reads, ↓reduceIte, Except.ok.injEq, Option.some.injEq] using found
      exact same ▸ rfl
    · simp only [reads, selected, ↓reduceIte] at found
      cases found
  · intro id opcode slice found
    cases found
  · intro left right a b equal lhs rhs
    simp only [Nested.sameExpression, reads, beq_iff_eq] at equal
    subst right
    exact Option.some.inj (lhs.symm.trans rhs)

theorem dispatch_preserved (other : Meaning) (memory : Session Nat) (value : Word) :
    let before := fixture memory value
    let ran := (Dispatch.simplifyWithInputs reads children 64 2 [1, 4] ()) before
    (ordinary ran.1 = true → ready ran.2) ∧
    Semantic.Ensures (Folding.wordMeaning other) before.graph ran.1 ran.2.graph
      (fun found after => ∀ id, found = some id → after.read id = some (Binary.mul.eval (BitVec.allOnes 256) value)) := by
  exact NativeRecursion.algebraic_dispatch_verified other reads children 64 2 1 4 () (fixture memory value)
    (some (BitVec.allOnes 256)) none .neg_right rfl rfl rfl (by decide) ready rfl
    (fixture_valid _ memory value) (rules _) (oracle_sound _ memory value) (BitVec.allOnes 256) value _ 0 rfl rfl
    (by simpa only [Folding.Op.opcode, Folding.Op.eval, Folding.Op.arity, Folding.Op.value] using
      Folding.word_meaning_operation other .mul 0 [BitVec.allOnes 256, value])

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeAlgebraicTests
