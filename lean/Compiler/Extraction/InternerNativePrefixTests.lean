/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeUnaryTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativePrefixTests
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul
open NativeUnaryTests

/-- The existing graph fixture supplies all constants. Operation queries fail
so a folding hit must stop before the unary stage. -/
def known : Nested.Reads where
  constant := fun id => .ok (some (if id = 1 then 1 else 0))
  operation := fun _ _ => .error .invalidOptional

theorem known_sound (other : Meaning) (memory : Session Nat) :
    Nested.Sound (Folding.wordMeaning other) (fixture memory).graph.read known := by
  constructor
  · intro id word found
    exact congrArg some (Option.some.inj (Except.ok.inj found))
  · intro id opcode slice found
    cases found
  · intro left right a b equal lhs rhs
    simp only [Nested.sameExpression, known, beq_iff_eq] at equal
    subst right
    exact Option.some.inj (lhs.symm.trans rhs)

/-- Reuse the preceding constant-callback proof at this actual initial world.
No child result or final invariant is assumed. -/
theorem constant_child (meaning : Meaning) (memory : Session Nat) (instruction : Opcode)
    (arguments : List NodeId) (expected : Word) :
    Dispatch.Preservation.ConstantChild (Semantic.builderLogic meaning ready) known children
      instruction arguments () (fixture memory) expected := by
  intro values bounded nonempty collected folded
  have checked := (NativeAlgebraicTests.rules meaning).constant expected (fixture memory)
    ⟨rfl, fixture_valid meaning memory⟩
  exact fun ordinary => ⟨trivial, (checked ordinary).2⟩

theorem folded_hit (before : World Nat) :
    (Dispatch.simplifyWithInputs known children 64 21 [1] () loading 0) before =
      (.ok (some 0), before.mapEffects Nat.succ) := rfl

theorem folded_oom (before : World Nat) :
    (Dispatch.simplifyWithInputs known children 64 21 [0] () loading 0) before =
      (.error (.language .outOfMemory), before.mapEffects Nat.succ) := rfl

/-- Both the folding hit and OOM use the general native dispatcher theorem,
with source soundness and child contracts derived from the reused fixture. -/
theorem folded_preserved (other : Meaning) (memory : Session Nat) (nonzero : Bool) :
    let before := fixture memory
    let id := if nonzero then 1 else 0
    let expected := if nonzero then 0 else 1
    let ran := (Dispatch.simplifyWithInputs known children 64 21 [id] () loading 0) before
    (ordinary ran.1 = true → ready ran.2) ∧
    Semantic.Ensures (Folding.wordMeaning other) before.graph ran.1 ran.2.graph
      (fun found after => ∀ result, found = some result → after.read result = some expected) := by
  dsimp only
  apply NativeRecursion.unary_dispatch_verified other known children 64 21 _ () (fixture memory) ready trivial
    (fixture_valid _ memory) (rules _ known) (known_sound other memory) (if nonzero then 1 else 0) _ 0
  · cases nonzero <;> rfl
  · cases nonzero <;> exact Folding.word_meaning_operation other .iszero 0 _
  · exact constant_child _ memory 21 _ _
  · intro id opcode slice found
    cases found

theorem collection_failure (before : World Nat) (error : Storage.ReadError) :
    (Dispatch.simplifyWithInputs (Dispatch.UnaryTests.faultReads error) children 64 21 [1] () loading 0) before =
      (.error (.language (match error with | .invalidId => .invalidId | .invalidOptional => .invalidOptional | .safetyFault => .safetyFault)), before) := by
  cases error <;> rfl

theorem arity_skips_queries (before : World Nat) (instruction : Opcode) (error : Storage.ReadError) :
    (Dispatch.constantStage (Dispatch.UnaryTests.faultReads error) children instruction [] ()) before = (.ok none, before) ∧
    (Dispatch.constantStage (Dispatch.UnaryTests.faultReads error) children instruction [0, 1, 2, 3] ()) before = (.ok none, before) :=
  ⟨rfl, rfl⟩

theorem no_applicable_fold (before : World Nat) :
    (Dispatch.simplifyWithInputs known children 64 254 [1] () loading 0) before = (.ok none, before) := rfl

theorem arithmetic_failure (before : World Nat) (fault : Folding.Fault) :
    ((do let id ← Dispatch.arithmetic (α := NodeId) (.error fault)
         children.operation 21 [id] ()) : GraphAction Nat NodeId) before =
      (.error (.language .safetyFault), before) := rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativePrefixTests
