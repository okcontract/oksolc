/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.NestedConstructionProgram

namespace Compiler.Extraction.Nested
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.Extraction.Interner Contract.Yul
set_option linter.unusedSimpArgs false

theorem nested_iszero_opcode : nestedIszeroOpcode = Folding.Op.iszero.opcode := rfl

theorem double_iszero_safe (other : Meaning) (build : OperationBuilder Debug)
    (constructs : Constructs other build) (before : Heap) (valid : Invariant (Folding.wordMeaning other) before)
    (id : NodeId) (value : Word) (debug : Debug) (actual : before.read id = some value) :
    Safe (Folding.wordMeaning other) (doubleIsZero build id debug) before
      (fun result after => after.read result = some (if value = 0 then 0 else 1)) := by
  unfold doubleIsZero
  apply Safe.bind (Folding.wordMeaning other) before _ _
    (fun inner middle => middle.read inner = some (Unary.iszero.eval value)) _
    (constructs .iszero [id] [value] _ debug before valid (by simp [readArguments, actual]) rfl)
  intro inner middle validMiddle _ innerRead
  have boolean : Unary.iszero.eval (Unary.iszero.eval value) = (if value = 0 then 0 else 1) := by
    by_cases zero : value = 0#256 <;> simp [Unary.eval, boolWord, zero]
  rw [← boolean]
  exact constructs .iszero [inner] [Unary.iszero.eval value] _ debug middle validMiddle
    (by simp [readArguments, innerRead]) rfl

/-- The second slot wins when both match. Captured IDs (and hence annotations)
are preserved even when semantic equality relates distinct occurrences. -/
theorem repeated_operands_found (reads : Reads) (left right repeated : NodeId) (first : Bool)
    (operands : List NodeId) (found : repeatedOperands reads left right repeated first = some operands) :
    (sameExpression reads right repeated = true ∧
      operands = (if first then [left, repeated] else [left, right])) ∨
    (sameExpression reads right repeated = false ∧ sameExpression reads left repeated = true ∧
      operands = (if first then [repeated, right] else [left, right])) := by
  unfold repeatedOperands repeatedIndex at found
  split at found
  · left
    refine ⟨by assumption, ?_⟩
    cases first <;> simpa [localArguments] using Option.some.inj found.symm
  · split at found
    · right
      refine ⟨Bool.eq_false_iff.mpr (by assumption), by assumption, ?_⟩
      cases first <;> simpa [localArguments] using Option.some.inj found.symm
    · contradiction

theorem repeated_operands_sound (meaning : Meaning) (read : Read) (reads : Reads)
    (sound : Sound meaning read reads) (left right repeated : NodeId) (first : Bool)
    (a b value : Word) (lhs : read left = some a) (rhs : read right = some b)
    (actual : read repeated = some value) (operands : List NodeId)
    (found : repeatedOperands reads left right repeated first = some operands) :
    readArguments read operands = some [a, b] ∧ (value = a ∨ value = b) := by
  rcases repeated_operands_found reads left right repeated first operands found with
    ⟨equal, selected⟩ | ⟨_, equal, selected⟩
  · have same := sound.equal right repeated b value equal rhs actual
    subst value
    subst operands
    exact ⟨by cases first <;> simp [readArguments, lhs, rhs, actual], Or.inr rfl⟩
  · have same := sound.equal left repeated a value equal lhs actual
    subst value
    subst operands
    exact ⟨by cases first <;> simp [readArguments, lhs, rhs, actual], Or.inl rfl⟩

theorem repeated_index_bound (reads : Reads) (left right repeated : NodeId) (selected : Nat)
    (found : repeatedIndex reads left right repeated = some selected) : selected < 2 := by
  unfold repeatedIndex at found
  split at found
  · cases Option.some.inj found; decide
  · split at found
    · cases Option.some.inj found; decide
    · contradiction

def Idempotent (op : Folding.Op) : Prop := op = .and ∨ op = .or

theorem idempotent_arity (op : Folding.Op) (idempotent : Idempotent op) : op.arity = 2 := by
  rcases idempotent with rfl | rfl <;> rfl

theorem idempotent_repeat (op : Folding.Op) (idempotent : Idempotent op) (a b value : Word)
    (repeated : value = a ∨ value = b) (first : Bool) :
    (if first then op.value value (op.value a b 0) 0 else op.value (op.value a b 0) value 0) =
      op.value a b 0 := by
  rcases idempotent with rfl | rfl <;> rcases repeated with repeated | repeated <;> subst value <;> cases first <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Folding.Op.value, Binary.eval]
  all_goals
    apply BitVec.eq_of_getLsbD_eq
    intro index _
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
    cases a.getLsbD index <;> cases b.getLsbD index <;> rfl

/-- Complete helper preservation, including failed constructors after graph
growth. The caller's AND/OR restriction is essential; ADD is not idempotent. -/
theorem drop_repeated_local_safe (other : Meaning) (reads : Reads)
    (localBuild : LocalOperationBuilder Debug) (constructs : LocalConstructs other localBuild) (before : Heap) (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (op : Folding.Op) (idempotent : Idempotent op) (nested repeated : NodeId) (first : Bool)
    (nestedValue value : Word) (nestedRead : before.read nested = some nestedValue)
    (actual : before.read repeated = some value) (debug : Debug) :
    Safe (Folding.wordMeaning other) (dropRepeatedLocal reads localBuild op.opcode nested repeated first debug) before
      (fun result after => ∀ id, result = some id → after.read id = some
        (if first then op.value value nestedValue 0 else op.value nestedValue value 0)) := by
  unfold dropRepeatedLocal
  apply read_action_bind_safe (Folding.wordMeaning other) before _ _ _ valid
  intro lookup found
  cases lookup with
  | none => exact Safe.pure _ before none _ valid (by simp)
  | some slice =>
    dsimp only
    split
    next left right items =>
      cases chosen : repeatedIndex reads left right repeated with
      | none => simp only [chosen]; exact Safe.pure _ before none _ valid (by simp)
      | some selected =>
        simp only [chosen]
        obtain ⟨a, b, lhs, rhs, nestedFact⟩ := binary_values other before.read reads sound op
          (idempotent_arity op idempotent) nested left right slice found items
        have same : nestedValue = op.value a b 0 := Option.some.inj (nestedRead.symm.trans nestedFact)
        subst nestedValue
        obtain ⟨arguments, repeatedFact⟩ := repeated_operands_sound _ before.read reads sound left right
          repeated first a b value lhs rhs actual (localArguments slice selected repeated first)
          (by simp only [repeatedOperands, chosen, Option.map_some, localArguments, items])
        rw [idempotent_repeat op idempotent a b value repeatedFact first]
        apply Safe.bind _ before _ _ (fun id after => after.read id = some (op.value a b 0)) _
          (constructs op slice selected repeated first [a, b] _ debug before valid arguments
            (by simp [Folding.Op.eval, idempotent_arity op idempotent]))
        intro result after validAfter _ valueRead
        exact Safe.pure _ after (some result) _ validAfter (by intro id equal; cases equal; exact valueRead)
    next => exact Safe.pure _ before none _ valid (by simp)

/-- The existing list-valued constructor is the storage-erasing specialization. -/
theorem drop_repeated_safe (other : Meaning) (reads : Reads) (build : OperationBuilder Debug)
    (constructs : Constructs other build) (before : Heap) (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (op : Folding.Op) (idempotent : Idempotent op) (nested repeated : NodeId) (first : Bool)
    (nestedValue value : Word) (nestedRead : before.read nested = some nestedValue)
    (actual : before.read repeated = some value) (debug : Debug) :
    Safe (Folding.wordMeaning other) (dropRepeatedNested reads build op.opcode nested repeated first debug) before
      (fun result after => ∀ id, result = some id → after.read id = some
        (if first then op.value value nestedValue 0 else op.value nestedValue value 0)) :=
  drop_repeated_local_safe other reads (localBuilder build) (local_constructs other build constructs)
    before valid sound op idempotent nested repeated first nestedValue value nestedRead actual debug

theorem interner_drop_repeated_safe (other : Meaning) (p : Primitives)
    (contracts : Contracts (Folding.wordMeaning other) p) (reads : Reads) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before) (sound : Sound (Folding.wordMeaning other) before.read reads)
    (op : Folding.Op) (idempotent : Idempotent op) (nested repeated : NodeId) (first : Bool)
    (nestedValue value : Word) (nestedRead : before.read nested = some nestedValue)
    (actual : before.read repeated = some value) (debug : Debug) :
    Safe (Folding.wordMeaning other)
      (dropRepeatedNested reads (internerBuilder p) op.opcode nested repeated first debug) before
      (fun result after => ∀ id, result = some id → after.read id = some
        (if first then op.value value nestedValue 0 else op.value nestedValue value 0)) :=
  drop_repeated_safe other reads (internerBuilder p) (interner_constructs other p contracts)
    before valid sound op idempotent nested repeated first nestedValue value nestedRead actual debug

end Compiler.Extraction.Nested
