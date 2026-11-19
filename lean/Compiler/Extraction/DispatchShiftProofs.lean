/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchAlgebraicProofs

namespace Compiler.Extraction.Dispatch
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
open Compiler.Extraction.OppositeShifts (Direction)
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192

/-- The EVM's large-shift result agrees with the total natural-index word
operation. This supports both logical directions without narrowing the amount. -/
theorem shift_word_value (direction : Direction) (amount value : Word) :
    direction.op.value amount value 0 = direction.shift value amount.toNat := by
  by_cases small : amount.toNat < 256
  · exact OppositeShifts.evm_shift direction amount value small
  · cases direction <;> simp [Direction.op, Direction.shift, Folding.Op.value, Binary.eval, small,
      BitVec.shiftLeft_eq_zero (by omega : 256 ≤ amount.toNat),
      BitVec.ushiftRight_eq_zero (by omega : 256 ≤ amount.toNat)]

theorem shift_large_value (direction : Direction) (amount value : Word) (large : 256 ≤ amount.toNat) :
    direction.op.value amount value 0 = 0 := by
  cases direction <;> simp [Direction.op, Folding.Op.value, Binary.eval, show ¬amount.toNat < 256 by omega]

theorem shift_sum_threshold (outer inner : Word) :
    256 - min inner.toNat 256 ≤ outer.toNat ↔ 256 ≤ outer.toNat + inner.toNat := by omega

theorem same_shift_nat_value (direction : Direction) (outer inner value : Word) :
    direction.op.value outer (direction.op.value inner value 0) 0 =
      direction.shift value (outer.toNat + inner.toNat) := by
  rw [shift_word_value, shift_word_value]
  cases direction <;> simp [Direction.shift, ← BitVec.shiftLeft_add, ← BitVec.shiftRight_add, Nat.add_comm]

theorem same_shift_zero_value (direction : Direction) (outer inner value : Word)
    (large : 256 - min inner.toNat 256 ≤ outer.toNat) :
    direction.op.value outer (direction.op.value inner value 0) 0 = 0 := by
  have bound := (shift_sum_threshold outer inner).mp large
  rw [same_shift_nat_value]
  cases direction <;> simp [Direction.shift, BitVec.shiftLeft_eq_zero bound, BitVec.ushiftRight_eq_zero bound]

theorem same_shift_sum_value (direction : Direction) (outer inner value : Word)
    (small : ¬256 - min inner.toNat 256 ≤ outer.toNat) :
    direction.op.value outer (direction.op.value inner value 0) 0 =
      direction.op.value (BitVec.ofNat 256 (outer.toNat + inner.toNat)) value 0 := by
  have sumBound : outer.toNat + inner.toNat < 256 := by rw [shift_sum_threshold] at small; omega
  have noWrap : outer.toNat + inner.toNat < 2 ^ 256 := by omega
  rw [same_shift_nat_value, shift_word_value]
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt noWrap]

theorem shift_index_add (outer inner : Word) (small : ¬256 - min inner.toNat 256 ≤ outer.toNat) :
    addWord (m := Action) outer inner = pure (BitVec.ofNat 256 (outer.toNat + inner.toNat)) := by
  have sumBound : outer.toNat + inner.toNat < 256 := by rw [shift_sum_threshold] at small; omega
  have noWrap : outer.toNat + inner.toNat < 2 ^ 256 := by omega
  unfold addWord
  rw [Folding.Zig.checkedAdd, if_pos noWrap]
  rfl

theorem shift_mask_value (direction : Direction) (amount value mask : Word) :
    direction.op.value amount (value &&& mask) 0 =
      direction.op.value amount value 0 &&& direction.shift mask amount.toNat := by
  rw [shift_word_value, shift_word_value]
  cases direction
  · exact BitVec.shiftLeft_and_distrib value mask amount.toNat
  · exact BitVec.ushiftRight_and_distrib value mask amount.toNat

theorem same_shift_candidate_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (direction : Direction) (right : NodeId) (amount value : Word) (debug : Debug)
    (rhs : before.read right = some value) (next : Action (Option NodeId))
    (rest : Safe (Folding.wordMeaning other) next before
      (fun result after => ∀ id, result = some id → after.read id = some (direction.op.value amount value 0))) :
    Safe (Folding.wordMeaning other) (do
      if let some inner ← readAction (reads.operation right direction.op.opcode) then
        if let [index, baseId] := inner.items then
          if let some innerShift ← readAction (reads.constant index) then
            if amount.toNat ≥ 256 - min innerShift.toNat 256 then
              return some (← constructors.constant 0 debug)
            return some (← constructors.operation direction.op.opcode
              [← constructors.constant (← addWord amount innerShift) debug, baseId] debug)
      next) before (fun result after => ∀ id, result = some id → after.read id = some (direction.op.value amount value 0)) := by
  apply read_action_bind_safe _ before _ _ _ valid
  intro option lookup
  cases option with
  | none => exact rest
  | some slice =>
    dsimp only
    split
    next amountId baseId items =>
      apply read_action_bind_safe _ before _ _ _ valid
      intro option found
      cases option with
      | none => exact rest
      | some inner =>
        obtain ⟨actual, base, amountRead, baseRead, nestedRead⟩ := binary_values other before.read reads sound direction.op
          (by cases direction <;> rfl) right amountId baseId slice lookup items
        have equal : actual = inner := Option.some.inj (amountRead.symm.trans (sound.constant amountId inner found))
        subst actual
        have same : value = direction.op.value inner base 0 := Option.some.inj (rhs.symm.trans nestedRead)
        by_cases large : 256 - min inner.toNat 256 ≤ amount.toNat
        · simp only [large, ↓reduceIte]
          rw [same, same_shift_zero_value direction amount inner base large]
          exact constant_some_safe other constructors correct before valid 0 debug
        · simp only [large, ↓reduceIte]
          rw [same, same_shift_sum_value direction amount inner base large, shift_index_add amount inner large]
          exact constant_left_operation_some_safe other constructors correct before valid direction.op
            (BitVec.ofNat 256 (amount.toNat + inner.toNat)) base _ baseId debug baseRead (by cases direction <;> rfl)
    next => exact rest

theorem opposite_shift_candidate_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (direction : Direction) (right : NodeId) (amount value : Word) (debug : Debug)
    (rhs : before.read right = some value) (next : Action (Option NodeId))
    (rest : Safe (Folding.wordMeaning other) next before
      (fun result after => ∀ id, result = some id → after.read id = some (direction.op.value amount value 0))) :
    Safe (Folding.wordMeaning other) (do
      if let some inner ← readAction (reads.operation right direction.opposite.op.opcode) then
        if let [index, baseId] := inner.items then
          if let some innerShift ← readAction (reads.constant index) then
            if amount.toNat < 256 ∧ innerShift.toNat < 256 then
              return some (← OppositeShifts.combineOppositeShifts constructors direction.op.opcode amount innerShift baseId debug)
      next) before (fun result after => ∀ id, result = some id → after.read id = some (direction.op.value amount value 0)) := by
  apply read_action_bind_safe _ before _ _ _ valid
  intro option lookup
  cases option with
  | none => exact rest
  | some slice =>
    dsimp only
    split
    next amountId baseId items =>
      apply read_action_bind_safe _ before _ _ _ valid
      intro option found
      cases option with
      | none => exact rest
      | some inner =>
        by_cases guard : amount.toNat < 256 ∧ inner.toNat < 256
        · simp only [guard, ↓reduceIte]
          obtain ⟨actual, base, amountRead, baseRead, nestedRead⟩ := binary_values other before.read reads sound direction.opposite.op
            (by cases direction <;> rfl) right amountId baseId slice lookup items
          have equal : actual = inner := Option.some.inj (amountRead.symm.trans (sound.constant amountId inner found))
          subst actual
          have same : value = direction.opposite.op.value inner base 0 := Option.some.inj (rhs.symm.trans nestedRead)
          rw [same]
          apply Safe.bind _ before _ _ _ _ (OppositeShifts.combine_safe other constructors correct direction amount inner
            guard.1 guard.2 before valid baseId base baseRead debug)
          intro result after validAfter _ resultRead
          exact Safe.pure _ after (some result) _ validAfter (by intro id equal; cases equal; exact resultRead)
        · simpa only [guard, ↓reduceIte] using rest
    next => exact rest

theorem masked_shift_candidate_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (direction : Direction) (left right : NodeId) (amount value : Word) (debug : Debug)
    (lhs : before.read left = some amount) (rhs : before.read right = some value)
    (next : Action (Option NodeId))
    (rest : Safe (Folding.wordMeaning other) next before
      (fun result after => ∀ id, result = some id → after.read id = some (direction.op.value amount value 0))) :
    Safe (Folding.wordMeaning other) (do
      if let some inner ← readAction (reads.operation right opAND) then
        if inner.items.length == 2 then
          if let some masked ← readAction (splitConstant reads inner.items) then
            if amount.toNat < 256 then
              let shift ← arithmetic (Folding.Zig.narrow 8 amount.toNat)
              let mask := direction.shift masked.value shift
              let shifted ← constructors.operation direction.op.opcode [left, masked.expression] debug
              return some (← constructors.operation opAND [shifted, ← constructors.constant mask debug] debug)
      next) before (fun result after => ∀ id, result = some id → after.read id = some (direction.op.value amount value 0)) := by
  apply read_action_bind_safe _ before _ _ _ valid
  intro option lookup
  cases option with
  | none => exact rest
  | some slice =>
    dsimp only
    split
    next arity =>
      apply read_action_bind_safe _ before _ _ _ valid
      intro option found
      cases option with
      | none => exact rest
      | some masked =>
        by_cases bound : amount.toNat < 256
        · simp only [bound, ↓reduceIte, Folding.Zig.narrow, arithmetic]
          obtain ⟨base, baseRead, nestedRead⟩ := split_value other before.read reads sound .and
            (Or.inr (Or.inr (Or.inl rfl))) right slice masked lookup found
          have same : value = base &&& masked.value := Option.some.inj (rhs.symm.trans nestedRead)
          rw [same, shift_mask_value direction amount base masked.value]
          apply Safe.bind _ before _ _ _ _ (correct.operation direction.op [left, masked.expression] [amount, base]
            (direction.op.value amount base 0) debug before valid (by simp [readArguments, lhs, baseRead]) (by cases direction <;> rfl))
          intro shifted middle validMiddle _ shiftedRead
          apply Safe.bind _ middle _ _ _ _ (correct.constant (direction.shift masked.value amount.toNat) debug middle validMiddle)
          intro maskId after validAfter stable maskRead
          exact operation_some_safe other constructors correct after validAfter .and [shifted, maskId]
            [direction.op.value amount base 0, direction.shift masked.value amount.toNat] _ debug
            (by simp [readArguments, stable _ _ shiftedRead, maskRead]) rfl
        · simpa only [bound, ↓reduceIte] using rest
    next => exact rest

end Compiler.Extraction.Dispatch
