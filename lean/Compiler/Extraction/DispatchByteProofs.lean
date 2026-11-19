/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchAlgebraicProofs

namespace Compiler.Extraction.Dispatch
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192

theorem byte_bits (index value : Word) (bit : Nat) :
    (Folding.Op.byte.value index value 0).getLsbD bit =
      if bit < 8 ∧ index.toNat < 32 then value.getLsbD (8 * (31 - index.toNat) + bit) else false := by
  have mask : (255#256).getLsbD bit = decide (bit < 8) := by
    change (BitVec.ofNat 256 (2 ^ 8 - 1)).getLsbD bit = _
    rw [BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
    by_cases small : bit < 8
    · simp [small, show bit < 256 by omega]
    · simp [small]
  by_cases inside : index.toNat < 32 <;>
    simp [Folding.Op.value, inside, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, mask, Bool.and_comm]

theorem byte_zero_value (index : Word) : Folding.Op.byte.value index 0 0 = 0 := by
  simp [Folding.Op.value]

theorem byte_large_value (index value : Word) (large : 32 ≤ index.toNat) :
    Folding.Op.byte.value index value 0 = 0 := by
  simp [Folding.Op.value, show ¬index.toNat < 32 by omega]

theorem byte_last_value (value : Word) : Folding.Op.byte.value 31 value 0 = value &&& 255 := by
  simp [Folding.Op.value]

private theorem shl_nat (amount value : Word) :
    Folding.Op.shl.value amount value 0 = value <<< amount.toNat := by
  by_cases small : amount.toNat < 256
  · simp [Folding.Op.value, Binary.eval, small]
  · simp [Folding.Op.value, Binary.eval, small, BitVec.shiftLeft_eq_zero (by omega : 256 ≤ amount.toNat)]

private theorem shr_nat (amount value : Word) :
    Folding.Op.shr.value amount value 0 = value >>> amount.toNat := by
  by_cases small : amount.toNat < 256
  · simp [Folding.Op.value, Binary.eval, small]
  · simp [Folding.Op.value, Binary.eval, small, BitVec.ushiftRight_eq_zero (by omega : 256 ≤ amount.toNat)]

/-- An aligned left shift moves the byte index forward. An index crossing 31
selects zero; this also covers the source guard's index 32 and shift 256. -/
theorem byte_left_shift_value (index amount value : Word)
    (aligned : amount.toNat % 8 = 0) (indexBound : index.toNat ≤ 32) (amountBound : amount.toNat ≤ 256) :
    Folding.Op.byte.value index (Folding.Op.shl.value amount value 0) 0 =
      Folding.Op.byte.value (BitVec.ofNat 256 (index.toNat + amount.toNat / 8)) value 0 := by
  have noWrap : index.toNat + amount.toNat / 8 < 2 ^ 256 := by omega
  have moved : (BitVec.ofNat 256 (index.toNat + amount.toNat / 8)).toNat = index.toNat + amount.toNat / 8 := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt noWrap]
  rw [shl_nat]
  apply BitVec.eq_of_getLsbD_eq
  intro bit _
  rw [byte_bits, byte_bits, moved]
  by_cases low : bit < 8
  · by_cases inside : index.toNat < 32
    · by_cases finalInside : index.toNat + amount.toNat / 8 < 32
      · have beforeBound : 8 * (31 - index.toNat) + bit < 256 := by omega
        have notLow : ¬8 * (31 - index.toNat) + bit < amount.toNat := by omega
        have same : 8 * (31 - index.toNat) + bit - amount.toNat =
            8 * (31 - (index.toNat + amount.toNat / 8)) + bit := by omega
        simp [low, inside, finalInside, BitVec.getLsbD_shiftLeft, beforeBound, notLow, same]
        rw [BitVec.getLsbD_eq_getElem]
      · have discarded : 8 * (31 - index.toNat) + bit < amount.toNat := by omega
        simp [low, inside, finalInside, BitVec.getLsbD_shiftLeft, discarded]
    · have outside : ¬index.toNat + amount.toNat / 8 < 32 := by omega
      simp [low, inside, outside]
  · simp [low]

/-- This zero rule does not require byte alignment or a bounded shift amount.
Even the highest selected bit comes from beyond the word. -/
theorem byte_right_shift_zero_value (index amount value : Word)
    (discarded : index.toNat < amount.toNat / 8) :
    Folding.Op.byte.value index (Folding.Op.shr.value amount value 0) 0 = 0 := by
  rw [shr_nat]
  apply BitVec.eq_of_getLsbD_eq
  intro bit _
  rw [byte_bits]
  by_cases selected : bit < 8 ∧ index.toNat < 32
  · have outside : 256 ≤ amount.toNat + (8 * (31 - index.toNat) + bit) := by omega
    simp [selected, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_of_ge value _ outside]
  · simp [selected]

theorem byte_right_shift_value (index amount value : Word)
    (aligned : amount.toNat % 8 = 0) (indexBound : index.toNat < 32)
    (ordered : amount.toNat / 8 ≤ index.toNat) :
    Folding.Op.byte.value index (Folding.Op.shr.value amount value 0) 0 =
      Folding.Op.byte.value (BitVec.ofNat 256 (index.toNat - amount.toNat / 8)) value 0 := by
  have noWrap : index.toNat - amount.toNat / 8 < 2 ^ 256 := by omega
  have moved : (BitVec.ofNat 256 (index.toNat - amount.toNat / 8)).toNat = index.toNat - amount.toNat / 8 := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt noWrap]
  have inside : index.toNat - amount.toNat / 8 < 32 := by omega
  rw [shr_nat]
  apply BitVec.eq_of_getLsbD_eq
  intro bit _
  rw [byte_bits, byte_bits, moved]
  have same : amount.toNat + (8 * (31 - index.toNat) + bit) =
      8 * (31 - (index.toNat - amount.toNat / 8)) + bit := by omega
  simp [indexBound, inside, BitVec.getLsbD_ushiftRight, same]

private theorem byte_quotient (amount : Word) (bound : amount.toNat ≤ 256) :
    (BitVec.ofNat 256 (amount.toNat / 8)).toNat = amount.toNat / 8 := by
  have noWrap : amount.toNat / 8 < 2 ^ 256 := by omega
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt noWrap]

theorem byte_index_add (index amount : Word) (indexBound : index.toNat ≤ 32) (amountBound : amount.toNat ≤ 256) :
    addWord (m := Action) index (BitVec.ofNat 256 (amount.toNat / 8)) =
      pure (BitVec.ofNat 256 (index.toNat + amount.toNat / 8)) := by
  have noWrap : index.toNat + amount.toNat / 8 < 2 ^ 256 := by omega
  unfold addWord
  rw [byte_quotient amount amountBound, Folding.Zig.checkedAdd, if_pos noWrap]
  rfl

theorem byte_index_sub (index amount : Word) (amountBound : amount.toNat ≤ 256)
    (ordered : amount.toNat / 8 ≤ index.toNat) :
    subWord (m := Action) index (BitVec.ofNat 256 (amount.toNat / 8)) =
      pure (BitVec.ofNat 256 (index.toNat - amount.toNat / 8)) := by
  unfold subWord
  rw [byte_quotient amount amountBound, Folding.Zig.checkedSub, if_pos ordered]
  rfl

theorem byte_left_candidate_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (right : NodeId) (index value : Word) (debug : Debug)
    (rhs : before.read right = some value) (next : Action (Option NodeId))
    (rest : Safe (Folding.wordMeaning other) next before
      (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.byte.value index value 0))) :
    Safe (Folding.wordMeaning other) (do
      if let some shift ← readAction (reads.operation right opSHL) then
        if let [amountId, baseId] := shift.items then
          if let some amount ← readAction (reads.constant amountId) then
            if amount.toNat % 8 = 0 ∧ index.toNat ≤ 32 ∧ amount.toNat ≤ 256 then
              return some (← constructors.operation opBYTE
                [← constructors.constant (← addWord index (BitVec.ofNat 256 (amount.toNat / 8))) debug, baseId] debug)
      next) before (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.byte.value index value 0)) := by
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
      | some amount =>
        by_cases guard : amount.toNat % 8 = 0 ∧ index.toNat ≤ 32 ∧ amount.toNat ≤ 256
        · simp only [guard, ↓reduceIte]
          obtain ⟨actual, base, amountRead, baseRead, shiftedRead⟩ := binary_values other before.read reads sound .shl rfl right amountId baseId slice lookup items
          have equal : actual = amount := Option.some.inj (amountRead.symm.trans (sound.constant amountId amount found))
          subst actual
          have same : value = Folding.Op.shl.value amount base 0 := Option.some.inj (rhs.symm.trans shiftedRead)
          rw [same, byte_left_shift_value index amount base guard.1 guard.2.1 guard.2.2,
            byte_index_add index amount guard.2.1 guard.2.2]
          exact constant_left_operation_some_safe other constructors correct before valid .byte
            (BitVec.ofNat 256 (index.toNat + amount.toNat / 8)) base _ baseId debug baseRead rfl
        · simpa only [guard, ↓reduceIte] using rest
    next => exact rest

theorem byte_right_candidate_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (right : NodeId) (index value : Word) (debug : Debug)
    (rhs : before.read right = some value) :
    Safe (Folding.wordMeaning other) (do
      if let some shift ← readAction (reads.operation right opSHR) then
        if let [amountId, baseId] := shift.items then
          if let some amount ← readAction (reads.constant amountId) then
            if index.toNat < amount.toNat / 8 then return some (← constructors.constant 0 debug)
            if amount.toNat % 8 = 0 ∧ index.toNat < 32 ∧ amount.toNat ≤ 256 then
              return some (← constructors.operation opBYTE
                [← constructors.constant (← subWord index (BitVec.ofNat 256 (amount.toNat / 8))) debug, baseId] debug)
      return none) before (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.byte.value index value 0)) := by
  apply read_action_bind_safe _ before _ _ _ valid
  intro option lookup
  cases option with
  | none => exact Safe.pure _ before none _ valid (by simp)
  | some slice =>
    dsimp only
    split
    next amountId baseId items =>
      apply read_action_bind_safe _ before _ _ _ valid
      intro option found
      cases option with
      | none => exact Safe.pure _ before none _ valid (by simp)
      | some amount =>
        obtain ⟨actual, base, amountRead, baseRead, shiftedRead⟩ := binary_values other before.read reads sound .shr rfl right amountId baseId slice lookup items
        have equal : actual = amount := Option.some.inj (amountRead.symm.trans (sound.constant amountId amount found))
        subst actual
        have same : value = Folding.Op.shr.value amount base 0 := Option.some.inj (rhs.symm.trans shiftedRead)
        by_cases discarded : index.toNat < amount.toNat / 8
        · simp only [discarded, ↓reduceIte]
          rw [same, byte_right_shift_zero_value index amount base discarded]
          exact constant_some_safe other constructors correct before valid 0 debug
        · simp only [discarded, ↓reduceIte]
          by_cases guard : amount.toNat % 8 = 0 ∧ index.toNat < 32 ∧ amount.toNat ≤ 256
          · simp only [guard, ↓reduceIte]
            have ordered : amount.toNat / 8 ≤ index.toNat := by omega
            rw [same, byte_right_shift_value index amount base guard.1 guard.2.1 ordered,
              byte_index_sub index amount guard.2.2 ordered]
            exact constant_left_operation_some_safe other constructors correct before valid .byte
              (BitVec.ofNat 256 (index.toNat - amount.toNat / 8)) base _ baseId debug baseRead rfl
          · simp only [guard, ↓reduceIte]
            exact Safe.pure _ before none _ valid (by simp)
    next => exact Safe.pure _ before none _ valid (by simp)

theorem byte_tail_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (known : Option Word) (debug : Debug)
    (lookup : reads.constant left = .ok known)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (do
      if let some index := known then
        if index.toNat ≥ 32 then return some (← constructors.constant 0 debug)
      if let some index := known then
        if let some shift ← readAction (reads.operation right opSHL) then
          if let [amountId, value] := shift.items then
            if let some amount ← readAction (reads.constant amountId) then
              if amount.toNat % 8 = 0 ∧ index.toNat ≤ 32 ∧ amount.toNat ≤ 256 then
                return some (← constructors.operation opBYTE
                  [← constructors.constant (← addWord index (BitVec.ofNat 256 (amount.toNat / 8))) debug, value] debug)
        if let some shift ← readAction (reads.operation right opSHR) then
          if let [amountId, value] := shift.items then
            if let some amount ← readAction (reads.constant amountId) then
              if index.toNat < amount.toNat / 8 then return some (← constructors.constant 0 debug)
              if amount.toNat % 8 = 0 ∧ index.toNat < 32 ∧ amount.toNat ≤ 256 then
                return some (← constructors.operation opBYTE
                  [← constructors.constant (← subWord index (BitVec.ofNat 256 (amount.toNat / 8))) debug, value] debug)
      return none) before (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.byte.value a b 0)) := by
  cases known with
  | none => exact Safe.pure _ before none _ valid (by simp)
  | some index =>
    have same : a = index := Option.some.inj (lhs.symm.trans (sound.constant left index lookup))
    subst a
    by_cases large : 32 ≤ index.toNat
    · simp only [large, ↓reduceIte]
      rw [byte_large_value index b large]
      exact constant_some_safe other constructors correct before valid 0 debug
    · simp only [large, ↓reduceIte]
      apply byte_left_candidate_safe other reads constructors correct before valid sound right index b debug rhs
      exact byte_right_candidate_safe other reads constructors correct before valid sound right index b debug rhs

private theorem pure_bind_action (value : α) (next : α → Action β) :
    (pure value >>= next) = next value := rfl

theorem binary_byte_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (binaryStage reads constructors usizeBits opBYTE left right debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.byte.value a b 0)) := by
  unfold binaryStage binaryStageWithInputs
  simp only [opSDIV, opAND, opBYTE, opSLT, opSGT, opXOR, opOR,
    opSIGNEXTEND, opMOD, opSHL, opSHR, opMUL, opDIV, opSUB, Associative.isAssociative,
    Bool.false_eq_true, ↓reduceIte, Bool.false_or, Bool.or_false, Bool.true_or, Bool.or_true,
    List.contains_cons, List.contains_nil, beq_self_eq_true, BitVec.reduceBEq]
  apply read_action_bind_safe _ before _ _ _ valid
  intro lc leftRead
  apply read_action_bind_safe _ before _ _ _ valid
  intro rc rightRead
  have reliable := constant_facts_reliable _ before.read reads sound left right a b lhs rhs lc rc leftRead rightRead
  split
  next replacement selected =>
    apply algebraic_selected_safe other constructors correct before valid _ 0 .constants _ left right a b _ debug lhs rhs reliable replacement selected
    rfl
  next =>
    have tail := byte_tail_safe other reads constructors correct before valid sound left right a b lc debug leftRead lhs rhs
    by_cases last : lc = some (31 : Word)
    · subst lc
      simp only [beq_self_eq_true, ↓reduceIte]
      have same : a = 31 := Option.some.inj (lhs.symm.trans (sound.constant left 31 leftRead))
      rw [same, byte_last_value]
      apply Safe.bind _ before _ _ _ _ (correct.constant 255 debug before valid)
      intro maskId after validAfter stable maskRead
      exact operation_some_safe other constructors correct after validAfter .and [right, maskId] [b, 255] _ debug
        (by simp [readArguments, maskRead, stable right b rhs]) rfl
    · have different : (lc == some (31 : Word)) = false := by simpa using last
      simp only [different, Bool.false_eq_true, ↓reduceIte]
      split
      next equal =>
        have facts := equal_facts_reliable _ before.read reads sound left right a b lhs rhs equal
        split
        next replacement selected =>
          apply algebraic_selected_safe other constructors correct before valid _ 0 .equal _ left right a b _ debug lhs rhs facts replacement selected
          rfl
        next => cases lc <;> simpa only [pure_bind_action] using tail
      next => cases lc <;> simpa only [pure_bind_action] using tail

theorem binary_byte_miss (reads : Reads) (constructors : Constructors Debug)
    (left right : NodeId) (debug : Debug) (options : Options) (usizeBits : Nat) :
    MissUnchanged (binaryStage reads constructors usizeBits opBYTE left right debug options) := by
  unfold binaryStage binaryStageWithInputs
  simp only [opSDIV, opAND, opBYTE, opSLT, opSGT, opXOR, opOR,
    opSIGNEXTEND, opMOD, opSHL, opSHR, opMUL, opDIV, opSUB, Associative.isAssociative,
    Bool.false_eq_true, ↓reduceIte, Bool.false_or, Bool.or_false, Bool.true_or, Bool.or_true,
    List.contains_cons, List.contains_nil, beq_self_eq_true, BitVec.reduceBEq]
  simp only [pure_bind_action]
  repeat first
    | exact pure_miss_unchanged _
    | exact terminal_miss_unchanged _
    | apply read_miss_unchanged; intro option
    | apply arithmetic_miss_unchanged; intro option
    | split
    | apply never_miss_unchanged
      repeat first
        | exact terminal_never_miss _
        | apply bind_never_miss; intro id

theorem byte_evm_stage (reads : Reads) (constructors : Constructors Debug)
    (arguments : List NodeId) (debug : Debug) (version : Version) (usizeBits : Nat) :
    evmStage reads constructors usizeBits opBYTE arguments debug version = pure none := by
  simp only [evmStage, evmStageWithInputs, logicalOperand, opBYTE, opBALANCE, opEXP, opMUL, opDIV,
    Bool.false_eq_true, ↓reduceIte, BitVec.reduceBEq]
  repeat first | rfl | split

/-- Complete BYTE dispatch, including the early last-byte mask, out-of-range
zero, ordered shift candidates and checked index arithmetic. -/
theorem byte_simplify_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (simplifyWithOptions reads constructors usizeBits opBYTE [left, right] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.byte.value a b 0)) := by
  apply binary_simplify_safe other reads constructors correct before valid sound opBYTE left right a b _ 0
    debug options usizeBits lhs rhs rfl
    (binary_byte_safe other reads constructors correct before valid sound left right a b debug options usizeBits lhs rhs)
    (binary_byte_miss reads constructors left right debug options usizeBits)
  intro version _
  rw [byte_evm_stage reads constructors]
  exact Safe.pure _ before none _ valid (by simp)

theorem interner_byte_simplify_safe (other : Meaning) (pushes : Pushes other) (p : Primitives)
    (contracts : Contracts (Folding.wordMeaning other) p) (reads : Reads) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (simplifyWithOptions reads (implementedConstructors p) usizeBits opBYTE [left, right] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.byte.value a b 0)) :=
  byte_simplify_safe other reads (implementedConstructors p)
    (implemented_constructors_sound other pushes p contracts) before valid sound
    left right a b debug options usizeBits lhs rhs

end Compiler.Extraction.Dispatch
