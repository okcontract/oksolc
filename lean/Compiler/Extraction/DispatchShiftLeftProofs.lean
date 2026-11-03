/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchShiftProofs

namespace Compiler.Extraction.Dispatch
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

private theorem pure_bind_action (value : α) (next : α → Action β) :
    (pure value >>= next) = next value := rfl

/-- Within the word, SIGNEXTEND preserves low bits and repeats the selected
sign bit. Indices at least 31 preserve every bit, without a separate premise. -/
theorem signextend_bits (index value : Word) (bit : Nat) (bound : bit < 256) :
    (Folding.Op.signextend.value index value 0).getLsbD bit =
      if bit < 8 * (index.toNat + 1) then value.getLsbD bit
      else value.getLsbD (8 * (index.toNat + 1) - 1) := by
  by_cases small : index.toNat < 31
  · have signBound : 8 * (index.toNat + 1) - 1 < 8 * (index.toNat + 1) := by omega
    simp only [Folding.Op.value, small, ↓reduceIte, BitVec.getLsbD_signExtend,
      bound, decide_true, Bool.true_and, BitVec.getLsbD_setWidth,
      BitVec.msb_eq_getLsbD_last, signBound]
    split <;> simp_all
  · have inside : bit < 8 * (index.toNat + 1) := by omega
    simp [Folding.Op.value, small, inside]

theorem shift_byte_alignment (amount : Word) (aligned : amount &&& 7 = 0) :
    amount.toNat % 8 = 0 := by
  have bits := congrArg BitVec.toNat aligned
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat] at bits
  change amount.toNat &&& (2 ^ 3 - 1) = 0 at bits
  simpa only [Nat.and_two_pow_sub_one_eq_mod] using bits

theorem shift_byte_quotient (amount : Word) :
    (amount >>> 3).toNat = amount.toNat / 8 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- Moving an aligned logical left shift inside SIGNEXTEND moves its sign bit
by the same amount. Crossing the word boundary discards the extension bits. -/
theorem shl_signextend_value (amount index value : Word)
    (aligned : amount.toNat % 8 = 0) (amountBound : amount.toNat ≤ 256)
    (indexBound : index.toNat ≤ 32) :
    Folding.Op.shl.value amount (Folding.Op.signextend.value index value 0) 0 =
      Folding.Op.signextend.value (BitVec.ofNat 256 (amount.toNat / 8 + index.toNat))
        (Folding.Op.shl.value amount value 0) 0 := by
  have noWrap : amount.toNat / 8 + index.toNat < 2 ^ 256 := by omega
  have moved : (BitVec.ofNat 256 (amount.toNat / 8 + index.toNat)).toNat =
      amount.toNat / 8 + index.toNat := by simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt noWrap]
  have movedWidth : 8 * (amount.toNat / 8 + index.toNat + 1) =
      amount.toNat + 8 * (index.toNat + 1) := by omega
  have shl (x : Word) : Folding.Op.shl.value amount x 0 = x <<< amount.toNat :=
    shift_word_value .left amount x
  rw [shl, shl]
  apply BitVec.eq_of_getLsbD_eq
  intro bit bound
  rw [BitVec.getLsbD_shiftLeft, signextend_bits _ _ bit bound, moved, movedWidth]
  by_cases low : bit < amount.toNat
  · have inside : bit < amount.toNat + 8 * (index.toNat + 1) := by omega
    simp [bound, low, inside, BitVec.getLsbD_shiftLeft, OppositeShifts.Direction.shift]
  · have sourceBound : bit - amount.toNat < 256 := by omega
    rw [signextend_bits index value _ sourceBound]
    by_cases sourceLow : bit - amount.toNat < 8 * (index.toNat + 1)
    · have inside : bit < amount.toNat + 8 * (index.toNat + 1) := by omega
      simp [bound, low, sourceLow, inside, BitVec.getLsbD_shiftLeft, OppositeShifts.Direction.shift]
      rw [BitVec.getLsbD_eq_getElem]
    · have outside : ¬bit < amount.toNat + 8 * (index.toNat + 1) := by omega
      have signBound : amount.toNat + 8 * (index.toNat + 1) - 1 < 256 := by omega
      have signNotLow : ¬amount.toNat + 8 * (index.toNat + 1) - 1 < amount.toNat := by omega
      have signIndex : amount.toNat + 8 * (index.toNat + 1) - 1 - amount.toNat =
          8 * (index.toNat + 1) - 1 := by omega
      simp [bound, low, sourceLow, outside, BitVec.getLsbD_shiftLeft,
        OppositeShifts.Direction.shift, signBound, signNotLow, signIndex]
      rw [BitVec.getLsbD_eq_getElem]

theorem shl_signextend_index_add (amount index : Word)
    (amountBound : amount.toNat ≤ 256) (indexBound : index.toNat ≤ 32) :
    addWord (m := Action) (amount >>> 3) index = pure (BitVec.ofNat 256 (amount.toNat / 8 + index.toNat)) := by
  have noWrap : amount.toNat / 8 + index.toNat < 2 ^ 256 := by omega
  unfold addWord
  rw [shift_byte_quotient, Folding.Zig.checkedAdd, if_pos noWrap]
  rfl

theorem shl_signextend_candidate_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (amount value : Word) (debug : Debug)
    (lhs : before.read left = some amount) (rhs : before.read right = some value)
    (next : Action (Option NodeId))
    (rest : Safe (Folding.wordMeaning other) next before
      (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.shl.value amount value 0))) :
    Safe (Folding.wordMeaning other) (do
      if let some inner ← readAction (reads.operation right opSIGNEXTEND) then
        if let [indexId, baseId] := inner.items then
          if let some index ← readAction (reads.constant indexId) then
            if amount &&& 7 = 0 ∧ amount.toNat ≤ 256 ∧ index.toNat ≤ 32 then
              let shifted ← constructors.operation opSHL [left, baseId] debug
              return some (← constructors.operation opSIGNEXTEND
                [← constructors.constant (← addWord (amount >>> 3) index) debug, shifted] debug)
      next) before (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.shl.value amount value 0)) := by
  apply read_action_bind_safe _ before _ _ _ valid
  intro option lookup
  cases option with
  | none => exact rest
  | some slice =>
    dsimp only
    split
    next indexId baseId items =>
      apply read_action_bind_safe _ before _ _ _ valid
      intro option found
      cases option with
      | none => exact rest
      | some index =>
        by_cases guard : amount &&& 7 = 0 ∧ amount.toNat ≤ 256 ∧ index.toNat ≤ 32
        · simp only [guard, ↓reduceIte]
          obtain ⟨actual, base, indexRead, baseRead, nestedRead⟩ := binary_values other before.read reads sound .signextend
            rfl right indexId baseId slice lookup items
          have equal : actual = index := Option.some.inj (indexRead.symm.trans (sound.constant indexId index found))
          subst actual
          have same : value = Folding.Op.signextend.value index base 0 := Option.some.inj (rhs.symm.trans nestedRead)
          rw [same, shl_signextend_value amount index base (shift_byte_alignment amount guard.1) guard.2.1 guard.2.2,
            shl_signextend_index_add amount index guard.2.1 guard.2.2]
          apply Safe.bind _ before _ _ _ _ (correct.operation .shl [left, baseId] [amount, base]
            (Folding.Op.shl.value amount base 0) debug before valid (by simp [readArguments, lhs, baseRead]) rfl)
          intro shifted middle validMiddle _ shiftedRead
          exact constant_left_operation_some_safe other constructors correct middle validMiddle .signextend
            (BitVec.ofNat 256 (amount.toNat / 8 + index.toNat)) (Folding.Op.shl.value amount base 0)
            _ shifted debug shiftedRead rfl
        · simpa only [guard, ↓reduceIte] using rest
    next => exact rest

theorem shl_tail_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (known : Option Word) (debug : Debug)
    (lookup : reads.constant left = .ok known)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (do
      if let some amount := known then
        if amount.toNat ≥ 256 then return some (← constructors.constant 0 debug)
      if let some outerShift := known then
        if let some inner ← readAction (reads.operation right opSHL) then
          if let [index, value] := inner.items then
            if let some innerShift ← readAction (reads.constant index) then
              if outerShift.toNat ≥ 256 - min innerShift.toNat 256 then
                return some (← constructors.constant 0 debug)
              return some (← constructors.operation opSHL
                [← constructors.constant (← addWord outerShift innerShift) debug, value] debug)
        let opposite := if opSHL == opSHL then opSHR else opSHL
        if let some inner ← readAction (reads.operation right opposite) then
          if let [index, value] := inner.items then
            if let some innerShift ← readAction (reads.constant index) then
              if outerShift.toNat < 256 ∧ innerShift.toNat < 256 then
                return some (← OppositeShifts.combineOppositeShifts constructors opSHL outerShift innerShift value debug)
        if let some inner ← readAction (reads.operation right opAND) then
          if inner.items.length == 2 then
            if let some masked ← readAction (splitConstant reads inner.items) then
              if outerShift.toNat < 256 then
                let shift ← arithmetic (Folding.Zig.narrow 8 outerShift.toNat)
                let mask := if opSHL == opSHL then masked.value <<< shift else masked.value >>> shift
                let shifted ← constructors.operation opSHL [left, masked.expression] debug
                return some (← constructors.operation opAND [shifted, ← constructors.constant mask debug] debug)
      if let some amount := known then
        if let some inner ← readAction (reads.operation right opSIGNEXTEND) then
          if let [indexId, value] := inner.items then
            if let some index ← readAction (reads.constant indexId) then
              if amount &&& 7 = 0 ∧ amount.toNat ≤ 256 ∧ index.toNat ≤ 32 then
                let shifted ← constructors.operation opSHL [left, value] debug
                return some (← constructors.operation opSIGNEXTEND
                  [← constructors.constant (← addWord (amount >>> 3) index) debug, shifted] debug)
      return none) before (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.shl.value a b 0)) := by
  cases known with
  | none => exact Safe.pure _ before none _ valid (by simp)
  | some amount =>
    have same : a = amount := Option.some.inj (lhs.symm.trans (sound.constant left amount lookup))
    subst a
    by_cases large : 256 ≤ amount.toNat
    · simp only [large, ↓reduceIte]
      have zero : Folding.Op.shl.value amount b 0 = 0 := shift_large_value .left amount b large
      rw [zero]
      exact constant_some_safe other constructors correct before valid 0 debug
    · simp only [large, ↓reduceIte]
      apply same_shift_candidate_safe other reads constructors correct before valid sound .left right amount b debug rhs
      apply opposite_shift_candidate_safe other reads constructors correct before valid sound .left right amount b debug rhs
      apply masked_shift_candidate_safe other reads constructors correct before valid sound .left left right amount b debug lhs rhs
      apply shl_signextend_candidate_safe other reads constructors correct before valid sound left right amount b debug lhs rhs
      exact Safe.pure _ before none _ valid (by simp)

theorem binary_shl_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (binaryStage reads constructors usizeBits opSHL left right debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.shl.value a b 0)) := by
  unfold binaryStage binaryStageWithInputs
  simp only [opSDIV, opAND, opBYTE, opSLT, opSGT, opXOR, opOR,
    opSIGNEXTEND, opMOD, opSHR, opSHL, opMUL, opDIV, opSUB, Associative.isAssociative,
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
    have tail := shl_tail_safe other reads constructors correct before valid sound left right a b lc debug leftRead lhs rhs
    by_cases equal : sameExpression reads left right = true
    · simp only [equal, ↓reduceIte]
      have facts := equal_facts_reliable _ before.read reads sound left right a b lhs rhs equal
      split
      next replacement selected =>
        apply algebraic_selected_safe other constructors correct before valid _ 0 .equal _ left right a b _ debug lhs rhs facts replacement selected
        rfl
      next => cases lc <;> simpa only [pure_bind_action] using tail
    · simp only [equal, ↓reduceIte]
      cases lc <;> simpa only [pure_bind_action] using tail

theorem binary_shl_miss (reads : Reads) (constructors : Constructors Debug)
    (left right : NodeId) (debug : Debug) (options : Options) (usizeBits : Nat) :
    MissUnchanged (binaryStage reads constructors usizeBits opSHL left right debug options) := by
  unfold binaryStage binaryStageWithInputs
  simp only [opSDIV, opAND, opBYTE, opSLT, opSGT, opXOR, opOR,
    opSIGNEXTEND, opMOD, opSHR, opSHL, opMUL, opDIV, opSUB, Associative.isAssociative,
    Bool.false_eq_true, ↓reduceIte, Bool.false_or, Bool.or_false, Bool.true_or, Bool.or_true,
    List.contains_cons, List.contains_nil, beq_self_eq_true, BitVec.reduceBEq]
  simp only [pure_bind_action]
  apply read_miss_unchanged
  intro lc
  apply read_miss_unchanged
  intro rc
  by_cases equal : sameExpression reads left right = true
  all_goals simp only [equal, Bool.false_eq_true, ↓reduceIte]
  all_goals cases lc
  all_goals simp only [pure_bind_action]
  all_goals repeat first
    | exact pure_miss_unchanged _
    | exact terminal_miss_unchanged _
    | apply read_miss_unchanged; intro option
    | apply arithmetic_miss_unchanged; intro option
    | split
    | apply never_miss_unchanged
      repeat first
        | exact terminal_never_miss _
        | apply bind_never_miss; intro id

theorem shl_evm_stage (reads : Reads) (constructors : Constructors Debug)
    (arguments : List NodeId) (debug : Debug) (version : Version) (usizeBits : Nat) :
    evmStage reads constructors usizeBits opSHL arguments debug version = pure none := by
  simp only [evmStage, evmStageWithInputs, logicalOperand, opSHL, opBALANCE, opEXP, opMUL, opDIV,
    Bool.false_eq_true, ↓reduceIte, BitVec.reduceBEq]
  repeat first | rfl | split

/-- Complete SHL dispatch: constant folding and tables, large shifts, nested
same/opposite shifts, mask distribution and sign extension, with actual failure states. -/
theorem shl_simplify_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (simplifyWithOptions reads constructors usizeBits opSHL [left, right] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.shl.value a b 0)) := by
  apply binary_simplify_safe other reads constructors correct before valid sound opSHL left right a b _ 0
    debug options usizeBits lhs rhs rfl
    (binary_shl_safe other reads constructors correct before valid sound left right a b debug options usizeBits lhs rhs)
    (binary_shl_miss reads constructors left right debug options usizeBits)
  intro version _
  rw [shl_evm_stage reads constructors]
  exact Safe.pure _ before none _ valid (by simp)

theorem interner_shl_simplify_safe (other : Meaning) (pushes : Pushes other) (p : Primitives)
    (contracts : Contracts (Folding.wordMeaning other) p) (reads : Reads) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (simplifyWithOptions reads (implementedConstructors p) usizeBits opSHL [left, right] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.shl.value a b 0)) :=
  shl_simplify_safe other reads (implementedConstructors p)
    (implemented_constructors_sound other pushes p contracts) before valid sound
    left right a b debug options usizeBits lhs rhs

end Compiler.Extraction.Dispatch
