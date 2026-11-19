/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchShiftLeftProofs
import Compiler.Extraction.ArithmeticShift

namespace Compiler.Extraction.Dispatch
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

private theorem pure_bind_action (value : α) (next : α → Action β) :
    (pure value >>= next) = next value := rfl

private theorem arithmetic_map_bind (result : Except Folding.Fault α) (f : α → β) (next : β → Action γ) :
    ((do return f (← arithmetic result)) >>= next) =
      (arithmetic result >>= fun value => next (f value)) := by
  cases result <;> rfl

theorem signextend_min_value (outer inner value : Word) :
    Folding.Op.signextend.value outer (Folding.Op.signextend.value inner value 0) 0 =
      Folding.Op.signextend.value (if outer.toNat ≤ inner.toNat then outer else inner) value 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit bound
  rw [signextend_bits outer _ bit bound]
  by_cases ordered : outer.toNat ≤ inner.toNat
  · simp only [ordered, ↓reduceIte]
    rw [signextend_bits outer value bit bound]
    by_cases low : bit < 8 * (outer.toNat + 1)
    · have innerLow : bit < 8 * (inner.toNat + 1) := by omega
      simp only [low, ↓reduceIte]
      rw [signextend_bits inner value bit bound, if_pos innerLow]
    · have signBound : 8 * (outer.toNat + 1) - 1 < 256 := by omega
      have signLow : 8 * (outer.toNat + 1) - 1 < 8 * (inner.toNat + 1) := by omega
      simp only [low, ↓reduceIte]
      rw [signextend_bits inner value _ signBound, if_pos signLow]
  · simp only [ordered, ↓reduceIte]
    rw [signextend_bits inner value bit bound]
    by_cases low : bit < 8 * (outer.toNat + 1)
    · simp only [low, ↓reduceIte]
    · have signBound : 8 * (outer.toNat + 1) - 1 < 256 := by omega
      have signHigh : ¬8 * (outer.toNat + 1) - 1 < 8 * (inner.toNat + 1) := by omega
      have bitHigh : ¬bit < 8 * (inner.toNat + 1) := by omega
      simp only [low, bitHigh, ↓reduceIte]
      rw [signextend_bits inner value _ signBound, if_neg signHigh]

theorem signextend_repeat_value (index value : Word) :
    Folding.Op.signextend.value index (Folding.Op.signextend.value index value 0) 0 =
      Folding.Op.signextend.value index value 0 := by
  simpa using signextend_min_value index index value

theorem signextend_large_value (index value : Word) (large : 31 ≤ index.toNat) :
    Folding.Op.signextend.value index value 0 = value := by
  simp [Folding.Op.value, show ¬index.toNat < 31 by omega]

/-- The byte selected by the native guard is exactly the original word's
sign bit after the logical shift. Arithmetic shift repeats that same bit. -/
theorem signextend_shr_value (index amount value : Word) (aligned : amount.toNat % 8 = 0)
    (amountBound : amount.toNat ≤ 256) (position : (256 - amount.toNat) / 8 = index.toNat + 1) :
    Folding.Op.signextend.value index (Folding.Op.shr.value amount value 0) 0 =
      ArithmeticShift.value amount value := by
  have width : 8 * (index.toNat + 1) = 256 - amount.toNat := by omega
  have sign : amount.toNat + (8 * (index.toNat + 1) - 1) = 255 := by omega
  have shr : Folding.Op.shr.value amount value 0 = value >>> amount.toNat := shift_word_value .right amount value
  rw [shr, ArithmeticShift.value_nat]
  apply BitVec.eq_of_getLsbD_eq
  intro bit bound
  rw [signextend_bits index _ bit bound, BitVec.getLsbD_sshiftRight]
  by_cases low : bit < 8 * (index.toNat + 1)
  · have inside : amount.toNat + bit < 256 := by omega
    simp [low, inside, show ¬256 ≤ bit by omega, BitVec.getLsbD_ushiftRight]
  · have outside : ¬amount.toNat + bit < 256 := by omega
    simp [low, outside, show ¬256 ≤ bit by omega, BitVec.getLsbD_ushiftRight,
      sign, BitVec.msb_eq_getLsbD_last]

namespace Preservation

/-- SAR is outside the folder's opcode set. Its child law retains the same
actual reached-state and caller-debug discipline as word operation rules. -/
def SarRule {State Failure Debug : Type} (logic : BuilderLogic (Effect State Failure) State)
    (constructors : Constructors Debug (Effect State Failure)) (debug : Debug) : Prop :=
  ∀ left right amount word before, logic.valid before →
    logic.read before left = some amount → logic.read before right = some word →
    logic.safe (constructors.operation ArithmeticShift.opcode [left, right] debug) before
      (fun id after => logic.read after id = some (ArithmeticShift.value amount word))

private theorem pure_bind_effect (value : α) (next : α → Effect State Failure β) :
    (pure value >>= next) = next value := rfl

theorem signextend_shift_sub {State Failure : Type} [MonadLift (Except Error) (Effect State Failure)] (amount : Word) (bound : amount.toNat ≤ 256) :
    subWord (m := Effect State Failure) 256 amount = pure (BitVec.ofNat 256 (256 - amount.toNat)) := by
  unfold subWord
  rw [Folding.Zig.checkedSub, show (256 : Word).toNat = 256 by rfl, if_pos bound]
  rfl

theorem signextend_index_add {State Failure : Type} [MonadLift (Except Error) (Effect State Failure)] (index : Word) (bound : index.toNat ≤ 256) :
    addWord (m := Effect State Failure) index 1 = pure (BitVec.ofNat 256 (index.toNat + 1)) := by
  have noWrap : index.toNat + 1 < 2 ^ 256 := by omega
  unfold addWord
  rw [Folding.Zig.checkedAdd, show (1 : Word).toNat = 1 by rfl, if_pos noWrap]
  rfl

theorem signextend_nested_safe {State Failure Debug : Type} [MonadLift (Except Error) (Effect State Failure)]
    (logic : BuilderLogic (Effect State Failure) State) (rules : ReadRules logic)
    (other : Meaning) (reads : Reads) (constructors : Constructors Debug (Effect State Failure)) (debug : Debug)
    (correct : BuilderRules logic (algebraicBuilder constructors) debug)
    (operation : OperationRule logic constructors debug .signextend) (before : State)
    (valid : logic.valid before)
    (sound : Sound (Folding.wordMeaning other) (logic.read before) reads)
    (operand : OperandRead (Effect State Failure))
    (inputs : ∀ middle, logic.valid middle → UnaryPreservation.Inputs logic reads operand middle)
    (left right : NodeId) (a b : Word) (known : Option Word)
    (lookup : reads.constant left = .ok known)
    (lhs : (logic.read before) left = some a) (rhs : (logic.read before) right = some b)
    (next : Effect State Failure (Option NodeId))
    (rest : logic.safe next before
      (fun result after => ∀ id, result = some id → logic.read after id = some (Folding.Op.signextend.value a b 0))) :
    logic.safe (do
      if let some inner ← readAction (reads.operation right opSIGNEXTEND) then
        if let [index, value] := inner.items then
          if sameExpression reads left index then
            return some (← constructors.operation opSIGNEXTEND [left, ← operand inner 1 value] debug)
          if let some outerByte := known then
            if let some innerByte ← readAction (reads.constant index) then
              return some (← constructors.operation opSIGNEXTEND
                [← constructors.constant (if outerByte.toNat ≤ innerByte.toNat then outerByte else innerByte) debug, ← operand inner 1 value] debug)
      next) before (fun result after => ∀ id, result = some id → logic.read after id = some (Folding.Op.signextend.value a b 0)) := by
  apply rules.bind before _ _ _ valid
  intro option found
  cases option with
  | none => exact rest
  | some slice =>
    dsimp only
    split
    next index value items =>
      obtain ⟨innerByte, base, indexRead, baseRead, nestedRead⟩ := binary_values other (logic.read before) reads sound .signextend
        rfl right index value slice found items
      have same : b = Folding.Op.signextend.value innerByte base 0 := Option.some.inj (rhs.symm.trans nestedRead)
      by_cases equal : sameExpression reads left index = true
      · simp only [equal, ↓reduceIte]
        have sameIndex := sound.equal left index a innerByte equal lhs indexRead
        rw [same, ← sameIndex, signextend_repeat_value]
        apply logic.bind before _ _ _ _ (inputs before valid right opSIGNEXTEND slice found 1 value (by simp [items]))
        intro loaded after validAfter stable actual
        subst loaded
        exact UnaryPreservation.some_safe logic _ after _
          (operation [left, value] [a, base] _ after validAfter
            (by simp [readArguments, stable _ _ lhs, stable _ _ baseRead]) rfl)
      · simp only [equal, ↓reduceIte]
        cases known with
        | none => exact rest
        | some outerByte =>
          apply rules.bind before _ _ _ valid
          intro option constantFound
          cases option with
          | none => exact rest
          | some actual =>
            have outerSame : a = outerByte := Option.some.inj (lhs.symm.trans (sound.constant left outerByte lookup))
            have innerSame : innerByte = actual := Option.some.inj (indexRead.symm.trans (sound.constant index actual constantFound))
            rw [same, outerSame, innerSame, signextend_min_value]
            exact constant_left_operation_inputs_safe logic constructors debug .signextend operation before
              (if outerByte.toNat ≤ actual.toNat then outerByte else actual) base _ value (operand slice 1 value)
              (correct.constant _ before valid)
              (fun middle invariant => inputs middle invariant right opSIGNEXTEND slice found 1 value (by simp [items])) baseRead rfl
    next => exact rest

theorem signextend_shift_safe {State Failure Debug : Type} [MonadLift (Except Error) (Effect State Failure)]
    (logic : BuilderLogic (Effect State Failure) State) (rules : ReadRules logic)
    (other : Meaning) (reads : Reads) (constructors : Constructors Debug (Effect State Failure)) (debug : Debug)
    (sarCorrect : SarRule logic constructors debug) (before : State)
    (valid : logic.valid before)
    (sound : Sound (ArithmeticShift.meaning other) (logic.read before) reads)
    (operand : OperandRead (Effect State Failure))
    (inputs : ∀ middle, logic.valid middle → UnaryPreservation.Inputs logic reads operand middle)
    (right : NodeId) (index value : Word)
    (rhs : (logic.read before) right = some value) (next : Effect State Failure (Option NodeId))
    (rest : logic.safe next before
      (fun result after => ∀ id, result = some id → logic.read after id = some (Folding.Op.signextend.value index value 0))) :
    logic.safe (do
      if let some shift ← readAction (reads.operation right opSHR) then
        if let [amountId, baseId] := shift.items then
          if let some amount ← readAction (reads.constant amountId) then
            if amount.toNat % 8 = 0 ∧ amount.toNat ≤ 256 ∧ index.toNat ≤ 256 then
              let remaining ← subWord 256 amount
              let endIndex ← addWord index 1
              if remaining.toNat / 8 = endIndex.toNat then
                return some (← constructors.operation opSAR [← operand shift 0 amountId, ← operand shift 1 baseId] debug)
      next) before (fun result after => ∀ id, result = some id → logic.read after id = some (Folding.Op.signextend.value index value 0)) := by
  apply rules.bind before _ _ _ valid
  intro option lookup
  cases option with
  | none => exact rest
  | some slice =>
    dsimp only
    split
    next amountId baseId items =>
      apply rules.bind before _ _ _ valid
      intro option found
      cases option with
      | none => exact rest
      | some amount =>
        by_cases guard : amount.toNat % 8 = 0 ∧ amount.toNat ≤ 256 ∧ index.toNat ≤ 256
        · simp only [guard, and_self, ↓reduceIte]
          have remainingNat : (BitVec.ofNat 256 (256 - amount.toNat)).toNat = 256 - amount.toNat := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          have endNat : (BitVec.ofNat 256 (index.toNat + 1)).toNat = index.toNat + 1 := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          rw [signextend_shift_sub amount guard.2.1, signextend_index_add index guard.2.2]
          simp only [pure_bind_effect, remainingNat, endNat]
          split
          next position =>
            obtain ⟨actual, base, amountRead, baseRead, nestedRead⟩ := binary_values (ArithmeticShift.shiftMeaning other)
              (logic.read before) reads sound .shr rfl right amountId baseId slice lookup items
            have equal : actual = amount := Option.some.inj (amountRead.symm.trans (sound.constant amountId amount found))
            subst actual
            have same : value = Folding.Op.shr.value amount base 0 := Option.some.inj (rhs.symm.trans nestedRead)
            rw [same, signextend_shr_value index amount base guard.1 guard.2.1 position]
            apply logic.bind before _ _ _ _ (inputs before valid right opSHR slice lookup 0 amountId (by simp [items]))
            intro loadedAmount middle validMiddle stableAmount actualAmount
            subst loadedAmount
            apply logic.bind middle _ _ _ _ (inputs middle validMiddle right opSHR slice lookup 1 baseId (by simp [items]))
            intro loadedBase after validAfter stableBase actualBase
            subst loadedBase
            exact UnaryPreservation.some_safe logic _ after _
              (sarCorrect amountId baseId amount base after validAfter
                (stableBase _ _ (stableAmount _ _ amountRead)) (stableBase _ _ (stableAmount _ _ baseRead)))
          next => exact rest
        · simpa only [guard, ↓reduceIte] using rest
    next => exact rest

theorem signextend_tail_safe {State Failure Debug : Type} [MonadLift (Except Error) (Effect State Failure)]
    (logic : BuilderLogic (Effect State Failure) State) (rules : ReadRules logic)
    (other : Meaning) (reads : Reads) (constructors : Constructors Debug (Effect State Failure)) (debug : Debug)
    (sarCorrect : SarRule logic constructors debug) (before : State)
    (valid : logic.valid before)
    (sound : Sound (ArithmeticShift.meaning other) (logic.read before) reads)
    (operand : OperandRead (Effect State Failure))
    (inputs : ∀ middle, logic.valid middle → UnaryPreservation.Inputs logic reads operand middle)
    (left right : NodeId) (a b : Word) (known : Option Word)
    (lookup : reads.constant left = .ok known)
    (lhs : (logic.read before) left = some a) (rhs : (logic.read before) right = some b) :
    logic.safe (do
      if let some index := known then
        if index.toNat ≥ 31 then return some right
      if let some index := known then
        if let some shift ← readAction (reads.operation right opSHR) then
          if let [amountId, value] := shift.items then
            if let some amount ← readAction (reads.constant amountId) then
              if amount.toNat % 8 = 0 ∧ amount.toNat ≤ 256 ∧ index.toNat ≤ 256 then
                let remaining ← subWord 256 amount
                let endIndex ← addWord index 1
                if remaining.toNat / 8 = endIndex.toNat then
                  return some (← constructors.operation opSAR [← operand shift 0 amountId, ← operand shift 1 value] debug)
      return none) before (fun result after => ∀ id, result = some id → logic.read after id = some (Folding.Op.signextend.value a b 0)) := by
  cases known with
  | none => exact logic.pure before none _ valid (by simp)
  | some index =>
    have same : a = index := Option.some.inj (lhs.symm.trans (sound.constant left index lookup))
    subst a
    by_cases large : 31 ≤ index.toNat
    · simp only [large, ↓reduceIte]
      rw [signextend_large_value index b large]
      exact logic.pure before (some right) _ valid (by intro id equal; cases equal; exact rhs)
    · simp only [large, ↓reduceIte]
      apply signextend_shift_safe logic rules other reads constructors debug sarCorrect before valid sound operand inputs right index b rhs
      exact logic.pure before none _ valid (by simp)

theorem binary_signextend_safe {State Failure Debug : Type} [MonadLift (Except Error) (Effect State Failure)]
    (logic : BuilderLogic (Effect State Failure) State) (rules : ReadRules logic)
    (other : Meaning) (reads : Reads) (constructors : Constructors Debug (Effect State Failure)) (debug : Debug)
    (correct : BuilderRules logic (algebraicBuilder constructors) debug)
    (operation : OperationRule logic constructors debug .signextend)
    (sarCorrect : SarRule logic constructors debug) (before : State)
    (valid : logic.valid before)
    (sound : Sound (ArithmeticShift.meaning other) (logic.read before) reads)
    (operand : OperandRead (Effect State Failure))
    (inputs : ∀ middle, logic.valid middle → UnaryPreservation.Inputs logic reads operand middle)
    (left right : NodeId) (a b : Word) (options : Options) (usizeBits : Nat)
    (lhs : (logic.read before) left = some a) (rhs : (logic.read before) right = some b) :
    logic.safe (binaryStageWithInputs reads constructors usizeBits opSIGNEXTEND left right debug options operand) before
      (fun result after => ∀ id, result = some id → logic.read after id = some (Folding.Op.signextend.value a b 0)) := by
  unfold binaryStageWithInputs
  simp only [opSDIV, opAND, opBYTE, opSLT, opSGT, opXOR, opOR,
    opSIGNEXTEND, opMOD, opSHL, opSHR, opMUL, opDIV, opSUB, Associative.isAssociative,
    Bool.false_eq_true, ↓reduceIte, Bool.false_or, Bool.or_false, Bool.true_or, Bool.or_true,
    List.contains_cons, List.contains_nil, beq_self_eq_true, BitVec.reduceBEq]
  apply rules.bind before _ _ _ valid
  intro lc leftRead
  apply rules.bind before _ _ _ valid
  intro rc rightRead
  have reliable := constant_facts_reliable _ (logic.read before) reads sound left right a b lhs rhs lc rc leftRead rightRead
  split
  next replacement selected =>
    apply algebraic_selected_safe logic (ArithmeticShift.shiftMeaning other) constructors debug correct before valid _ 0 .constants _ left right a b _ lhs rhs reliable replacement selected
    rfl
  next =>
    have tail := signextend_tail_safe logic rules other reads constructors debug sarCorrect before valid sound operand inputs left right a b lc leftRead lhs rhs
    have nested := signextend_nested_safe logic rules (ArithmeticShift.shiftMeaning other) reads constructors debug correct operation before valid sound operand inputs
      left right a b lc leftRead lhs rhs _ tail
    by_cases equal : sameExpression reads left right = true
    · simp only [equal, ↓reduceIte]
      have facts := equal_facts_reliable _ (logic.read before) reads sound left right a b lhs rhs equal
      split
      next replacement selected =>
        apply algebraic_selected_safe logic (ArithmeticShift.shiftMeaning other) constructors debug correct before valid _ 0 .equal _ left right a b _ lhs rhs facts replacement selected
        rfl
      next => cases lc <;> simpa only [pure_bind_effect] using nested
    · simp only [equal, ↓reduceIte]
      cases lc <;> simpa only [pure_bind_effect] using nested

end Preservation

theorem signextend_shift_sub (amount : Word) (bound : amount.toNat ≤ 256) :
    subWord (m := Action) 256 amount = pure (BitVec.ofNat 256 (256 - amount.toNat)) := by
  exact Preservation.signextend_shift_sub amount bound

theorem signextend_index_add (index : Word) (bound : index.toNat ≤ 256) :
    addWord (m := Action) index 1 = pure (BitVec.ofNat 256 (index.toNat + 1)) := by
  exact Preservation.signextend_index_add index bound

theorem signextend_nested_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (known : Option Word) (debug : Debug)
    (lookup : reads.constant left = .ok known)
    (lhs : before.read left = some a) (rhs : before.read right = some b)
    (next : Action (Option NodeId))
    (rest : Safe (Folding.wordMeaning other) next before
      (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.signextend.value a b 0))) :
    Safe (Folding.wordMeaning other) (do
      if let some inner ← readAction (reads.operation right opSIGNEXTEND) then
        if let [index, value] := inner.items then
          if sameExpression reads left index then
            return some (← constructors.operation opSIGNEXTEND [left, value] debug)
          if let some outerByte := known then
            if let some innerByte ← readAction (reads.constant index) then
              return some (← constructors.operation opSIGNEXTEND
                [← constructors.constant (if outerByte.toNat ≤ innerByte.toNat then outerByte else innerByte) debug, value] debug)
      next) before (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.signextend.value a b 0)) := by
  exact Preservation.signextend_nested_safe (Interner.builderLogic (Folding.wordMeaning other))
    (Preservation.logicalReadRules _) other reads constructors debug
    (Preservation.logicalBuilderRules other constructors correct debug)
    (fun ids values value state invariant read evaluated =>
      correct.operation .signextend ids values value debug state invariant read evaluated)
    before valid sound logicalOperand (fun middle invariant => UnaryPreservation.logicalInputs _ reads middle invariant)
    left right a b known lookup lhs rhs next rest

theorem signextend_shift_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (sarCorrect : ArithmeticShift.Constructs other constructors.operation) (before : Heap)
    (valid : Invariant (ArithmeticShift.meaning other) before)
    (sound : Sound (ArithmeticShift.meaning other) before.read reads)
    (right : NodeId) (index value : Word) (debug : Debug)
    (rhs : before.read right = some value) (next : Action (Option NodeId))
    (rest : Safe (ArithmeticShift.meaning other) next before
      (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.signextend.value index value 0))) :
    Safe (ArithmeticShift.meaning other) (do
      if let some shift ← readAction (reads.operation right opSHR) then
        if let [amountId, baseId] := shift.items then
          if let some amount ← readAction (reads.constant amountId) then
            if amount.toNat % 8 = 0 ∧ amount.toNat ≤ 256 ∧ index.toNat ≤ 256 then
              let remaining ← subWord 256 amount
              let endIndex ← addWord index 1
              if remaining.toNat / 8 = endIndex.toNat then
                return some (← constructors.operation opSAR [amountId, baseId] debug)
      next) before (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.signextend.value index value 0)) := by
  exact Preservation.signextend_shift_safe (Interner.builderLogic (ArithmeticShift.meaning other))
    (Preservation.logicalReadRules _) other reads constructors debug
    (fun left right amount value state invariant lhs rhs => sarCorrect left right amount value debug state invariant lhs rhs)
    before valid sound logicalOperand (fun middle invariant => UnaryPreservation.logicalInputs _ reads middle invariant)
    right index value rhs next rest

theorem signextend_tail_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (sarCorrect : ArithmeticShift.Constructs other constructors.operation) (before : Heap)
    (valid : Invariant (ArithmeticShift.meaning other) before)
    (sound : Sound (ArithmeticShift.meaning other) before.read reads)
    (left right : NodeId) (a b : Word) (known : Option Word) (debug : Debug)
    (lookup : reads.constant left = .ok known)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (ArithmeticShift.meaning other) (do
      if let some index := known then
        if index.toNat ≥ 31 then return some right
      if let some index := known then
        if let some shift ← readAction (reads.operation right opSHR) then
          if let [amountId, value] := shift.items then
            if let some amount ← readAction (reads.constant amountId) then
              if amount.toNat % 8 = 0 ∧ amount.toNat ≤ 256 ∧ index.toNat ≤ 256 then
                let remaining ← subWord 256 amount
                let endIndex ← addWord index 1
                if remaining.toNat / 8 = endIndex.toNat then
                  return some (← constructors.operation opSAR [amountId, value] debug)
      return none) before (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.signextend.value a b 0)) := by
  exact Preservation.signextend_tail_safe (Interner.builderLogic (ArithmeticShift.meaning other))
    (Preservation.logicalReadRules _) other reads constructors debug
    (fun left right amount value state invariant lhs rhs => sarCorrect left right amount value debug state invariant lhs rhs)
    before valid sound logicalOperand (fun middle invariant => UnaryPreservation.logicalInputs _ reads middle invariant)
    left right a b known lookup lhs rhs

theorem binary_signextend_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound (ArithmeticShift.shiftMeaning other) constructors)
    (sarCorrect : ArithmeticShift.Constructs other constructors.operation) (before : Heap)
    (valid : Invariant (ArithmeticShift.meaning other) before)
    (sound : Sound (ArithmeticShift.meaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (ArithmeticShift.meaning other) (binaryStage reads constructors usizeBits opSIGNEXTEND left right debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.signextend.value a b 0)) := by
  exact Preservation.binary_signextend_safe (Interner.builderLogic (ArithmeticShift.meaning other))
    (Preservation.logicalReadRules _) other reads constructors debug
    (Preservation.logicalBuilderRules (ArithmeticShift.shiftMeaning other) constructors correct debug)
    (fun ids values value state invariant read evaluated =>
      correct.operation .signextend ids values value debug state invariant read evaluated)
    (fun left right amount value state invariant lhs rhs => sarCorrect left right amount value debug state invariant lhs rhs)
    before valid sound logicalOperand (fun middle invariant => UnaryPreservation.logicalInputs _ reads middle invariant)
    left right a b options usizeBits lhs rhs

theorem binary_signextend_miss (reads : Reads) (constructors : Constructors Debug)
    (left right : NodeId) (debug : Debug) (options : Options) (usizeBits : Nat) :
    MissUnchanged (binaryStage reads constructors usizeBits opSIGNEXTEND left right debug options) := by
  unfold binaryStage binaryStageWithInputs
  simp only [opSDIV, opAND, opBYTE, opSLT, opSGT, opXOR, opOR,
    opSIGNEXTEND, opMOD, opSHL, opSHR, opMUL, opDIV, opSUB, Associative.isAssociative,
    Bool.false_eq_true, ↓reduceIte, Bool.false_or, Bool.or_false, Bool.true_or, Bool.or_true,
    List.contains_cons, List.contains_nil, beq_self_eq_true, BitVec.reduceBEq]
  simp only [addWord, subWord, arithmetic_map_bind, pure_bind_action]
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

theorem signextend_evm_stage (reads : Reads) (constructors : Constructors Debug)
    (arguments : List NodeId) (debug : Debug) (version : Version) (usizeBits : Nat) :
    evmStage reads constructors usizeBits opSIGNEXTEND arguments debug version = pure none := by
  simp only [evmStage, evmStageWithInputs, logicalOperand, opSIGNEXTEND, opBALANCE, opEXP, opMUL, opDIV,
    Bool.false_eq_true, ↓reduceIte, BitVec.reduceBEq]
  repeat first | rfl | split

/-- Complete SIGNEXTEND dispatch with an explicit, independent SAR meaning.
Read coherence and recursive construction remain visible hypotheses. -/
theorem signextend_simplify_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound (ArithmeticShift.shiftMeaning other) constructors)
    (sarCorrect : ArithmeticShift.Constructs other constructors.operation) (before : Heap)
    (valid : Invariant (ArithmeticShift.meaning other) before)
    (sound : Sound (ArithmeticShift.meaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (ArithmeticShift.meaning other) (simplifyWithOptions reads constructors usizeBits opSIGNEXTEND [left, right] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.signextend.value a b 0)) := by
  apply binary_simplify_safe (ArithmeticShift.shiftMeaning other) reads constructors correct before valid sound opSIGNEXTEND left right a b _ 0
    debug options usizeBits lhs rhs rfl
    (binary_signextend_safe other reads constructors correct sarCorrect before valid sound left right a b debug options usizeBits lhs rhs)
    (binary_signextend_miss reads constructors left right debug options usizeBits)
  intro version _
  rw [signextend_evm_stage reads constructors]
  exact Safe.pure _ before none _ valid (by simp)

theorem interner_signextend_simplify_safe (other : Meaning) (pushes : Pushes other) (p : Primitives)
    (contracts : Contracts (ArithmeticShift.meaning other) p) (reads : Reads) (before : Heap)
    (valid : Invariant (ArithmeticShift.meaning other) before)
    (sound : Sound (ArithmeticShift.meaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (ArithmeticShift.meaning other) (simplifyWithOptions reads (implementedConstructors p) usizeBits opSIGNEXTEND [left, right] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.signextend.value a b 0)) :=
  signextend_simplify_safe other reads (implementedConstructors p)
    (implemented_constructors_sound (ArithmeticShift.shiftMeaning other) pushes p contracts)
    (ArithmeticShift.interner_constructs other p contracts) before valid sound
    left right a b debug options usizeBits lhs rhs

end Compiler.Extraction.Dispatch
