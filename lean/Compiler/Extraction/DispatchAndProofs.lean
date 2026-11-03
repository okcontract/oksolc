/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchAssociativeProofs
import Compiler.Extraction.DispatchShiftProofs

namespace Compiler.Extraction.Dispatch
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

private theorem pure_bind_action (value : α) (next : α → Action β) :
    (pure value >>= next) = next value := rfl

theorem signextend_mask_miss (reads : Reads) (constructors : Constructors Debug)
    (left right : NodeId) (debug : Debug) :
    MissUnchanged (SignExtendMask.stripRedundantSignExtendMask reads constructors left right debug) := by
  unfold SignExtendMask.stripRedundantSignExtendMask
  repeat first
    | exact pure_miss_unchanged _
    | exact terminal_miss_unchanged _
    | apply read_miss_unchanged; intro option
    | split
    | apply never_miss_unchanged
      repeat first
        | exact terminal_never_miss _
        | apply bind_never_miss; intro id

theorem covered_mask_miss (reads : Reads) (constructors : Constructors Debug)
    (left right : NodeId) (debug : Debug) :
    MissUnchanged (ShiftMasks.removeCoveredShiftMask reads constructors left right debug) := by
  unfold ShiftMasks.removeCoveredShiftMask
  repeat first
    | exact pure_miss_unchanged _
    | exact terminal_miss_unchanged _
    | apply read_miss_unchanged; intro option
    | split

theorem alternating_search_miss (reads : Reads) (constructors : Constructors Debug)
    (left right : NodeId) (debug : Debug) (choices : List AlternatingMask.Choice) :
    MissUnchanged (AlternatingMask.search reads constructors left right debug choices) := by
  induction choices with
  | nil => exact pure_miss_unchanged none
  | cons choice rest ih =>
    unfold AlternatingMask.search
    apply read_miss_unchanged
    intro option
    cases option
    · exact ih
    · exact terminal_miss_unchanged _

theorem byte_value_mask (index value third : Word) :
    Folding.Op.byte.value index value third &&& 255 = Folding.Op.byte.value index value third := by
  by_cases small : index.toNat < 32 <;> simp [Folding.Op.value, small, BitVec.and_assoc]

theorem byte_mask_candidate_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (known : Option Word) (debug : Debug)
    (lookup : reads.constant right = .ok known)
    (lhs : before.read left = some a) (rhs : before.read right = some b)
    (next : Action (Option NodeId))
    (rest : Safe (Folding.wordMeaning other) next before
      (fun result after => ∀ id, result = some id → after.read id = some (a &&& b))) :
    Safe (Folding.wordMeaning other) (do
      if known == some 255 then
        if let some inner ← readAction (reads.operation left opBYTE) then
          return some (← constructors.borrowedOperation inner.address opBYTE inner.items debug)
      next) before (fun result after => ∀ id, result = some id → after.read id = some (a &&& b)) := by
  by_cases mask : known = some 255
  · simp only [mask, beq_self_eq_true, ↓reduceIte]
    apply read_action_bind_safe _ before _ _ _ valid
    intro option found
    cases option with
    | none => exact rest
    | some slice =>
      obtain ⟨sequence, values, value, arguments, actual, denotation⟩ := sound.operation left opBYTE slice found
      have eval : Folding.Op.byte.eval values = some value := by
        simpa only [show opBYTE = Folding.Op.byte.opcode by rfl, Folding.word_meaning_operation] using denotation
      have masked : value &&& 255 = value := by
        unfold Folding.Op.eval at eval
        split at eval
        next => cases eval; exact byte_value_mask _ _ _
        next => contradiction
      have same : a = value := Option.some.inj (lhs.symm.trans actual)
      have rightSame : b = 255 := Option.some.inj (rhs.symm.trans (sound.constant right 255 (by simpa [mask] using lookup)))
      rw [same, rightSame, masked]
      exact borrowed_operation_some_safe other constructors correct before valid slice.address .byte slice.items values value debug arguments eval
  · have wrong : ¬(known == some 255) = true := by simpa only [beq_iff_eq] using mask
    simpa only [wrong, ↓reduceIte, pure_bind_action] using rest

theorem and_absorption_value (other : Meaning) (read : Read) (reads : Reads)
    (sound : Sound (Folding.wordMeaning other) read reads) (left right result : NodeId) (a b : Word)
    (lhs : read left = some a) (rhs : read right = some b)
    (found : absorbedOccurrence reads left right opOR = .ok (some result)) :
    a &&& b = a ∧ read result = some a := by
  obtain ⟨nestedValue, nestedRead, resultRead, equation⟩ :=
    absorbed_or_sound other read reads sound left right result a lhs found
  have same := Option.some.inj (nestedRead.symm.trans rhs)
  subst nestedValue
  exact ⟨equation, resultRead⟩

theorem and_negation_value (other : Meaning) (read : Read) (reads : Reads)
    (sound : Sound (Folding.wordMeaning other) read reads) (left right : NodeId) (a b : Word)
    (lhs : read left = some a) (rhs : read right = some b)
    (found : isNegation reads left right = .ok true) : a &&& b = 0 := by
  have node := negation_sound other read reads sound left right a lhs found
  have same : b = ~~~a := Option.some.inj (rhs.symm.trans node)
  simp [same]

theorem and_shifts_value (amount a b : Word) :
    Folding.Op.shl.value amount a 0 &&& Folding.Op.shl.value amount b 0 =
      Folding.Op.shl.value amount (a &&& b) 0 := by
  have shl (word : Word) : Folding.Op.shl.value amount word 0 = word <<< amount.toNat :=
    shift_word_value .left amount word
  rw [shl, shl, shl, BitVec.shiftLeft_and_distrib]

theorem merged_shifts_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (do
      if let some lhs ← readAction (reads.operation left opSHL) then
        if let some rhs ← readAction (reads.operation right opSHL) then
          if let [amount, x] := lhs.items then
            if let [otherAmount, y] := rhs.items then
              if sameExpression reads amount otherAmount then
                let combined ← constructors.operation opAND [x, y] debug
                return some (← constructors.operation opSHL [amount, combined] debug)
      return none) before (fun result after => ∀ id, result = some id → after.read id = some (a &&& b)) := by
  apply read_action_bind_safe _ before _ _ _ valid
  intro leftOption leftFound
  cases leftOption with
  | none => exact Safe.pure _ before none _ valid (by simp)
  | some leftSlice =>
    apply read_action_bind_safe _ before _ _ _ valid
    intro rightOption rightFound
    cases rightOption with
    | none => exact Safe.pure _ before none _ valid (by simp)
    | some rightSlice =>
      dsimp only
      split
      next amountId x leftItems =>
        split
        next otherAmountId y rightItems =>
          split
          next equal =>
            obtain ⟨amount, av, amountRead, xRead, leftRead⟩ := binary_values other before.read reads sound .shl
              rfl left amountId x leftSlice leftFound leftItems
            obtain ⟨otherAmount, bv, otherAmountRead, yRead, rightRead⟩ := binary_values other before.read reads sound .shl
              rfl right otherAmountId y rightSlice rightFound rightItems
            have sameAmount := sound.equal amountId otherAmountId amount otherAmount equal amountRead otherAmountRead
            have sameLeft := Option.some.inj (lhs.symm.trans leftRead)
            have sameRight := Option.some.inj (rhs.symm.trans rightRead)
            rw [sameLeft, sameRight, ← sameAmount, and_shifts_value]
            apply Safe.bind _ before _ _ _ _ (correct.operation .and [x, y] [av, bv] (av &&& bv) debug before valid
              (by simp [readArguments, xRead, yRead]) rfl)
            intro combined after validAfter stable combinedRead
            exact operation_some_safe other constructors correct after validAfter .shl [amountId, combined] [amount, av &&& bv]
              _ debug (by simp [readArguments, stable _ _ amountRead, combinedRead]) rfl
          next => exact Safe.pure _ before none _ valid (by simp)
        next => exact Safe.pure _ before none _ valid (by simp)
      next => exact Safe.pure _ before none _ valid (by simp)

theorem address_mask_candidate_safe (env : AddressMask.Environment) (other : Meaning) (reads : Reads)
    (constructors : Constructors Debug) (addressCorrect : AddressMask.Constructs env other constructors.operation)
    (before : Heap) (valid : Invariant (AddressMask.meaning env other) before)
    (sound : Sound (AddressMask.meaning env other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug)
    (lhs : before.read left = some a) (rhs : before.read right = some b)
    (next : Action (Option NodeId))
    (rest : Safe (AddressMask.meaning env other) next before
      (fun result after => ∀ id, result = some id → after.read id = some (a &&& b))) :
    Safe (AddressMask.meaning env other) (do
      if let some opcode ← readAction (AddressMask.addressInstruction reads left right) then
        return some (← constructors.operation opcode [] debug)
      next) before (fun result after => ∀ id, result = some id → after.read id = some (a &&& b)) := by
  apply read_action_bind_safe _ before _ _ _ valid
  intro option found
  cases option with
  | none => exact rest
  | some opcode =>
    obtain ⟨kind, rfl, maskFound, valueFound⟩ := AddressMask.found_sound env other before.read reads sound left right opcode found
    have sameValue : a = kind.value env := Option.some.inj (lhs.symm.trans valueFound)
    have sameMask : b = AddressMask.mask := Option.some.inj (rhs.symm.trans maskFound)
    rw [sameValue, sameMask, (AddressMask.kind_mask env kind).1]
    apply Safe.bind _ before _ _ _ _ (addressCorrect kind debug before valid)
    intro result after validAfter _ resultRead
    exact Safe.pure _ after (some result) _ validAfter (by intro id equal; cases equal; exact resultRead)

private theorem and_optional_pair_safe (meaning : Meaning) (before : Heap) (a b : Word)
    (first second next : Action (Option NodeId))
    (firstSafe : Safe meaning first before (fun result after => ∀ id, result = some id → after.read id = some (a &&& b)))
    (secondSafe : Safe meaning second before (fun result after => ∀ id, result = some id → after.read id = some (b &&& a)))
    (firstMiss : MissUnchanged first) (secondMiss : MissUnchanged second)
    (rest : Safe meaning next before (fun result after => ∀ id, result = some id → after.read id = some (a &&& b))) :
    Safe meaning (do
      if let some id ← first then return some id
      if let some id ← second then return some id
      next) before (fun result after => ∀ id, result = some id → after.read id = some (a &&& b)) := by
  apply optional_bind_safe_of_unchanged _ _ _ before _ firstSafe firstMiss
  · intro id; rfl
  · apply optional_bind_safe_of_unchanged _ _ _ before _
      (by simpa only [BitVec.and_comm b a] using secondSafe) secondMiss
    · intro id; rfl
    · exact rest

theorem and_tail_safe (env : AddressMask.Environment) (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound (AddressMask.addressMeaning env other) constructors)
    (addressCorrect : AddressMask.Constructs env other constructors.operation)
    (before : Heap) (valid : Invariant (AddressMask.meaning env other) before)
    (sound : Sound (AddressMask.meaning env other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (AddressMask.meaning env other) (do
      if (← readAction (absorbedOccurrence reads left right opOR)).isSome then return some left
      if let some id ← readAction (absorbedOccurrence reads right left opOR) then return some id
      if (← readAction (isNegation reads left right)) then return some (← constructors.constant 0 debug)
      if (← readAction (isNegation reads right left)) then return some (← constructors.constant 0 debug)
      if let some id ← dropRepeatedLocal reads constructors.localOperation opAND left right false debug then return some id
      if let some id ← dropRepeatedLocal reads constructors.localOperation opAND right left true debug then return some id
      if let some id ← SignExtendMask.stripRedundantSignExtendMask reads constructors left right debug then return some id
      if let some id ← SignExtendMask.stripRedundantSignExtendMask reads constructors right left debug then return some id
      if let some opcode ← readAction (AddressMask.addressInstruction reads left right) then
        return some (← constructors.operation opcode [] debug)
      if let some opcode ← readAction (AddressMask.addressInstruction reads right left) then
        return some (← constructors.operation opcode [] debug)
      if let some id ← reassociate reads constructors opAND left right false debug then return some id
      if let some id ← reassociate reads constructors opAND right left true debug then return some id
      if let some id ← AlternatingMask.distributeAlternatingMask reads constructors left right debug then return some id
      if let some id ← ShiftMasks.removeCoveredShiftMask reads constructors left right debug then return some id
      if let some id ← ShiftMasks.removeCoveredShiftMask reads constructors right left debug then return some id
      if let some lhs ← readAction (reads.operation left opSHL) then
        if let some rhs ← readAction (reads.operation right opSHL) then
          if let [amount, x] := lhs.items then
            if let [otherAmount, y] := rhs.items then
              if sameExpression reads amount otherAmount then
                let combined ← constructors.operation opAND [x, y] debug
                return some (← constructors.operation opSHL [amount, combined] debug)
      return none) before (fun result after => ∀ id, result = some id → after.read id = some (a &&& b)) := by
  let words := AddressMask.addressMeaning env other
  apply read_action_bind_safe _ before _ _ _ valid
  intro option found
  cases option with
  | some id =>
    obtain ⟨value, _⟩ := and_absorption_value words before.read reads sound left right id a b lhs rhs found
    exact Safe.pure _ before (some left) _ valid (by intro result equal; cases equal; simpa [value] using lhs)
  | none =>
    apply read_action_bind_safe _ before _ _ _ valid
    intro option found
    cases option with
    | some id =>
      obtain ⟨value, resultRead⟩ := and_absorption_value words before.read reads sound right left id b a rhs lhs found
      exact Safe.pure _ before (some id) _ valid (by
        intro result equal; cases equal
        simpa [BitVec.and_comm a b, value] using resultRead)
    | none =>
      apply read_action_bind_safe _ before _ _ _ valid
      intro negated found
      cases negated with
      | true =>
        rw [and_negation_value words before.read reads sound left right a b lhs rhs found]
        exact constant_some_safe words constructors correct before valid 0 debug
      | false =>
        apply read_action_bind_safe _ before _ _ _ valid
        intro negated found
        cases negated with
        | true =>
          rw [BitVec.and_comm a b, and_negation_value words before.read reads sound right left b a rhs lhs found]
          exact constant_some_safe words constructors correct before valid 0 debug
        | false =>
          apply repeated_pair_safe words reads constructors correct before valid sound .and (Or.inl rfl) left right a b debug lhs rhs
          apply and_optional_pair_safe _ before a b _ _ _
            (SignExtendMask.strip_safe words reads constructors correct before valid sound left right a b debug lhs rhs)
            (SignExtendMask.strip_safe words reads constructors correct before valid sound right left b a debug rhs lhs)
            (signextend_mask_miss reads constructors left right debug) (signextend_mask_miss reads constructors right left debug)
          apply address_mask_candidate_safe env other reads constructors addressCorrect before valid sound left right a b debug lhs rhs
          rw [BitVec.and_comm a b]
          apply address_mask_candidate_safe env other reads constructors addressCorrect before valid sound right left b a debug rhs lhs
          rw [BitVec.and_comm b a]
          apply reassociation_pair_safe words reads constructors correct before valid sound .and
            (Or.inr (Or.inr (Or.inl rfl))) left right a b debug lhs rhs
          apply optional_bind_safe_of_unchanged _ _ _ before _
            (AlternatingMask.distribute_safe words reads constructors correct before valid sound left right a b lhs rhs debug)
            (alternating_search_miss reads constructors left right debug AlternatingMask.choices)
          · intro id; rfl
          · apply and_optional_pair_safe _ before a b _ _ _
              (ShiftMasks.remove_mask_safe words reads constructors correct.borrowedOperation before valid sound left right a b debug lhs rhs)
              (ShiftMasks.remove_mask_safe words reads constructors correct.borrowedOperation before valid sound right left b a debug rhs lhs)
              (covered_mask_miss reads constructors left right debug) (covered_mask_miss reads constructors right left debug)
            exact merged_shifts_safe words reads constructors correct before valid sound left right a b debug lhs rhs

theorem binary_and_safe (env : AddressMask.Environment) (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound (AddressMask.addressMeaning env other) constructors)
    (addressCorrect : AddressMask.Constructs env other constructors.operation)
    (before : Heap) (valid : Invariant (AddressMask.meaning env other) before)
    (sound : Sound (AddressMask.meaning env other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (AddressMask.meaning env other) (binaryStage reads constructors usizeBits opAND left right debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (a &&& b)) := by
  let words := AddressMask.addressMeaning env other
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
    apply algebraic_selected_safe words constructors correct before valid _ 0 .constants _ left right a b _ debug lhs rhs reliable replacement selected
    rfl
  next =>
    apply byte_mask_candidate_safe words reads constructors correct before valid sound left right a b rc debug rightRead lhs rhs
    have tail := and_tail_safe env other reads constructors correct addressCorrect before valid sound left right a b debug lhs rhs
    by_cases equal : sameExpression reads left right = true
    · simp only [equal, ↓reduceIte]
      have facts := equal_facts_reliable _ before.read reads sound left right a b lhs rhs equal
      split
      next replacement selected =>
        apply algebraic_selected_safe words constructors correct before valid _ 0 .equal _ left right a b _ debug lhs rhs facts replacement selected
        rfl
      next => simpa only [pure_bind_action] using tail
    · simpa only [equal, Bool.false_eq_true, ↓reduceIte, pure_bind_action] using tail

theorem binary_and_miss (reads : Reads) (constructors : Constructors Debug)
    (left right : NodeId) (debug : Debug) (options : Options) (usizeBits : Nat) :
    MissUnchanged (binaryStage reads constructors usizeBits opAND left right debug options) := by
  unfold binaryStage binaryStageWithInputs
  simp only [opSDIV, opAND, opBYTE, opSLT, opSGT, opXOR, opOR,
    opSIGNEXTEND, opMOD, opSHL, opSHR, opMUL, opDIV, opSUB, Associative.isAssociative,
    Bool.false_eq_true, ↓reduceIte, Bool.false_or, Bool.or_false, Bool.true_or, Bool.or_true,
    List.contains_cons, List.contains_nil, beq_self_eq_true, BitVec.reduceBEq]
  have mask (a b : NodeId) : SignExtendMask.stripRedundantSignExtendMaskWithInputs reads constructors a b debug =
      SignExtendMask.stripRedundantSignExtendMask reads constructors a b debug := rfl
  have alternating : AlternatingMask.distributeAlternatingMaskWithInputs reads constructors left right debug =
      AlternatingMask.distributeAlternatingMask reads constructors left right debug := rfl
  simp only [mask, alternating, logicalOperand, pure_bind_action]
  repeat first
    | exact pure_miss_unchanged _
    | exact terminal_miss_unchanged _
    | apply read_miss_unchanged; intro option
    | apply optional_bind_miss_unchanged _ _ (repeated_miss _ _ _ _ _ _ _) (by intro id; rfl)
    | apply optional_bind_miss_unchanged _ _ (signextend_mask_miss _ _ _ _ _) (by intro id; rfl)
    | apply optional_bind_miss_unchanged _ _ (reassociate_miss _ _ _ _ _ _ _) (by intro id; rfl)
    | apply optional_bind_miss_unchanged _ _ (alternating_search_miss _ _ _ _ _ _) (by intro id; rfl)
    | apply optional_bind_miss_unchanged _ _ (covered_mask_miss _ _ _ _ _) (by intro id; rfl)
    | split
    | apply never_miss_unchanged
      repeat first
        | exact terminal_never_miss _
        | apply bind_never_miss; intro id

theorem and_evm_stage (reads : Reads) (constructors : Constructors Debug)
    (arguments : List NodeId) (debug : Debug) (version : Version) (usizeBits : Nat) :
    evmStage reads constructors usizeBits opAND arguments debug version = pure none := by
  simp only [evmStage, evmStageWithInputs, logicalOperand, opAND, opBALANCE, opEXP, opMUL, opDIV,
    Bool.false_eq_true, ↓reduceIte, BitVec.reduceBEq]
  repeat first | rfl | split

/-- Complete ordered AND dispatch, including its fixed-frame address cases. -/
theorem and_simplify_safe (env : AddressMask.Environment) (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound (AddressMask.addressMeaning env other) constructors)
    (addressCorrect : AddressMask.Constructs env other constructors.operation)
    (before : Heap) (valid : Invariant (AddressMask.meaning env other) before)
    (sound : Sound (AddressMask.meaning env other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (AddressMask.meaning env other) (simplifyWithOptions reads constructors usizeBits opAND [left, right] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (a &&& b)) := by
  apply binary_simplify_safe (AddressMask.addressMeaning env other) reads constructors correct before valid sound opAND left right a b _ 0
    debug options usizeBits lhs rhs rfl
    (binary_and_safe env other reads constructors correct addressCorrect before valid sound left right a b debug options usizeBits lhs rhs)
    (binary_and_miss reads constructors left right debug options usizeBits)
  intro version _
  rw [and_evm_stage reads constructors]
  exact Safe.pure _ before none _ valid (by simp)

theorem interner_and_simplify_safe (env : AddressMask.Environment) (other : Meaning) (pushes : Pushes other) (p : Primitives)
    (contracts : Contracts (AddressMask.meaning env other) p) (reads : Reads) (before : Heap)
    (valid : Invariant (AddressMask.meaning env other) before)
    (sound : Sound (AddressMask.meaning env other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (AddressMask.meaning env other) (simplifyWithOptions reads (implementedConstructors p) usizeBits opAND [left, right] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (a &&& b)) :=
  and_simplify_safe env other reads (implementedConstructors p)
    (implemented_constructors_sound (AddressMask.addressMeaning env other) pushes p contracts)
    (AddressMask.interner_constructs env other p contracts) before valid sound
    left right a b debug options usizeBits lhs rhs

end Compiler.Extraction.Dispatch
