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

theorem shr_tail_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
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
        if let some inner ← readAction (reads.operation right opSHR) then
          if let [index, value] := inner.items then
            if let some innerShift ← readAction (reads.constant index) then
              if outerShift.toNat ≥ 256 - min innerShift.toNat 256 then
                return some (← constructors.constant 0 debug)
              return some (← constructors.operation opSHR
                [← constructors.constant (← addWord outerShift innerShift) debug, value] debug)
        let opposite := if opSHR == opSHL then opSHR else opSHL
        if let some inner ← readAction (reads.operation right opposite) then
          if let [index, value] := inner.items then
            if let some innerShift ← readAction (reads.constant index) then
              if outerShift.toNat < 256 ∧ innerShift.toNat < 256 then
                return some (← OppositeShifts.combineOppositeShifts constructors opSHR outerShift innerShift value debug)
        if let some inner ← readAction (reads.operation right opAND) then
          if inner.items.length == 2 then
            if let some masked ← readAction (splitConstant reads inner.items) then
              if outerShift.toNat < 256 then
                let shift ← arithmetic (Folding.Zig.narrow 8 outerShift.toNat)
                let mask := if opSHR == opSHL then masked.value <<< shift else masked.value >>> shift
                let shifted ← constructors.operation opSHR [left, masked.expression] debug
                return some (← constructors.operation opAND [shifted, ← constructors.constant mask debug] debug)
      return none) before (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.shr.value a b 0)) := by
  cases known with
  | none => exact Safe.pure _ before none _ valid (by simp)
  | some amount =>
    have same : a = amount := Option.some.inj (lhs.symm.trans (sound.constant left amount lookup))
    subst a
    by_cases large : 256 ≤ amount.toNat
    · simp only [large, ↓reduceIte]
      have zero : Folding.Op.shr.value amount b 0 = 0 := shift_large_value .right amount b large
      rw [zero]
      exact constant_some_safe other constructors correct before valid 0 debug
    · simp only [large, ↓reduceIte]
      apply same_shift_candidate_safe other reads constructors correct before valid sound .right right amount b debug rhs
      apply opposite_shift_candidate_safe other reads constructors correct before valid sound .right right amount b debug rhs
      apply masked_shift_candidate_safe other reads constructors correct before valid sound .right left right amount b debug lhs rhs
      exact Safe.pure _ before none _ valid (by simp)

theorem binary_shr_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (binaryStage reads constructors usizeBits opSHR left right debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.shr.value a b 0)) := by
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
    have tail := shr_tail_safe other reads constructors correct before valid sound left right a b lc debug leftRead lhs rhs
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

theorem binary_shr_miss (reads : Reads) (constructors : Constructors Debug)
    (left right : NodeId) (debug : Debug) (options : Options) (usizeBits : Nat) :
    MissUnchanged (binaryStage reads constructors usizeBits opSHR left right debug options) := by
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

theorem shr_evm_stage (reads : Reads) (constructors : Constructors Debug)
    (arguments : List NodeId) (debug : Debug) (version : Version) (usizeBits : Nat) :
    evmStage reads constructors usizeBits opSHR arguments debug version = pure none := by
  simp only [evmStage, evmStageWithInputs, logicalOperand, opSHR, opBALANCE, opEXP, opMUL, opDIV,
    Bool.false_eq_true, ↓reduceIte, BitVec.reduceBEq]
  repeat first | rfl | split

/-- Complete SHR dispatch: constant folding and tables, large shifts, nested
same/opposite shifts and mask distribution, with actual failure states. -/
theorem shr_simplify_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (simplifyWithOptions reads constructors usizeBits opSHR [left, right] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.shr.value a b 0)) := by
  apply binary_simplify_safe other reads constructors correct before valid sound opSHR left right a b _ 0
    debug options usizeBits lhs rhs rfl
    (binary_shr_safe other reads constructors correct before valid sound left right a b debug options usizeBits lhs rhs)
    (binary_shr_miss reads constructors left right debug options usizeBits)
  intro version _
  rw [shr_evm_stage reads constructors]
  exact Safe.pure _ before none _ valid (by simp)

theorem interner_shr_simplify_safe (other : Meaning) (pushes : Pushes other) (p : Primitives)
    (contracts : Contracts (Folding.wordMeaning other) p) (reads : Reads) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (simplifyWithOptions reads (implementedConstructors p) usizeBits opSHR [left, right] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.shr.value a b 0)) :=
  shr_simplify_safe other reads (implementedConstructors p)
    (implemented_constructors_sound other pushes p contracts) before valid sound
    left right a b debug options usizeBits lhs rhs

end Compiler.Extraction.Dispatch
