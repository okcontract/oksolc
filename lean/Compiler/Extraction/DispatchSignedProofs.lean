/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchAlgebraicProofs

namespace Compiler.Extraction.Dispatch
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096

theorem signed_division_zero_right (a : Word) : Folding.Op.sdiv.value a 0 0 = 0 := by
  simp [Folding.Op.value]

theorem signed_division_zero_left (b : Word) : Folding.Op.sdiv.value 0 b 0 = 0 := by
  simp [Folding.Op.value]

theorem signed_division_one (a : Word) : Folding.Op.sdiv.value a 1 0 = a := by
  simp [Folding.Op.value]

/-- The inline signed-division cases precede semantic-equality matching. The
fallback is entered only after both constant tests miss. -/
theorem signed_division_inline_safe (other : Meaning) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before) (left : NodeId) (a b : Word)
    (lc rc : Option Word) (reliable : (Facts.mk lc rc false).Reliable a b)
    (lhs : before.read left = some a) (debug : Debug) (next : Action (Option NodeId))
    (rest : Safe (Folding.wordMeaning other) next before
      (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.sdiv.value a b 0))) :
    Safe (Folding.wordMeaning other) (do
      if rc == some 0 || lc == some 0 then return some (← constructors.constant 0 debug)
      if rc == some 1 then return some left
      next) before
      (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.sdiv.value a b 0)) := by
  by_cases zero : (rc == some 0 || lc == some 0) = true
  · simp only [zero, ↓reduceIte]
    have zeroValue : Folding.Op.sdiv.value a b 0 = 0 := by
      simp only [Bool.or_eq_true, beq_iff_eq] at zero
      rcases zero with right | left
      · rw [reliable.right 0 right, signed_division_zero_right]
      · rw [reliable.left 0 left, signed_division_zero_left]
    rw [zeroValue]
    exact constant_some_safe other constructors correct before valid 0 debug
  · simp only [zero, ↓reduceIte]
    by_cases one : (rc == some 1) = true
    · simp only [one, ↓reduceIte]
      have same : b = 1 := reliable.right 1 (by simpa using one)
      rw [same, signed_division_one]
      exact Safe.pure _ before (some left) _ valid (by intro id equal; cases equal; exact lhs)
    · simpa only [one, ↓reduceIte] using rest

def SignedArithmetic (op : Folding.Op) : Prop := op = .sdiv ∨ op = .smod

theorem binary_signed_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (op : Folding.Op) (signed : SignedArithmetic op) (left right : NodeId) (a b : Word)
    (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (binaryStage reads constructors usizeBits op.opcode left right debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (op.value a b 0)) := by
  rcases signed with rfl | rfl
  all_goals
    unfold binaryStage binaryStageWithInputs
    simp only [Folding.Op.opcode, opSDIV, opAND, opBYTE, opSLT, opSGT, opXOR, opOR,
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
      try apply signed_division_inline_safe other constructors correct before valid left a b lc rc reliable lhs debug
      split
      next equal =>
        have facts := equal_facts_reliable _ before.read reads sound left right a b lhs rhs equal
        split
        next replacement selected =>
          apply algebraic_selected_safe other constructors correct before valid _ 0 .equal _ left right a b _ debug lhs rhs facts replacement selected
          rfl
        next => exact Safe.pure _ before none _ valid (by simp)
      next => exact Safe.pure _ before none _ valid (by simp)

theorem binary_signed_miss (reads : Reads) (constructors : Constructors Debug)
    (op : Folding.Op) (signed : SignedArithmetic op) (left right : NodeId)
    (debug : Debug) (options : Options) (usizeBits : Nat) :
    MissUnchanged (binaryStage reads constructors usizeBits op.opcode left right debug options) := by
  rcases signed with rfl | rfl
  all_goals
    unfold binaryStage binaryStageWithInputs
    simp only [Folding.Op.opcode, opSDIV, opAND, opBYTE, opSLT, opSGT, opXOR, opOR,
      opSIGNEXTEND, opMOD, opSHL, opSHR, opMUL, opDIV, opSUB, Associative.isAssociative,
      Bool.false_eq_true, ↓reduceIte, Bool.false_or, Bool.or_false, Bool.true_or, Bool.or_true,
      List.contains_cons, List.contains_nil, beq_self_eq_true, BitVec.reduceBEq]
    repeat first
      | exact pure_miss_unchanged _
      | exact terminal_miss_unchanged _
      | apply read_miss_unchanged; intro option
      | split

theorem signed_evm_stage (reads : Reads) (constructors : Constructors Debug)
    (op : Folding.Op) (signed : SignedArithmetic op) (arguments : List NodeId)
    (debug : Debug) (version : Version) (usizeBits : Nat) :
    evmStage reads constructors usizeBits op.opcode arguments debug version = pure none := by
  rcases signed with rfl | rfl
  all_goals
    simp only [evmStage, evmStageWithInputs, logicalOperand, Folding.Op.opcode, opBALANCE, opEXP, opMUL, opDIV,
      Bool.false_eq_true, ↓reduceIte, BitVec.reduceBEq]
    repeat first | rfl | split

/-- SDIV and SMOD compose every dispatcher stage, including constant-folding
priority and all dialect/revision options. The fallible constructor contract
remains explicit; SMOD has no additional inline rewrite after table selection. -/
theorem signed_simplify_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (op : Folding.Op) (signed : SignedArithmetic op) (left right : NodeId) (a b : Word)
    (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (simplifyWithOptions reads constructors usizeBits op.opcode [left, right] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (op.value a b 0)) := by
  have denotation : (Folding.wordMeaning other).operation op.opcode 0 [a, b] = some (op.value a b 0) := by
    rw [Folding.word_meaning_operation]
    rcases signed with rfl | rfl <;> rfl
  apply binary_simplify_safe other reads constructors correct before valid sound op.opcode left right a b _ 0
    debug options usizeBits lhs rhs denotation
    (binary_signed_safe other reads constructors correct before valid sound op signed left right a b debug options usizeBits lhs rhs)
    (binary_signed_miss reads constructors op signed left right debug options usizeBits)
  intro version _
  rw [signed_evm_stage reads constructors op signed]
  exact Safe.pure _ before none _ valid (by simp)

theorem interner_signed_simplify_safe (other : Meaning) (pushes : Pushes other) (p : Primitives)
    (contracts : Contracts (Folding.wordMeaning other) p) (reads : Reads) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (op : Folding.Op) (signed : SignedArithmetic op) (left right : NodeId) (a b : Word)
    (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (simplifyWithOptions reads (implementedConstructors p) usizeBits op.opcode [left, right] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (op.value a b 0)) :=
  signed_simplify_safe other reads (implementedConstructors p)
    (implemented_constructors_sound other pushes p contracts) before valid sound
    op signed left right a b debug options usizeBits lhs rhs

end Compiler.Extraction.Dispatch
