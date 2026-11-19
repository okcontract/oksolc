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

namespace Preservation

/-- All five comparisons use the complete extracted binary stage, including
constant-table priority, operand equality, signed-comparison fallback and errors.
No independent reimplementation of the selected path is used. -/
theorem binary_comparison_safe {State Failure Debug : Type} [MonadLift (Except Error) (Effect State Failure)]
    (logic : BuilderLogic (Effect State Failure) State) (rules : ReadRules logic)
    (other : Meaning) (reads : Reads) (constructors : Constructors Debug (Effect State Failure))
    (debug : Debug) (correct : BuilderRules logic (algebraicBuilder constructors) debug)
    (before : State) (valid : logic.valid before)
    (sound : Sound (Folding.wordMeaning other) (logic.read before) reads)
    (op : Folding.Op) (comparison : BooleanOperation op) (left right : NodeId) (a b : Word)
    (options : Options) (usizeBits : Nat) (operand : OperandRead (Effect State Failure))
    (lhs : (logic.read before) left = some a) (rhs : (logic.read before) right = some b) :
    logic.safe (binaryStageWithInputs reads constructors usizeBits op.opcode left right debug options operand) before
      (fun result after => ∀ id, result = some id → logic.read after id = some (op.value a b 0)) := by
  rcases comparison with rfl | rfl | rfl | rfl | rfl
  all_goals
    unfold binaryStageWithInputs
    simp only [Folding.Op.opcode, opSDIV, opAND, opBYTE, opSLT, opSGT, opXOR, opOR,
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
      apply algebraic_selected_safe logic other constructors debug correct before valid _ 0 .constants _ left right a b _ lhs rhs reliable replacement selected
      rfl
    next =>
      split
      next equal =>
        have facts := equal_facts_reliable _ (logic.read before) reads sound left right a b lhs rhs equal
        split
        next replacement selected =>
          apply algebraic_selected_safe logic other constructors debug correct before valid _ 0 .equal _ left right a b _ lhs rhs facts replacement selected
          rfl
        next =>
          first
          | exact logic.pure before none _ valid (by simp)
          | have same := sound.equal left right a b equal lhs rhs
            subst b
            simp only [Folding.Op.value, Int.lt_irrefl, ↓reduceIte]
            apply logic.bind before _ _ _ _ (correct.constant 0 before valid)
            intro result after validAfter _ resultRead
            exact logic.pure after (some result) _ validAfter (by intro id equation; cases equation; exact resultRead)
      next => exact logic.pure before none _ valid (by simp)

end Preservation

theorem binary_comparison_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (op : Folding.Op) (comparison : BooleanOperation op) (left right : NodeId) (a b : Word)
    (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (binaryStage reads constructors usizeBits op.opcode left right debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (op.value a b 0)) := by
  exact Preservation.binary_comparison_safe (Interner.builderLogic (Folding.wordMeaning other))
    (Preservation.logicalReadRules _) other reads constructors debug
    (Preservation.logicalBuilderRules other constructors correct debug) before valid sound op comparison
    left right a b options usizeBits logicalOperand lhs rhs

theorem binary_comparison_miss (reads : Reads) (constructors : Constructors Debug)
    (op : Folding.Op) (comparison : BooleanOperation op) (left right : NodeId)
    (debug : Debug) (options : Options) (usizeBits : Nat) :
    MissUnchanged (binaryStage reads constructors usizeBits op.opcode left right debug options) := by
  rcases comparison with rfl | rfl | rfl | rfl | rfl
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

theorem comparison_evm_stage (reads : Reads) (constructors : Constructors Debug)
    (op : Folding.Op) (comparison : BooleanOperation op) (arguments : List NodeId)
    (debug : Debug) (version : Version) (usizeBits : Nat) :
    evmStage reads constructors usizeBits op.opcode arguments debug version = pure none := by
  rcases comparison with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [evmStage, evmStageWithInputs, logicalOperand, Folding.Op.opcode, opBALANCE, opEXP, opMUL, opDIV,
      Bool.false_eq_true, ↓reduceIte, BitVec.reduceBEq]
    repeat first | rfl | split

/-- All comparison words are independent of the expression sequence tag. -/
theorem comparison_word_value (other : Meaning) (op : Folding.Op) (comparison : BooleanOperation op)
    (sequence : BitVec 32) (a b : Word) :
    (Folding.wordMeaning other).operation op.opcode sequence [a, b] = some (op.value a b 0) := by
  rw [Folding.word_meaning_operation]
  rcases comparison with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- For comparison inputs this composes every native dispatcher stage, including
constant-folding priority and every dialect/revision option. Constructors retain
their explicit recursive preservation contract. -/
theorem comparison_simplify_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (op : Folding.Op) (comparison : BooleanOperation op) (left right : NodeId) (a b : Word)
    (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (simplifyWithOptions reads constructors usizeBits op.opcode [left, right] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (op.value a b 0)) := by
  have denotation : (Folding.wordMeaning other).operation op.opcode 0 [a, b] = some (op.value a b 0) := by
    exact comparison_word_value other op comparison 0 a b
  apply binary_simplify_safe other reads constructors correct before valid sound op.opcode left right a b _ 0
    debug options usizeBits lhs rhs denotation
    (binary_comparison_safe other reads constructors correct before valid sound op comparison left right a b debug options usizeBits lhs rhs)
    (binary_comparison_miss reads constructors op comparison left right debug options usizeBits)
  intro version _
  rw [comparison_evm_stage reads constructors op comparison]
  exact Safe.pure _ before none _ valid (by simp)

theorem interner_comparison_simplify_safe (other : Meaning) (pushes : Pushes other) (p : Primitives)
    (contracts : Contracts (Folding.wordMeaning other) p) (reads : Reads) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (op : Folding.Op) (comparison : BooleanOperation op) (left right : NodeId) (a b : Word)
    (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (simplifyWithOptions reads (implementedConstructors p) usizeBits op.opcode [left, right] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (op.value a b 0)) :=
  comparison_simplify_safe other reads (implementedConstructors p)
    (implemented_constructors_sound other pushes p contracts) before valid sound
    op comparison left right a b debug options usizeBits lhs rhs

end Compiler.Extraction.Dispatch
