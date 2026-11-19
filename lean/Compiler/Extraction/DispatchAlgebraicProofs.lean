/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchUnaryProofs

namespace Compiler.Extraction.Dispatch
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
set_option linter.unusedSimpArgs false

/-- Bridge the table's existing language vocabulary to the independent EVM word
vocabulary. This does not admit any additional native table entries. -/
def binaryWordOp : Binary → Folding.Op
  | .add => .add | .sub => .sub | .mul => .mul | .div => .div | .mod => .mod
  | .and => .and | .or => .or | .xor => .xor | .shl => .shl | .shr => .shr
  | .lt => .lt | .gt => .gt | .eq => .eq

theorem binary_word_opcode (op : Binary) : (binaryWordOp op).opcode = productionOpcode op := by
  cases op <;> rfl

theorem binary_word_eval (op : Binary) (a b : Word) : (binaryWordOp op).eval [a, b] = some (op.eval a b) := by
  cases op <;> rfl

private def buildWordOp : BuildOp → Folding.Op
  | .NOT => .not | .SUB => .sub | .ISZERO => .iszero

private theorem build_word_eval (op : BuildOp) (values : List Word) :
    (buildWordOp op).eval values = op.eval values := by
  cases op <;> cases values with
  | nil => rfl
  | cons a rest =>
    cases rest with
    | nil => rfl
    | cons b tail =>
      cases tail with
      | nil => rfl
      | cons c more => simp [buildWordOp, Folding.Op.eval, Folding.Op.arity, BuildOp.eval]

theorem algebraic_builder_safe (other : Meaning) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) :
    BuilderSafe (Folding.wordMeaning other) (algebraicBuilder constructors) where
  constant := correct.constant
  operation := by
    intro op ids values value debug before valid actual denotation
    have safe := correct.operation (buildWordOp op) ids values value debug before valid actual
      ((build_word_eval op values).trans denotation)
    cases op <;> exact safe

theorem algebraic_apply_safe (other : Meaning) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (replacement : Replacement) (left right : NodeId) (a b : Word) (debug : Debug)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (zigApply replacement (algebraicBuilder constructors) left right debug) before
      (fun id after => after.read id = some (replacement.eval a b)) := by
  rw [zigApply_eq]
  exact replacement_safe_of_builder _ _ (algebraic_builder_safe other constructors correct)
    before valid replacement left right a b debug lhs rhs

theorem constant_some_safe (other : Meaning) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before) (value : Word) (debug : Debug) :
    Safe (Folding.wordMeaning other) (do return some (← constructors.constant value debug)) before
      (fun result after => ∀ id, result = some id → after.read id = some value) := by
  apply Safe.bind _ before _ _ _ _ (correct.constant value debug before valid)
  intro result after validAfter _ resultRead
  exact Safe.pure _ after (some result) _ validAfter (by intro id equal; cases equal; exact resultRead)

namespace Preservation

/-- The constant child returns before the indexed operand initializer runs.
Both effects retain their actual reached states; the final child sees the
new constant and preserved original operand at the end of initialization. -/
theorem constant_left_operation_inputs_safe {State Failure Debug : Type}
    (logic : BuilderLogic (Effect State Failure) State)
    (constructors : Constructors Debug (Effect State Failure)) (debug : Debug)
    (op : Folding.Op) (operation : OperationRule logic constructors debug op)
    (before : State) (constant value expected : Word) (annotation : NodeId)
    (operand : Effect State Failure NodeId)
    (constantSafe : logic.safe (constructors.constant constant debug) before
      (fun id after => logic.read after id = some constant))
    (input : ∀ middle, logic.valid middle → logic.safe operand middle (fun loaded _ => loaded = annotation))
    (actual : logic.read before annotation = some value)
    (evaluated : op.eval [constant, value] = some expected) :
    logic.safe (do return some (← constructors.operation op.opcode
      [← constructors.constant constant debug, ← operand] debug)) before
      (fun result after => ∀ id, result = some id → logic.read after id = some expected) := by
  apply logic.bind before _ _ _ _ constantSafe
  intro constantId middle validMiddle stableConstant constantRead
  apply logic.bind middle _ _ _ _ (input middle validMiddle)
  intro loaded after validAfter stableInput same
  subst loaded
  exact UnaryPreservation.some_safe logic _ after expected
    (operation [constantId, annotation] [constant, value] expected after validAfter
      (by simp [readArguments, stableInput _ _ constantRead, stableInput _ _ (stableConstant _ _ actual)]) evaluated)

end Preservation

/-- Allocate a constant before rebuilding an operation that consumes it. Old
operands remain readable in the intermediate heap, including on failure. -/
theorem constant_left_operation_some_safe (other : Meaning) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (op : Folding.Op) (constant value expected : Word) (operand : NodeId) (debug : Debug)
    (actual : before.read operand = some value) (evaluated : op.eval [constant, value] = some expected) :
    Safe (Folding.wordMeaning other) (do
      return some (← constructors.operation op.opcode [← constructors.constant constant debug, operand] debug)) before
      (fun result after => ∀ id, result = some id → after.read id = some expected) := by
  exact Preservation.constant_left_operation_inputs_safe (Interner.builderLogic (Folding.wordMeaning other))
    constructors debug op
    (fun ids values value state invariant read evaluated =>
      correct.operation op ids values value debug state invariant read evaluated)
    before constant value expected operand (pure operand) (correct.constant constant debug before valid)
    (fun middle invariant => Safe.pure _ middle operand _ invariant rfl) actual evaluated

/-- A selected rule identifies a supported opcode. Unknown opcode bytes cannot
use a table theorem by assuming their denotation equals a known operation. -/
theorem selected_word_value (other : Meaning) (instruction : Opcode) (sequence : BitVec 32)
    (stage : Stage) (facts : Facts) (a b : Word) (reliable : facts.Reliable a b)
    (replacement : Replacement) (selected : zigSelect instruction stage facts = some replacement) :
    (Folding.wordMeaning other).operation instruction sequence [a, b] = some (replacement.eval a b) := by
  classical
  by_cases known : ∃ op, instruction = productionOpcode op
  · obtain ⟨op, rfl⟩ := known
    rw [← binary_word_opcode, Folding.word_meaning_operation, binary_word_eval]
    exact congrArg some (zigSelect_sound op stage facts a b reliable replacement selected)
  · have unknown : ∀ rule ∈ productionRules, productionOpcode rule.op ≠ instruction := by
      intro rule _ equal
      exact known ⟨rule.op, equal.symm⟩
    have absent := zigSelectFrom_unknown productionRules instruction stage facts unknown
    change zigSelect instruction stage facts = none at absent
    rw [absent] at selected
    contradiction

namespace Preservation

/-- Logical and native constructors use the same bridge from the table's
three builder operations to the independent word vocabulary. -/
def builderRules_of_operations {State Failure Debug : Type}
    (logic : BuilderLogic (Effect State Failure) State)
    (constructors : Constructors Debug (Effect State Failure)) (debug : Debug)
    (constant : ∀ value before, logic.valid before →
      logic.safe (constructors.constant value debug) before (fun id after => logic.read after id = some value))
    (operations : ∀ op, OperationRule logic constructors debug op) :
    BuilderRules logic (algebraicBuilder constructors) debug where
  constant := constant
  operation := by
    intro op ids values value before valid actual evaluated
    have checked := operations (buildWordOp op) ids values value before valid actual
      ((build_word_eval op values).trans evaluated)
    cases op <;> exact checked

/-- The logical dispatcher instantiates the shared constructor laws at the
caller's debug value. Native clients use the same laws on reached worlds. -/
def logicalBuilderRules (other : Meaning) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (debug : Debug) :
    BuilderRules (Interner.builderLogic (Folding.wordMeaning other)) (algebraicBuilder constructors) debug :=
  builderRules_of_operations (Interner.builderLogic (Folding.wordMeaning other)) constructors debug
    (fun value before valid => correct.constant value debug before valid)
    (fun op ids values value before valid actual evaluated => correct.operation op ids values value debug before valid actual evaluated)

/-- Both rule tables use the existing denotation bridge and replacement proof.
Sequential children keep their actual reached states and failure policy. -/
theorem algebraic_selected_safe {m : Type → Type} [Monad m] {State Debug : Type}
    (logic : BuilderLogic m State) (other : Meaning) (constructors : Constructors Debug m)
    (debug : Debug) (correct : BuilderRules logic (algebraicBuilder constructors) debug)
    (before : State) (valid : logic.valid before)
    (instruction : Opcode) (sequence : BitVec 32) (stage : Stage) (facts : Facts)
    (left right : NodeId) (a b expected : Word)
    (lhs : logic.read before left = some a) (rhs : logic.read before right = some b)
    (reliable : facts.Reliable a b) (replacement : Replacement)
    (selected : zigSelect instruction stage facts = some replacement)
    (denotation : (Folding.wordMeaning other).operation instruction sequence [a, b] = some expected) :
    logic.safe (do return some (← zigApply replacement (algebraicBuilder constructors) left right debug)) before
      (fun result after => ∀ id, result = some id → logic.read after id = some expected) := by
  have same := Option.some.inj ((selected_word_value other instruction sequence stage facts a b reliable replacement selected).symm.trans denotation)
  rw [← same]
  have built : logic.safe (zigApply replacement (algebraicBuilder constructors) left right debug) before
      (fun id after => logic.read after id = some (replacement.eval a b)) := by
    rw [zigApply_eq]
    exact correct.replacement before valid replacement left right a b lhs rhs
  apply logic.bind before _ _ _ _ built
  intro result after validAfter _ resultRead
  exact logic.pure after (some result) _ validAfter (by intro id equal; cases equal; exact resultRead)

end Preservation

theorem algebraic_selected_safe (other : Meaning) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (instruction : Opcode) (sequence : BitVec 32) (stage : Stage) (facts : Facts)
    (left right : NodeId) (a b expected : Word) (debug : Debug)
    (lhs : before.read left = some a) (rhs : before.read right = some b)
    (reliable : facts.Reliable a b) (replacement : Replacement)
    (selected : zigSelect instruction stage facts = some replacement)
    (denotation : (Folding.wordMeaning other).operation instruction sequence [a, b] = some expected) :
    Safe (Folding.wordMeaning other) (do return some (← zigApply replacement (algebraicBuilder constructors) left right debug)) before
      (fun result after => ∀ id, result = some id → after.read id = some expected) := by
  exact Preservation.algebraic_selected_safe (Interner.builderLogic (Folding.wordMeaning other)) other constructors debug
    (Preservation.logicalBuilderRules other constructors correct debug) before valid instruction sequence stage facts
    left right a b expected lhs rhs reliable replacement selected denotation

theorem constant_facts_reliable (meaning : Meaning) (read : Read) (reads : Reads)
    (sound : Sound meaning read reads) (left right : NodeId) (a b : Word)
    (lhs : read left = some a) (rhs : read right = some b) (lc rc : Option Word)
    (leftRead : reads.constant left = .ok lc) (rightRead : reads.constant right = .ok rc) :
    (Facts.mk lc rc false).Reliable a b where
  left := by
    intro value actual
    change lc = some value at actual
    rw [actual] at leftRead
    exact Option.some.inj (lhs.symm.trans (sound.constant left value leftRead))
  right := by
    intro value actual
    change rc = some value at actual
    rw [actual] at rightRead
    exact Option.some.inj (rhs.symm.trans (sound.constant right value rightRead))
  equal := by simp

theorem equal_facts_reliable (meaning : Meaning) (read : Read) (reads : Reads)
    (sound : Sound meaning read reads) (left right : NodeId) (a b : Word)
    (lhs : read left = some a) (rhs : read right = some b)
    (equal : sameExpression reads left right = true) : (Facts.mk none none true).Reliable a b where
  left := by simp
  right := by simp
  equal := fun _ => sound.equal left right a b equal lhs rhs

end Compiler.Extraction.Dispatch
