/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.DispatchProofs

namespace Compiler.Extraction.Dispatch
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
set_option linter.unusedSimpArgs false

theorem triple_iszero (value : Word) :
    Unary.iszero.eval (Unary.iszero.eval (Unary.iszero.eval value)) = Unary.iszero.eval value := by
  by_cases zero : value = 0 <;> simp [Unary.eval, boolWord, zero]

def BooleanOperation (op : Folding.Op) : Prop :=
  op = .eq ∨ op = .lt ∨ op = .slt ∨ op = .gt ∨ op = .sgt

theorem boolean_double_iszero (op : Folding.Op) (boolean : BooleanOperation op)
    (values : List Word) (value : Word) (evaluated : op.eval values = some value) :
    op.eval values = some (Unary.iszero.eval (Unary.iszero.eval value)) := by
  have result : value = 0 ∨ value = 1 := by
    unfold Folding.Op.eval at evaluated
    split at evaluated
    · have same := Option.some.inj evaluated
      subst value
      rcases boolean with rfl | rfl | rfl | rfl | rfl <;>
        simp only [Folding.Op.value, Binary.eval, boolWord] <;> split <;> simp
    · contradiction
  rcases result with rfl | rfl <;> simpa [Unary.eval, boolWord] using evaluated

theorem equality_of_zero_test (op : Folding.Op) (supported : op = .xor ∨ op = .sub)
    (values : List Word) (value : Word) (evaluated : op.eval values = some value) :
    Folding.Op.eq.eval values = some (Unary.iszero.eval value) := by
  have law (a b : Word) : Unary.iszero.eval (op.value a b 0) = Folding.Op.eq.value a b 0 := by
    rcases supported with rfl | rfl
    · simp [Folding.Op.value, Binary.eval, Unary.eval, boolWord, BitVec.xor_eq_zero_iff]
    · simp [Folding.Op.value, Binary.eval, Unary.eval, boolWord, BitVec.sub_eq_iff_eq_add]
  have arity : op.arity = 2 := by rcases supported with rfl | rfl <;> rfl
  unfold Folding.Op.eval at evaluated
  split at evaluated
  · have same := Option.some.inj evaluated
    subst value
    have third : op.value (values[0]?.getD 0) (values[1]?.getD 0) (values[2]?.getD 0) =
        op.value (values[0]?.getD 0) (values[1]?.getD 0) 0 := by
      rcases supported with rfl | rfl <;> rfl
    rw [third, law]
    have length : values.length = 2 := by simpa [arity] using (‹values.length = op.arity›)
    simp [Folding.Op.eval, Folding.Op.arity, length, Folding.Op.value, Binary.eval]
  · contradiction

namespace UnaryPreservation
open Preservation
variable {State Failure Debug : Type} [MonadLift (Except Error) (Effect State Failure)]

/-- Borrowed calls are required only for actual query-returned slices. Both
routes use the caller's debug and valid reached states. -/
structure Children (logic : BuilderLogic (Effect State Failure) State) (reads : Reads)
    (constructors : Constructors Debug (Effect State Failure)) (debug : Debug) : Prop where
  operation : ∀ (op : Folding.Op) ids values value before, logic.valid before →
    readArguments (logic.read before) ids = some values → op.eval values = some value →
    logic.safe (constructors.operation op.opcode ids debug) before
      (fun id after => logic.read after id = some value)
  borrowed : ∀ id queried source, reads.operation id queried = .ok (some source) →
    ∀ (op : Folding.Op) values value before, logic.valid before →
    readArguments (logic.read before) source.items = some values → op.eval values = some value →
    logic.safe (constructors.borrowedOperation source.address op.opcode source.items debug) before
      (fun result after => logic.read after result = some value)

/-- The unary initializer loads only a queried slice at its actual index. The
read may have effects, but must retain the state invariant and old word reads. -/
def Inputs (logic : BuilderLogic (Effect State Failure) State) (reads : Reads) (operand : OperandRead (Effect State Failure)) (before : State) : Prop :=
  ∀ id opcode source, reads.operation id opcode = .ok (some source) →
    ∀ index annotation, source.items[index]? = some annotation →
    logic.safe (operand source index annotation) before (fun loaded _ => loaded = annotation)

omit [MonadLift (Except Error) (Effect State Failure)] in
theorem some_safe (logic : BuilderLogic (Effect State Failure) State) (action : (Effect State Failure) NodeId) (before : State) (value : Word)
    (checked : logic.safe action before (fun id after => logic.read after id = some value)) :
    logic.safe (do return some (← action)) before
      (fun result after => ∀ id, result = some id → logic.read after id = some value) := by
  apply logic.bind before _ _ _ _ checked
  intro result after valid _ actual
  exact logic.pure after (some result) _ valid (by intro id same; cases same; exact actual)

theorem operation_probe_safe (logic : BuilderLogic (Effect State Failure) State) (rules : ReadRules logic)
    (other : Meaning) (reads : Reads) (constructors : Constructors Debug (Effect State Failure)) (debug : Debug)
    (correct : Children logic reads constructors debug) (before : State) (valid : logic.valid before)
    (sound : Sound (Folding.wordMeaning other) (logic.read before) reads)
    (source target : Folding.Op) (transform : Word → Word)
    (law : ∀ values value, source.eval values = some value → target.eval values = some (transform value))
    (operand : NodeId) (value : Word) (actual : logic.read before operand = some value)
    (next : (Effect State Failure) (Option NodeId))
    (rest : logic.safe next before (fun result after => ∀ id, result = some id → logic.read after id = some (transform value))) :
    logic.safe (do
      if let some inner ← readAction (reads.operation operand source.opcode) then
        return some (← constructors.borrowedOperation inner.address target.opcode inner.items debug)
      next) before (fun result after => ∀ id, result = some id → logic.read after id = some (transform value)) := by
  apply rules.bind before _ _ _ valid
  intro option lookup
  cases option with
  | none => exact rest
  | some slice =>
    obtain ⟨values, word, arguments, node, evaluated⟩ := operation_values other (logic.read before) reads sound source operand slice lookup
    have same := Option.some.inj (node.symm.trans actual)
    subst word
    exact some_safe logic _ before _ (correct.borrowed operand source.opcode slice lookup target values
      (transform value) before valid arguments (law values value evaluated))

private theorem iszero_tail_safe (logic : BuilderLogic (Effect State Failure) State) (rules : ReadRules logic)
    (other : Meaning) (reads : Reads) (constructors : Constructors Debug (Effect State Failure)) (debug : Debug)
    (correct : Children logic reads constructors debug) (before : State) (valid : logic.valid before)
    (sound : Sound (Folding.wordMeaning other) (logic.read before) reads)
    (operand : NodeId) (value : Word) (actual : logic.read before operand = some value) :
    logic.safe (do
      if let some inner ← readAction (reads.operation operand opXOR) then
        return some (← constructors.borrowedOperation inner.address opEQ inner.items debug)
      if let some inner ← readAction (reads.operation operand opSUB) then
        return some (← constructors.borrowedOperation inner.address opEQ inner.items debug)
      return none) before
      (fun result after => ∀ id, result = some id → logic.read after id = some (Unary.iszero.eval value)) := by
  apply operation_probe_safe logic rules other reads constructors debug correct before valid sound .xor .eq Unary.iszero.eval
    (equality_of_zero_test .xor (Or.inl rfl)) operand value actual
  apply operation_probe_safe logic rules other reads constructors debug correct before valid sound .sub .eq Unary.iszero.eval
    (equality_of_zero_test .sub (Or.inr rfl)) operand value actual
  exact logic.pure before none _ valid (by simp)

theorem unary_not_safe (logic : BuilderLogic (Effect State Failure) State) (rules : ReadRules logic)
    (other : Meaning) (reads : Reads) (constructors : Constructors Debug (Effect State Failure)) (debug : Debug)
    (before : State) (valid : logic.valid before)
    (sound : Sound (Folding.wordMeaning other) (logic.read before) reads)
    (id : NodeId) (value : Word) (actual : logic.read before id = some value) (operand : OperandRead (Effect State Failure)) :
    logic.safe (unaryStageWithInputs reads constructors opNOT id debug operand) before
      (fun result after => ∀ id, result = some id → logic.read after id = some (Unary.bitnot.eval value)) := by
  simp only [unaryStageWithInputs, show (opNOT == opISZERO) = false from rfl,
    beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
  apply rules.bind before _ _ _ valid
  intro option lookup
  cases option with
  | none => exact logic.pure before none _ valid (by simp)
  | some slice =>
    obtain ⟨inner, word, items, child, node⟩ := unary_values other (logic.read before) reads sound .not rfl id slice lookup
    have same : value = Unary.bitnot.eval word := Option.some.inj (actual.symm.trans node)
    subst value
    simp only [items]
    exact logic.pure before (some inner) _ valid (by
      intro result equal; cases equal; simpa [Unary.eval] using child)

theorem unary_iszero_safe (logic : BuilderLogic (Effect State Failure) State) (rules : ReadRules logic)
    (other : Meaning) (reads : Reads) (constructors : Constructors Debug (Effect State Failure)) (debug : Debug)
    (correct : Children logic reads constructors debug) (before : State) (valid : logic.valid before)
    (sound : Sound (Folding.wordMeaning other) (logic.read before) reads)
    (id : NodeId) (value : Word) (actual : logic.read before id = some value)
    (operand : OperandRead (Effect State Failure)) (inputs : Inputs logic reads operand before) :
    logic.safe (unaryStageWithInputs reads constructors opISZERO id debug operand) before
      (fun result after => ∀ id, result = some id → logic.read after id = some (Unary.iszero.eval value)) := by
  simp only [unaryStageWithInputs, show (opISZERO == opNOT) = false from rfl,
    beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
  apply rules.bind before _ _ _ valid
  intro option lookup
  cases option with
  | none => exact iszero_tail_safe logic rules other reads constructors debug correct before valid sound id value actual
  | some second =>
    obtain ⟨inner, word, items, child, node⟩ := unary_values other (logic.read before) reads sound .iszero rfl id second lookup
    have same : value = Unary.iszero.eval word := Option.some.inj (actual.symm.trans node)
    subst value
    simp only [items]
    apply rules.bind before _ _ _ valid
    intro option found
    cases option with
    | some third =>
      obtain ⟨original, innerWord, innerItems, innerRead, idRead⟩ :=
        unary_values other (logic.read before) reads sound .iszero rfl inner third found
      have same : word = Unary.iszero.eval innerWord := Option.some.inj (child.symm.trans idRead)
      subst word
      simp only [innerItems, triple_iszero]
      apply logic.bind before _ _ (fun loaded _ => loaded = original) _
        (inputs inner opISZERO third found 0 original (by simp [innerItems]))
      intro loaded after validAfter stable same
      subst loaded
      exact some_safe logic _ after _ (correct.operation .iszero [original] [innerWord]
        (Unary.iszero.eval innerWord) after validAfter (by simp [readArguments, stable original innerWord innerRead]) rfl)
    | none =>
      apply operation_probe_safe logic rules other reads constructors debug correct before valid sound .eq .eq
        (fun word => Unary.iszero.eval (Unary.iszero.eval word))
        (boolean_double_iszero .eq (Or.inl rfl)) inner word child
      apply operation_probe_safe logic rules other reads constructors debug correct before valid sound .lt .lt
        (fun word => Unary.iszero.eval (Unary.iszero.eval word))
        (boolean_double_iszero .lt (Or.inr (Or.inl rfl))) inner word child
      apply operation_probe_safe logic rules other reads constructors debug correct before valid sound .slt .slt
        (fun word => Unary.iszero.eval (Unary.iszero.eval word))
        (boolean_double_iszero .slt (Or.inr (Or.inr (Or.inl rfl)))) inner word child
      apply operation_probe_safe logic rules other reads constructors debug correct before valid sound .gt .gt
        (fun word => Unary.iszero.eval (Unary.iszero.eval word))
        (boolean_double_iszero .gt (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) inner word child
      apply operation_probe_safe logic rules other reads constructors debug correct before valid sound .sgt .sgt
        (fun word => Unary.iszero.eval (Unary.iszero.eval word))
        (boolean_double_iszero .sgt (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) inner word child
      exact iszero_tail_safe logic rules other reads constructors debug correct before valid sound id
        (Unary.iszero.eval word) actual

/-- The whole shared unary body: ordered queries, indexed initialization,
borrowed reconstruction, misses and every read/child failure. -/
theorem unary_stage_safe (logic : BuilderLogic (Effect State Failure) State) (rules : ReadRules logic)
    (other : Meaning) (reads : Reads) (constructors : Constructors Debug (Effect State Failure)) (debug : Debug)
    (correct : Children logic reads constructors debug) (before : State) (valid : logic.valid before)
    (sound : Sound (Folding.wordMeaning other) (logic.read before) reads)
    (instruction : Opcode) (id : NodeId) (value expected : Word) (sequence : BitVec 32)
    (actual : logic.read before id = some value)
    (denotation : (Folding.wordMeaning other).operation instruction sequence [value] = some expected)
    (operand : OperandRead (Effect State Failure)) (inputs : Inputs logic reads operand before) :
    logic.safe (unaryStageWithInputs reads constructors instruction id debug operand) before
      (fun result after => ∀ id, result = some id → logic.read after id = some expected) := by
  by_cases bitnot : instruction = opNOT
  · subst instruction
    change (Folding.wordMeaning other).operation Folding.Op.not.opcode sequence [value] = some expected at denotation
    rw [Folding.word_meaning_operation] at denotation
    have same : Unary.bitnot.eval value = expected := Option.some.inj denotation
    rw [← same]
    exact unary_not_safe logic rules other reads constructors debug before valid sound id value actual operand
  · by_cases iszero : instruction = opISZERO
    · subst instruction
      change (Folding.wordMeaning other).operation Folding.Op.iszero.opcode sequence [value] = some expected at denotation
      rw [Folding.word_meaning_operation] at denotation
      have same : Unary.iszero.eval value = expected := Option.some.inj denotation
      rw [← same]
      exact unary_iszero_safe logic rules other reads constructors debug correct before valid sound id value actual operand inputs
    · simp only [unaryStageWithInputs, beq_iff_eq, bitnot, iszero, ↓reduceIte]
      exact logic.pure before none _ valid (by simp)

def logicalChildren (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (debug : Debug) :
    Children (Interner.builderLogic (Folding.wordMeaning other)) reads constructors debug where
  operation := fun op ids values value before valid actual evaluated =>
    correct.operation op ids values value debug before valid actual evaluated
  borrowed := fun _ _ source _ op values value before valid actual evaluated =>
    correct.borrowedOperation source.address op source.items values value debug before valid actual evaluated

omit [MonadLift (Except Error) (Effect State Failure)] in
theorem logicalInputs (logic : BuilderLogic (Effect State Failure) State) (reads : Reads) (before : State) (valid : logic.valid before) :
    Inputs logic reads logicalOperand before :=
  fun _ _ _ _ _ annotation _ => logic.pure before annotation _ valid rfl

end UnaryPreservation
end Compiler.Extraction.Dispatch
