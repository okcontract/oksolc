/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.AssociativeProgram

namespace Compiler.Extraction.Associative
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.Extraction.Interner Compiler.Extraction.Nested Contract.Yul
set_option linter.unusedSimpArgs false

private theorem branch_bind (condition : Bool) (left right : Action α) (next : α → Action β) :
    (if condition then left >>= next else right >>= next) =
      ((if condition then left else right) >>= next) := by cases condition <;> rfl

theorem selection_complete (instruction : Opcode) :
    isAssociative instruction = true ↔ ∃ op, Supported op ∧ instruction = op.opcode := by
  simp [isAssociative, Supported, Folding.Op.opcode]

theorem combination_correct (op : Folding.Op) (supported : Supported op) (a b : Word) :
    combineConstants op.opcode a b = .ok (op.value a b 0) := by
  rcases supported with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem combination_fault (instruction : Opcode) (a b : Word) (unsupported : isAssociative instruction = false) :
    combineConstants instruction a b = .error .safetyFault := by
  simp [isAssociative] at unsupported
  simp [combineConstants, unsupported]

def implementedConstructors (p : Primitives) : Constructors Debug :=
  { operation := internerBuilder p, constant := internerConstant p, materialize := materializeConstant (internerConstant p) }

theorem implemented_constructors_sound (other : Meaning) (pushes : Pushes other) (p : Primitives)
    (contracts : Contracts (Folding.wordMeaning other) p) :
    ConstructorSound other (implementedConstructors p : Constructors Debug) := by
  constructor
  · exact interner_constructs other p contracts
  · exact interner_constant_safe other pushes p contracts
  · intro original value debug before valid
    exact interner_constant_safe other pushes p contracts value debug before valid
  · intro address; exact interner_constructs other p contracts
  · exact local_constructs other _ (interner_constructs other p contracts)

/-- Both constant positions have the same denotation for the supported
commutative operations. Captured IDs and constant-selection priority are not
erased from the generated helper. -/
theorem split_value (other : Meaning) (read : Read) (reads : Reads)
    (sound : Sound (Folding.wordMeaning other) read reads) (op : Folding.Op) (supported : Supported op)
    (nested : NodeId) (slice : ArgumentSlice) (parts : ConstantOperand)
    (lookup : reads.operation nested op.opcode = .ok (some slice))
    (split : splitConstant reads slice.items = .ok (some parts)) :
    ∃ value, read parts.expression = some value ∧ read nested = some (op.value value parts.value 0) := by
  obtain ⟨left, right, items, constant, selected⟩ := split_constant_found reads slice.items parts split
  obtain ⟨a, b, lhs, rhs, nestedFact⟩ := binary_values other read reads sound op
    (supported_arity op supported) nested left right slice lookup items
  have literal := sound.constant parts.constantExpression parts.value constant
  rcases selected with ⟨expression, id⟩ | ⟨_, expression, id⟩
  · rw [id] at literal
    have same : b = parts.value := Option.some.inj (rhs.symm.trans literal)
    exact ⟨a, by rw [expression]; exact lhs, by rw [← same]; exact nestedFact⟩
  · rw [id] at literal
    have same : a = parts.value := Option.some.inj (lhs.symm.trans literal)
    exact ⟨b, by rw [expression]; exact rhs, by rw [← same, commutative op supported b a]; exact nestedFact⟩

theorem folded_value (op : Folding.Op) (supported : Supported op) (x c y : Word) (right : Bool) :
    (if right then op.value y (op.value x c 0) 0 else op.value (op.value x c 0) y 0) =
      op.value x (op.value c y 0) 0 := by
  cases right
  · exact associative op supported x c y
  · rw [commutative op supported y (op.value x c 0)]
    exact associative op supported x c y

theorem moved_value (op : Folding.Op) (supported : Supported op) (x c y : Word) (right : Bool) :
    (if right then op.value y (op.value x c 0) 0 else op.value (op.value x c 0) y 0) =
      op.value (if right then op.value y x 0 else op.value x y 0) c 0 := by
  cases right
  · change op.value (op.value x c 0) y 0 = op.value (op.value x y 0) c 0
    rw [associative op supported, associative op supported, commutative op supported c y]
  · exact (associative op supported y x c).symm

theorem binary_construct (other : Meaning) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (op : Folding.Op) (supported : Supported op)
    (left right : NodeId) (a b : Word) (debug : Debug) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (constructors.operation op.opcode [left, right] debug) before
      (fun id after => after.read id = some (op.value a b 0)) :=
  correct.operation op [left, right] [a, b] _ debug before valid
    (by simp [readArguments, lhs, rhs]) (by simp [Folding.Op.eval, supported_arity op supported])

theorem reassociate_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap) (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (op : Folding.Op) (supported : Supported op) (nested otherId : NodeId) (right : Bool)
    (nestedValue value : Word) (nestedRead : before.read nested = some nestedValue)
    (otherRead : before.read otherId = some value) (debug : Debug) :
    Safe (Folding.wordMeaning other) (reassociate reads constructors op.opcode nested otherId right debug) before
      (fun result after => ∀ id, result = some id → after.read id = some
        (if right then op.value value nestedValue 0 else op.value nestedValue value 0)) := by
  unfold reassociate
  apply read_action_bind_safe _ before _ _ _ valid
  intro nestedOption lookup
  cases nestedOption with
  | none => exact Safe.pure _ before none _ valid (by simp)
  | some slice =>
    apply read_action_bind_safe _ before _ _ _ valid
    intro partsOption split
    cases partsOption with
    | none => exact Safe.pure _ before none _ valid (by simp)
    | some parts =>
      obtain ⟨x, expressionRead, nestedFact⟩ := split_value other before.read reads sound op supported nested slice parts lookup split
      have same : nestedValue = op.value x parts.value 0 := Option.some.inj (nestedRead.symm.trans nestedFact)
      subst nestedValue
      apply read_action_bind_safe _ before _ _ _ valid
      intro constantOption found
      cases constantOption with
      | some otherConstant =>
        have literal := sound.constant otherId otherConstant found
        have same : otherConstant = value := Option.some.inj (literal.symm.trans otherRead)
        subst otherConstant
        simp only [combination_correct op supported, readAction]
        rw [folded_value op supported x parts.value value right]
        apply Safe.bind _ before _ _ (fun id after => after.read id = some (op.value parts.value value 0)) _
          (correct.constant _ debug before valid)
        intro constant middle validMiddle stable constantRead
        apply Safe.bind _ middle _ _ (fun id after => after.read id = some (op.value x (op.value parts.value value 0) 0)) _
          (binary_construct other constructors correct op supported parts.expression constant x _ debug middle validMiddle
            (stable _ _ expressionRead) constantRead)
        intro result after validAfter _ resultRead
        exact Safe.pure _ after (some result) _ validAfter (by intro id equal; cases equal; exact resultRead)
      | none =>
        rw [moved_value op supported x parts.value value right]
        dsimp only
        simp only [branch_bind]
        have innerSafe : Safe (Folding.wordMeaning other)
            (if right then constructors.operation op.opcode [otherId, parts.expression] debug
              else constructors.operation op.opcode [parts.expression, otherId] debug) before
            (fun id after => after.read id = some (if right then op.value value x 0 else op.value x value 0)) := by
          cases right
          · exact binary_construct other constructors correct op supported parts.expression otherId x value debug before valid expressionRead otherRead
          · exact binary_construct other constructors correct op supported otherId parts.expression value x debug before valid otherRead expressionRead
        apply Safe.bind _ before _ _ _ _ innerSafe
        intro inner middle validMiddle _ innerRead
        apply Safe.bind _ middle _ _ (fun id after => after.read id = some parts.value) _
          (correct.materialize parts.constantExpression parts.value debug middle validMiddle)
        intro constant next validNext stable constantRead
        apply Safe.bind _ next _ _ (fun id after => after.read id = some (op.value _ parts.value 0)) _
          (binary_construct other constructors correct op supported inner constant _ parts.value debug next validNext
            (stable _ _ innerRead) constantRead)
        intro result after validAfter _ resultRead
        exact Safe.pure _ after (some result) _ validAfter (by intro id equal; cases equal; exact resultRead)

theorem interner_reassociate_safe (other : Meaning) (pushes : Pushes other) (p : Primitives)
    (contracts : Contracts (Folding.wordMeaning other) p) (reads : Reads) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before) (sound : Sound (Folding.wordMeaning other) before.read reads)
    (op : Folding.Op) (supported : Supported op) (nested otherId : NodeId) (right : Bool)
    (nestedValue value : Word) (nestedRead : before.read nested = some nestedValue)
    (otherRead : before.read otherId = some value) (debug : Debug) :
    Safe (Folding.wordMeaning other)
      (reassociate reads (implementedConstructors p) op.opcode nested otherId right debug) before
      (fun result after => ∀ id, result = some id → after.read id = some
        (if right then op.value value nestedValue 0 else op.value nestedValue value 0)) :=
  reassociate_safe other reads (implementedConstructors p) (implemented_constructors_sound other pushes p contracts)
    before valid sound op supported nested otherId right nestedValue value nestedRead otherRead debug

end Compiler.Extraction.Associative
