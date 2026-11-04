/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.NestedProgram

namespace Compiler.Extraction.Nested
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
set_option linter.unusedSimpArgs false

private theorem pure_ok (value : α) : (pure value : Except ReadError α) = .ok value := rfl
private theorem bind_ok (value : α) (next : α → Except ReadError β) :
    ((.ok value : Except ReadError α) >>= next) = next value := rfl
private theorem bind_error (error : ReadError) (next : α → Except ReadError β) :
    ((.error error : Except ReadError α) >>= next) = .error error := rfl
attribute [local simp] pure_ok bind_ok bind_error

theorem nested_not_opcode : nestedNotOpcode = Folding.Op.not.opcode := rfl

structure Sound (meaning : Meaning) (read : Read) (reads : Reads) : Prop where
  constant : ∀ id value, reads.constant id = .ok (some value) → read id = some value
  operation : ∀ id opcode slice, reads.operation id opcode = .ok (some slice) →
    ∃ sequence values value, readArguments read slice.items = some values ∧
      read id = some value ∧ meaning.operation opcode sequence values = some value
  equal : ∀ left right a b, sameExpression reads left right = true →
    read left = some a → read right = some b → a = b

theorem storage_reads_sound (meaning : Meaning) (cells : List Cell) (coherent : Coherent meaning cells) :
    Sound meaning (readValue cells) (storageReads cells) := by
  constructor
  · exact constant_fact_sound cells
  · exact operation_fact_sound meaning cells coherent
  · intro left right a b equal leftRead rightRead
    simp only [sameExpression, storageReads, beq_iff_eq] at equal
    subst right
    exact Option.some.inj (leftRead.symm.trans rightRead)

theorem cancel_found (reads : Reads) (opcode : Opcode) (single nested result : NodeId)
    (found : cancelNestedBinary reads opcode single nested = .ok (some result)) :
    ∃ slice left right, reads.operation nested opcode = .ok (some slice) ∧
      slice.items = [left, right] ∧
      ((sameExpression reads left single = true ∧ result = right) ∨
        (sameExpression reads left single = false ∧ sameExpression reads right single = true ∧ result = left)) := by
  cases lookup : reads.operation nested opcode with
  | error error => simp [cancelNestedBinary, lookup] at found
  | ok option =>
    cases option with
    | none => simp [cancelNestedBinary, lookup] at found
    | some slice =>
      cases items : slice.items with
      | nil => simp [cancelNestedBinary, lookup, items] at found
      | cons left rest =>
        cases rest with
        | nil => simp [cancelNestedBinary, lookup, items] at found
        | cons right rest =>
          cases rest with
          | cons => simp [cancelNestedBinary, lookup, items] at found
          | nil =>
            by_cases first : sameExpression reads left single = true
            · simp [cancelNestedBinary, lookup, items, first] at found
              exact ⟨slice, left, right, rfl, items, Or.inl ⟨first, found.symm⟩⟩
            · have firstFalse : sameExpression reads left single = false := Bool.eq_false_iff.mpr first
              by_cases second : sameExpression reads right single = true
              · simp [cancelNestedBinary, lookup, items, firstFalse, second] at found
                exact ⟨slice, left, right, rfl, items, Or.inr ⟨firstFalse, second, found.symm⟩⟩
              · simp [cancelNestedBinary, lookup, items, firstFalse, second] at found

theorem absorbed_found (reads : Reads) (opcode : Opcode) (single nested result : NodeId)
    (found : absorbedOccurrence reads single nested opcode = .ok (some result)) :
    ∃ slice left right, reads.operation nested opcode = .ok (some slice) ∧
      slice.items = [left, right] ∧
      ((sameExpression reads left single = true ∧ result = left) ∨
        (sameExpression reads left single = false ∧ sameExpression reads right single = true ∧ result = right)) := by
  cases lookup : reads.operation nested opcode with
  | error error => simp [absorbedOccurrence, lookup] at found
  | ok option =>
    cases option with
    | none => simp [absorbedOccurrence, lookup] at found
    | some slice =>
      cases items : slice.items with
      | nil => simp [absorbedOccurrence, lookup, items] at found
      | cons left rest =>
        cases rest with
        | nil => simp [absorbedOccurrence, lookup, items] at found
        | cons right rest =>
          cases rest with
          | cons => simp [absorbedOccurrence, lookup, items] at found
          | nil =>
            by_cases first : sameExpression reads left single = true
            · simp [absorbedOccurrence, lookup, items, first] at found
              exact ⟨slice, left, right, rfl, items, Or.inl ⟨first, found.symm⟩⟩
            · have firstFalse : sameExpression reads left single = false := Bool.eq_false_iff.mpr first
              by_cases second : sameExpression reads right single = true
              · simp [absorbedOccurrence, lookup, items, firstFalse, second] at found
                exact ⟨slice, left, right, rfl, items, Or.inr ⟨firstFalse, second, found.symm⟩⟩
              · simp [absorbedOccurrence, lookup, items, firstFalse, second] at found

theorem negation_found (reads : Reads) (value possibleNot : NodeId)
    (found : isNegation reads value possibleNot = .ok true) :
    ∃ slice operand, reads.operation possibleNot Folding.Op.not.opcode = .ok (some slice) ∧
      slice.items = [operand] ∧ sameExpression reads operand value = true := by
  cases lookup : reads.operation possibleNot nestedNotOpcode with
  | error error => simp [isNegation, lookup] at found
  | ok option =>
    cases option with
    | none => simp [isNegation, lookup] at found
    | some slice =>
      cases items : slice.items with
      | nil => simp [isNegation, lookup, items] at found
      | cons operand rest =>
        cases rest with
        | cons => simp [isNegation, lookup, items] at found
        | nil =>
          simp [isNegation, lookup, items] at found
          exact ⟨slice, operand, lookup, items, found⟩

theorem split_constant_found (reads : Reads) (arguments : List NodeId) (result : ConstantOperand)
    (found : splitConstant reads arguments = .ok (some result)) :
    ∃ left right, arguments = [left, right] ∧
      reads.constant result.constantExpression = .ok (some result.value) ∧
      ((result.expression = left ∧ result.constantExpression = right) ∨
        (reads.constant right = .ok none ∧ result.expression = right ∧ result.constantExpression = left)) := by
  cases arguments with
  | nil => simp [splitConstant] at found
  | cons left rest =>
    cases rest with
    | nil => simp [splitConstant] at found
    | cons right rest =>
      cases rest with
      | cons => simp [splitConstant] at found
      | nil =>
        cases rightRead : reads.constant right with
        | error error => simp [splitConstant, rightRead] at found
        | ok value =>
          cases value with
          | some value =>
            simp [splitConstant, rightRead] at found
            subst result
            exact ⟨left, right, rfl, rightRead, Or.inl ⟨rfl, rfl⟩⟩
          | none =>
            cases leftRead : reads.constant left with
            | error error => simp [splitConstant, rightRead, leftRead] at found
            | ok value =>
              cases value with
              | none => simp [splitConstant, rightRead, leftRead] at found
              | some value =>
                simp [splitConstant, rightRead, leftRead] at found
                subst result
                exact ⟨left, right, rfl, leftRead, Or.inr ⟨rightRead, rfl, rfl⟩⟩

private theorem pair_reads (read : Read) (left right : NodeId) (values : List Word)
    (actual : readArguments read [left, right] = some values) :
    ∃ a b, read left = some a ∧ read right = some b ∧ values = [a, b] := by
  cases lhs : read left with
  | none => simp [readArguments, lhs] at actual
  | some a =>
    cases rhs : read right with
    | none => simp [readArguments, lhs, rhs] at actual
    | some b =>
      simp [readArguments, lhs, rhs] at actual
      exact ⟨a, b, rfl, rfl, actual.symm⟩

theorem operation_values (other : Meaning) (read : Read) (reads : Reads)
    (sound : Sound (Folding.wordMeaning other) read reads) (op : Folding.Op)
    (nested : NodeId) (slice : ArgumentSlice)
    (lookup : reads.operation nested op.opcode = .ok (some slice)) :
    ∃ values value, readArguments read slice.items = some values ∧ read nested = some value ∧
      op.eval values = some value := by
  obtain ⟨sequence, values, value, arguments, actual, denotation⟩ := sound.operation nested op.opcode slice lookup
  exact ⟨values, value, arguments, actual, (Folding.word_meaning_operation other op sequence values) ▸ denotation⟩

/-- Sound reads force a unary operation's actual arity. A malformed callback
result cannot satisfy the independent operation semantics. -/
theorem unary_values (other : Meaning) (read : Read) (reads : Reads)
    (sound : Sound (Folding.wordMeaning other) read reads) (op : Folding.Op) (arity : op.arity = 1)
    (nested : NodeId) (slice : ArgumentSlice)
    (lookup : reads.operation nested op.opcode = .ok (some slice)) :
    ∃ id value, slice.items = [id] ∧ read id = some value ∧ read nested = some (op.value value 0 0) := by
  obtain ⟨values, value, arguments, actual, denotation⟩ := operation_values other read reads sound op nested slice lookup
  have length : values.length = 1 := by
    by_cases size : values.length = 1
    · exact size
    · simp [Folding.Op.eval, arity, size] at denotation
  obtain ⟨id, items⟩ := List.length_eq_one_iff.mp ((readArguments_length read _ _ arguments).symm.trans length)
  rw [items] at arguments
  cases child : read id with
  | none => simp [readArguments, child] at arguments
  | some word =>
    simp [readArguments, child] at arguments
    subst values
    have equation : op.value word 0 0 = value := by simpa [Folding.Op.eval, arity] using denotation
    exact ⟨id, word, items, child, equation ▸ actual⟩

theorem binary_values (other : Meaning) (read : Read) (reads : Reads)
    (sound : Sound (Folding.wordMeaning other) read reads) (op : Folding.Op) (arity : op.arity = 2)
    (nested left right : NodeId) (slice : ArgumentSlice)
    (lookup : reads.operation nested op.opcode = .ok (some slice)) (items : slice.items = [left, right]) :
    ∃ a b, read left = some a ∧ read right = some b ∧ read nested = some (op.value a b 0) := by
  obtain ⟨values, value, arguments, actual, denotation⟩ := operation_values other read reads sound op nested slice lookup
  rw [items] at arguments
  obtain ⟨a, b, lhs, rhs, words⟩ := pair_reads read left right values arguments
  subst values
  have equation : op.value a b 0 = value := by
    simpa [Folding.Op.eval, arity] using denotation
  exact ⟨a, b, lhs, rhs, equation ▸ actual⟩

theorem split_constant_sound (meaning : Meaning) (read : Read) (reads : Reads)
    (sound : Sound meaning read reads) (arguments : List NodeId) (result : ConstantOperand)
    (found : splitConstant reads arguments = .ok (some result)) :
    read result.constantExpression = some result.value := by
  obtain ⟨_, _, _, constant, _⟩ := split_constant_found reads arguments result found
  exact sound.constant _ _ constant

/-- The cancellation helper is used for XOR, whose nested value equation and
captured equality imply the returned operand has the complete outer value. -/
theorem cancel_xor_sound (other : Meaning) (read : Read) (reads : Reads)
    (sound : Sound (Folding.wordMeaning other) read reads) (single nested result : NodeId) (value : Word)
    (singleRead : read single = some value)
    (found : cancelNestedBinary reads Folding.Op.xor.opcode single nested = .ok (some result)) :
    ∃ nestedValue resultValue, read nested = some nestedValue ∧ read result = some resultValue ∧
      value ^^^ nestedValue = resultValue := by
  obtain ⟨slice, left, right, lookup, items, matched⟩ := cancel_found reads _ single nested result found
  obtain ⟨a, b, lhs, rhs, actual⟩ := binary_values other read reads sound .xor rfl nested left right slice lookup items
  rcases matched with ⟨equal, result⟩ | ⟨_, equal, result⟩
  · have same := sound.equal left single a value equal lhs singleRead
    subst a
    subst result
    exact ⟨value ^^^ b, b, actual, rhs, by simp [← BitVec.xor_assoc]⟩
  · have same := sound.equal right single b value equal rhs singleRead
    subst b
    subst result
    exact ⟨a ^^^ value, a, actual, lhs, by rw [BitVec.xor_comm a value]; simp [← BitVec.xor_assoc]⟩

private theorem absorption_sound (other : Meaning) (read : Read) (reads : Reads)
    (sound : Sound (Folding.wordMeaning other) read reads) (op : Folding.Op) (arity : op.arity = 2)
    (combine : Word → Word → Word)
    (leftLaw : ∀ a b, combine a (op.value a b 0) = a)
    (rightLaw : ∀ a b, combine b (op.value a b 0) = b)
    (single nested result : NodeId) (value : Word) (singleRead : read single = some value)
    (found : absorbedOccurrence reads single nested op.opcode = .ok (some result)) :
    ∃ nestedValue, read nested = some nestedValue ∧ read result = some value ∧ combine value nestedValue = value := by
  obtain ⟨slice, left, right, lookup, items, matched⟩ := absorbed_found reads _ single nested result found
  obtain ⟨a, b, lhs, rhs, actual⟩ := binary_values other read reads sound op arity nested left right slice lookup items
  rcases matched with ⟨equal, result⟩ | ⟨_, equal, result⟩
  · have same := sound.equal left single a value equal lhs singleRead
    subst a
    subst result
    exact ⟨op.value value b 0, actual, lhs, leftLaw value b⟩
  · have same := sound.equal right single b value equal rhs singleRead
    subst b
    subst result
    exact ⟨op.value a value 0, actual, rhs, rightLaw a value⟩

private theorem or_and_absorb (a b : Word) : a ||| (a &&& b) = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro index _
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and]
  cases a.getLsbD index <;> rfl

private theorem and_or_absorb (a b : Word) : a &&& (a ||| b) = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro index _
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and]
  cases a.getLsbD index <;> rfl

theorem absorbed_and_sound (other : Meaning) (read : Read) (reads : Reads)
    (sound : Sound (Folding.wordMeaning other) read reads) (single nested result : NodeId) (value : Word)
    (singleRead : read single = some value)
    (found : absorbedOccurrence reads single nested Folding.Op.and.opcode = .ok (some result)) :
    ∃ nestedValue, read nested = some nestedValue ∧ read result = some value ∧ value ||| nestedValue = value :=
  absorption_sound other read reads sound .and rfl (· ||| ·) or_and_absorb
    (fun a b => by change b ||| (a &&& b) = b; rw [BitVec.and_comm]; exact or_and_absorb b a)
    single nested result value singleRead found

theorem absorbed_or_sound (other : Meaning) (read : Read) (reads : Reads)
    (sound : Sound (Folding.wordMeaning other) read reads) (single nested result : NodeId) (value : Word)
    (singleRead : read single = some value)
    (found : absorbedOccurrence reads single nested Folding.Op.or.opcode = .ok (some result)) :
    ∃ nestedValue, read nested = some nestedValue ∧ read result = some value ∧ value &&& nestedValue = value :=
  absorption_sound other read reads sound .or rfl (· &&& ·) and_or_absorb
    (fun a b => by change b &&& (a ||| b) = b; rw [BitVec.or_comm]; exact and_or_absorb b a)
    single nested result value singleRead found

theorem negation_sound (other : Meaning) (read : Read) (reads : Reads)
    (sound : Sound (Folding.wordMeaning other) read reads) (value possibleNot : NodeId) (word : Word)
    (valueRead : read value = some word) (found : isNegation reads value possibleNot = .ok true) :
    read possibleNot = some (~~~word) := by
  obtain ⟨slice, operand, lookup, items, equal⟩ := negation_found reads value possibleNot found
  obtain ⟨sequence, values, result, arguments, actual, denotation⟩ := sound.operation possibleNot _ slice lookup
  rw [items] at arguments
  cases operandRead : read operand with
  | none => simp [readArguments, operandRead] at arguments
  | some operandValue =>
    have same := sound.equal operand value operandValue word equal operandRead valueRead
    subst operandValue
    simp [readArguments, operandRead] at arguments
    subst values
    rw [Folding.word_meaning_operation] at denotation
    have resultValue : (~~~word) = result := by
      simpa [Folding.Op.eval, Folding.Op.arity, Folding.Op.value, Unary.eval] using denotation
    exact resultValue ▸ actual

/-- Concrete native expression-class specialization: no abstract equality or
operation-lookup soundness premise remains beyond the graph invariant. -/
theorem storage_cancel_xor_sound (other : Meaning) (cells : List Cell)
    (coherent : Coherent (Folding.wordMeaning other) cells) (single nested result : NodeId) (value : Word)
    (singleRead : readValue cells single = some value)
    (found : cancelNestedBinary (storageReads cells) Folding.Op.xor.opcode single nested = .ok (some result)) :
    ∃ nestedValue resultValue, readValue cells nested = some nestedValue ∧
      readValue cells result = some resultValue ∧ value ^^^ nestedValue = resultValue :=
  cancel_xor_sound other (readValue cells) (storageReads cells)
    (storage_reads_sound _ cells coherent) single nested result value singleRead found

private theorem bind_total (first : Except ReadError α) (next : α → Except ReadError β)
    (total : ∃ value, first = .ok value) (following : ∀ value, ∃ result, next value = .ok result) :
    ∃ result, (first >>= next) = .ok result := by
  obtain ⟨value, actual⟩ := total
  simpa only [actual, bind_ok] using following value

/-- Every helper terminates without a modeled read/optional fault on a coherent
native graph, including wrong-arity, invalid-ID and no-match cases. -/
theorem storage_helpers_total (meaning : Meaning) (cells : List Cell) (coherent : Coherent meaning cells) :
    (∀ arguments, ∃ result, splitConstant (storageReads cells) arguments = .ok result) ∧
    (∀ opcode single nested, ∃ result, cancelNestedBinary (storageReads cells) opcode single nested = .ok result) ∧
    (∀ opcode single nested, ∃ result, absorbedOccurrence (storageReads cells) single nested opcode = .ok result) ∧
    (∀ value possibleNot, ∃ result, isNegation (storageReads cells) value possibleNot = .ok result) := by
  have constants : ∀ id, ∃ result, (storageReads cells).constant id = .ok result := by
    intro id
    exact ⟨_, constant_correct cells id⟩
  have operations : ∀ id opcode, ∃ result, (storageReads cells).operation id opcode = .ok result :=
    operation_no_fault meaning cells coherent
  constructor
  · intro arguments
    unfold splitConstant
    split
    next left right =>
      apply bind_total _ _ (constants right)
      intro first
      cases first with
      | some value => exact ⟨_, rfl⟩
      | none =>
        apply bind_total _ _ (constants left)
        intro second
        cases second <;> exact ⟨_, rfl⟩
    next => exact ⟨_, rfl⟩
  constructor
  · intro opcode single nested
    unfold cancelNestedBinary
    apply bind_total _ _ (operations nested opcode)
    intro lookup
    cases lookup with
    | none => exact ⟨_, rfl⟩
    | some slice =>
      dsimp only
      simp only [pure_ok, bind_ok]
      split
      next left right =>
        split
        · exact ⟨_, rfl⟩
        · split <;> exact ⟨_, rfl⟩
      next => exact ⟨_, rfl⟩
  constructor
  · intro opcode single nested
    unfold absorbedOccurrence
    apply bind_total _ _ (operations nested opcode)
    intro lookup
    cases lookup with
    | none => exact ⟨_, rfl⟩
    | some slice =>
      dsimp only
      simp only [pure_ok, bind_ok]
      split
      next left right =>
        split
        · exact ⟨_, rfl⟩
        · split <;> exact ⟨_, rfl⟩
      next => exact ⟨_, rfl⟩
  · intro value possibleNot
    unfold isNegation
    apply bind_total _ _ (operations possibleNot nestedNotOpcode)
    intro lookup
    cases lookup with
    | none => exact ⟨_, rfl⟩
    | some slice =>
      dsimp only
      split <;> exact ⟨_, rfl⟩

end Compiler.Extraction.Nested
