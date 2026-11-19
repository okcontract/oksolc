/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchAndProofs
import Compiler.Extraction.DispatchArityProofs
import Compiler.Extraction.DispatchComparisonProofs
import Compiler.Extraction.DispatchMultiplicationProofs
import Compiler.Extraction.DispatchDivisionProofs
import Compiler.Extraction.DispatchSignedProofs
import Compiler.Extraction.DispatchExponentProofs
import Compiler.Extraction.DispatchModuloProofs
import Compiler.Extraction.DispatchSubtractionProofs
import Compiler.Extraction.DispatchByteProofs
import Compiler.Extraction.DispatchShiftRightProofs
import Compiler.Extraction.DispatchSignExtendProofs

namespace Compiler.Extraction.Dispatch
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
set_option linter.unusedSimpArgs false

/-- These disjoint extensions commute, including their undefined arities.
Every other opcode and atom keeps its original observation epoch. -/
theorem address_shift_commute (env : AddressMask.Environment) (other : Meaning) :
    ArithmeticShift.shiftMeaning (AddressMask.addressMeaning env other) =
      AddressMask.addressMeaning env (ArithmeticShift.shiftMeaning other) := by
  unfold ArithmeticShift.shiftMeaning AddressMask.addressMeaning
  congr 1
  funext opcode sequence values
  by_cases shift : opcode = ArithmeticShift.opcode
  · subst opcode
    rfl
  · simp only [show (opcode == ArithmeticShift.opcode) = false by simpa using shift,
      Bool.false_eq_true, ↓reduceIte]

def wordBaseMeaning (env : AddressMask.Environment) (other : Meaning) : Meaning :=
  ArithmeticShift.shiftMeaning (AddressMask.addressMeaning env other)

def wordDispatchMeaning (env : AddressMask.Environment) (other : Meaning) : Meaning :=
  Folding.wordMeaning (wordBaseMeaning env other)

theorem word_dispatch_address_model (env : AddressMask.Environment) (other : Meaning) :
    wordDispatchMeaning env other = AddressMask.meaning env (ArithmeticShift.shiftMeaning other) := by
  unfold wordDispatchMeaning wordBaseMeaning AddressMask.meaning
  rw [address_shift_commute]

theorem word_dispatch_operation (env : AddressMask.Environment) (other : Meaning)
    (op : Folding.Op) (sequence : BitVec 32) (values : List Word) :
    (wordDispatchMeaning env other).operation op.opcode sequence values = op.eval values :=
  Folding.word_meaning_operation _ op sequence values

theorem word_dispatch_other (env : AddressMask.Environment) (other : Meaning)
    (opcode : Opcode) (sequence : BitVec 32) (values : List Word)
    (notWord : Folding.decodeWord opcode = none) (notShift : opcode ≠ ArithmeticShift.opcode)
    (notAddress : AddressMask.decode opcode = none) :
    (wordDispatchMeaning env other).operation opcode sequence values = other.operation opcode sequence values := by
  simp [wordDispatchMeaning, wordBaseMeaning, Folding.wordMeaning, notWord,
    ArithmeticShift.shiftMeaning, notShift, AddressMask.addressMeaning, notAddress]

theorem word_dispatch_decoded (opcode : Opcode) (op : Folding.Op)
    (decoded : Folding.decodeWord opcode = some op) : opcode = op.opcode := by
  have found := List.find?_some decoded
  exact (beq_iff_eq.mp found).symm

/-- All binary operations in the word vocabulary use the same interpretation.
Constructor contracts remain explicit; this is not recursive closure. -/
theorem word_binary_simplify_safe (env : AddressMask.Environment) (other : Meaning)
    (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound (wordBaseMeaning env other) constructors)
    (addressCorrect : AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) constructors.operation)
    (sarCorrect : ArithmeticShift.Constructs (AddressMask.addressMeaning env other) constructors.operation)
    (before : Heap) (valid : Invariant (wordDispatchMeaning env other) before)
    (sound : Sound (wordDispatchMeaning env other) before.read reads)
    (op : Folding.Op) (arity : op.arity = 2) (left right : NodeId) (a b : Word)
    (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (wordDispatchMeaning env other)
      (simplifyWithOptions reads constructors usizeBits op.opcode [left, right] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (op.value a b 0)) := by
  cases op with
  | not | iszero | addmod | mulmod => simp [Folding.Op.arity] at arity
  | add | or | xor =>
    exact add_or_xor_simplify_safe _ reads constructors correct before valid sound _ (by simp [AddOrXor])
      left right a b debug options usizeBits lhs rhs
  | eq | lt | gt | slt | sgt =>
    exact comparison_simplify_safe _ reads constructors correct before valid sound _ (by simp [BooleanOperation])
      left right a b debug options usizeBits lhs rhs
  | sdiv | smod =>
    exact signed_simplify_safe _ reads constructors correct before valid sound _ (by simp [SignedArithmetic])
      left right a b debug options usizeBits lhs rhs
  | mul => exact mul_simplify_safe _ reads constructors correct before valid sound left right a b debug options usizeBits lhs rhs
  | div => exact div_simplify_safe _ reads constructors correct before valid sound left right a b debug options usizeBits lhs rhs
  | sub => exact sub_simplify_safe _ reads constructors correct before valid sound left right a b debug options usizeBits lhs rhs
  | mod => exact mod_simplify_safe _ reads constructors correct before valid sound left right a b debug options usizeBits lhs rhs
  | exp => exact exp_simplify_safe _ reads constructors correct before valid sound left right a b debug options usizeBits lhs rhs
  | byte => exact byte_simplify_safe _ reads constructors correct before valid sound left right a b debug options usizeBits lhs rhs
  | shl => exact shl_simplify_safe _ reads constructors correct before valid sound left right a b debug options usizeBits lhs rhs
  | shr => exact shr_simplify_safe _ reads constructors correct before valid sound left right a b debug options usizeBits lhs rhs
  | signextend =>
    exact signextend_simplify_safe _ reads constructors correct sarCorrect before valid sound
      left right a b debug options usizeBits lhs rhs
  | and =>
    rw [word_dispatch_address_model] at valid sound ⊢
    exact and_simplify_safe env (ArithmeticShift.shiftMeaning other) reads constructors
      (by simpa only [wordBaseMeaning, address_shift_commute] using correct) addressCorrect
      before valid sound left right a b debug options usizeBits lhs rhs

/-- One preservation statement for every defined application of all 24 word
operations. The semantic evaluation supplies arity; no opcode or arity is
excluded by a caller-chosen list of proved cases. -/
theorem word_simplify_safe (env : AddressMask.Environment) (other : Meaning)
    (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound (wordBaseMeaning env other) constructors)
    (addressCorrect : AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) constructors.operation)
    (sarCorrect : ArithmeticShift.Constructs (AddressMask.addressMeaning env other) constructors.operation)
    (before : Heap) (valid : Invariant (wordDispatchMeaning env other) before)
    (sound : Sound (wordDispatchMeaning env other) before.read reads)
    (op : Folding.Op) (arguments : List NodeId) (values : List Word) (expected : Word)
    (debug : Debug) (options : Options) (usizeBits : Nat)
    (actual : readArguments before.read arguments = some values)
    (evaluated : op.eval values = some expected) :
    Safe (wordDispatchMeaning env other)
      (simplifyWithOptions reads constructors usizeBits op.opcode arguments debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some expected) := by
  have length : values.length = op.arity := by
    unfold Folding.Op.eval at evaluated
    split at evaluated
    · assumption
    · contradiction
  have inputLength := readArguments_length before.read arguments values actual
  by_cases unary : arguments.length = 1
  · obtain ⟨operand, rfl⟩ := List.length_eq_one_iff.mp unary
    cases found : before.read operand with
    | none => simp [readArguments, found] at actual
    | some value =>
      have same : values = [value] := by simpa [readArguments, found] using actual.symm
      subst values
      have supported : UnaryWordOperation op := by
        cases op <;> simp_all [Folding.Op.arity, UnaryWordOperation]
      have result : op.value value 0 0 = expected := by
        simpa [Folding.Op.eval, ← length] using evaluated
      rw [← result]
      exact word_unary_simplify_safe _ reads constructors correct before valid sound op supported
        operand value debug options usizeBits found
  · by_cases binary : arguments.length = 2
    · cases arguments with
      | nil => simp at binary
      | cons left tail =>
        cases tail with
        | nil => simp at binary
        | cons right tail =>
          have empty : tail = [] := by simpa using binary
          subst tail
          cases lhs : before.read left with
          | none => simp [readArguments, lhs] at actual
          | some a =>
            cases rhs : before.read right with
            | none => simp [readArguments, lhs, rhs] at actual
            | some b =>
              have same : values = [a, b] := by simpa [readArguments, lhs, rhs] using actual.symm
              subst values
              have result : op.value a b 0 = expected := by
                simpa [Folding.Op.eval, ← length] using evaluated
              rw [← result]
              exact word_binary_simplify_safe env other reads constructors correct addressCorrect sarCorrect
                before valid sound op length.symm left right a b debug options usizeBits lhs rhs
    · apply other_arity_simplify_safe (wordBaseMeaning env other) reads constructors correct before valid sound
        op.opcode arguments values expected 0 debug options usizeBits unary binary actual
      simpa only [Folding.word_meaning_operation] using evaluated

/-- Raw opcode clients can use the same theorem from a checked vocabulary
lookup and the model's denotation at any observation epoch. -/
theorem decoded_word_simplify_safe (env : AddressMask.Environment) (other : Meaning)
    (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound (wordBaseMeaning env other) constructors)
    (addressCorrect : AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) constructors.operation)
    (sarCorrect : ArithmeticShift.Constructs (AddressMask.addressMeaning env other) constructors.operation)
    (before : Heap) (valid : Invariant (wordDispatchMeaning env other) before)
    (sound : Sound (wordDispatchMeaning env other) before.read reads)
    (opcode : Opcode) (op : Folding.Op) (decoded : Folding.decodeWord opcode = some op)
    (arguments : List NodeId) (values : List Word) (expected : Word) (sequence : BitVec 32)
    (debug : Debug) (options : Options) (usizeBits : Nat)
    (actual : readArguments before.read arguments = some values)
    (evaluated : (wordDispatchMeaning env other).operation opcode sequence values = some expected) :
    Safe (wordDispatchMeaning env other)
      (simplifyWithOptions reads constructors usizeBits opcode arguments debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some expected) := by
  obtain rfl := word_dispatch_decoded opcode op decoded
  exact word_simplify_safe env other reads constructors correct addressCorrect sarCorrect before valid sound
    op arguments values expected debug options usizeBits actual
    (by simpa only [word_dispatch_operation] using evaluated)

/-- Use the implemented constructors, retaining the interner's explicit
primitive contracts. In particular, its recursive simplify field is still a
hypothesis; this theorem does not justify a circular use of that field. -/
theorem interner_word_simplify_safe (env : AddressMask.Environment) (other : Meaning)
    (pushes : Pushes other) (p : Primitives) (contracts : Contracts (wordDispatchMeaning env other) p)
    (reads : Reads) (before : Heap) (valid : Invariant (wordDispatchMeaning env other) before)
    (sound : Sound (wordDispatchMeaning env other) before.read reads)
    (op : Folding.Op) (arguments : List NodeId) (values : List Word) (expected : Word)
    (debug : Debug) (options : Options) (usizeBits : Nat)
    (actual : readArguments before.read arguments = some values)
    (evaluated : op.eval values = some expected) :
    Safe (wordDispatchMeaning env other)
      (simplifyWithOptions reads (implementedConstructors p) usizeBits op.opcode arguments debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some expected) := by
  apply word_simplify_safe env other reads (implementedConstructors p)
    (implemented_constructors_sound (wordBaseMeaning env other) pushes p contracts) _ _
    before valid sound op arguments values expected debug options usizeBits actual evaluated
  · exact AddressMask.interner_constructs env (ArithmeticShift.shiftMeaning other) p
      (by simpa only [word_dispatch_address_model] using contracts)
  · exact ArithmeticShift.interner_constructs (AddressMask.addressMeaning env other) p contracts

end Compiler.Extraction.Dispatch
