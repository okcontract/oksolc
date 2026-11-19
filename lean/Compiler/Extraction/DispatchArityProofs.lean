/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchProofs

namespace Compiler.Extraction.Dispatch
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul

/-- Revision rules only match one or two arguments, independently of opcode. -/
theorem evm_stage_other_arity (reads : Reads) (constructors : Constructors Debug)
    (usizeBits : Nat) (instruction : Opcode) (arguments : List NodeId)
    (debug : Debug) (version : Version)
    (notUnary : arguments.length ≠ 1) (notBinary : arguments.length ≠ 2) :
    evmStage reads constructors usizeBits instruction arguments debug version = pure none := by
  cases arguments with
  | nil => simp [evmStage, evmStageWithInputs]; rfl
  | cons a rest =>
    cases rest with
    | nil => simp at notUnary
    | cons b rest =>
      cases rest with
      | nil => simp at notBinary
      | cons c rest => simp [evmStage, evmStageWithInputs]; rfl

/-- At other arities the complete extracted dispatcher is exactly its constant
prefix. This includes zero and arbitrarily many arguments, not only ternaries. -/
theorem other_arity_simplify (reads : Reads) (constructors : Constructors Debug)
    (usizeBits : Nat) (instruction : Opcode) (arguments : List NodeId)
    (debug : Debug) (options : Options)
    (notUnary : arguments.length ≠ 1) (notBinary : arguments.length ≠ 2) :
    simplifyWithOptions reads constructors usizeBits instruction arguments debug options =
      constantStage reads constructors instruction arguments debug := by
  have finish (arguments : List NodeId) :
      orNext (constantStage reads constructors instruction arguments debug) (pure none) =
        constantStage reads constructors instruction arguments debug := by
    funext before
    generalize execution : (constantStage reads constructors instruction arguments debug) before = result
    obtain ⟨result, after⟩ := result
    cases result with
    | error error => exact or_next_failure _ _ before after error execution
    | ok result =>
      cases result with
      | none => exact or_next_miss _ _ before after execution
      | some id => exact or_next_match _ _ before after id execution
  cases arguments with
  | nil =>
    unfold simplifyWithOptions simplifyOptionsWithInputs
    cases options.evmVersion with
    | none => exact finish []
    | some version =>
      change orNext (constantStage reads constructors instruction [] debug)
        (evmStage reads constructors usizeBits instruction [] debug version) = _
      rw [evm_stage_other_arity reads constructors usizeBits instruction [] debug version notUnary notBinary]
      exact finish []
  | cons a rest =>
    cases rest with
    | nil => simp at notUnary
    | cons b rest =>
      cases rest with
      | nil => simp at notBinary
      | cons c rest =>
        unfold simplifyWithOptions simplifyOptionsWithInputs
        cases options.evmVersion with
        | none => exact finish _
        | some version =>
          change orNext (constantStage reads constructors instruction (a :: b :: c :: rest) debug)
            (evmStage reads constructors usizeBits instruction (a :: b :: c :: rest) debug version) = _
          rw [evm_stage_other_arity reads constructors usizeBits instruction (a :: b :: c :: rest) debug version notUnary notBinary]
          exact finish _

theorem other_arity_simplify_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (instruction : Opcode) (arguments : List NodeId) (values : List Word) (expected : Word)
    (sequence : BitVec 32) (debug : Debug) (options : Options) (usizeBits : Nat)
    (notUnary : arguments.length ≠ 1) (notBinary : arguments.length ≠ 2)
    (actual : readArguments before.read arguments = some values)
    (denotation : (Folding.wordMeaning other).operation instruction sequence values = some expected) :
    Safe (Folding.wordMeaning other) (simplifyWithOptions reads constructors usizeBits instruction arguments debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some expected) := by
  rw [other_arity_simplify reads constructors usizeBits instruction arguments debug options notUnary notBinary]
  exact constant_stage_safe other reads constructors correct instruction arguments values expected sequence debug before valid sound actual denotation

theorem other_arity_simplify_miss (reads : Reads) (constructors : Constructors Debug)
    (usizeBits : Nat) (instruction : Opcode) (arguments : List NodeId) (debug : Debug) (options : Options)
    (notUnary : arguments.length ≠ 1) (notBinary : arguments.length ≠ 2) :
    MissUnchanged (simplifyWithOptions reads constructors usizeBits instruction arguments debug options) := by
  rw [other_arity_simplify reads constructors usizeBits instruction arguments debug options notUnary notBinary]
  exact constant_stage_miss reads constructors instruction arguments debug

/-- Full ADDMOD and MULMOD paths use mathematical addition/multiplication
before reduction, including zero moduli. They do not wrap the intermediate word. -/
theorem ternary_simplify_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (op : Folding.Op) (ternary : op = .addmod ∨ op = .mulmod)
    (left right modulus : NodeId) (a b c : Word) (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) (modRead : before.read modulus = some c) :
    Safe (Folding.wordMeaning other) (simplifyWithOptions reads constructors usizeBits op.opcode [left, right, modulus] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (op.value a b c)) := by
  apply other_arity_simplify_safe other reads constructors correct before valid sound op.opcode [left, right, modulus]
    [a, b, c] _ 0 debug options usizeBits (by simp) (by simp)
    (by simp [readArguments, lhs, rhs, modRead])
  rw [Folding.word_meaning_operation]
  rcases ternary with rfl | rfl <;> rfl

theorem interner_ternary_simplify_safe (other : Meaning) (pushes : Pushes other) (p : Primitives)
    (contracts : Contracts (Folding.wordMeaning other) p) (reads : Reads) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (op : Folding.Op) (ternary : op = .addmod ∨ op = .mulmod)
    (left right modulus : NodeId) (a b c : Word) (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) (modRead : before.read modulus = some c) :
    Safe (Folding.wordMeaning other) (simplifyWithOptions reads (implementedConstructors p) usizeBits op.opcode [left, right, modulus] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (op.value a b c)) :=
  ternary_simplify_safe other reads (implementedConstructors p)
    (implemented_constructors_sound other pushes p contracts) before valid sound
    op ternary left right modulus a b c debug options usizeBits lhs rhs modRead

end Compiler.Extraction.Dispatch
