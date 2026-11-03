/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchUnaryPreservation

namespace Compiler.Extraction.Dispatch
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
set_option linter.unusedSimpArgs false

theorem operation_some_safe (other : Meaning) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (op : Folding.Op) (ids : List NodeId) (values : List Word) (value : Word) (debug : Debug)
    (actual : readArguments before.read ids = some values) (evaluated : op.eval values = some value) :
    Safe (Folding.wordMeaning other) (do return some (← constructors.operation op.opcode ids debug)) before
      (fun result after => ∀ id, result = some id → after.read id = some value) := by
  exact UnaryPreservation.some_safe (Interner.builderLogic (Folding.wordMeaning other)) _ before value
    (correct.operation op ids values value debug before valid actual evaluated)

theorem borrowed_operation_some_safe (other : Meaning) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before) (address : Nat)
    (op : Folding.Op) (ids : List NodeId) (values : List Word) (value : Word) (debug : Debug)
    (actual : readArguments before.read ids = some values) (evaluated : op.eval values = some value) :
    Safe (Folding.wordMeaning other) (do return some (← constructors.borrowedOperation address op.opcode ids debug)) before
      (fun result after => ∀ id, result = some id → after.read id = some value) := by
  exact UnaryPreservation.some_safe (Interner.builderLogic (Folding.wordMeaning other)) _ before value
    (correct.borrowedOperation address op ids values value debug before valid actual evaluated)

theorem operation_probe_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (source target : Folding.Op) (transform : Word → Word)
    (law : ∀ values value, source.eval values = some value → target.eval values = some (transform value))
    (operand : NodeId) (value : Word) (debug : Debug) (actual : before.read operand = some value)
    (next : Action (Option NodeId))
    (rest : Safe (Folding.wordMeaning other) next before
      (fun result after => ∀ id, result = some id → after.read id = some (transform value))) :
    Safe (Folding.wordMeaning other) (do
      if let some inner ← readAction (reads.operation operand source.opcode) then
        return some (← constructors.borrowedOperation inner.address target.opcode inner.items debug)
      next) before (fun result after => ∀ id, result = some id → after.read id = some (transform value)) := by
  exact UnaryPreservation.operation_probe_safe (Interner.builderLogic (Folding.wordMeaning other))
    (Preservation.logicalReadRules _) other reads constructors debug
    (UnaryPreservation.logicalChildren other reads constructors correct debug) before valid sound
    source target transform law operand value actual next rest

theorem unary_not_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (before : Heap) (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (operand : NodeId) (value : Word) (debug : Debug) (actual : before.read operand = some value) :
    Safe (Folding.wordMeaning other) (unaryStage reads constructors opNOT operand debug) before
      (fun result after => ∀ id, result = some id → after.read id = some (Unary.bitnot.eval value)) := by
  exact UnaryPreservation.unary_not_safe (Interner.builderLogic (Folding.wordMeaning other))
    (Preservation.logicalReadRules _) other reads constructors debug before valid sound operand value actual logicalOperand

theorem unary_iszero_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (operand : NodeId) (value : Word) (debug : Debug) (actual : before.read operand = some value) :
    Safe (Folding.wordMeaning other) (unaryStage reads constructors opISZERO operand debug) before
      (fun result after => ∀ id, result = some id → after.read id = some (Unary.iszero.eval value)) := by
  exact UnaryPreservation.unary_iszero_safe (Interner.builderLogic (Folding.wordMeaning other))
    (Preservation.logicalReadRules _) other reads constructors debug
    (UnaryPreservation.logicalChildren other reads constructors correct debug) before valid sound operand value actual logicalOperand
    (UnaryPreservation.logicalInputs _ reads before valid)

theorem unary_stage_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (instruction : Opcode) (operand : NodeId) (value expected : Word) (sequence : BitVec 32)
    (debug : Debug) (actual : before.read operand = some value)
    (denotation : (Folding.wordMeaning other).operation instruction sequence [value] = some expected) :
    Safe (Folding.wordMeaning other) (unaryStage reads constructors instruction operand debug) before
      (fun result after => ∀ id, result = some id → after.read id = some expected) := by
  exact UnaryPreservation.unary_stage_safe (Interner.builderLogic (Folding.wordMeaning other))
    (Preservation.logicalReadRules _) other reads constructors debug
    (UnaryPreservation.logicalChildren other reads constructors correct debug) before valid sound
    instruction operand value expected sequence actual denotation logicalOperand
    (UnaryPreservation.logicalInputs _ reads before valid)

theorem interner_unary_stage_safe (other : Meaning) (pushes : Pushes other) (p : Primitives)
    (contracts : Contracts (Folding.wordMeaning other) p) (reads : Reads) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (instruction : Opcode) (operand : NodeId) (value expected : Word) (sequence : BitVec 32)
    (debug : Debug) (actual : before.read operand = some value)
    (denotation : (Folding.wordMeaning other).operation instruction sequence [value] = some expected) :
    Safe (Folding.wordMeaning other) (unaryStage reads (implementedConstructors p) instruction operand debug) before
      (fun result after => ∀ id, result = some id → after.read id = some expected) :=
  unary_stage_safe other reads (implementedConstructors p)
    (implemented_constructors_sound other pushes p contracts) before valid sound
    instruction operand value expected sequence debug actual denotation

/-- No constructor can run along a normal miss: each construction is terminal.
This exact heap equation needs neither semantic coherence nor constructor laws. -/
theorem unary_stage_miss (reads : Reads) (constructors : Constructors Debug)
    (instruction : Opcode) (operand : NodeId) (debug : Debug) (before after : Heap)
    (missed : unaryStage reads constructors instruction operand debug before = (.ok none, after)) :
    after = before := by
  have unchanged : MissUnchanged (unaryStage reads constructors instruction operand debug) := by
    unfold unaryStage unaryStageWithInputs
    repeat first
      | exact pure_miss_unchanged _
      | exact terminal_miss_unchanged _
      | apply read_miss_unchanged; intro option
      | split
  exact unchanged before after missed

/-- Full stage composition for unary inputs. Account-specific revision rules
still require their own preservation proof; the premise cannot skip them. -/
theorem unary_simplify_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (instruction : Opcode) (operand : NodeId) (value expected : Word) (sequence : BitVec 32)
    (debug : Debug) (options : Options) (usizeBits : Nat)
    (actual : before.read operand = some value)
    (denotation : (Folding.wordMeaning other).operation instruction sequence [value] = some expected)
    (revision : ∀ version, options.evmVersion = some version →
      Safe (Folding.wordMeaning other) (evmStage reads constructors usizeBits instruction [operand] debug version) before
        (fun result after => ∀ id, result = some id → after.read id = some expected)) :
    Safe (Folding.wordMeaning other) (simplifyWithOptions reads constructors usizeBits instruction [operand] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some expected) := by
  unfold simplifyWithOptions simplifyOptionsWithInputs
  apply or_next_safe_of_unchanged _ _ _ before _
    (constant_stage_safe other reads constructors correct instruction [operand] [value] expected sequence debug before valid sound
      (by simp [readArguments, actual]) denotation)
    (constant_stage_miss reads constructors instruction [operand] debug)
  change Safe _ (orNext (unaryStage reads constructors instruction operand debug)
    (match options.evmVersion with
    | some version => evmStage reads constructors usizeBits instruction [operand] debug version
    | none => pure none)) before _
  apply or_next_safe_of_unchanged _ _ _ before _
    (unary_stage_safe other reads constructors correct before valid sound instruction operand value expected sequence debug actual denotation)
    (unary_stage_miss reads constructors instruction operand debug)
  cases choice : options.evmVersion with
  | none => exact Safe.pure _ before none _ valid (by simp)
  | some version => exact revision version choice

def UnaryWordOperation (op : Folding.Op) : Prop := op = .not ∨ op = .iszero

theorem word_unary_evm_stage (reads : Reads) (constructors : Constructors Debug)
    (op : Folding.Op) (unary : UnaryWordOperation op) (arguments : List NodeId)
    (debug : Debug) (version : Version) (usizeBits : Nat) :
    evmStage reads constructors usizeBits op.opcode arguments debug version = pure none := by
  rcases unary with rfl | rfl
  all_goals
    simp only [evmStage, evmStageWithInputs, logicalOperand, Folding.Op.opcode, opBALANCE, opEXP, opMUL, opDIV,
      Bool.false_eq_true, ↓reduceIte, BitVec.reduceBEq]
    repeat first | rfl | split

theorem word_unary_simplify_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (op : Folding.Op) (unary : UnaryWordOperation op) (operand : NodeId) (value : Word)
    (debug : Debug) (options : Options) (usizeBits : Nat)
    (actual : before.read operand = some value) :
    Safe (Folding.wordMeaning other) (simplifyWithOptions reads constructors usizeBits op.opcode [operand] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (op.value value 0 0)) := by
  have denotation : (Folding.wordMeaning other).operation op.opcode 0 [value] = some (op.value value 0 0) := by
    rw [Folding.word_meaning_operation]
    rcases unary with rfl | rfl <;> rfl
  apply unary_simplify_safe other reads constructors correct before valid sound op.opcode operand value _ 0
    debug options usizeBits actual denotation
  intro version _
  rw [word_unary_evm_stage reads constructors op unary]
  exact Safe.pure _ before none _ valid (by simp)

theorem interner_word_unary_simplify_safe (other : Meaning) (pushes : Pushes other) (p : Primitives)
    (contracts : Contracts (Folding.wordMeaning other) p) (reads : Reads) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (op : Folding.Op) (unary : UnaryWordOperation op) (operand : NodeId) (value : Word)
    (debug : Debug) (options : Options) (usizeBits : Nat)
    (actual : before.read operand = some value) :
    Safe (Folding.wordMeaning other) (simplifyWithOptions reads (implementedConstructors p) usizeBits op.opcode [operand] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (op.value value 0 0)) :=
  word_unary_simplify_safe other reads (implementedConstructors p)
    (implemented_constructors_sound other pushes p contracts) before valid sound
    op unary operand value debug options usizeBits actual

end Compiler.Extraction.Dispatch
