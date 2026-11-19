/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.ConstructorProgram
import Compiler.Extraction.BuilderPreservation

namespace Compiler.Extraction.Interner
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul
set_option linter.unusedSimpArgs false

theorem buildOpcode_correct (op : BuildOp) : buildOpcode op = specifiedOpcode op := by
  cases op <;> rfl

theorem constructorMeaning_laws (other : Meaning) : MeaningLaws (constructorMeaning other) := by
  constructor
  · intro value; rfl
  · intro op values; cases op <;> rfl

def implementedBuilder (p : Primitives) : Builder Action Debug where
  makeConstant := fun value _ => findCode.run p (constructorCode.constantRequest value)
  makeOperation := fun op ids _ => findCode.run p (constructorCode.operationRequest (buildOpcode op) ids)

theorem constant_request_sound (meaning : Meaning) (laws : MeaningLaws meaning)
    (read : Read) (value : Word) :
    let request := constructorCode.constantRequest value
    request.item.eval meaning read request.arguments request.sequence = some value := by
  simpa [constructorCode, ConstructorCode.constantRequest, Scalar.run, Item.eval, readArguments] using laws.constant value

theorem operation_request_sound (meaning : Meaning) (laws : MeaningLaws meaning)
    (read : Read) (op : BuildOp) (ids : List NodeId) (values : List Word) (value : Word)
    (arguments : readArguments read ids = some values) (denotation : op.eval values = some value) :
    let request := constructorCode.operationRequest (buildOpcode op) ids
    request.item.eval meaning read request.arguments request.sequence = some value := by
  simpa [constructorCode, ConstructorCode.operationRequest, Scalar.run, Item.eval, arguments,
    buildOpcode_correct] using (laws.operation op values).trans denotation

theorem constant_safe (meaning : Meaning) (laws : MeaningLaws meaning) (p : Primitives)
    (contracts : Contracts meaning p) (before : Heap) (valid : Invariant meaning before)
    (value : Word) (debug : Debug) :
    Safe meaning ((implementedBuilder p).makeConstant value debug) before (fun id after => after.read id = some value) :=
  find_safe meaning p contracts _ before value valid (constant_request_sound meaning laws before.read value)

theorem operation_safe (meaning : Meaning) (laws : MeaningLaws meaning) (p : Primitives)
    (contracts : Contracts meaning p) (before : Heap) (valid : Invariant meaning before)
    (op : BuildOp) (ids : List NodeId) (values : List Word) (value : Word) (debug : Debug)
    (arguments : readArguments before.read ids = some values) (denotation : op.eval values = some value) :
    Safe meaning ((implementedBuilder p).makeOperation op ids debug) before (fun id after => after.read id = some value) :=
  find_safe meaning p contracts _ before value valid
    (operation_request_sound meaning laws before.read op ids values value arguments denotation)

/-- Fallible builders preserve the cache invariant as well as values. Unlike
`Builder.Valid`, this contract is needed only on invariant-satisfying heaps. -/
structure BuilderSafe (meaning : Meaning) (builder : Builder Action Debug) : Prop where
  constant : ∀ value debug before, Invariant meaning before →
    Safe meaning (builder.makeConstant value debug) before (fun id after => after.read id = some value)
  operation : ∀ op ids values value debug before, Invariant meaning before →
    readArguments before.read ids = some values → op.eval values = some value →
    Safe meaning (builder.makeOperation op ids debug) before (fun id after => after.read id = some value)

theorem implemented_builder_safe (meaning : Meaning) (laws : MeaningLaws meaning) (p : Primitives)
    (contracts : Contracts meaning p) : BuilderSafe meaning (implementedBuilder p : Builder Action Debug) where
  constant := fun value debug before valid => constant_safe meaning laws p contracts before valid value debug
  operation := fun op ids values value debug before valid actual denotation =>
    operation_safe meaning laws p contracts before valid op ids values value debug actual denotation

/-- The logical heap instance of the shared construction rules. -/
def builderLogic (meaning : Meaning) : BuilderLogic Action Heap where
  read := Heap.read
  valid := Invariant meaning
  safe := Safe meaning
  pure := Safe.pure meaning
  bind := Safe.bind meaning

/-- One construction proof for the extracted apply body, reusable by both the
interner wrappers and the dispatcher's callbacks. The invariant is required only
on reachable input heaps, and all failure outcomes retain it and old IDs. -/
theorem replacement_safe_of_builder (meaning : Meaning) (builder : Builder Action Debug)
    (correct : BuilderSafe meaning builder) (before : Heap) (valid : Invariant meaning before)
    (replacement : Replacement) (left right : NodeId) (a b : Word) (debug : Debug)
    (ha : before.read left = some a) (hb : before.read right = some b) :
    Safe meaning (replacement.build builder left right debug) before
      (fun id after => after.read id = some (replacement.eval a b)) := by
  apply BuilderRules.replacement (logic := builderLogic meaning) (builder := builder) (debug := debug)
    (before := before) (valid := valid) (replacement := replacement) (left := left) (right := right)
    (a := a) (b := b) (lhs := ha) (rhs := hb)
  exact ⟨fun value state invariant => correct.constant value debug state invariant,
    fun op ids values value state invariant actual evaluated =>
      correct.operation op ids values value debug state invariant actual evaluated⟩

/-- The concrete interner instance retains its recursive simplifier and
storage/container primitive contracts. -/
theorem replacement_safe (meaning : Meaning) (laws : MeaningLaws meaning) (p : Primitives)
    (contracts : Contracts meaning p) (before : Heap) (valid : Invariant meaning before)
    (replacement : Replacement) (left right : NodeId) (a b : Word) (debug : Debug)
    (ha : before.read left = some a) (hb : before.read right = some b) :
    Safe meaning (replacement.build (implementedBuilder p) left right debug) before
      (fun id after => after.read id = some (replacement.eval a b)) :=
  replacement_safe_of_builder meaning (implementedBuilder p)
    (implemented_builder_safe meaning laws p contracts) before valid replacement left right a b debug ha hb

theorem extracted_apply_safe (meaning : Meaning) (laws : MeaningLaws meaning) (p : Primitives)
    (contracts : Contracts meaning p) (before : Heap) (valid : Invariant meaning before)
    (replacement : Replacement) (left right : NodeId) (a b : Word) (debug : Debug)
    (ha : before.read left = some a) (hb : before.read right = some b) :
    Safe meaning (zigApply replacement (implementedBuilder p) left right debug) before
      (fun id after => after.read id = some (replacement.eval a b)) := by
  rw [zigApply_eq]
  exact replacement_safe meaning laws p contracts before valid replacement left right a b debug ha hb

theorem extracted_rewrite_safe (meaning : Meaning) (laws : MeaningLaws meaning) (p : Primitives)
    (contracts : Contracts meaning p) (before : Heap) (valid : Invariant meaning before)
    (op : Binary) (stage : Stage) (facts : Facts) (a b : Word) (reliable : facts.Reliable a b)
    (replacement : Replacement) (selected : zigSelect (productionOpcode op) stage facts = some replacement)
    (left right : NodeId) (debug : Debug) (ha : before.read left = some a) (hb : before.read right = some b) :
    Safe meaning (zigApply replacement (implementedBuilder p) left right debug) before
      (fun id after => after.read id = some (op.eval a b)) := by
  rw [zigSelect_sound op stage facts a b reliable replacement selected]
  exact extracted_apply_safe meaning laws p contracts before valid replacement left right a b debug ha hb

end Compiler.Extraction.Interner
