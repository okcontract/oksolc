/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorArguments
import Compiler.Extraction.DispatchProgram

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ShiftInput
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul Compiler.ZigAir.Memory.WordArray

/-- The native constructor boundary of the four admitted shift literals.
This is not installed as a dispatcher-wide logical-list adapter. -/
structure Context (σ : Type) where
  external : External σ
  budget : Nat
  allocator : Nat
  primitives : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives σ
  queries : Caller.Queries

def constructors (context : Context σ) : Associative.Constructors AssemblyItem.Fields.Values (GraphAction σ) where
  constant := fun value debug before =>
    let ran := ConstructorItem.constant context.external context.budget context.allocator
      (context.primitives ⟨0, 0, 0⟩) context.queries value debug before
    (ran.1, ran.2.world)
  operation := Arguments.operation context.external context.budget context.allocator context.primitives context.queries
  materialize := fun _ _ _ before => (.error .outsideOwnedContinuation, before)
  borrowedOperation := fun _ _ _ _ before => (.error .outsideOwnedContinuation, before)

def operand (source : View) (index : Nat) : GraphAction σ NodeId := fun before =>
  if index < source.length then
    match TemporaryMemory.readId before.memory.memory source index with
    | .ok value => (.ok value, before)
    | .error fault => (.error (.memory (.preparation (.memory fault))), before)
  else (.error (.memory (.preparation (.memory .sourceBounds))), before)

def run (context : Context σ) (constantFirst : Bool) (opcode : Opcode) (value : Word)
    (source : View) (index : Nat) (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId :=
  Dispatch.shiftInput (constructors context) constantFirst opcode value (operand source index) debug

attribute [local irreducible] Arguments.operation ConstructorItem.constant

theorem source_projection (c : Associative.Constructors Debug (Effect Heap Error))
    (first : Bool) (opcode : Opcode) (value : Word) (id : NodeId) (debug : Debug) :
    Dispatch.shiftInput c first opcode value (pure id) debug =
      (do let constant ← c.constant value debug
          c.operation opcode (if first then [constant, id] else [id, constant]) debug) := by
  cases first <;> rfl

theorem operand_loaded (source : View) (index : Nat) (id : NodeId) (before : World σ)
    (inside : index < source.length)
    (loaded : Compiler.ZigAir.Memory.load before.memory.memory (source.pointer index) = .ok (number id)) :
    operand source index before = (.ok id, before) := by
  simp only [operand, inside, ↓reduceIte, TemporaryMemory.readId_of_load _ _ _ _ loaded]

theorem operand_fault (source : View) (index : Nat) (before : World σ) (fault : Compiler.ZigAir.Memory.Fault)
    (inside : index < source.length)
    (failed : TemporaryMemory.readId before.memory.memory source index = .error fault) :
    operand source index before = (.error (.memory (.preparation (.memory fault))), before) := by
  simp only [operand, inside, ↓reduceIte, failed]

/-- Read the initializer operand from its initialized native view, including
the view's actual offset. The values are never supplied by a logical lookup. -/
theorem operand_good (source : View) (values : List NodeId) (before : World σ)
    (good : Good source values before) (index : Nat) (inside : index < values.length) :
    operand source index before = (.ok values[index], before) :=
  operand_loaded source index values[index] before (by rw [← good.2.1]; exact inside) (good.2.2 index inside)

/-- A proper child's reached validity and native allocation frame derive the
later load. This does not assume final Good or erase the child's reached world. -/
theorem operand_after_frame (source : View) (values : List NodeId) (before after : World σ)
    (good : Good source values before) (valid : Valid after.memory)
    (native : ∀ id cell, before.memory.memory.heap.lookup id = some cell →
      after.memory.memory.heap.lookup id = some cell)
    (index : Nat) (inside : index < values.length) :
    operand source index after = (.ok values[index], after) :=
  operand_good source values after (ConstructorItem.good_frame before after source values good valid native) index inside

theorem constant_forwarded (context : Context σ) (value : Word) (debug : AssemblyItem.Fields.Values)
    (before : World σ) :
    (constructors context).constant value debug before =
      (let ran := ConstructorItem.constant context.external context.budget context.allocator
        (context.primitives ⟨0, 0, 0⟩) context.queries value debug before
       (ran.1, ran.2.world)) := rfl

theorem constant_error (context : Context σ) (opcode : Opcode) (value : Word) (source : View)
    (index : Nat) (debug : AssemblyItem.Fields.Values) (before after : World σ) (fault : Fault)
    (failed : (constructors context).constant value debug before = (.error fault, after)) :
    run context true opcode value source index debug before = (.error fault, after) :=
  Effect.bind_failure _ _ _ _ _ failed

/-- The borrowed load uses the world returned by the actual child. In the
recursive induction its load premise must follow from that child's live frame. -/
theorem after_constant (context : Context σ) (opcode : Opcode) (value : Word) (source : View)
    (index : Nat) (debug : AssemblyItem.Fields.Values) (before after : World σ) (constant id : NodeId)
    (called : (constructors context).constant value debug before = (.ok constant, after))
    (inside : index < source.length)
    (loaded : Compiler.ZigAir.Memory.load after.memory.memory (source.pointer index) = .ok (number id)) :
    run context true opcode value source index debug before =
      Arguments.operation context.external context.budget context.allocator context.primitives context.queries
        opcode [constant, id] debug after := by
  exact (Effect.bind_success _ _ _ _ _ called).trans
    (Effect.bind_success _ _ _ _ _ (operand_loaded source index id after inside loaded))

theorem operand_error (context : Context σ) (opcode : Opcode) (value : Word) (source : View)
    (index : Nat) (debug : AssemblyItem.Fields.Values) (before after : World σ) (fault : Fault)
    (failed : operand source index before = (.error fault, after)) :
    run context false opcode value source index debug before = (.error fault, after) :=
  Effect.bind_failure _ _ _ _ _ failed

theorem after_constant_fault (context : Context σ) (opcode : Opcode) (value : Word) (source : View)
    (index : Nat) (debug : AssemblyItem.Fields.Values) (before after : World σ) (constant : NodeId) (fault : Fault)
    (called : (constructors context).constant value debug before = (.ok constant, after))
    (failed : operand source index after = (.error fault, after)) :
    run context true opcode value source index debug before = (.error fault, after) := by
  exact (Effect.bind_success _ _ _ _ _ called).trans (Effect.bind_failure _ _ _ _ _ failed)

theorem operand_first (context : Context σ) (opcode : Opcode) (value : Word) (source : View)
    (index : Nat) (debug : AssemblyItem.Fields.Values) (before : World σ) (id : NodeId)
    (loaded : operand source index before = (.ok id, before)) :
    run context false opcode value source index debug before =
      (do let constant ← (constructors context).constant value debug
          Arguments.operation context.external context.budget context.allocator context.primitives context.queries
            opcode [id, constant] debug) before :=
  Effect.bind_success _ _ _ _ _ loaded

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ShiftInput
