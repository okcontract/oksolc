/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerShiftInput

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.AlgebraicInput
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul Compiler.ZigAir.Memory.WordArray

abbrev Context := ShiftInput.Context

/-- All nine constructor sites in the admitted Algebraic.apply body. Its input
IDs are scalar parameters, including the selected negation operand after the
constant child. Each literal callback enters the existing allocation/store,
constructor-local item, normalization and return route. The source-extracted
body alone orders those callbacks; this is not a dispatcher-wide list adapter. -/
def builder (context : Context σ) : Builder (GraphAction σ) AssemblyItem.Fields.Values :=
  Dispatch.algebraicBuilder (ShiftInput.constructors context)

def run (context : Context σ) (replacement : Replacement) (left right : NodeId)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId :=
  zigApply replacement (builder context) left right debug

attribute [local irreducible] Arguments.operation ConstructorItem.constant

theorem source_body (context : Context σ) (replacement : Replacement) (left right : NodeId)
    (debug : AssemblyItem.Fields.Values) :
    run context replacement left right debug =
      zigApply replacement (Dispatch.algebraicBuilder (ShiftInput.constructors context)) left right debug := rfl

theorem operation_forwarded (context : Context σ) (opcode : BuildOp) (values : List NodeId)
    (debug : AssemblyItem.Fields.Values) :
    (builder context).makeOperation opcode values debug =
      Arguments.operation context.external context.budget context.allocator context.primitives context.queries
        (Interner.buildOpcode opcode) values debug := by
  cases opcode <;> rfl

theorem constant_forwarded (context : Context σ) (value : Word) (debug : AssemblyItem.Fields.Values)
    (before : World σ) :
    (builder context).makeConstant value debug before =
      (let called := ConstructorItem.constant context.external context.budget context.allocator
        (context.primitives ⟨0, 0, 0⟩) context.queries value debug before
       (called.1, called.2.world)) := rfl

theorem captures (context : Context σ) (left right : NodeId) (debug : AssemblyItem.Fields.Values) :
    run context .left left right debug = pure left ∧ run context .right left right debug = pure right := ⟨rfl, rfl⟩

theorem constants (context : Context σ) (replacement : Replacement) (left right : NodeId)
    (debug : AssemblyItem.Fields.Values)
    (selected : replacement = .zero ∨ replacement = .one ∨ replacement = .max) :
    run context replacement left right debug = (builder context).makeConstant
      (if replacement == .zero then 0 else if replacement == .one then 1 else BitVec.allOnes 256) debug := by
  rcases selected with rfl | rfl | rfl <;> rfl

/-- The shared initializer establishes contents, extent, address, separation
and validity at every reached literal site. The equality exposes the actual
local item and caller that consume that view, followed by ordinary cleanup.
For a later site, `before` is the earlier child's reached world, not its entry. -/
theorem literal_input (context : Context σ) (opcode : BuildOp) (values : List NodeId)
    (debug : AssemblyItem.Fields.Values) (before prepared : World σ) (source : View)
    (valid : Valid before.memory)
    (initialized : Arguments.prepare values before = (.ok source, prepared)) :
    Arguments.Prepared values before source prepared ∧
    (builder context).makeOperation opcode values debug before =
      Arguments.returned values before.memory.memory.nextId
        (ConstructorItem.operation context.external context.budget context.allocator (context.primitives source)
          context.queries source (Interner.buildOpcode opcode) values debug prepared) := by
  refine ⟨Arguments.prepare_success values before prepared source valid initialized, ?_⟩
  rw [operation_forwarded]
  exact Arguments.operation_prepared _ _ _ _ _ _ _ _ _ _ _ initialized

theorem unary (context : Context σ) (replacement : Replacement) (left right : NodeId)
    (debug : AssemblyItem.Fields.Values)
    (selected : replacement = .not_right ∨ replacement = .iszero_left ∨ replacement = .iszero_right) :
    run context replacement left right debug =
      (builder context).makeOperation (if replacement == .not_right then .NOT else .ISZERO)
        [if replacement == .iszero_left then left else right] debug := by
  rcases selected with rfl | rfl | rfl <;> rfl

theorem negation (context : Context σ) (replacement : Replacement) (left right : NodeId)
    (debug : AssemblyItem.Fields.Values) (selected : replacement = .neg_left ∨ replacement = .neg_right) :
    run context replacement left right debug = (do
      let zero ← (builder context).makeConstant 0 debug
      (builder context).makeOperation .SUB [zero, if replacement == .neg_left then left else right] debug) := by
  rcases selected with rfl | rfl <;> rfl

theorem boolean (context : Context σ) (replacement : Replacement) (left right : NodeId)
    (debug : AssemblyItem.Fields.Values) (selected : replacement = .bool_left ∨ replacement = .bool_right) :
    run context replacement left right debug = (do
      let first ← (builder context).makeOperation .ISZERO
        [if replacement == .bool_left then left else right] debug
      (builder context).makeOperation .ISZERO [first] debug) := by
  rcases selected with rfl | rfl <;> rfl

theorem unary_input (context : Context σ) (replacement : Replacement) (left right : NodeId)
    (debug : AssemblyItem.Fields.Values)
    (selected : replacement = .not_right ∨ replacement = .iszero_left ∨ replacement = .iszero_right)
    (before prepared : World σ) (source : View) (valid : Valid before.memory)
    (initialized : Arguments.prepare [if replacement == .iszero_left then left else right] before = (.ok source, prepared)) :
    Arguments.Prepared [if replacement == .iszero_left then left else right] before source prepared ∧
    run context replacement left right debug before =
      Arguments.returned [if replacement == .iszero_left then left else right] before.memory.memory.nextId
        (ConstructorItem.operation context.external context.budget context.allocator (context.primitives source)
          context.queries source (Interner.buildOpcode (if replacement == .not_right then .NOT else .ISZERO))
          [if replacement == .iszero_left then left else right] debug prepared) := by
  rw [unary _ _ _ _ _ selected]
  exact literal_input context _ _ debug before prepared source valid initialized

/-- A failed initializer child retains its reached graph and memory and never
prepares the outer SUB array. This includes observation rejection as well as
ordinary native errors; no cleanup is invented by the source bind. -/
theorem negation_error (context : Context σ) (replacement : Replacement) (left right : NodeId)
    (debug : AssemblyItem.Fields.Values) (selected : replacement = .neg_left ∨ replacement = .neg_right)
    (before after : World σ) (fault : Fault)
    (called : (builder context).makeConstant 0 debug before = (.error fault, after)) :
    run context replacement left right debug before = (.error fault, after) := by
  rw [negation _ _ _ _ _ selected]
  exact Effect.bind_failure _ _ _ _ _ called

theorem boolean_error (context : Context σ) (replacement : Replacement) (left right : NodeId)
    (debug : AssemblyItem.Fields.Values) (selected : replacement = .bool_left ∨ replacement = .bool_right)
    (before after : World σ) (fault : Fault)
    (called : (builder context).makeOperation .ISZERO
      [if replacement == .bool_left then left else right] debug before = (.error fault, after)) :
    run context replacement left right debug before = (.error fault, after) := by
  rw [boolean _ _ _ _ _ selected]
  exact Effect.bind_failure _ _ _ _ _ called

/-- The second input uses the ID and world returned by the full first call.
Its validity is an obligation of that proper child's induction hypothesis.
The outer input's Good, address and initialized words are derived here. -/
theorem negation_input (context : Context σ) (replacement : Replacement) (left right : NodeId)
    (debug : AssemblyItem.Fields.Values) (selected : replacement = .neg_left ∨ replacement = .neg_right)
    (before middle prepared : World σ) (zero : NodeId) (source : View)
    (called : (builder context).makeConstant 0 debug before = (.ok zero, middle))
    (valid : Valid middle.memory)
    (initialized : Arguments.prepare [zero, if replacement == .neg_left then left else right] middle = (.ok source, prepared)) :
    Arguments.Prepared [zero, if replacement == .neg_left then left else right] middle source prepared ∧
    run context replacement left right debug before =
      Arguments.returned [zero, if replacement == .neg_left then left else right] middle.memory.memory.nextId
        (ConstructorItem.operation context.external context.budget context.allocator (context.primitives source)
          context.queries source (Interner.buildOpcode .SUB)
          [zero, if replacement == .neg_left then left else right] debug prepared) := by
  have input := literal_input context .SUB _ debug middle prepared source valid initialized
  refine ⟨input.1, ?_⟩
  rw [negation _ _ _ _ _ selected]
  exact (Effect.bind_success _ _ _ _ _ called).trans input.2

theorem boolean_input (context : Context σ) (replacement : Replacement) (left right : NodeId)
    (debug : AssemblyItem.Fields.Values) (selected : replacement = .bool_left ∨ replacement = .bool_right)
    (before middle prepared : World σ) (first : NodeId) (source : View)
    (called : (builder context).makeOperation .ISZERO
      [if replacement == .bool_left then left else right] debug before = (.ok first, middle))
    (valid : Valid middle.memory) (initialized : Arguments.prepare [first] middle = (.ok source, prepared)) :
    Arguments.Prepared [first] middle source prepared ∧
    run context replacement left right debug before = Arguments.returned [first] middle.memory.memory.nextId
      (ConstructorItem.operation context.external context.budget context.allocator (context.primitives source)
        context.queries source (Interner.buildOpcode .ISZERO) [first] debug prepared) := by
  have input := literal_input context .ISZERO [first] debug middle prepared source valid initialized
  refine ⟨input.1, ?_⟩
  rw [boolean _ _ _ _ _ selected]
  exact (Effect.bind_success _ _ _ _ _ called).trans input.2

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.AlgebraicInput
