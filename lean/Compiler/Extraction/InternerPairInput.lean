/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerShiftInput

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.PairInput
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul Compiler.ZigAir.Memory.WordArray

abbrev Context := ShiftInput.Context

/-- Scalar literal sites use the complete existing constructor routes. The
source materializer ignores its expression ID and calls makeConstant. Borrowed
array calls remain outside this boundary. -/
def constructors (context : Context σ) : Associative.Constructors AssemblyItem.Fields.Values (GraphAction σ) :=
  { ShiftInput.constructors context with
    materialize := fun id value debug before =>
      let ran := ConstructorItem.materialize context.external context.budget context.allocator
        (context.primitives ⟨0, 0, 0⟩) context.queries id value debug before
      (ran.1, ran.2.world) }

attribute [local irreducible] Arguments.operation ConstructorItem.constant

theorem constant_forwarded (context : Context σ) (value : Word) (debug : AssemblyItem.Fields.Values) :
    (constructors context).constant value debug = (ShiftInput.constructors context).constant value debug := rfl

theorem materialize_forwarded (context : Context σ) (id : NodeId) (value : Word)
    (debug : AssemblyItem.Fields.Values) :
    (constructors context).materialize id value debug = (constructors context).constant value debug := by
  unfold constructors ShiftInput.constructors ConstructorItem.materialize
  with_reducible rfl

theorem scalars_forwarded (context : Context σ) (opcode : Opcode) (a b : NodeId)
    (debug : AssemblyItem.Fields.Values) :
    ConstructorPair.scalars (constructors context) opcode a b debug =
      Arguments.operation context.external context.budget context.allocator context.primitives context.queries
        opcode [a, b] debug := by
  unfold ConstructorPair.scalars constructors ShiftInput.constructors
  with_reducible rfl

/-- Contents, separation, extent, and the reached world come from the actual
pair allocation and stores. Later sites use the proper child's returned world.
Validity of that world is still an obligation of the recursive induction. -/
theorem input (context : Context σ) (opcode : Opcode) (a b : NodeId)
    (debug : AssemblyItem.Fields.Values) (before prepared : World σ) (source : View)
    (valid : Valid before.memory) (initialized : Arguments.prepare [a, b] before = (.ok source, prepared)) :
    Arguments.Prepared [a, b] before source prepared ∧
    ConstructorPair.scalars (constructors context) opcode a b debug before =
      Arguments.returned [a, b] before.memory.memory.nextId
        (ConstructorItem.operation context.external context.budget context.allocator (context.primitives source)
          context.queries source opcode [a, b] debug prepared) :=
  ⟨Arguments.prepare_success _ _ _ _ valid initialized,
    Arguments.operation_prepared _ _ _ _ _ _ _ _ _ _ _ initialized⟩

theorem first_error (context : Context σ) (opcode : Opcode) (child : GraphAction σ NodeId)
    (b : NodeId) (debug : AssemblyItem.Fields.Values) (before after : World σ) (fault : Fault)
    (called : child before = (.error fault, after)) :
    ConstructorPair.first (constructors context) opcode child b debug before = (.error fault, after) :=
  Effect.bind_failure _ _ _ _ _ called

theorem second_error (context : Context σ) (opcode : Opcode) (a : NodeId)
    (child : GraphAction σ NodeId) (debug : AssemblyItem.Fields.Values) (before after : World σ) (fault : Fault)
    (called : child before = (.error fault, after)) :
    ConstructorPair.second (constructors context) opcode a child debug before = (.error fault, after) :=
  Effect.bind_failure _ _ _ _ _ called

theorem first_input (context : Context σ) (opcode : Opcode) (child : GraphAction σ NodeId)
    (a b : NodeId) (debug : AssemblyItem.Fields.Values) (before middle prepared : World σ) (source : View)
    (called : child before = (.ok a, middle)) (valid : Valid middle.memory)
    (initialized : Arguments.prepare [a, b] middle = (.ok source, prepared)) :
    Arguments.Prepared [a, b] middle source prepared ∧
    ConstructorPair.first (constructors context) opcode child b debug before =
      Arguments.returned [a, b] middle.memory.memory.nextId
        (ConstructorItem.operation context.external context.budget context.allocator (context.primitives source)
          context.queries source opcode [a, b] debug prepared) := by
  have reached := input context opcode a b debug middle prepared source valid initialized
  exact ⟨reached.1, (Effect.bind_success _ _ _ _ _ called).trans reached.2⟩

theorem second_input (context : Context σ) (opcode : Opcode) (a b : NodeId)
    (child : GraphAction σ NodeId) (debug : AssemblyItem.Fields.Values) (before middle prepared : World σ) (source : View)
    (called : child before = (.ok b, middle)) (valid : Valid middle.memory)
    (initialized : Arguments.prepare [a, b] middle = (.ok source, prepared)) :
    Arguments.Prepared [a, b] middle source prepared ∧
    ConstructorPair.second (constructors context) opcode a child debug before =
      Arguments.returned [a, b] middle.memory.memory.nextId
        (ConstructorItem.operation context.external context.budget context.allocator (context.primitives source)
          context.queries source opcode [a, b] debug prepared) := by
  have reached := input context opcode a b debug middle prepared source valid initialized
  exact ⟨reached.1, (Effect.bind_success _ _ _ _ _ called).trans reached.2⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.PairInput
