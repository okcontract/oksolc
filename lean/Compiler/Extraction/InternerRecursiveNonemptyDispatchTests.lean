/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursiveNonemptyReturnTests
import Compiler.Extraction.InternerAlgebraicInput

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveNonemptyTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops lifetime growth GraphFacts)
open RecursiveTests (Call debug)

attribute [local irreducible] ready rootArguments childArguments Arguments.operation

/-- The shared source-bound Algebraic.apply input route, selected by EQ below.
Other dispatcher/helper call-site inputs remain outside this connection. -/
def childContext (safety : Bool) : AlgebraicInput.Context (Publication.Effects Nat) :=
  ⟨Publication.external ops.arguments, 160, 7, childPrimitives safety, Interner.Queries.queries⟩
def childConstructors (safety : Bool) : Associative.Constructors AssemblyItem.Fields.Values (GraphAction (Publication.Effects Nat)) :=
  ShiftInput.constructors (childContext safety)
def parentSeed (safety : Bool) : Primitives (Publication.Effects Nat) where
  simplify := fun key _ before => Dispatch.simplify (Interner.representativeReads before.graph)
    (childConstructors safety) 64 key.instruction key.arguments debug before
  publish := Publication.publish ops.probe ops.arguments 7 rootSource
  insert := fun _ _ _ before => (.error (.language .unsupported), before)
def parentPrimitives (safety : Bool) (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue) :=
  callerPrimitives ops failing safety 7 6 rootSource address Insertion.Tests.model native (parentSeed safety) (some growth)
def full (safety : Bool) := operation (Publication.external ops.arguments) 160 7 (parentPrimitives safety)
  Interner.Queries.queries rootSource 20 [0, 4] debug (parent safety).before
def complete (safety : Bool) := Arguments.operation (Publication.external ops.arguments) 160 7
  (fun _ => parentPrimitives safety) Interner.Queries.queries 20 [0, 4] debug (ready safety)

/-- Derive the selected literal's native input at the actual reached parent
state, then identify the complete recursive call used by the dispatcher. -/
theorem child_source (safety : Bool) :
    Arguments.Prepared [0] (parent safety).taken.2.world childSource (child safety).before ∧
    AlgebraicInput.run (childContext safety) .iszero_left 0 4 debug (parent safety).taken.2.world = childFull safety := by
  have literal : Arguments.prepare [0] (parent safety).taken.2.world = (.ok childSource, (child safety).before) := by
    simpa only [child, childArguments] using
      (Prod.ext (literals_observed safety).2.2.1 rfl : childArguments safety = (.ok childSource, (childArguments safety).2))
  have input := AlgebraicInput.unary_input (childContext safety) .iszero_left 0 4 debug (Or.inr (Or.inl rfl))
    (parent safety).taken.2.world (child safety).before childSource (parent_established safety).taken.valid literal
  refine ⟨input.1, ?_⟩
  rw [input.2]
  symm
  exact Arguments.operation_prepared _ _ _ _ _ _ _ _ _ _ _ literal

theorem iszero_result (reads : Nested.Reads)
    (constructors : Associative.Constructors AssemblyItem.Fields.Values (GraphAction (Publication.Effects Nat)))
    (before after : World (Publication.Effects Nat)) (result : Except Fault NodeId)
    (left : reads.constant 0 = .ok none) (right : reads.constant 4 = .ok (some 0))
    (called : zigApply .iszero_left (Dispatch.algebraicBuilder constructors) 0 4 debug before =
      (result, after))
    (input : Nested.OperandRead (GraphAction (Publication.Effects Nat)) := Nested.logicalOperand)
    (address : Nat := 0) :
    (Dispatch.simplifyWithInputs reads constructors 64 20 [0, 4] debug input address) before = (result.map some, after) := by
  have collected : Dispatch.collectConstants reads [0, 4] = .ok none := by
    unfold Dispatch.collectConstants; rw [left]; rfl
  have first : (Dispatch.constantStage reads constructors 20 [0, 4] debug) before = (.ok none, before) := by
    simp only [Dispatch.constantStage, collected]; rfl
  have binary : (Dispatch.binaryStageWithInputs reads constructors 64 20 0 4 debug Dispatch.defaultOptions input) before =
      (result.map some, after) := by
    unfold Dispatch.binaryStageWithInputs
    simp (config := { zeta := false }) only [left, right]
    change (do let id ← constructors.operation 21 [0] debug; pure (some id) : GraphAction (Publication.Effects Nat) (Option NodeId)) before = _
    cases result with
    | error fault => exact Effect.bind_failure _ _ _ _ _ called
    | ok id => exact (Effect.bind_success _ _ _ _ _ called).trans rfl
  unfold Dispatch.simplifyWithInputs Dispatch.simplifyOptionsWithInputs
  cases result <;> simp only [Dispatch.orNext, bind, Effect.bind, first, binary, Except.map, pure, Effect.pure]

theorem iszero_failure (reads : Nested.Reads)
    (constructors : Associative.Constructors AssemblyItem.Fields.Values (GraphAction (Publication.Effects Nat)))
    (before after : World (Publication.Effects Nat)) {fault : Fault}
    (left : reads.constant 0 = .ok none) (right : reads.constant 4 = .ok (some 0))
    (called : zigApply .iszero_left (Dispatch.algebraicBuilder constructors) 0 4 debug before =
      (.error fault, after))
    (input : Nested.OperandRead (GraphAction (Publication.Effects Nat)) := Nested.logicalOperand)
    (address : Nat := 0) :
    (Dispatch.simplifyWithInputs reads constructors 64 20 [0, 4] debug input address) before = (.error fault, after) :=
  iszero_result reads constructors before after (.error fault) left right called input address

theorem parent_continuation (safety : Bool) (after : Native.Frame Nat)
    (called : childFull safety = (.error (.language .outOfMemory), childReturned safety after)) :
    (parent safety).continuation (parentPrimitives safety (parent safety).address (parent safety).native) =
      (.error (.language .outOfMemory), ⟨childReturned safety after, (parent safety).taken.2.scope⟩) := by
  have scope := (parent_established safety).entry.origin.scope
  have simplified : (parentSeed safety).simplify (parent safety).key (parent safety).normalized (parent safety).taken.2.world =
      (.error (.language .outOfMemory), childReturned safety after) :=
    iszero_failure _ _ _ _ (first_constant safety _ (parent_established safety).taken).1 (parent_zero safety).1
      ((child_source safety).2.trans called)
  simp only [Call.continuation, Interner.FindCode.controlMiss, Caller.execution, OwnedCall.execution,
    show (parent safety).request.item.kind = 1 from rfl, beq_self_eq_true, Bool.and_self, ↓reduceIte,
    parentPrimitives, callerPrimitives, graph, scope, simplified, bind, Effect.bind]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveNonemptyTests
