/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursiveBorrowedReturnTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveBorrowedTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops lifetime growth GraphFacts)
open RecursiveTests (Call debug)

attribute [local irreducible] ready rootArguments Arguments.operation

def childConstructors (safety : Bool) := ViewInput.constructors (childContext safety)
def parentSeed (safety : Bool) : Primitives (Publication.Effects Nat) where
  simplify := fun key _ before => Dispatch.simplify (Interner.representativeReads before.graph)
    (childConstructors safety) 64 key.instruction key.arguments debug before
  publish := Publication.publish ops.probe ops.arguments 7 rootSource
  insert := fun _ _ _ before => (.error (.language .unsupported), before)
def parentPrimitives (safety : Bool) (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue) :=
  callerPrimitives ops failing safety 7 6 rootSource address Insertion.Tests.model native (parentSeed safety) (some growth)
def full (safety : Bool) := operation (Publication.external ops.arguments) 160 7 (parentPrimitives safety)
  Interner.Queries.queries rootSource 21 [4] debug (parent safety).before
def complete (safety : Bool) := Arguments.operation (Publication.external ops.arguments) 160 7
  (fun _ => parentPrimitives safety) Interner.Queries.queries 21 [4] debug (ready safety)

theorem child_source (safety : Bool) :
    Good childSource [0, 1] (parent safety).taken.2.world ∧
    (childConstructors safety).borrowedOperation xorOperands.address 20 xorOperands.items debug
      (parent safety).taken.2.world = childFull safety :=
  ⟨(child_input safety).2.1, congrFun (ViewInput.borrowed_forwards (childContext safety) xorOperands 20 debug) _⟩

theorem borrowed_failure {fault : Fault} (reads : Nested.Reads)
    (constructors : Associative.Constructors AssemblyItem.Fields.Values (GraphAction (Publication.Effects Nat)))
    (before after : World (Publication.Effects Nat))
    (constant : reads.constant 4 = .ok none) (iszero : reads.operation 4 21 = .ok none)
    (xor : reads.operation 4 24 = .ok (some xorOperands))
    (called : constructors.borrowedOperation xorOperands.address 20 xorOperands.items debug before =
      (.error fault, after))
    (input : Nested.OperandRead (GraphAction (Publication.Effects Nat)) := Nested.logicalOperand)
    (address : Nat := 0) :
    (Dispatch.simplifyWithInputs reads constructors 64 21 [4] debug input address) before = (.error fault, after) := by
  have collected : Dispatch.collectConstants reads [4] = .ok none := by
    unfold Dispatch.collectConstants; rw [constant]; rfl
  have first : (Dispatch.constantStage reads constructors 21 [4] debug) before = (.ok none, before) := by
    simp only [Dispatch.constantStage, collected]; rfl
  have unary : (Dispatch.unaryStageWithInputs reads constructors 21 4 debug input) before = (.error fault, after) := by
    simp only [Dispatch.unaryStageWithInputs, Dispatch.opNOT, Dispatch.opISZERO, Dispatch.opXOR,
      BitVec.reduceBEq, Bool.false_eq_true, ↓reduceIte, iszero, xor, Nested.readAction]
    change (do let id ← constructors.borrowedOperation xorOperands.address 20 xorOperands.items debug
               pure (some id) : GraphAction (Publication.Effects Nat) (Option NodeId)) before = _
    exact Effect.bind_failure _ _ _ _ _ called
  unfold Dispatch.simplifyWithInputs Dispatch.simplifyOptionsWithInputs
  simp only [Dispatch.orNext, bind, Effect.bind, first]
  exact (Effect.bind_failure _ _ _ _ _ unary).trans rfl

theorem parent_continuation (safety : Bool) (after : Native.Frame Nat)
    (called : childFull safety = (.error (.language .outOfMemory), childReturned safety after)) :
    (parent safety).continuation (parentPrimitives safety (parent safety).address (parent safety).native) =
      (.error (.language .outOfMemory), ⟨childReturned safety after, (parent safety).taken.2.scope⟩) := by
  have scope := (parent_established safety).entry.origin.scope
  have simplified : (parentSeed safety).simplify (parent safety).key (parent safety).normalized (parent safety).taken.2.world =
      (.error (.language .outOfMemory), childReturned safety after) :=
    borrowed_failure _ _ _ _ (constants safety _ (parent_established safety).taken 4 (Or.inr (Or.inr rfl))).1
      (parent_iszero safety).1 (xor_query safety).1 ((child_source safety).2.trans called)
  simp only [Call.continuation, Interner.FindCode.controlMiss, Caller.execution, OwnedCall.execution,
    show (parent safety).request.item.kind = 1 from rfl, beq_self_eq_true, Bool.and_self, ↓reduceIte,
    parentPrimitives, callerPrimitives, graph, scope, simplified, bind, Effect.bind]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveBorrowedTests
