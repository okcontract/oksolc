/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursiveChildReturnTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops cells lifetime growth GraphFacts)

attribute [local irreducible] rootArguments RecursiveNonemptyTests.ready

/-- This path's child callbacks execute the complete constructor. Unvisited
operation paths remain explicitly unsupported in this scoped fixture. -/
def childConstructors (safety : Bool) : Associative.Constructors AssemblyItem.Fields.Values (GraphAction (Publication.Effects Nat)) where
  constant := fun value metadata before =>
    let ran := constant (Publication.external ops.arguments) 160 7 (childPrimitives safety) Interner.Queries.queries value metadata before
    (ran.1, ran.2.world)
  materialize := fun id value metadata before =>
    let ran := materialize (Publication.external ops.arguments) 160 7 (childPrimitives safety) Interner.Queries.queries id value metadata before
    (ran.1, ran.2.world)
  operation := fun _ _ _ before => (.error (.language .unsupported), before)
  borrowedOperation := fun _ _ _ _ before => (.error (.language .unsupported), before)

theorem child_constant_forwarded (safety : Bool) (value : Contract.Yul.Word)
    (metadata : AssemblyItem.Fields.Values) (before : World (Publication.Effects Nat)) :
    (childConstructors safety).constant value metadata before =
      (let ran := constant (Publication.external ops.arguments) 160 7 (childPrimitives safety)
         Interner.Queries.queries value metadata before
       (ran.1, ran.2.world)) := by
  unfold childConstructors
  with_reducible rfl

def parentSeed (safety : Bool) : Primitives (Publication.Effects Nat) where
  simplify := fun key _ before => Dispatch.simplify (Interner.representativeReads before.graph)
    (childConstructors safety) 64 key.instruction key.arguments debug before
  publish := Publication.publish ops.probe ops.arguments 7 rootSource
  insert := fun _ _ _ before => (.error (.language .unsupported), before)
def parentPrimitives (safety : Bool) (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue) :=
  callerPrimitives ops failing safety 7 6 rootSource address Insertion.Tests.model native (parentSeed safety) (some growth)
def full (safety : Bool) := operation (Publication.external ops.arguments) 160 7 (parentPrimitives safety)
  Interner.Queries.queries rootSource 20 [0, 0] debug (parent safety).before
def complete (safety : Bool) := Arguments.operation (Publication.external ops.arguments) 160 7
  (fun _ => parentPrimitives safety) Interner.Queries.queries 20 [0, 0] debug (old safety)

/-- The only queried representative is related to the native descriptor/item
loads at the parent's reached take state, not an independently assumed oracle. -/
theorem parent_constant (safety : Bool) :
    (Interner.representativeReads (parent safety).taken.2.world.graph).constant 0 = .ok none ∧
    Constant.value (parent safety).taken.2.world.memory.memory (Owner.headerAddress ⟨6, 0⟩) 0 = .ok (.ok none) :=
  RecursiveNonemptyTests.first_constant safety _ (parent_established safety).taken

/-- Ordered source dispatch selects exactly makeConstant(1). Errors retain the
child's reached state and stop later rules, publication and parent insertion. -/
theorem equal_failure (reads : Nested.Reads)
    (constructors : Associative.Constructors AssemblyItem.Fields.Values (GraphAction (Publication.Effects Nat)))
    (metadata : AssemblyItem.Fields.Values) (before after : World (Publication.Effects Nat)) {fault : Fault}
    (missed : reads.constant 0 = .ok none) (equality : reads.overrideEquality = none)
    (called : constructors.constant 1 metadata before = (.error fault, after))
    (input : Nested.OperandRead (GraphAction (Publication.Effects Nat)) := Nested.logicalOperand)
    (address : Nat := 0) :
    (Dispatch.simplifyWithInputs reads constructors 64 20 [0, 0] metadata input address) before = (.error fault, after) := by
  have collected : Dispatch.collectConstants reads [0, 0] = .ok none := by
    unfold Dispatch.collectConstants; rw [missed]; rfl
  have first : (Dispatch.constantStage reads constructors 20 [0, 0] metadata) before = (.ok none, before) := by
    simp only [Dispatch.constantStage, collected]
    rfl
  have binary : (Dispatch.binaryStageWithInputs reads constructors 64 20 0 0 metadata Dispatch.defaultOptions input) before =
      (.error fault, after) := by
    unfold Dispatch.binaryStageWithInputs
    simp only [Dispatch.opSDIV, Dispatch.opAND, Dispatch.opBYTE, Dispatch.opSLT, Dispatch.opSGT, Dispatch.opXOR, Dispatch.opOR,
      Dispatch.opSIGNEXTEND, Dispatch.opMOD, Dispatch.opSHL, Dispatch.opSHR, Dispatch.opMUL, Dispatch.opDIV, Dispatch.opSUB,
      Associative.isAssociative, Bool.false_eq_true, ↓reduceIte, Bool.false_or,
      List.contains_cons, List.contains_nil, BitVec.reduceBEq]
    simp only [missed, Nested.sameExpression, equality]
    change (do let id ← constructors.constant 1 metadata; pure (some id) : GraphAction (Publication.Effects Nat) (Option NodeId)) before = _
    simp only [bind, Effect.bind, called]
  unfold Dispatch.simplifyWithInputs Dispatch.simplifyOptionsWithInputs
  simp only [Dispatch.orNext, bind, Effect.bind, first, binary]

theorem parent_simplified (safety : Bool) (after : Native.Frame Nat)
    (called : childFull safety = (.error (.language .outOfMemory),
      ⟨childReturned safety after, ⟨none, some (child safety).normalized, true⟩⟩)) :
    (parentSeed safety).simplify (parent safety).key (parent safety).normalized (parent safety).taken.2.world =
      (.error (.language .outOfMemory), childReturned safety after) := by
  have facts := (parent_established safety).taken
  apply equal_failure _ _ _ _ _ (parent_constant safety).1
  · simp only [Interner.representativeReads, facts.projected, Nested.storageReads]
  · exact congrArg (fun result => (result.1, result.2.world)) called

theorem parent_continuation (safety : Bool) (after : Native.Frame Nat)
    (called : childFull safety = (.error (.language .outOfMemory),
      ⟨childReturned safety after, ⟨none, some (child safety).normalized, true⟩⟩)) :
    (parent safety).continuation (parentPrimitives safety (parent safety).address (parent safety).native) =
      (.error (.language .outOfMemory), ⟨childReturned safety after, (parent safety).taken.2.scope⟩) :=
  (parent safety).simplify_error _ _ _ rfl (parent_established safety).entry.origin.scope
    (parent_simplified safety after called)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveTests
