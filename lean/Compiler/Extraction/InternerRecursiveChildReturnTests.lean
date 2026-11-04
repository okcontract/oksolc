/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursiveChildAllocationTests
import Compiler.Extraction.InternerRecursiveCallReturnTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops cells lifetime growth GraphFacts)

attribute [local irreducible] rootArguments RecursiveNonemptyTests.ready

def childPrimitives (safety : Bool) (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue) :=
  callerPrimitives ops failing safety 7 6 ⟨0, 0, 0⟩ address Insertion.Tests.model native childSeed (some growth)
def childFull (safety : Bool) := constant (Publication.external ops.arguments) 160 7 (childPrimitives safety)
  Interner.Queries.queries 1 debug (child safety).before
def childReturned (safety : Bool) (after : Native.Frame Nat) := (child safety).returnedWorld (failedWorld safety after)

theorem child_result (safety : Bool) (after : Native.Frame Nat)
    (ran : executed safety = ((.ok (some .allocationFailure), closed), after)) :
    childFull safety = (.error (.language .outOfMemory),
      ⟨childReturned safety after, ⟨none, some (child safety).normalized, true⟩⟩) := by
  have established := child_established safety
  have room : Interner.Queries.queries.atCapacity (child safety).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ established.constructed.projected, RecursiveNonemptyTests.rows_count]; decide
  have routed := (child safety).route (childPrimitives safety) (observed safety true) established.item.graph room rfl
  have finished := established.entry.finish_native ops failing safety 7 6 (child safety).source (child safety).address
    Insertion.Tests.model (child safety).request (child safety).request.arguments (child safety).native (child safety).key
    (child safety).normalized (child safety).lookup (child safety).constructed (child safety).taken.2 true (some growth)
  rw [child_insert safety after ran] at finished
  change childFull safety =
    (let done := finishInsertion ops failing safety 7 6 (child safety).source (child safety).address Insertion.Tests.model
      (child safety).native (child safety).key true (child safety).taken.2 (some growth)
     if ordinary done.1 then (done.1, (child safety).returned done.2) else done) at routed
  rw [finished] at routed
  exact routed

/-- The complete constant constructor returns through both child frames. Every
allocation and registry owner live at entry survives, including the parent's
normalized arguments and constructor local. No child result or final Good is
assumed. -/
theorem child_contract (safety : Bool) : ∃ after,
    childFull safety = (.error (.language .outOfMemory),
      ⟨childReturned safety after, ⟨none, some (child safety).normalized, true⟩⟩) ∧
    GraphFacts safety ReachablePrefixTests.backing 5 (childReturned safety after) (RecursiveNonemptyTests.rows safety) ∧
    (childReturned safety after).memory.effects.keys = (child safety).before.memory.effects.keys ∧
    (∀ id native, (child safety).before.memory.memory.heap.lookup id = some native →
      (childReturned safety after).memory.memory.heap.lookup id = some native) ∧
    (∀ id block, (child safety).before.memory.heap id = some block →
      (childReturned safety after).memory.heap id = some block) := by
  obtain ⟨after, ran, valid, _, _, keys, native, registry, _⟩ := child_allocation safety
  have established := child_established safety
  have bounded : (RecursiveNonemptyTests.rows safety).length ≤ 5 := by rw [RecursiveNonemptyTests.rows_count]; decide
  have nativeBefore : ∀ id cell, (child safety).before.memory.memory.heap.lookup id = some cell →
      (failedWorld safety after).memory.memory.heap.lookup id = some cell := by
    intro id cell found; exact native id cell (established.item.memory id cell found)
  have registeredBefore : ∀ id block, (child safety).before.memory.heap id = some block →
      (childReturned safety after).memory.heap id = some block := by
    intro id block found; apply registry id block; rw [established.item.heap]; exact found
  have frame := (child safety).returned_frame (failedWorld safety after) (parent_established safety).taken.valid nativeBefore
  have reachedValid := (child safety).returned_valid (failedWorld safety after) valid
  refine ⟨after, child_result safety after ran, ?_, keys.trans (congrArg Publication.Effects.keys established.item.effects), frame, registeredBefore⟩
  apply (parent_established safety).taken.frame bounded reachedValid
  · exact established.taken.projected
  · exact congrArg Interner.Heap.table (established.entry.origin.graph.trans established.item.graph)
  · exact keys.trans (congrArg Publication.Effects.keys established.item.effects)
  · exact frame
  · exact registeredBefore

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveTests
