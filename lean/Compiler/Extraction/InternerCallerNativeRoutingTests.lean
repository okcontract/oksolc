/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerNativeRoutingReturnTests
import Compiler.Extraction.InternerCallerInsertionCapacityCompletionTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.RoutingTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open AssemblyItem.Creation.NativeFields.Tests (input source)
open CallerInputTests (values)

def cached (safety empty : Bool) (find : Recursive.Find (Publication.Effects Nat)) :=
  ConstructorFrame.find (Publication.external ops.arguments) 160 7
    (callerPrimitives ops allocate safety 7 6 (parent empty) source Insertion.Tests.model input (seed empty find) (some growth))
    Interner.Queries.queries (parent empty) (CallerInputTests.request empty) (before safety empty 4)

theorem cached_entry (safety empty : Bool) :
    (before safety empty 4).graph.table (CallerInputTests.key empty) = some 4 ∧
      (prepared safety empty 4).2.scope = { lookup := some (lookup empty) } := by
  cases safety <;> cases empty <;> constructor <;> insertion_kernel_rfl

/-- The earlier repeated-key fixture is a cache hit under full find. It never
reaches take or insertion, and cannot witness full-caller growth. -/
theorem cached_result (safety empty : Bool) (find : Recursive.Find (Publication.Effects Nat)) :
    (cached safety empty find).1 = .ok 4 ∧
    (cached safety empty find).2.world.graph = (before safety empty 4).graph ∧
    (cached safety empty find).2.scope = ⟨none, none, false⟩ := by
  have calls := prefix_results safety empty 4 (by decide)
  have observed := cached_entry safety empty
  have closed := deinit_detached (Publication.external ops.arguments) 7 (prepared safety empty 4).2 (lookup empty)
    (by rw [observed.2]) rfl
  have outer : finish (Publication.external ops.arguments) 7 (Except.ok 4 : Except OwnedCall.Fault NodeId)
      (prepared safety empty 4).2 =
        (.ok 4, ⟨(prepared safety empty 4).2.world, ⟨none, none, false⟩⟩) := by
    simp only [finish, ordinary, ↓reduceIte, cleanup, observed.2, Bool.false_eq_true, closed]
  have routed := Caller.find_cached (Publication.external ops.arguments) 160 7
    (callerPrimitives ops allocate safety 7 6 (parent empty) source Insertion.Tests.model input (seed empty find) (some growth))
    Interner.Queries.queries (parent empty) ⟨(before safety empty 4).memory.memory.nextId, 0, 2⟩ (CallerInputTests.request empty)
    { before safety empty 4 with memory := { (before safety empty 4).memory with memory := stack safety empty 4 } }
    (values empty) (prepared safety empty 4).2 (CallerInputTests.key empty) 4 (room safety empty)
    (Prod.ext calls.2.1 rfl) (classified empty) (CallerInputTests.prefix_results safety empty).2.2.2.2 observed.1
  rw [outer] at routed
  have graph := Caller.initialize_graph (Publication.external ops.arguments) 160 7 (parent empty)
    ⟨(before safety empty 4).memory.memory.nextId, 0, 2⟩ (CallerInputTests.request empty)
    ⟨{ before safety empty 4 with memory := { (before safety empty 4).memory with memory := stack safety empty 4 } }, { lookup := none }⟩
  change (prepared safety empty 4).2.world.graph = (before safety empty 4).graph at graph
  simp only [cached, ConstructorFrame.find, room, Bool.false_eq_true, ↓reduceIte, calls.1, routed, ordinary]
  exact ⟨trivial, graph, trivial⟩

def rejected (safety empty : Bool) (find : Recursive.Find (Publication.Effects Nat)) :=
  ConstructorFrame.find (Publication.external ops.arguments) 160 7
    (callerPrimitives ops allocate safety 7 (CompletionTests.missingContainer safety empty) (parent empty) source
      Insertion.Tests.model input (seed empty find) (some growth))
    Interner.Queries.queries (parent empty) (request empty) (before safety empty 4)

/-- Count rejection after the actual dispatcher retains the reached normalized
owner, detached handle and child frame. It is not an ordinary allocation error. -/
theorem rejected_result (safety empty : Bool) (find : Recursive.Find (Publication.Effects Nat)) :
    rejected safety empty find = (.error (.language .safetyFault),
      ⟨(taken safety empty 4).2.world, ⟨some (lookup empty), some (normalized safety empty 4), true⟩⟩) ∧
    Memory.SliceValid 7 (rejected safety empty find).2.world.memory.heap (normalized safety empty 4) ∧
    ordinary (rejected safety empty find).1 = false := by
  have incoming := entry safety empty
  have prior := initialized_prefix safety empty 4 (by decide)
  have calls := prefix_results safety empty 4 (by decide)
  have finished := incoming.rejected_completed ops allocate safety 7 (CompletionTests.missingContainer safety empty) (parent empty) source
    Insertion.Tests.model (request empty) (values empty) input (key empty) (normalized safety empty 4) (lookup empty)
    (before safety empty 4) (taken safety empty 4).2 true (cells safety empty 4) (some growth)
    prior.facts.projected (.memory .unallocated) (CompletionTests.missing_owner safety empty)
  have routed := incoming.find_after_simplify ops allocate safety 160 7 (CompletionTests.missingContainer safety empty)
    (parent empty) source Insertion.Tests.model input (seed empty find) Interner.Queries.queries (request empty)
    (before safety empty 4) (taken safety empty 4).2.world (stack safety empty 4) _ (values empty)
    (prepared safety empty 4).2 (taken safety empty 4).2 (key empty) (normalized safety empty 4) (lookup empty) (some growth)
    (room safety empty) calls.1 (Prod.ext calls.2.1 rfl) (classified empty) (made empty) (missed safety empty)
    (Prod.ext calls.2.2.1 rfl) rfl (simplified safety empty find)
  rw [finished] at routed
  change rejected safety empty find = _ at routed
  refine ⟨routed, ?_, ?_⟩
  · rw [routed]; exact incoming.origin.held.2.1
  · rw [routed]; rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.RoutingTests
