/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionFirstSuccessTests
import Compiler.Extraction.InternerCallerPublicationCompletion

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication.GraphTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray
open Insertion.Native.CallerInputTests (values request key object operands)
open Insertion.Native

/-- The starting graph is the actual initialized caller's successful first
insertion. The next caller borrows its native representative arguments and
replaces the same key, through publication and both outer ownership defers.
This fixture does not assert cache routing or a recursive constructor result. -/
def before (safety empty : Bool) := CallerFirstSuccessTests.reached safety empty
def source (empty : Bool) := view (operands empty)
def host := Normalization.Tests.success
def probe : OwnedKeys.Physical.Probe Nat := fun _ state => (true, state.effects * 10 + 1)
def stack (safety empty : Bool) := ((Compiler.ZigAir.Memory.allocate (before safety empty).memory.memory (.array 2 word)).toOption.getD
  (.pointer (.pointer true false (.array 2 word)) ⟨object empty + 3, 0⟩, (before safety empty).memory.memory)).2
def prepared (safety empty : Bool) := Caller.initLookup (external host) 160 7 (source empty)
  ⟨(before safety empty).memory.memory.nextId, 0, 2⟩ (request empty)
  ⟨{ before safety empty with memory := { (before safety empty).memory with memory := stack safety empty } }, { lookup := none }⟩
def taken (safety empty : Bool) := take (external host) 7 (prepared safety empty).2
def owned (empty : Bool) : ArgumentSlice := ⟨object empty + 4, values empty⟩
def remaining (empty : Bool) : Handle := ⟨source empty, values empty, none⟩
def execute (safety empty : Bool) :=
  let (result, reached) := (do let _ ← graph (fun slice => publish probe host 7 (source empty) (key empty) slice 0); handoff :
    Action (Effects Nat) Unit) (taken safety empty).2
  finish (external host) 7 result reached

theorem initial_facts (safety empty : Bool) :
    Memory.GraphResident 7 (before safety empty).memory.heap [CallerFirstSuccessTests.row safety empty] ∧
    OwnedKeys.Live 7 ⟨(before safety empty).memory.effects.keys, (before safety empty).memory.heap⟩ ∧
    OwnedKeys.Unique (before safety empty).memory.effects.keys ∧
    OwnedKeys.Apart (before safety empty).memory.effects.keys
      (fun address => ∃ cell ∈ [CallerFirstSuccessTests.row safety empty], cell.arguments ≠ [] ∧ address = cell.argumentsAddress) := by
  obtain ⟨after, ran, _, resident, _, _, _, _, _, _, _, _, _, live, unique, _, _, _, _, _, _, apart⟩ := CallerFirstSuccessTests.derived_contract safety empty
  have same : (before safety empty).memory = Insertion.memory after := by
    change Insertion.memory (CallerFirstSuccessTests.execute safety empty).2 = Insertion.memory after
    rw [ran]
  rw [same]
  refine ⟨resident, live, unique, ?_⟩
  intro query old found nonempty kept
  obtain ⟨cell, member, arguments, address⟩ := kept
  have equal := List.mem_singleton.mp member
  subst cell
  exact apart query old found nonempty ⟨arguments, address⟩

theorem prefix_results (safety empty : Bool) :
    Compiler.ZigAir.Memory.allocate (before safety empty).memory.memory (.array 2 word) =
      .ok (.pointer (.pointer true false (.array 2 word)) ⟨object empty + 3, 0⟩, stack safety empty) ∧
    (prepared safety empty).1 = .ok (values empty) ∧ (taken safety empty).1 = .ok () ∧
    (taken safety empty).2.scope = ⟨some (remaining empty), some (owned empty), false⟩ := by
  cases safety <;> cases empty <;>
    exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem derived_input (safety empty : Bool) :
    Caller.Origin 7 (source empty) (request empty) (values empty) (before safety empty) (taken safety empty).2 (owned empty) (remaining empty) ∧
    (taken safety empty).2.world.memory.effects.keys = (before safety empty).memory.effects.keys ∧
    Input 7 (source empty) (key empty) (owned empty) (taken safety empty).2.world := by
  have calls := prefix_results safety empty
  obtain ⟨slice, handle, origin, keys, input⟩ := caller_input host 160 7 (source empty) (request empty) (before safety empty)
    (stack safety empty) _ (values empty) (prepared safety empty).2 (taken safety empty).2 (key empty)
    (CallerFirstSuccessTests.native_borrow_good safety empty).2 (Normalization.Tests.external_admitted _) calls.1 (Prod.ext calls.2.1 rfl)
    (Prod.ext calls.2.2.1 rfl) (Insertion.Native.CallerInputTests.prefix_results safety empty).2.2.2.2
    ((initial_facts safety empty).2.1 (key empty)) (CallerFirstSuccessTests.borrowed_source_apart safety empty (key empty))
  have same := Local.mk.inj (origin.scope.symm.trans calls.2.2.2)
  cases Option.some.inj same.1
  cases Option.some.inj same.2.1
  exact ⟨origin, keys, input⟩

/-- Ownership and graph residency are conclusions of this same publication
execution, including replacement retirement and the caller's outer cleanup. -/
theorem derived_contract (safety empty : Bool) :
    (execute safety empty).1 = .ok () ∧
    Completion host 7 (source empty) (request empty) (key empty) (owned empty) 0
      (before safety empty) (taken safety empty).2.world true
      ((taken safety empty).2.world.memory.effects.allocator * 10 + 1) (execute safety empty).2 ∧
    Memory.GraphResident 7 (execute safety empty).2.world.memory.heap [CallerFirstSuccessTests.row safety empty] ∧
    (∀ cell ∈ [CallerFirstSuccessTests.row safety empty],
      (execute safety empty).2.world.memory.memory.heap.lookup cell.itemAddress = (taken safety empty).2.world.memory.memory.heap.lookup cell.itemAddress ∧
      (cell.arguments ≠ [] → (execute safety empty).2.world.memory.memory.heap.lookup cell.argumentsAddress =
        (taken safety empty).2.world.memory.memory.heap.lookup cell.argumentsAddress)) ∧
    (execute safety empty).2.world.memory.heap (object empty + 1) = (taken safety empty).2.world.memory.heap (object empty + 1) ∧
    (execute safety empty).2.world.memory.memory.heap.lookup (object empty + 1) =
      (taken safety empty).2.world.memory.memory.heap.lookup (object empty + 1) := by
  obtain ⟨origin, keys, input⟩ := derived_input safety empty
  obtain ⟨resident, live, unique, apart⟩ := initial_facts safety empty
  obtain ⟨after, finished, completion⟩ := complete_taken probe host 7 (source empty) (request empty) (values empty) (key empty)
    (owned empty) (remaining empty) 0 (before safety empty) (taken safety empty).2 true
    ((taken safety empty).2.world.memory.effects.allocator * 10 + 1) origin input keys live unique rfl
  have finished : execute safety empty = (.ok (), after) := finished
  obtain ⟨published, ran, completed, _⟩ := publish_success probe host 7 (source empty) (key empty) (owned empty) 0
    (taken safety empty).2.world ((taken safety empty).2.world.memory.effects.allocator * 10 + 1) origin.held.1.1 input origin.held.2.1 rfl
  have currentResident : Memory.GraphResident 7 (taken safety empty).2.world.memory.heap [CallerFirstSuccessTests.row safety empty] := by
    intro cell member
    refine ⟨origin.registry _ _ (resident cell member).1, ?_⟩
    rcases (resident cell member).2 with empty | stored
    · exact Or.inl empty
    · exact Or.inr (origin.registry _ _ stored)
  have preserved := completed.graph_resident (external host) 7 (key empty) _ _ published [CallerFirstSuccessTests.row safety empty]
    input.live currentResident (by simpa only [keys] using apart)
  have payloadStored : (taken safety empty).2.world.memory.heap (object empty + 1) = some ⟨7, .bytes 2⟩ := by
    cases safety <;> cases empty <;> insertion_kernel_rfl
  have payloadFrame := completed.non_arguments_frame (external host) 7 (key empty) _ _ published input.live
    (object empty + 1) ⟨7, .bytes 2⟩ payloadStored (by intro impossible; cases impossible)
  have memory : (execute safety empty).2.world.memory.heap = published.memory.heap ∧
      (execute safety empty).2.world.memory.memory = published.memory.memory := by
    simp only [execute, Effect.bind, graph, origin.scope, ran, commit, handoff, finish, ordinary,
      cleanup, deinit, deinitialize]
    exact ⟨rfl, rfl⟩
  refine ⟨congrArg Prod.fst finished, ?_, ?_, ?_, ?_, ?_⟩
  · rw [finished]; exact completion
  · rw [memory.1]; exact preserved.1
  · rw [memory.2]; exact preserved.2
  · rw [memory.1]; exact payloadFrame.1
  · rw [memory.2]; exact payloadFrame.2

theorem live_keys_and_borrow (safety empty : Bool) :
    OwnedKeys.Live 7 ⟨(execute safety empty).2.world.memory.effects.keys, (execute safety empty).2.world.memory.heap⟩ ∧
    OwnedKeys.Unique (execute safety empty).2.world.memory.effects.keys ∧
    Good (source empty) (values empty) (execute safety empty).2.world := by
  have completed := (derived_contract safety empty).2.1
  exact ⟨completed.live, completed.unique, completed.good⟩

theorem graph_key_separation (safety empty : Bool) :
    OwnedKeys.Apart (execute safety empty).2.world.memory.effects.keys
      (fun address => ∃ cell ∈ [CallerFirstSuccessTests.row safety empty], cell.arguments ≠ [] ∧ address = cell.argumentsAddress) := by
  obtain ⟨origin, keys, _⟩ := derived_input safety empty
  obtain ⟨resident, _, _, apart⟩ := initial_facts safety empty
  have completed := (derived_contract safety empty).2.1
  rw [completed.keys]
  simp only [↓reduceIte, keys]
  apply OwnedKeys.store_apart _ _ _ _ apart
  intro _ kept
  obtain ⟨cell, member, nonempty, address⟩ := kept
  exact origin.fresh _ _ ((resident cell member).2.resolve_left nonempty) address

theorem reached_observations (safety empty : Bool) :
    (execute safety empty).2.scope = ⟨none, some (owned empty), true⟩ ∧
    (execute safety empty).2.world.memory.effects.keys (key empty) = some ⟨(owned empty).address, 0⟩ ∧
    ((execute safety empty).2.world.memory.memory.heap.lookup 9).isSome = empty ∧
    [object empty, object empty + 1, object empty + 2, (operands empty).address].map
      (fun id => ((execute safety empty).2.world.memory.memory.heap.lookup id).isSome) = [true, true, true, true] ∧
    Operation.run (execute safety empty).2.world.memory.memory (Owner.headerAddress ⟨6, 0⟩) 0 254 =
      .ok (.ok (some (Operation.returned (operands empty)))) := by
  cases safety <;> cases empty <;>
    exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

/-- Deliberately violating graph/key separation lets an otherwise admitted
publication retire a live representative argument. This state is a negative
memory fixture, not an accepted compiler execution. -/
def aliased (safety : Bool) :=
  let world := (taken safety false).2.world
  { world with memory := { world.memory with effects := { world.memory.effects with
    keys := OwnedKeys.store world.memory.effects.keys (key false) ⟨(operands false).address, 0⟩ } } }
def aliasPublication (safety : Bool) := publish probe host 7 (Insertion.Native.CallerInputTests.argumentView false)
  (key false) (owned false) 0 (aliased safety)

theorem aliasing_retires_graph_argument (safety : Bool) :
    (aliasPublication safety).1 = .ok () ∧
    (aliasPublication safety).2.memory.heap (operands false).address = none ∧
    (aliasPublication safety).2.memory.memory.heap.lookup (operands false).address = none := by
  cases safety <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication.GraphTests
