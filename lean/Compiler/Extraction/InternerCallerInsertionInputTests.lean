/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionPreparation
import Compiler.Extraction.InternerInsertionFirstPrepared
import Compiler.Extraction.InternerInsertionPreparationTests
import Compiler.Extraction.InternerGraphInitOwnershipTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerInputTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray
open AssemblyItem.Creation.NativeFields.Tests (input source)

def raw (safety : Bool) : Session Nat := AssemblyClone.NativeFields.QueryTests.initial safety true
def sentinel : Compiler.ZigAir.Memory.Address := ⟨999, 19⟩
def world (safety : Bool) : World (Publication.Effects Nat) :=
  ((GraphInit.Ownership.run safety 7 (raw safety) ⟨6, 0⟩ sentinel).toOption.getD
    (7, ⟨GraphInit.emptyGraph, ⟨(raw safety).heap, (raw safety).memory, ⟨fun _ => none, (raw safety).effects⟩⟩⟩)).2
def argumentView (empty : Bool) : View := if empty then ⟨6, 19, 0⟩ else ⟨0, 0, 1⟩
def values (empty : Bool) : List NodeId := if empty then [] else [0]
def request (empty : Bool) : Interner.Request := ⟨input.item, values empty, 77⟩
def key (empty : Bool) : Key := (Interner.makeKey (request empty) (values empty)).toOption.getD ⟨0, 0, 0, [], 0⟩
def stack (safety : Bool) : Compiler.ZigAir.Memory.State :=
  ((Compiler.ZigAir.Memory.allocate (world safety).memory.memory (.array 2 word)).toOption.getD
    (.pointer (.pointer true false (.array 2 word)) ⟨8, 0⟩, (world safety).memory.memory)).2
def prepared (safety empty : Bool) := Caller.initLookup (Publication.external Normalization.Tests.success) 160 7
  (argumentView empty) ⟨8, 0, 2⟩ (request empty)
  ⟨{ world safety with memory := { (world safety).memory with memory := stack safety } }, { lookup := none }⟩
def taken (safety empty : Bool) := take (Publication.external Normalization.Tests.success) 7 (prepared safety empty).2
def normalized (empty : Bool) : ArgumentSlice := ⟨9, values empty⟩
def remaining (empty : Bool) : Handle := ⟨argumentView empty, values empty, none⟩

theorem initializer (safety : Bool) : GraphInit.Ownership.run safety 7 (raw safety) ⟨6, 0⟩ sentinel = .ok (7, world safety) := by
  cases safety <;> insertion_kernel_rfl

theorem source_inputs (safety empty : Bool) :
    Represents (world safety).memory.memory (argumentView empty) (request empty).arguments ∧
    AssemblyClone.NativeFields.Represents (world safety).memory.memory source input := by
  constructor
  · cases empty
    · refine ⟨rfl, ?_⟩
      intro index inside
      have only : index = 0 := by change index < 1 at inside; omega
      subst index
      have loaded : Compiler.ZigAir.Memory.load (world safety).memory.memory ((argumentView false).pointer 0) = .ok (number 0) := by
        cases safety <;> insertion_kernel_rfl
      exact loaded
    · exact ⟨rfl, by intro index impossible; cases impossible⟩
  · apply AssemblyItem.Creation.NativeFields.Tests.source_represented.frame
    cases safety <;> insertion_kernel_rfl

theorem prefix_results (safety empty : Bool) :
    Compiler.ZigAir.Memory.allocate (world safety).memory.memory (.array 2 word) =
      .ok (.pointer (.pointer true false (.array 2 word)) ⟨8, 0⟩, stack safety) ∧
    (prepared safety empty).1 = .ok (values empty) ∧ (taken safety empty).1 = .ok () ∧
    (taken safety empty).2.scope = ⟨some (remaining empty), some (normalized empty), false⟩ ∧
    Interner.makeKey (request empty) (values empty) = .ok (key empty) := by
  cases safety <;> cases empty <;>
    exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

/-- The initial table, its liveness/uniqueness and the normalized owner all
come from initialization and caller execution, including an empty source that
aliases the graph owner. No input publication or ownership predicate is given. -/
theorem derived_input (safety empty : Bool) :
    CallerInput 7 (argumentView empty) source (request empty) (values empty) input (key empty)
      (world safety) (taken safety empty).2 (normalized empty) (remaining empty) := by
  have ran := prefix_results safety empty
  obtain ⟨owned, handle, _, entry⟩ := initialized_caller_input Normalization.Tests.success 160 7 6 safety
    (raw safety) (AssemblyClone.NativeFields.QueryTests.ownerCell safety true) sentinel Insertion.Tests.model
    (argumentView empty) source (request empty) input (world safety) (stack safety) _ (values empty)
    (prepared safety empty).2 (taken safety empty).2 (key empty)
    (AssemblyClone.NativeFields.QueryTests.initial_valid safety true) (by cases safety <;> rfl) rfl rfl rfl
    (initializer safety) (source_inputs safety empty).1 (Normalization.Tests.external_admitted _)
    (source_inputs safety empty).2 rfl ran.1 (Prod.ext ran.2.1 rfl) (Prod.ext ran.2.2.1 rfl) ran.2.2.2.2
  have same := Local.mk.inj (entry.origin.scope.symm.trans ran.2.2.2.1)
  cases Option.some.inj same.1
  cases Option.some.inj same.2.1
  exact entry

def ops : Operations Nat := { Insertion.Tests.ops (some .publish) with arguments := Normalization.Tests.success }
def allocate : Backing.Registry.Allocate Nat := fun _ _ _ effects => (some 4096, effects * 10 + 7)
def handle (empty : Bool) : Handle := ⟨view (normalized empty), values empty, none⟩
def duplicated (safety empty : Bool) := takeOwned normalizationOwnershipCode (Publication.external ops.arguments) 7
  (handle empty) (taken safety empty).2.world.memory
def made (safety empty : Bool) := AssemblyItem.Creation.create (observe ops.create) 7 input.item (duplicated safety empty).2
def cloned (safety empty : Bool) := AssemblyClone.Physical.run (observe ops.copy) 7 input (made safety empty).2
def object (empty : Bool) : Nat := if empty then 9 else 11
def operands (empty : Bool) : ArgumentSlice := ⟨if empty then 9 else 10, values empty⟩
def copied (empty : Bool) : AssemblyClone.NativeFields.ItemValue :=
  { input with verbatim := some ⟨2, 3, ⟨object empty + 1, [8, 9], 0⟩⟩ }
def ready (safety empty : Bool) : Session (Publication.Effects Nat) :=
  (AssemblyClone.NativeFields.install (copied empty) (object empty) (cloned safety empty).2).toOption.getD (cloned safety empty).2
def execute (safety empty : Bool) := execution ops allocate safety 7 6 (argumentView empty) source Insertion.Tests.model
  input (key empty) (normalized empty) true [] (taken safety empty).2.world

theorem preparation (safety empty : Bool) :
    duplicated safety empty = (.ok (operands empty, handle empty), (duplicated safety empty).2) ∧
    made safety empty = (.ok (object empty), (made safety empty).2) ∧
    cloned safety empty = (.ok (copied empty), (cloned safety empty).2) ∧
    AssemblyClone.NativeFields.install (copied empty) (object empty) (cloned safety empty).2 = .ok (ready safety empty) := by
  cases safety <;> cases empty <;>
    exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem prepared_contract (safety empty : Bool) :
    AssemblyClone.NativeFields.Installed 7 (object empty) (copied empty) (cloned safety empty).2 (ready safety empty) ∧
    Memory.SliceValid 7 (ready safety empty).heap (operands empty) ∧
    Memory.SliceValid 7 (ready safety empty).heap (normalized empty) ∧
    OwnedKeys.Live 7 ⟨(ready safety empty).effects.keys, (ready safety empty).heap⟩ ∧
    OwnedKeys.Unique (ready safety empty).effects.keys ∧ (ready safety empty).effects.keys = (world safety).memory.effects.keys := by
  let value := ((key empty).eval Insertion.Tests.model (taken safety empty).2.world.graph.read).getD 0
  let projection : Storage.State → Frame Nat → Interner.Heap := fun owner state =>
    Interner.InsertionExecution.project [] (taken safety empty).2.world.graph.table
      (cell input (key empty) (normalized empty) value owner state) (key empty) owner
  have calls := preparation safety empty
  obtain ⟨installed, _, _, _, post, assigned, _, operandsLive, normalizedLive, _, _, live, unique, keys, _, _⟩ :=
    CallerInput.prepare ops allocate safety 7 6 (object empty) (argumentView empty) source (request empty) (values empty)
      input (copied empty) (key empty) (normalized empty) (operands empty) (remaining empty) (handle empty)
      (world safety) (taken safety empty).2 [] value projection (duplicated safety empty).2 (made safety empty).2
      (cloned safety empty).2 (derived_input safety empty) (Normalization.Tests.external_admitted _)
      calls.1 calls.2.1 calls.2.2.1
  have same := Except.ok.inj (assigned.symm.trans calls.2.2.2)
  exact same ▸ ⟨post, operandsLive, normalizedLive, live, unique, keys⟩

def owner (safety : Bool) : Compiler.ZigAir.Memory.Allocation :=
  ((world safety).memory.memory.heap.lookup 6).getD (AssemblyClone.NativeFields.QueryTests.ownerCell safety true)

theorem initialized_owner (safety : Bool) :
    (world safety).memory.memory.heap.lookup 6 = some (owner safety) ∧
    (owner safety).type = Owner.viewType safety ∧ (owner safety).writable = true ∧
    readItems (world safety).memory.memory (Owner.headerAddress ⟨6, 0⟩) = .ok (.slice itemsType sentinel 0) ∧
    readField (world safety).memory.memory (Owner.headerAddress ⟨6, 0⟩) capacityOffset = .ok (.scalar (.int false 64 0)) := by
  cases safety <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl,
    by insertion_kernel_rfl, by insertion_kernel_rfl⟩

/-- This entry observation is established by the same native initializer used
by the caller fixture, then transported across its actual preparation. -/
theorem initialized_lock (safety : Bool) :
    Owner.NativeLock.checkHeader (world safety).memory.memory (Owner.headerAddress ⟨6, 0⟩) = .ok () := by
  obtain ⟨result, executed, established⟩ := GraphInit.Ownership.initialize_verified safety 7 (raw safety) 6
    (AssemblyClone.NativeFields.QueryTests.ownerCell safety true) sentinel Insertion.Tests.model
    (AssemblyClone.NativeFields.QueryTests.initial_valid safety true) (by cases safety <;> rfl) rfl rfl rfl
  have equal : result = world safety := (Prod.mk.inj (Except.ok.inj (executed.symm.trans (initializer safety)))).2
  subst result
  rw [Owner.NativeLock.checkHeader_owner safety _ 6 (owner safety) (initialized_owner safety).1 (initialized_owner safety).2.1]
  exact established.unlocked

theorem backing_response (safety empty : Bool) :
    allocate 7 160 8 (ready safety empty).effects.allocator =
      (some 4096, (ready safety empty).effects.allocator * 10 + 7) ∧
    Compiler.ZigAir.Memory.RegionAllocation.Fits (ready safety empty).memory ⟨160, 8⟩ 4096 := by
  refine ⟨rfl, by decide, by decide, by decide, ?_⟩
  have bound : (ready safety empty).memory.heap.all (fun entry =>
      decide (entry.2.base + (entry.2.type.layout.getD ⟨0, 1⟩).bytes ≤ 4096)) = true := by
    cases safety <;> cases empty <;> decide +kernel
  intro entry present layout shaped
  have checked := (List.all_eq_true.mp bound) entry present
  simp only [shaped, Option.getD_some, decide_eq_true_eq] at checked
  exact Or.inr checked

def probeEffects (safety empty : Bool) : Nat := ((ready safety empty).effects.allocator * 10 + 7) * 10 + 8

theorem probe_result (safety empty : Bool) :
    ops.probe (key empty) (Publication.forget (memory (append safety allocate 7 6 [] input (key empty) (normalized empty)
      (((key empty).eval Insertion.Tests.model (taken safety empty).2.world.graph.read).getD 0) Storage.preparationOwnership
      (preparedFrame (object empty) (copied empty) (operands empty) (ready safety empty))).2)) =
      (false, probeEffects safety empty) := by
  cases safety <;> cases empty <;> insertion_kernel_rfl

/-- The actual initialized caller supplies insertion's ownership, item reads
and publication input. The complete native insertion execution then derives
clone/destructor owners, rollback and normalized cleanup at publication OOM. -/
theorem insertion_oom_from_caller (safety empty : Bool) : ∃ after,
    execute safety empty = ((.ok (some .allocationFailure),
      (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).run Storage.publicationOwnership), after) ∧
    Valid (memory after) ∧ Memory.Vector 7 (memory after).heap (object empty + 2) [] ∧
    readHeader (memory after).memory (Owner.headerAddress ⟨6, 0⟩) =
      .ok (.slice itemsType ⟨object empty + 2, 0⟩ 0, .scalar (.int false 64 5)) ∧
    (memory after).memory.nextId = object empty + 3 ∧ (memory after).memory.nextAddress = 4256 ∧
    after.item.object = none ∧ after.item.clone.value = none ∧ after.item.clone.execution.invalidated = true := by
  have entry := derived_input safety empty
  have original := initialized_owner safety
  have frame := entry.native_frame 6 (owner safety) original.1
  have observations := preparation safety empty
  have result := deterministic_first_oom ops allocate safety 7 6 (object empty) 4096 (owner safety) sentinel
    (argumentView empty) source Insertion.Tests.model input (copied empty) (key empty) (normalized empty) (operands empty)
    (taken safety empty).2.world (duplicated safety empty).2 (made safety empty).2 (cloned safety empty).2 (handle empty)
    entry.origin.held.1.1 entry.origin.held.2.1 entry.item (Normalization.Tests.external_admitted _)
    (frame.trans original.1) original.2.1 original.2.2.1
    ((readField_eq_of_lookup _ _ (Owner.headerAddress ⟨6, 0⟩) itemsOffset frame).trans original.2.2.2.1)
    ((readField_eq_of_lookup _ _ (Owner.headerAddress ⟨6, 0⟩) capacityOffset frame).trans original.2.2.2.2)
    entry.publication observations.1 observations.2.1 observations.2.2.1
    ((ready safety empty).effects.allocator * 10 + 7) (by
      intro installed assigned
      have same := Except.ok.inj (assigned.symm.trans observations.2.2.2)
      rw [same]
      exact backing_response safety empty)
    (probeEffects safety empty) (by
      intro installed assigned
      have same := Except.ok.inj (assigned.symm.trans observations.2.2.2)
      rw [same]
      exact probe_result safety empty)
    ((Owner.NativeLock.checkHeader_eq_of_lookup safety (world safety).memory.memory (taken safety empty).2.world.memory.memory 6
      (owner safety) entry.origin.held.1.1.memory original.1 original.2.1 frame).trans (initialized_lock safety))
  have nextId : (cloned safety empty).2.memory.nextId = object empty + 2 := by
    cases safety <;> cases empty <;> insertion_kernel_rfl
  have nextAddress : max (cloned safety empty).2.memory.nextAddress (4096 + 160) = 4256 := by
    cases safety <;> cases empty <;> insertion_kernel_rfl
  simpa only [nextId, nextAddress, Nat.add_assoc] using result

/-- Fixture boundary using the existing storage outcome and graph projection.
This exercises the real native insertion control; it is not an admission of
the complete find/cache/recursive path or its word semantics. -/
def insert (safety empty : Bool) (slice : ArgumentSlice) : GraphAction (Publication.Effects Nat) NodeId := fun before =>
  let ran := execution ops allocate safety 7 6 (argumentView empty) source Insertion.Tests.model
    input (key empty) slice true [] before
  let value := ((key empty).eval Insertion.Tests.model before.graph.read).getD 0
  let after := Insertion.projected [] before (key empty) (cell input (key empty) slice value ran.1.2 ran.2) ran.1.2 ran.2
  let result := match ran.1.1 with
    | .error _ => .error (.language .safetyFault)
    | .ok outcome => (Interner.insertionOutcome [] outcome).mapError OwnedCall.Fault.language
  (result, after)

def reached (safety empty : Bool) : World (Publication.Effects Nat) :=
  (insert safety empty (normalized empty) (taken safety empty).2.world).2

theorem insert_result (safety empty : Bool) :
    insert safety empty (normalized empty) (taken safety empty).2.world =
      (.error (.language .outOfMemory), reached safety empty) := by
  obtain ⟨after, ran, _⟩ := insertion_oom_from_caller safety empty
  have call := ran
  unfold execute at call
  apply Prod.ext
  · simp only [insert, call, Interner.insertionOutcome, Except.mapError]
  · rfl

theorem handoff_and_outer_cleanup (safety empty : Bool) :
    (let (result, reached) := (do handoff; graph (insert safety empty) : Action (Publication.Effects Nat) NodeId) (taken safety empty).2
     finish (Publication.external ops.arguments) 7 result reached) =
      (.error (.language .outOfMemory), ⟨reached safety empty, ⟨none, some (normalized empty), true⟩⟩) := by
  have completed := (derived_input safety empty).handoff_insert ops.arguments (insert safety empty)
  simpa only [insert_result, ordinary, OwnedCall.Fault.recoverable, ↓reduceIte,
    (prefix_results safety empty).2.2.2.1] using completed

theorem outer_cleanup_after_insertion (safety empty : Bool) :
    finish (Publication.external ops.arguments) 7 (.error (.language .outOfMemory) : Except OwnedCall.Fault NodeId)
      ⟨reached safety empty, { (taken safety empty).2.scope with handedOff := true }⟩ =
      (.error (.language .outOfMemory), ⟨reached safety empty, ⟨none, some (normalized empty), true⟩⟩) := by
  have completed := (derived_input safety empty).finish_insert ops.arguments (reached safety empty)
    (.error (.language .outOfMemory) : Except OwnedCall.Fault NodeId)
  simpa only [ordinary, Fault.recoverable, ↓reduceIte, (prefix_results safety empty).2.2.2.1] using completed

theorem rejection_retains_reached_locals (safety empty : Bool) :
    finish (Publication.external ops.arguments) 7 (.error (.language .safetyFault) : Except OwnedCall.Fault NodeId)
      ⟨reached safety empty, { (taken safety empty).2.scope with handedOff := true }⟩ =
      (.error (.language .safetyFault), ⟨reached safety empty, { (taken safety empty).2.scope with handedOff := true }⟩) := by
  have completed := (derived_input safety empty).finish_insert ops.arguments (reached safety empty)
    (.error (.language .safetyFault) : Except OwnedCall.Fault NodeId)
  simpa only [ordinary, Fault.recoverable, Bool.false_eq_true, ↓reduceIte] using completed

theorem reached_observations (safety empty : Bool) :
    ((reached safety empty).memory.effects.allocator, (reached safety empty).memory.memory.nextId,
      (reached safety empty).memory.memory.nextAddress) =
      (if empty then 567823 else 8568025, if empty then 12 else 14, 4256) := by
  cases safety <;> cases empty <;> insertion_kernel_rfl

theorem retired_owners (safety empty : Bool) :
    ((reached safety empty).memory.memory.heap.lookup (normalized empty).address,
      (reached safety empty).memory.memory.heap.lookup (operands empty).address,
      (reached safety empty).memory.memory.heap.lookup (object empty),
      (reached safety empty).memory.memory.heap.lookup (object empty + 1)) =
      (none, none, none, none) := by
  cases safety <;> cases empty <;> insertion_kernel_rfl

theorem key_table_retained (safety empty : Bool) :
    (reached safety empty).memory.effects.keys = (world safety).memory.effects.keys := by
  cases safety <;> cases empty <;> insertion_kernel_rfl

theorem original_allocations_retained (safety empty : Bool) :
    [0, 1, 3, 5, 7].map (reached safety empty).memory.memory.heap.lookup =
      [0, 1, 3, 5, 7].map (raw safety).memory.heap.lookup := by
  cases safety <;> cases empty <;> insertion_kernel_rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerInputTests
