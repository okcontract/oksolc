/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionGrowingChainTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray
open AssemblyItem.Creation.NativeFields.Tests (input source)
open CallerInputTests (values request key)

def grownLifetime (empty : Bool) := if empty then 27 else 39

theorem prepared_geometry (safety empty : Bool) :
    ((cloned safety empty 4).2.memory.nextId, decide ((ready safety empty 4).memory.nextAddress ≤ 8192)) =
      (grownLifetime empty, true) := by
  cases safety <;> cases empty <;> insertion_kernel_rfl

theorem ready_contract (safety empty : Bool) : Valid (ready safety empty 4) ∧
    (ready safety empty 4).memory.nextAddress = (cloned safety empty 4).2.memory.nextAddress := by
  have prior := initialized_prefix safety empty 4 (by decide)
  have entry := prior.caller_input (by decide)
  have observations := preparation_results safety empty 4 (by decide)
  let graph : Storage.State → Frame Nat → Interner.Heap := fun owner state => Interner.InsertionExecution.project
    (cells safety empty 4) (taken safety empty 4).2.world.graph.table
    (cell input (key empty) (normalized safety empty 4) (value safety empty 4) owner state) (key empty) owner
  obtain ⟨installed, _, _, _, established, assigned, _⟩ := entry.prepare ops allocate safety 7 6 (object safety empty 4)
    (parent empty) source (request empty) (values empty) input (copied safety empty 4) (key empty) (normalized safety empty 4)
    (operands safety empty 4) (lookup empty) (handle safety empty 4) (before safety empty 4) (taken safety empty 4).2
    (cells safety empty 4) (value safety empty 4) graph (duplicated safety empty 4).2 (made safety empty 4).2 (cloned safety empty 4).2
    (Normalization.Tests.external_admitted _) observations.1 observations.2.1 observations.2.2
  have same : ready safety empty 4 = installed := by simp only [ready, assigned, Except.toOption, Option.getD_some]
  rw [same]
  exact ⟨established.valid, established.written.nextAddress⟩

/-- The successful callback's region is disjoint from every live allocation in
the actual reached preparation. The proof uses its complete native validity and
address high-water mark, not a manufactured heap or selected footprint. -/
theorem backing_fits (safety empty : Bool) : Compiler.ZigAir.Memory.RegionAllocation.Fits (ready safety empty 4).memory ⟨416, 8⟩ 8192 := by
  have valid := (ready_contract safety empty).1.memory
  have bound := (Prod.mk.inj (prepared_geometry safety empty)).2
  simp only [decide_eq_true_eq] at bound
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro entry present layout shaped
  simp only [Compiler.ZigAir.Memory.State.valid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at valid
  have checked := valid.1.2 entry present
  simp only [shaped, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact Or.inr (by omega)

/-- Initialization, five published rows, and one actual relocating insertion.
Every intermediate caller consumes the previous reached graph. The final owner,
key table, native queries, clone and old-backing retirement all follow from the
composed calls; no populated initial graph or final ownership is assumed. -/
theorem growing_contract (safety empty : Bool) :
    run safety empty 5 = (.ok 5, ⟨before safety empty 5, ⟨none, some (normalized safety empty 4), true⟩⟩) ∧
    cells safety empty 5 = cells safety empty 4 ++ [row safety empty 4] ∧
    (cells safety empty 5).length = 6 ∧
    (cells safety empty 5).head? = some (CallerFirstSuccessTests.row safety empty) ∧
    GraphFacts safety (grownLifetime empty) 13 (before safety empty 5) (cells safety empty 5) ∧
    (before safety empty 5).memory.heap (lifetime empty) = none ∧
    (before safety empty 5).memory.memory.heap.lookup (lifetime empty) = none ∧
    (before safety empty 5).memory.memory.nextId = grownLifetime empty + 1 ∧
    (before safety empty 5).memory.memory.nextAddress = 8608 ∧
    (before safety empty 5).memory.effects.keys = OwnedKeys.store (before safety empty 4).memory.effects.keys (key empty)
      ⟨(normalized safety empty 4).address, 5⟩ ∧
    AssemblyItem.Owned 7 (object safety empty 4) (before safety empty 5).memory ∧
    AssemblyClone.NativeFields.Represents (before safety empty 5).memory.memory ⟨object safety empty 4, 0⟩ (copied safety empty 4) ∧
    (∀ slice, AssemblyClone.Physical.payload (copied safety empty 4) = some slice → AssemblyItemDeinit.Owned 7 slice (before safety empty 5).memory) ∧
    (∀ payload, (copied safety empty 4).verbatim = some payload → AssemblyClone.Physical.Reads (before safety empty 5).memory.memory payload.data) ∧
    (∀ previous, (before safety empty 4).memory.effects.keys (key empty) = some previous → (key empty).arguments ≠ [] →
      (before safety empty 5).memory.heap previous.address = none ∧ (before safety empty 5).memory.memory.heap.lookup previous.address = none) ∧
    (∀ parent, Caller.Custody 7 parent (before safety empty 4).memory →
      Caller.Custody 7 parent (before safety empty 5).memory ∧
        Good (view parent) parent.items (before safety empty 5)) := by
  have prior := initialized_prefix safety empty 4 (by decide)
  have entry := prior.caller_input (by decide)
  have observations := preparation_results safety empty 4 (by decide)
  obtain ⟨owner, found, typed, writable⟩ := prior.facts.owner
  let probeEffects := (memory (append safety allocate 7 6 (cells safety empty 4) input (key empty) (normalized safety empty 4)
    (value safety empty 4) preparationOwnership (preparedFrame (object safety empty 4) (copied safety empty 4)
      (operands safety empty 4) (ready safety empty 4)) (some growth)).2).effects.allocator * 10 + 8
  have result := entry.growing_success ops allocate releaseBacking safety 7 6 (lifetime empty) 5 13 (object safety empty 4) 8192 17 23 owner
    (parent empty) source Insertion.Tests.model (request empty) (values empty) input (copied safety empty 4) (key empty)
    (normalized safety empty 4) (operands safety empty 4) (lookup empty) (handle safety empty 4) (before safety empty 4) (taken safety empty 4).2
    (cells safety empty 4) (duplicated safety empty 4).2 (made safety empty 4).2 (cloned safety empty 4).2
    (Normalization.Tests.external_admitted _) found typed writable prior.facts.owned (readHeader_items _ _ _ _ prior.facts.header)
    prior.facts.capacity_read prior.facts.vector prior.facts.descriptors prior.facts.resident prior.facts.apart prior.facts.items
    (by decide) (by decide) (by rw [prior.count]; decide) (by rw [prior.count]; decide) (by decide) (by rw [prior.count]; decide)
    observations.1 observations.2.1 observations.2.2 ((ready safety empty 4).effects.allocator * 10 + 7) (by
      intro installed assigned
      have same : ready safety empty 4 = installed := by simp only [ready, assigned, Except.toOption, Option.getD_some]
      rw [← same]
      exact ⟨rfl, backing_fits safety empty⟩)
    probeEffects (by
      intro installed assigned
      have same : ready safety empty 4 = installed := by simp only [ready, assigned, Except.toOption, Option.getD_some]
      rw [← same]
      rfl) (growth_entry_unlocked safety empty)
  obtain ⟨_, _, after, finalOwner, _, _, ran, valid, ownerFound, ownerTyped, ownerWritable, vector, owned, header,
      descriptors, resident, itemOwned, itemReads, payloadOwned, contents, _, live, unique, apart, accepted, table, _,
      nextId, nextAddress, oldDead, nativeDead, retired, frame, _, items, custody, _, _, candidate⟩ := result
  have selected : selectedGrowth (cells safety empty 4) = some growth := by simp only [selectedGrowth, prior.count, ↓reduceIte]
  have executed : execute safety empty 4 = ((.ok (some .success), Storage.publishedOwnership), after) := by
    simpa only [execute, selected, growth] using ran
  have completed := prior.completed (by decide) after executed candidate
  have same : before safety empty 5 = reached safety empty 4 := congrArg (fun result => result.2.world) completed.1
  have memorySame : (before safety empty 5).memory = memory after := by rw [same, completed.2]; rfl
  have rows : cells safety empty 5 = cells safety empty 4 ++ [row safety empty 4] := by
    unfold cells
    rw [same, completed.2]
    rfl
  have fresh := (Prod.mk.inj (prepared_geometry safety empty)).1
  have bound := (Prod.mk.inj (prepared_geometry safety empty)).2
  simp only [decide_eq_true_eq, (ready_contract safety empty).2] at bound
  refine ⟨?_, rows, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [← same] using completed.1
  · rw [rows, List.length_append, List.length_singleton, prior.count]
  · rw [rows, List.head?_append, prior.first]; rfl
  · rw [same, rows, completed.2]
    obtain ⟨native, located, inputTyped, inputReads⟩ := prior.facts.nativeInput
    have inputFrame := frame source.allocation native located (by decide)
      (by cases empty <;> decide) (prior.facts.input_apart (key empty))
    rw [fresh] at vector owned header descriptors
    refine ⟨rfl, ?_, valid, ⟨finalOwner, ownerFound, ownerTyped, ownerWritable⟩, owned, vector, ?_,
      descriptors, resident, items, ⟨native, inputFrame, inputTyped, inputReads.frame (inputFrame.trans located.symm)⟩,
      live, unique, apart, accepted, ?_⟩
    · change Cache.put equalityFields (taken safety empty 4).2.world.graph.table (key empty) (Storage.idFor (cells safety empty 4)) =
        OwnedKeys.view (memory after).effects.keys
      rw [table, OwnedKeys.view_store, entry.origin.graph, prior.facts.linked]
      rfl
    · simpa only [List.length_append, List.length_singleton] using header
    · intro logical member
      rcases List.mem_append.mp member with old | added
      · exact prior.facts.data_after (key empty) (memory after).memory frame logical old
      · have sameRow := List.mem_singleton.mp added
        subst logical
        exact Constant.Data.nonpush (memory after).memory (row safety empty 4)
          (by change (1#32) ≠ 2#32; decide)
  · rw [memorySame]; exact oldDead
  · rw [memorySame]; exact nativeDead
  · rw [memorySame, nextId, fresh]
  · rw [memorySame, nextAddress, Nat.max_eq_right (by omega)]
  · rw [memorySame, table, prior.count]; rfl
  · rw [memorySame]; exact itemOwned
  · rw [memorySame]; exact itemReads
  · rw [memorySame]; exact payloadOwned
  · rw [memorySame]; exact contents
  · rw [memorySame]; exact retired
  · intro parent held
    have kept := custody parent held
    refine ⟨memorySame ▸ kept.1, ?_⟩
    have good := kept.2 (before safety empty 5).graph
    simpa only [← memorySame] using good

/-- A parent borrow obtained before the intervening calls still reads its exact
arguments after relocation and key replacement. The native result derives Good. -/
theorem parent_borrow_after_growth (safety empty : Bool) :
    Operation.run (before safety empty 5).memory.memory (Owner.headerAddress ⟨6, 0⟩) 0 254 =
      .ok (.ok (some (Operation.returned (CallerInputTests.operands empty)))) ∧
    Good (parent empty) (request empty).arguments (before safety empty 5) := by
  have reached := growing_contract safety empty
  exact reached.2.2.2.2.1.first_borrow reached.2.2.2.1

/-- The allocator trace includes allocation, release of the actual old 160-byte
backing, probing, and replacement-key cleanup. Outer defers add no release. -/
theorem allocator_effects (safety empty : Bool) : (before safety empty 5).memory.effects.allocator =
    (((ready safety empty 4).effects.allocator * 10 + 7) * 10 + 9) * 10 + 8 + (if empty then 0 else 101) := by
  cases safety <;> cases empty <;> insertion_kernel_rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests
