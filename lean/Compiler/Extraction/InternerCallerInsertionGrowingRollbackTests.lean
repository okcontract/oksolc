/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionGrowingRollbackSetupTests
import Compiler.Extraction.InternerInsertionNativeDeinitTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.RollbackTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open AssemblyItem.Creation.NativeFields.Tests (input source)
open CallerInputTests (values request key)

/-- Five initialized, caller-owned rows survive a sixth insertion's publication
OOM. Relocation and allocator history remain, the logical row is popped, the old
key is retained and the detached outer lookup closes on the actual reached state. -/
theorem derived_contract (safety empty : Bool) :
    outcome safety empty = (.error (.language .outOfMemory),
      ⟨world safety empty, ⟨none, some (normalized safety empty 4), true⟩⟩) ∧
    GraphFacts safety (grownLifetime empty) 13 (world safety empty) (cells safety empty 4) ∧
    (world safety empty).memory.heap (lifetime empty) = none ∧
    (world safety empty).memory.memory.heap.lookup (lifetime empty) = none ∧
    (world safety empty).memory.memory.nextId = grownLifetime empty + 1 ∧
    (world safety empty).memory.memory.nextAddress = 8608 ∧
    (world safety empty).memory.effects.keys = (before safety empty 4).memory.effects.keys ∧
    (∀ id native, (before safety empty 4).memory.memory.heap.lookup id = some native → id ≠ 6 → id ≠ lifetime empty →
      (world safety empty).memory.memory.heap.lookup id = some native) ∧
    (∃ original current, (before safety empty 4).memory.memory.heap.lookup 6 = some original ∧
      (world safety empty).memory.memory.heap.lookup 6 = some current ∧ original.SameShape current) ∧
    (∀ id, id = object safety empty 4 ∨ AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload (copied safety empty 4)) id ∨
      ((operands safety empty 4).items ≠ [] ∧ id = (operands safety empty 4).address) ∨
      ((normalized safety empty 4).items ≠ [] ∧ id = (normalized safety empty 4).address) →
      (world safety empty).memory.heap id = none ∧ (world safety empty).memory.memory.heap.lookup id = none) := by
  have prior := initialized_prefix safety empty 4 (by decide)
  have entry := prior.caller_input (by decide)
  have observations := preparation_results safety empty 4 (by decide)
  obtain ⟨owner, found, typed, writable⟩ := prior.facts.owner
  let probeEffects := (memory (append safety allocate 7 6 (cells safety empty 4) input (key empty) (normalized safety empty 4)
    (value safety empty 4) preparationOwnership (preparedFrame (object safety empty 4) (copied safety empty 4)
      (operands safety empty 4) (ready safety empty 4)) (some growth)).2).effects.allocator * 10 + 8
  have result := entry.growing_oom failing allocate releaseBacking safety 7 6 (lifetime empty) 5 13 (object safety empty 4) 8192 17 23 owner
    (parent empty) source Insertion.Tests.model (request empty) (values empty) input (copied safety empty 4) (key empty)
    (normalized safety empty 4) (operands safety empty 4) (lookup empty) (handle safety empty 4) (before safety empty 4) (taken safety empty 4).2
    (cells safety empty 4) (duplicated safety empty 4).2 (made safety empty 4).2 (cloned safety empty 4).2
    (Normalization.Tests.external_admitted _) found typed writable prior.facts.owned (readHeader_items _ _ _ _ prior.facts.header)
    prior.facts.capacity_read prior.facts.vector prior.facts.descriptors prior.facts.resident prior.facts.apart prior.facts.items
    prior.facts.valid prior.facts.live (by decide) (by rw [prior.count]; decide) (by rw [prior.count]; decide) (by decide) (by rw [prior.count]; decide)
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
  obtain ⟨after, ran, valid, vector, owned, header, descriptors, resident, table, live, unique, apart,
      accepted, nextId, nextAddress, oldDead, nativeDead, _, _, _, frame, _, items, finalOwner, destroyed⟩ := result
  obtain ⟨currentOwner, currentFound, ownerShape⟩ := finalOwner
  have executed : RollbackTests.executed safety empty = ((.ok (some .allocationFailure), closed), after) := ran
  have complete := completed safety empty after executed
  have same : world safety empty = reached safety empty := congrArg (fun result => result.2.world) complete.1
  have memorySame : (world safety empty).memory = memory after := by rw [same]; exact complete.2.1
  have fresh := (Prod.mk.inj (prepared_geometry safety empty)).1
  have bound := (Prod.mk.inj (prepared_geometry safety empty)).2
  simp only [decide_eq_true_eq, (ready_contract safety empty).2] at bound
  rw [fresh] at vector owned header descriptors nextId
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨owner, currentOwner, found, memorySame ▸ currentFound, ownerShape⟩, ?_⟩
  · simpa only [← same] using complete.1
  · obtain ⟨native, located, inputTyped, inputReads⟩ := prior.facts.nativeInput
    have inputFrame := frame source.allocation native located (by decide) (by cases empty <;> decide)
    refine ⟨by rw [same]; exact complete.2.2.1, ?_, memorySame ▸ valid,
      ⟨currentOwner, memorySame ▸ currentFound, ownerShape.2.1.trans typed, ownerShape.2.2.1.trans writable⟩,
      memorySame ▸ owned, memorySame ▸ vector, memorySame ▸ header, memorySame ▸ descriptors,
      memorySame ▸ resident, memorySame ▸ items, ?_, memorySame ▸ live, memorySame ▸ unique, memorySame ▸ apart,
      memorySame ▸ accepted, ?_⟩
    · rw [same, complete.2.2.2, prior.facts.linked, complete.2.1, table]
    · exact ⟨native, memorySame ▸ inputFrame, inputTyped, memorySame ▸ inputReads.frame (inputFrame.trans located.symm)⟩
    · rw [memorySame]
      exact prior.facts.data_after (key empty) (memory after).memory
        (fun id native found ownerApart backingApart _ => frame id native found ownerApart backingApart)
  · rw [memorySame]; exact oldDead
  · rw [memorySame]; exact nativeDead
  · rw [memorySame]; exact nextId
  · rw [memorySame, nextAddress]
    exact Nat.max_eq_right (by omega)
  · rw [memorySame]; exact table
  · intro id native found ownerApart oldApart
    rw [memorySame]
    exact frame id native found ownerApart oldApart
  · intro id selected
    rw [memorySame]
    exact destroyed id selected

/-- The same previously borrowed native arguments remain a valid parent input,
with unchanged contents, after relocation, failed publication and outer cleanup. -/
theorem parent_borrow_after_rollback (safety empty : Bool) :
    Operation.run (world safety empty).memory.memory (Owner.headerAddress ⟨6, 0⟩) 0 254 =
      .ok (.ok (some (Operation.returned (CallerInputTests.operands empty)))) ∧
    Good (parent empty) (request empty).arguments (world safety empty) :=
  (derived_contract safety empty).2.1.first_borrow (initialized_prefix safety empty 4 (by decide)).first

/-- The old key owns its existing buffer after OOM, including replacement at the
same key. It is not replaced by the newly normalized allocation. -/
theorem key_unchanged (safety empty : Bool) :
    (world safety empty).memory.effects.keys (key empty) = some ⟨if empty then 22 else 30, 4⟩ := by
  have previous : (before safety empty 4).memory.effects.keys (key empty) = some ⟨if empty then 22 else 30, 4⟩ := by
    cases safety <;> cases empty <;> insertion_kernel_rfl
  exact (congrFun (derived_contract safety empty).2.2.2.2.2.2.1 (key empty)).trans previous

/-- A native invalidation failure retains the completed payload free and private
effect, while the table is preserved without any successful-cleanup premise. -/
theorem partial_failure_keys :
    (memory CleanupTests.readonly.2).effects.keys =
      (memory (CleanupTests.frame (AssemblyItemDeinit.Native.Tests.withItem
        { AssemblyItemDeinit.Native.Tests.itemCell with writable := false }))).effects.keys ∧
    CleanupTests.readonly.1 = .error (.cleanup (.memory .readOnly)) ∧
    (memory CleanupTests.readonly.2).memory.heap.lookup 3 = none ∧
    (memory CleanupTests.readonly.2).effects.allocator = 12 := by
  refine ⟨?_, CleanupTests.rejection_keeps_reached.1,
    CleanupTests.rejection_keeps_reached.2.1, CleanupTests.rejection_keeps_reached.2.2.1⟩
  simpa only [CleanupTests.readonly] using releaseValue_keys Insertion.Tests.ops 7
    (CleanupTests.frame (AssemblyItemDeinit.Native.Tests.withItem
      { AssemblyItemDeinit.Native.Tests.itemCell with writable := false }))

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.RollbackTests
