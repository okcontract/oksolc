/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionTransferredGrowthSetupTests
import Compiler.Extraction.InternerNativeGrowingInsertionTests
import Compiler.Extraction.InternerEnclosingRollbackFrames

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.TransferredGrowthTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open AssemblyItem.Creation.NativeFields.Tests (input source)
open CallerInputTests (values request key)

/-- Reuse the initialized five-row execution for the general recursive
consumer. Only actual create/clone, backing and lock observations are supplied. -/
theorem transferred_observed (safety empty : Bool) :
    RelocatedTransferred ops allocate 7 6 input (some growth) (taken safety empty 4).2.world := by
  have prior := initialized_prefix safety empty 4 (by decide)
  have entry := prior.caller_input (by decide)
  have observed := preparation_results safety empty
  obtain ⟨owner, found, typed, _⟩ := prior.facts.owner
  have nativeFrame := entry.native_frame 6 owner found
  have projected : (taken safety empty 4).2.world.graph.representatives.getD [] = cells safety empty 4 := by
    rw [entry.origin.graph, prior.facts.projected]
    rfl
  refine ⟨by decide, 5, 13, ?_, by decide, ?_, ?_, by decide, 17, 23, releaseBacking, rfl,
    object empty, (made safety empty).2, copied empty, (cloned safety empty).2, 8192,
    (ready safety empty).effects.allocator * 10 + 7, Prod.ext observed.1 rfl, Prod.ext observed.2 rfl, ?_, ?_⟩
  · exact (readField_eq_of_lookup _ _ (Owner.headerAddress ⟨6, 0⟩) capacityOffset nativeFrame).trans prior.facts.capacity_read
  · rw [projected, prior.count]; decide
  · rw [projected, prior.count]; decide
  · intro installed assigned
    have same : ready safety empty = installed := by
      simp only [ready, assigned, Except.toOption, Option.getD_some]
    rw [← same]
    exact ⟨rfl, backing_fits safety empty⟩
  · exact (Owner.NativeLock.checkHeader_eq_of_lookup safety (before safety empty 4).memory.memory
      (taken safety empty 4).2.world.memory.memory 6 owner entry.origin.held.1.1.memory found typed nativeFrame).trans
      (growth_entry_unlocked safety empty)

/-- The same reducer consumed by the general item step derives the complete
handoff/return frame, for both layouts and empty/nonempty transferred buffers. -/
theorem shared_completion (safety empty : Bool) :
    let ran := (do let _ ← handoff; graph (fun slice => Insertion.Native.insert ops allocate safety 7 6
      (parent empty) source Insertion.Tests.model input (key empty) slice false (some growth)) : Action (Publication.Effects Nat) NodeId)
      ⟨(taken safety empty 4).2.world, ⟨some (lookup empty), some (normalized safety empty 4), false⟩⟩
    ConstructorItem.NativeRecursion.FramePost
      (ConstructorItem.NativeRecursion.GraphFrame safety 7 6 (cells safety empty 4) (fun _ => True))
      (OwnedCall.finish (Publication.external ops.arguments) 7 ran.1 ran.2) := by
  have prior := initialized_prefix safety empty 4 (by decide)
  have entry := prior.caller_input (by decide)
  let stack : ConstructorItem.NativeRecursion.Enclosing (σ := Nat) safety 7 6 (fun _ => True) := .root
  exact stack.insertion_rollback_derived trivial entry.origin (NativeGrowingTests.reached_frame safety empty)
    ops allocate (some growth) Insertion.Tests.model (key empty) false (Normalization.Tests.external_admitted _)
    entry.publication.aligned (fun _ _ _ _ _ absent => False.elim (absent rfl (Or.inr (transferred_observed safety empty))))

/-- Initialization and the actual caller prefix supply all entry ownership.
The generic theorem derives graph/native correspondence after transfer and growth;
closed fixture evaluation is used only for callback results and initial geometry. -/
theorem derived_contract (safety empty : Bool) :
    outcome safety empty = (.ok 5, ⟨world safety empty, ⟨none, some (normalized safety empty 4), true⟩⟩) ∧
    GraphFacts safety (grownLifetime empty) 13 (world safety empty) (cells safety empty 4 ++ [row safety empty]) ∧
    (world safety empty).memory.effects.keys = (before safety empty 4).memory.effects.keys ∧
    (world safety empty).memory.memory.nextId = grownLifetime empty + 1 ∧
    (world safety empty).memory.memory.nextAddress = 8608 ∧
    (world safety empty).memory.heap (lifetime empty) = none ∧
    (world safety empty).memory.memory.heap.lookup (lifetime empty) = none ∧
    AssemblyItem.Owned 7 (object empty) (world safety empty).memory ∧
    AssemblyClone.NativeFields.Represents (world safety empty).memory.memory ⟨object empty, 0⟩ (copied empty) ∧
    (∀ slice, AssemblyClone.Physical.payload (copied empty) = some slice → AssemblyItemDeinit.Owned 7 slice (world safety empty).memory) ∧
    (∀ payload, (copied empty).verbatim = some payload → AssemblyClone.Physical.Reads (world safety empty).memory.memory payload.data) ∧
    Memory.SliceValid 7 (world safety empty).memory.heap (normalized safety empty 4) ∧
    (∀ id native, (before safety empty 4).memory.memory.heap.lookup id = some native → id ≠ 6 → id ≠ lifetime empty →
      (world safety empty).memory.memory.heap.lookup id = some native) := by
  have prior := initialized_prefix safety empty 4 (by decide)
  have entry := prior.caller_input (by decide)
  have observed := preparation_results safety empty
  obtain ⟨owner, found, typed, writable⟩ := prior.facts.owner
  obtain ⟨_, after, finalOwner, _, _, ran, valid, ownerFound, ownerTyped, ownerWritable, vector, owned, header,
      descriptors, resident, itemOwned, itemReads, payloadOwned, contents, normalizedLive, live, unique, apart,
      accepted, table, _, nextId, nextAddress, oldDead, nativeDead, frame, _, items, candidate⟩ :=
    entry.transferred_growing_success ops allocate releaseBacking safety 7 6 (lifetime empty) 5 13 (object empty) 8192 17 23 owner
      (parent empty) source Insertion.Tests.model (request empty) (values empty) input (copied empty) (key empty)
      (normalized safety empty 4) (lookup empty) (before safety empty 4) (taken safety empty 4).2
      (cells safety empty 4) (made safety empty).2 (cloned safety empty).2
      found typed writable prior.facts.owned (readHeader_items _ _ _ _ prior.facts.header)
      prior.facts.capacity_read prior.facts.vector prior.facts.descriptors prior.facts.resident prior.facts.apart prior.facts.items
      (by decide) (by decide) (by rw [prior.count]; decide) (by rw [prior.count]; decide) (by decide) (by rw [prior.count]; decide)
      (Prod.ext observed.1 rfl) (Prod.ext observed.2 rfl) ((ready safety empty).effects.allocator * 10 + 7) (by
        intro installed assigned
        have same : ready safety empty = installed := by simp only [ready, assigned, Except.toOption, Option.getD_some]
        rw [← same]
        exact ⟨rfl, backing_fits safety empty⟩) (growth_entry_unlocked safety empty)
  have complete := completed safety empty after ran candidate
  have same : world safety empty = reached safety empty := congrArg (fun result => result.2.world) complete.1
  have memorySame : (world safety empty).memory = memory after := by rw [same]; exact complete.2.1
  have fresh := (Prod.mk.inj (prepared_geometry safety empty)).1
  have bound := (Prod.mk.inj (prepared_geometry safety empty)).2
  simp only [decide_eq_true_eq, (ready_contract safety empty).2] at bound
  refine ⟨?_, ?_, memorySame ▸ table, ?_, ?_, memorySame ▸ oldDead, memorySame ▸ nativeDead,
    memorySame ▸ itemOwned, memorySame ▸ itemReads, memorySame ▸ payloadOwned, memorySame ▸ contents,
    memorySame ▸ normalizedLive, ?_⟩
  · simpa only [← same] using complete.1
  · obtain ⟨native, located, inputTyped, inputReads⟩ := prior.facts.nativeInput
    have inputFrame := frame source.allocation native located (by decide) (by cases empty <;> decide)
    rw [fresh] at vector owned header descriptors
    refine ⟨by rw [same]; exact complete.2.2.1, ?_, memorySame ▸ valid,
      ⟨finalOwner, memorySame ▸ ownerFound, ownerTyped, ownerWritable⟩,
      memorySame ▸ owned, memorySame ▸ vector, ?_, memorySame ▸ descriptors, memorySame ▸ resident,
      memorySame ▸ items, ⟨native, memorySame ▸ inputFrame, inputTyped, memorySame ▸ inputReads.frame (inputFrame.trans located.symm)⟩,
      memorySame ▸ live, memorySame ▸ unique, memorySame ▸ apart, memorySame ▸ accepted, ?_⟩
    · rw [same, complete.2.2.2, prior.facts.linked, complete.2.1, table]
    · rw [memorySame]
      simpa only [List.length_append, List.length_singleton] using header
    · rw [memorySame]
      intro logical member
      rcases List.mem_append.mp member with old | added
      · exact prior.facts.data_after (key empty) (memory after).memory
          (fun id native found ownerApart backingApart _ => frame id native found ownerApart backingApart) logical old
      · have sameRow := List.mem_singleton.mp added
        subst logical
        exact Constant.Data.nonpush (memory after).memory (row safety empty)
          (by change (1#32) ≠ 2#32; decide)
  · rw [memorySame, nextId, fresh]
  · rw [memorySame, nextAddress, Nat.max_eq_right (by omega)]
  · intro id native found ownerApart backingApart
    exact memorySame ▸ frame id native found ownerApart backingApart

theorem parent_borrow_after_growth (safety empty : Bool) :
    Operation.run (world safety empty).memory.memory (Owner.headerAddress ⟨6, 0⟩) 0 254 =
      .ok (.ok (some (Operation.returned (CallerInputTests.operands empty)))) ∧
    Good (parent empty) (request empty).arguments (world safety empty) := by
  apply (derived_contract safety empty).2.1.first_borrow
  rw [List.head?_append, (initialized_prefix safety empty 4 (by decide)).first]
  rfl

theorem key_unchanged (safety empty : Bool) :
    (world safety empty).memory.effects.keys (key empty) = some ⟨if empty then 22 else 30, 4⟩ := by
  have previous : (before safety empty 4).memory.effects.keys (key empty) = some ⟨if empty then 22 else 30, 4⟩ := by
    cases safety <;> cases empty <;> insertion_kernel_rfl
  exact (congrFun (derived_contract safety empty).2.2.1 (key empty)).trans previous

/-- Callback effects observe only backing allocation and old-backing release
following create/clone. There is no key probe, duplicate, or normalized free. -/
theorem effects_observed (safety empty : Bool) :
    (world safety empty).memory.effects.allocator = ((ready safety empty).effects.allocator * 10 + 7) * 10 + 9 := by
  cases safety <;> cases empty <;> insertion_kernel_rfl

/-- The representative reads the exact transferred descriptor, including the
empty sentinel. The typed query derives its nonempty contents and owner. -/
theorem transferred_query (safety empty : Bool) :
    Operation.run (world safety empty).memory.memory (Owner.headerAddress ⟨6, 0⟩) 5 254 =
      .ok (.ok (some (Operation.returned (normalized safety empty 4)))) := by
  have facts := (derived_contract safety empty).2.1
  have logical : Storage.operationProgram.run (cells safety empty 4 ++ [row safety empty]) 5 254 =
      .ok (some (normalized safety empty 4)) := by
    cases safety <;> cases empty <;> insertion_kernel_rfl
  exact (facts.accepted.1 5 254).trans (by rw [logical]; rfl)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.TransferredGrowthTests
