/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionGrowingSuccess
import Compiler.Extraction.InternerInsertionGrowingTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.GrowingSuccessTests
open Compiler.ZigAir.Memory Compiler.Algebraic Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray
open AssemblyClone.NativeFields.QueryTests (old)
open AssemblyItem.Creation.NativeFields.Tests (input source expectedCells)
open GrowingTests (ownerCell oldBacking object backing normalized operands copied key releaseBacking growth handle)

abbrev allocate := GrowingTests.allocate
abbrev normalized := GrowingTests.normalized

def oldKeyAddress (empty : Bool) : Nat := if empty then backing empty else 1
/-- Empty replaced keys deliberately alias the new representative backing. -/
def keys (empty replacement : Bool) : OwnedKeys.Table :=
  if replacement then OwnedKeys.store (fun _ => none) (key empty) ⟨oldKeyAddress empty, 0⟩ else fun _ => none

def initial (safety empty replacement : Bool) : Session (Publication.Effects Nat) :=
  { GrowingTests.initial safety with effects := ⟨keys empty replacement, 0⟩ }
def world (safety empty replacement : Bool) : World (Publication.Effects Nat) :=
  ⟨Interner.observedHeap [old] (OwnedKeys.view (keys empty replacement)), initial safety empty replacement⟩
def ops (empty : Bool) : Operations Nat := { GrowingTests.ops empty with
  probe := fun _ reached =>
    (readItems reached.memory (Owner.headerAddress ⟨6, 0⟩) == .ok (.slice itemsType ⟨backing empty, 0⟩ 2) &&
      (reached.memory.heap.lookup 7).isNone, reached.effects * 10 + 1)
  arguments := { ExpressionDeinit.Tests.external with free := fun slice reached => reached.effects * 10 +
    (if slice.address = 1 && readItems reached.memory (Owner.headerAddress ⟨6, 0⟩) ==
      .ok (.slice itemsType ⟨backing empty, 0⟩ 2) && (reached.memory.heap.lookup 1).isSome then 6 else 9) } }
def taken (safety empty replacement : Bool) := takeOwned normalizationOwnershipCode (Publication.external (ops empty).arguments)
  7 (handle empty) (initial safety empty replacement)
def made (safety empty replacement : Bool) := AssemblyItem.Creation.create (observe (ops empty).create) 7 input.item (taken safety empty replacement).2
def cloned (safety empty replacement : Bool) := AssemblyClone.Physical.run (observe (ops empty).copy) 7 input (made safety empty replacement).2
def ready (safety empty replacement : Bool) : Session (Publication.Effects Nat) :=
  { (cloned safety empty replacement).2 with memory := { (cloned safety empty replacement).2.memory with
    heap := (cloned safety empty replacement).2.memory.heap.replace (object empty)
      { AssemblyItem.Creation.cell 80 with cells := expectedCells (object empty + 1) 0 } } }
def execute (safety empty replacement : Bool) := execution (ops empty) allocate safety 7 6 ⟨2, 0, 0⟩ source Insertion.Tests.model
  input (key empty) (normalized empty) true [old] (world safety empty replacement) (some growth)
def row (empty : Bool) : Storage.Cell := ⟨(copied empty).item, 0, object empty, (operands empty).items, (key empty).sequence, 9⟩

theorem initial_valid (safety empty replacement : Bool) : Valid (initial safety empty replacement) :=
  ⟨(GrowingTests.initial_valid safety).memory, (GrowingTests.initial_valid safety).related, (GrowingTests.initial_valid safety).injected⟩

theorem preparation_results (safety empty replacement : Bool) :
    taken safety empty replacement = (.ok (operands empty, handle empty), (taken safety empty replacement).2) ∧
    made safety empty replacement = (.ok (object empty), (made safety empty replacement).2) ∧
    cloned safety empty replacement = (.ok (copied empty), (cloned safety empty replacement).2) ∧
    AssemblyClone.NativeFields.install (copied empty) (object empty) (cloned safety empty replacement).2 = .ok (ready safety empty replacement) := by
  cases safety <;> cases empty <;> cases replacement <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem backing_response (safety empty replacement : Bool) :
    allocate 7 224 8 (ready safety empty replacement).effects.allocator = (some 2304, if empty then 567 else 1567) ∧
    RegionAllocation.Fits (ready safety empty replacement).memory ⟨224, 8⟩ 2304 := by
  refine ⟨by cases safety <;> cases empty <;> cases replacement <;> insertion_kernel_rfl, ?_⟩
  refine ⟨by decide, by decide, by decide, ?_⟩
  have bound : (ready safety empty replacement).memory.heap.all (fun entry =>
      decide (entry.2.base + (entry.2.type.layout.getD ⟨0, 1⟩).bytes ≤ 2304)) = true := by
    cases safety <;> cases empty <;> cases replacement <;> decide +kernel
  intro entry present layout shaped
  have checked := (List.all_eq_true.mp bound) entry present
  simp only [shaped, Option.getD_some, decide_eq_true_eq] at checked
  exact Or.inr checked

theorem probe_result (safety empty replacement : Bool) :
    (ops empty).probe (key empty) (Publication.forget (memory (append safety allocate 7 6 [old] input (key empty) (normalized empty)
      (((key empty).eval Insertion.Tests.model (world safety empty replacement).graph.read).getD 0) Storage.preparationOwnership
      (preparedFrame (object empty) (copied empty) (operands empty) (ready safety empty replacement)) (some growth)).2)) =
      (true, if empty then 56781 else 156781) := by
  cases safety <;> cases empty <;> cases replacement <;> insertion_kernel_rfl

theorem derived_contract (safety empty replacement : Bool) : ∃ after,
    execute safety empty replacement = ((.ok (some .success), Storage.publishedOwnership), after) ∧
    Valid (memory after) ∧ Memory.Vector 7 (memory after).heap (backing empty) [old, row empty] ∧
    Backing.Release.Owned 7 ⟨backing empty, 0⟩ 7 (memory after) ∧
    DescriptorRelation.Prefix (memory after).memory (backing empty) [old, row empty] ∧
    (∀ id, representativeFields (memory after).memory (Owner.headerAddress ⟨6, 0⟩) id =
      .ok ((Storage.representativeProgram.run [old, row empty] id).map (DescriptorRelation.values id.toNat))) ∧
    Memory.SliceValid 7 (memory after).heap (normalized empty) ∧
    (memory after).effects.keys = OwnedKeys.store (keys empty replacement) (key empty) ⟨(normalized empty).address, 1⟩ ∧
    (memory after).memory.nextId = backing empty + 1 ∧ (memory after).memory.nextAddress = 2528 ∧
    (memory after).heap 7 = none ∧ (memory after).memory.heap.lookup 7 = none := by
  have represented : AssemblyClone.NativeFields.Represents (initial safety empty replacement).memory source input :=
    AssemblyItem.Creation.NativeFields.Tests.source_represented.frame
      ((GrowingTests.initial_frame safety 5 (by decide) (by decide)).trans ((AppendOwnershipTests.initial_frame safety 5 (by decide)).trans
        (AssemblyClone.NativeFields.QueryTests.initial_frame safety false 5 (by decide))))
  have live : Memory.SliceValid 7 (initial safety empty replacement).heap (normalized empty) := by
    cases empty
    · exact Or.inr (by rfl')
    · exact Or.inl rfl
  have publication : Publication.Input 7 ⟨2, 0, 0⟩ (key empty) (normalized empty) (world safety empty replacement) := by
    refine ⟨rfl, ?_, ?_, ?_⟩
    all_goals intro entry found
    all_goals cases replacement
    all_goals try cases found
    all_goals have same : entry = ⟨oldKeyAddress empty, 0⟩ := by simpa only [world, initial, keys, ↓reduceIte, OwnedKeys.store, ite_true, Option.some.injEq] using found.symm
    all_goals subst entry
    · cases empty
      · exact Or.inr (by rfl')
      · exact Or.inl rfl
    · cases empty <;> decide
    · intro _ impossible; exact False.elim (impossible rfl)
  have oldOwned : Backing.Release.Owned 7 ⟨7, 0⟩ 1 (initial safety empty replacement) :=
    ⟨rfl, ⟨[old], by rfl'⟩, oldBacking, by cases safety <;> cases empty <;> cases replacement <;> decide +kernel, rfl, rfl, rfl⟩
  have rows : DescriptorRelation.Prefix (initial safety empty replacement).memory 7 [old] := by
    intro index cell found
    cases index with
    | zero => cases Option.some.inj found; unfold DescriptorRelation.Row; cases safety <;> cases empty <;> cases replacement <;> decide +kernel
    | succ index => simp at found
  have observations := preparation_results safety empty replacement
  have result := deterministic_growing_success (ops empty) allocate releaseBacking safety 7 6 7 1 7 (object empty) 2304 17 23
    (ownerCell safety) ⟨2, 0, 0⟩ source Insertion.Tests.model input (copied empty) (key empty) (normalized empty) (operands empty) [old]
    (world safety empty replacement) (taken safety empty replacement).2 (made safety empty replacement).2 (cloned safety empty replacement).2 (handle empty)
    (initial_valid safety empty replacement) live represented ExpressionDeinit.Tests.external_admitted
    (by cases safety <;> cases empty <;> cases replacement <;> decide +kernel) rfl rfl oldOwned (by cases safety <;> cases empty <;> cases replacement <;> decide +kernel) (by cases safety <;> cases empty <;> cases replacement <;> decide +kernel)
    (by rfl') rows (by decide) (by decide) (by decide) (by decide) (by decide) publication observations.1 observations.2.1 observations.2.2.1
    (if empty then 567 else 1567) (by
      intro installed assigned
      cases Except.ok.inj (assigned.symm.trans observations.2.2.2)
      exact backing_response safety empty replacement) (if empty then 56781 else 156781) (by
      intro installed assigned
      cases Except.ok.inj (assigned.symm.trans observations.2.2.2)
      exact probe_result safety empty replacement) (by
      apply Owner.NativeLock.checkHeader_of_cell safety _ 6 (ownerCell safety)
        (initial_valid safety empty replacement).memory
        (by cases safety <;> cases empty <;> cases replacement <;> decide +kernel) rfl
      intro active
      subst safety
      rfl)
  obtain ⟨installed, appended, after, _, _, executed, valid, vector, _, owned, prefixKept, queries, normalizedLive,
      publishedKeys, nextId, nextAddress, retired, nativeRetired, _⟩ := result
  have id : (cloned safety empty replacement).2.memory.nextId = backing empty := by
    cases safety <;> cases empty <;> cases replacement <;> insertion_kernel_rfl
  have address : max (cloned safety empty replacement).2.memory.nextAddress (2304 + 7 * 32) = 2528 := by
    cases safety <;> cases empty <;> cases replacement <;> insertion_kernel_rfl
  have value : ((key empty).eval Insertion.Tests.model (world safety empty replacement).graph.read).getD 0 = 0 := by
    cases safety <;> cases empty <;> cases replacement <;> insertion_kernel_rfl
  refine ⟨after, executed, valid, ?_, ?_, ?_, ?_, normalizedLive, publishedKeys, ?_, nextAddress.trans address, retired, nativeRetired⟩
  · simpa only [id, value] using vector
  · simpa only [id] using owned
  · simpa only [id, value] using prefixKept
  · simpa only [value] using queries
  · simpa only [id] using nextId

/-- Record all actual reached observations in one closed equality, avoiding
repeated elaboration of the same insertion execution. -/
def observations (safety empty replacement : Bool) :=
  let reached := execute safety empty replacement
  let state := memory reached.2
  (state.effects.allocator, (state.memory.heap.lookup 1).isNone,
    [object empty, object empty + 1, backing empty, 8, 9].map (fun id => (state.memory.heap.lookup id).isSome),
    state.effects.keys (key empty), reached.2.item.object, reached.2.item.clone.value, reached.2.item.clone.execution.invalidated)

/-- Replacement frees only the old nonempty key, after probing the reached
relocated row. Empty old sentinels never release the live backing they name. -/
theorem reached_observations (safety empty replacement : Bool) :
    observations safety empty replacement =
      (if empty then 56781 else if replacement then 1567816 else 156781,
       replacement && !empty, [true, true, true, true, true],
       some ⟨(normalized empty).address, 1⟩, some (object empty), some (copied empty), false) := by
  cases safety <;> cases empty <;> cases replacement <;> insertion_kernel_rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.GrowingSuccessTests
