/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionGrowingPrepared
import Compiler.Extraction.InternerInsertionPreparationTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.GrowingTests
open Compiler.ZigAir.Memory Compiler.Algebraic Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray
open AssemblyClone.NativeFields.QueryTests (old)
open AssemblyItem.Creation.NativeFields.Tests (input source copy expectedCells)

def ownerCell (safety : Bool) : Compiler.ZigAir.Memory.Allocation :=
  { AssemblyClone.NativeFields.QueryTests.ownerCell safety false with cells :=
    [(16, .pointer Publication.pointerType ⟨7, 0⟩), (24, .scalar (.int false 64 1)), (32, .scalar (.int false 64 1))] ++ (if safety then [(40, .scalar (.int false 64 0))] else []) }
def oldBacking : Compiler.ZigAir.Memory.Allocation := { AssemblyClone.NativeFields.QueryTests.backing with type := Backing.type 1 }
def initial (safety : Bool) : Session (Publication.Effects Nat) :=
  { AppendOwnershipTests.initial safety with memory :=
    { (AppendOwnershipTests.initial safety).memory with
      heap := ((AppendOwnershipTests.initial safety).memory.heap.replace 6 (ownerCell safety)).replace 7 oldBacking } }

theorem initial_frame (safety : Bool) (id : Nat) (ownerApart : id ≠ 6) (backingApart : id ≠ 7) :
    (initial safety).memory.heap.lookup id = (AppendOwnershipTests.initial safety).memory.heap.lookup id :=
  (replace_other _ 7 id _ backingApart).trans (replace_other _ 6 id _ ownerApart)

theorem initial_valid (safety : Bool) : Valid (initial safety) := by
  have prior := AppendOwnershipTests.initial_valid safety
  refine ⟨by cases safety <;> decide +kernel, ?_, ?_⟩
  · intro allocator id values nonempty stored
    have ownerApart : id ≠ 6 := by intro same; subst id; cases stored
    have backingApart : id ≠ 7 := by intro same; subst id; cases stored
    obtain ⟨⟨cell, found, typed, writable, persistent⟩, represented⟩ := prior.related allocator id values nonempty stored
    exact ⟨⟨cell, (initial_frame safety id ownerApart backingApart).trans found, typed, writable, persistent⟩,
      represented_frame _ values represented (initial_frame safety id ownerApart backingApart)⟩
  · intro id block stored
    have ownerApart : id ≠ 6 := by intro same; subst id; cases stored
    by_cases backingSame : id = 7
    · subst id; exact ⟨oldBacking, by cases safety <;> decide +kernel, rfl⟩
    obtain ⟨cell, found, persistent⟩ := prior.injected id block stored
    exact ⟨cell, (initial_frame safety id ownerApart backingSame).trans found, persistent⟩

def object (empty : Bool) := if empty then 9 else 10
def backing (empty : Bool) := object empty + 2
/-- The empty normalized sentinel aliases the new backing; the empty duplicate
aliases the newly created object. Neither is freed as an argument allocation. -/
def normalized (empty : Bool) : Storage.ArgumentSlice := if empty then ⟨backing empty, []⟩ else AppendOwnershipTests.normalized
def operands (empty : Bool) : Storage.ArgumentSlice := ⟨9, (normalized empty).items⟩
def copied (empty : Bool) : AssemblyClone.NativeFields.ItemValue :=
  { input with verbatim := some ⟨2, 3, ⟨object empty + 1, [8, 9], 0⟩⟩ }
def key (empty : Bool) : Key := { AppendOwnershipTests.key with arguments := (normalized empty).items }
def allocate : Backing.Registry.Allocate Nat := fun allocator bytes alignment effects =>
  if allocator = 7 && bytes = 224 && alignment = 8 then (some 2304, effects * 10 + 7) else (none, effects * 10 + 9)
def releaseBacking : Backing.Release.External Nat := fun allocator base bytes alignment effects =>
  effects * 10 + (if allocator = 7 && base = 1024 && bytes = 32 && alignment = 8 then 8 else 9)
def growth : Growth.Registered.Callbacks Nat := ⟨.noRemap 17 23, releaseBacking⟩
def ops (empty : Bool) : Operations Nat := { PreparationTests.ops with
  probe := fun _ reached =>
    (readItems reached.memory (Owner.headerAddress ⟨6, 0⟩) != .ok (.slice itemsType ⟨backing empty, 0⟩ 2), reached.effects * 10 + 1)
  arguments := { ExpressionDeinit.Tests.external with free := fun slice reached => reached.effects * 10 +
    (if slice.address = 9 then 4 else if readItems reached.memory (Owner.headerAddress ⟨6, 0⟩) ==
      .ok (.slice itemsType ⟨backing empty, 0⟩ 1) && (reached.memory.heap.lookup (object empty)).isNone then 5 else 9) } }
def world (safety : Bool) : World (Publication.Effects Nat) := ⟨Interner.observedHeap [old] (fun _ => none), initial safety⟩
def handle (empty : Bool) : Handle := ⟨view (normalized empty), (normalized empty).items, none⟩
def taken (safety empty : Bool) := takeOwned normalizationOwnershipCode (Publication.external (ops empty).arguments) 7 (handle empty) (initial safety)
def made (safety empty : Bool) := AssemblyItem.Creation.create (observe (ops empty).create) 7 input.item (taken safety empty).2
def cloned (safety empty : Bool) := AssemblyClone.Physical.run (observe (ops empty).copy) 7 input (made safety empty).2
def ready (safety empty : Bool) : Session (Publication.Effects Nat) :=
  { (cloned safety empty).2 with memory := { (cloned safety empty).2.memory with
    heap := (cloned safety empty).2.memory.heap.replace (object empty)
      { AssemblyItem.Creation.cell 80 with cells := expectedCells (object empty + 1) 0 } } }
def execute (safety empty : Bool) := execution (ops empty) allocate safety 7 6 ⟨2, 0, 0⟩ source Insertion.Tests.model
  input (key empty) (normalized empty) true [old] (world safety) (some growth)

theorem preparation_results (safety empty : Bool) :
    taken safety empty = (.ok (operands empty, handle empty), (taken safety empty).2) ∧
    made safety empty = (.ok (object empty), (made safety empty).2) ∧
    cloned safety empty = (.ok (copied empty), (cloned safety empty).2) ∧
    AssemblyClone.NativeFields.install (copied empty) (object empty) (cloned safety empty).2 = .ok (ready safety empty) := by
  cases safety <;> cases empty <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem backing_response (safety empty : Bool) :
    allocate 7 224 8 (ready safety empty).effects.allocator = (some 2304, if empty then 567 else 1567) ∧
    RegionAllocation.Fits (ready safety empty).memory ⟨224, 8⟩ 2304 := by
  refine ⟨by cases safety <;> cases empty <;> insertion_kernel_rfl, ?_⟩
  refine ⟨by decide, by decide, by decide, ?_⟩
  have bound : (ready safety empty).memory.heap.all (fun entry =>
      decide (entry.2.base + (entry.2.type.layout.getD ⟨0, 1⟩).bytes ≤ 2304)) = true := by
    cases safety <;> cases empty <;> decide +kernel
  intro entry present layout shaped
  have checked := (List.all_eq_true.mp bound) entry present
  simp only [shaped, Option.getD_some, decide_eq_true_eq] at checked
  exact Or.inr checked

theorem probe_result (safety empty : Bool) :
    (ops empty).probe (key empty) (Publication.forget (memory (append safety allocate 7 6 [old] input (key empty) (normalized empty)
      (((key empty).eval Insertion.Tests.model (world safety).graph.read).getD 0) Storage.preparationOwnership
      (preparedFrame (object empty) (copied empty) (operands empty) (ready safety empty)) (some growth)).2)) =
      (false, if empty then 56781 else 156781) := by
  cases safety <;> cases empty <;> insertion_kernel_rfl

theorem derived_contract (safety empty : Bool) : ∃ after,
    execute safety empty = ((.ok (some .allocationFailure),
      (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).run Storage.publicationOwnership), after) ∧
    Valid (memory after) ∧ Memory.Vector 7 (memory after).heap (backing empty) [old] ∧
    readHeader (memory after).memory (Owner.headerAddress ⟨6, 0⟩) =
      .ok (.slice itemsType ⟨backing empty, 0⟩ 1, .scalar (.int false 64 7)) ∧
    (memory after).memory.nextId = backing empty + 1 ∧ (memory after).memory.nextAddress = 2528 ∧
    after.item.object = none ∧ after.item.clone.value = none ∧ after.item.clone.execution.invalidated = true ∧
    Backing.Release.Owned 7 ⟨backing empty, 0⟩ 7 (memory after) ∧
    DescriptorRelation.Prefix (memory after).memory (backing empty) [old] ∧
    (memory after).heap 7 = none ∧ (memory after).memory.heap.lookup 7 = none ∧
    (∀ id, representativeFields (memory after).memory (Owner.headerAddress ⟨6, 0⟩) id =
      .ok ((Storage.representativeProgram.run [old] id).map (DescriptorRelation.values id.toNat))) := by
  have represented : AssemblyClone.NativeFields.Represents (initial safety).memory source input :=
    AssemblyItem.Creation.NativeFields.Tests.source_represented.frame
      ((initial_frame safety 5 (by decide) (by decide)).trans ((AppendOwnershipTests.initial_frame safety 5 (by decide)).trans
        (AssemblyClone.NativeFields.QueryTests.initial_frame safety false 5 (by decide))))
  have live : Memory.SliceValid 7 (initial safety).heap (normalized empty) := by
    cases empty
    · exact Or.inr (by rfl')
    · exact Or.inl rfl
  have publication : Publication.Input 7 ⟨2, 0, 0⟩ (key empty) (normalized empty) (world safety) :=
    ⟨rfl, (fun _ impossible => by cases impossible), (fun _ impossible => by cases impossible),
      (fun _ impossible => by cases impossible)⟩
  have oldOwned : Backing.Release.Owned 7 ⟨7, 0⟩ 1 (initial safety) :=
    ⟨rfl, ⟨[old], by rfl'⟩, oldBacking, by cases safety <;> decide +kernel, rfl, rfl, rfl⟩
  have rows : DescriptorRelation.Prefix (initial safety).memory 7 [old] := by
    intro index cell found
    cases index with
    | zero => cases Option.some.inj found; unfold DescriptorRelation.Row; cases safety <;> decide +kernel
    | succ index => simp at found
  have observations := preparation_results safety empty
  have result := deterministic_growing_oom (ops empty) allocate releaseBacking safety 7 6 7 1 7 (object empty) 2304 17 23 (ownerCell safety)
    ⟨2, 0, 0⟩ source Insertion.Tests.model input (copied empty) (key empty) (normalized empty) (operands empty) [old] (world safety)
    (taken safety empty).2 (made safety empty).2 (cloned safety empty).2 (handle empty)
    (initial_valid safety) live represented ExpressionDeinit.Tests.external_admitted
    (by cases safety <;> decide +kernel) rfl rfl oldOwned (by cases safety <;> decide +kernel) (by cases safety <;> decide +kernel)
    (by rfl') rows (by decide) (by decide) (by decide) (by decide) (by decide) publication observations.1 observations.2.1 observations.2.2.1 (if empty then 567 else 1567) (by
      intro installed assigned
      cases Except.ok.inj (assigned.symm.trans observations.2.2.2)
      exact backing_response safety empty) (if empty then 56781 else 156781) (by
      intro installed assigned
      cases Except.ok.inj (assigned.symm.trans observations.2.2.2)
      exact probe_result safety empty)
    (Owner.NativeLock.checkHeader_of_cell safety _ 6 (ownerCell safety) (initial_valid safety).memory
      (by cases safety <;> decide +kernel) rfl (by intro active; subst safety; rfl))
  have nextId : (cloned safety empty).2.memory.nextId = backing empty := by cases safety <;> cases empty <;> insertion_kernel_rfl
  have nextAddress : max (cloned safety empty).2.memory.nextAddress (2304 + 224) = 2528 := by
    cases safety <;> cases empty <;> insertion_kernel_rfl
  simpa only [nextId, nextAddress] using result

theorem reached_observations (safety empty : Bool) :
    (memory (execute safety empty).2).effects.allocator = (if empty then 5678123 else 1567812345) ∧
    ((memory (execute safety empty).2).memory.heap.lookup (object empty)).isNone = true ∧
    ((memory (execute safety empty).2).memory.heap.lookup (object empty + 1)).isNone = true ∧
    Backing.Release.Owned 7 ⟨backing empty, 0⟩ 7 (memory (execute safety empty).2) ∧
    (memory (execute safety empty).2).effects.keys = (initial safety).effects.keys := by
  cases safety <;> cases empty <;> refine ⟨by insertion_kernel_rfl, by insertion_kernel_rfl,
    by insertion_kernel_rfl, ?_, by insertion_kernel_rfl⟩
  all_goals refine ⟨rfl, ⟨[old], ?_⟩, ⟨2304, Backing.type 7, oldBacking.cells.reverse, true, false⟩, ?_, rfl, rfl, rfl⟩
  all_goals try unfold Memory.Vector
  all_goals insertion_kernel_rfl

theorem retained_allocations (safety empty : Bool) :
    ([0, 1, 3, 5].map fun id => (memory (execute safety empty).2).memory.heap.lookup id) =
      ([0, 1, 3, 5].map fun id => (initial safety).memory.heap.lookup id) ∧
    ((memory (execute safety empty).2).memory.heap.lookup 8).isNone = !empty ∧
    (memory (execute safety empty).2).heap 7 = none ∧
    (memory (execute safety empty).2).memory.heap.lookup 7 = none ∧
    DescriptorRelation.Prefix (memory (execute safety empty).2).memory (backing empty) [old] := by
  cases safety <;> cases empty <;> refine ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, ?_⟩
  all_goals
    intro index cell found
    cases index with
    | zero => cases Option.some.inj found; unfold DescriptorRelation.Row; insertion_kernel_rfl
    | succ index => simp at found

def rejectedAllocation (safety empty : Bool) (response : Option Nat) :=
  execution (ops empty) (fun _ _ _ effects => (response, effects * 10 + 7)) safety 7 6 ⟨2, 0, 0⟩ source
    Insertion.Tests.model input (key empty) (normalized empty) true [old] (world safety) (some growth)

/-- Backing OOM unwinds local owners; the old full container remains live. -/
theorem backing_oom (safety empty : Bool) :
    (rejectedAllocation safety empty none).1.1 = .ok (some .allocationFailure) ∧
    (memory (rejectedAllocation safety empty none).2).effects.allocator = (if empty then 56723 else 15672349) ∧
    readHeader (memory (rejectedAllocation safety empty none).2).memory (Owner.headerAddress ⟨6, 0⟩) =
      .ok (.slice itemsType ⟨7, 0⟩ 1, .scalar (.int false 64 1)) ∧
    (memory (rejectedAllocation safety empty none).2).memory.nextId = backing empty ∧
    (memory (rejectedAllocation safety empty none).2).heap (backing empty) = none := by
  cases safety <;> cases empty <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl,
    by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

/-- A misaligned external response is an explicit checked rejection. It keeps
the reached private effect and local owners; it is not ordinary OOM unwinding. -/
theorem invalid_backing_response (safety empty : Bool) :
    (rejectedAllocation safety empty (some 2305)).1.1 = .error (.append (.memory .memoryValidity)) ∧
    (memory (rejectedAllocation safety empty (some 2305)).2).effects.allocator = (if empty then 567 else 1567) ∧
    (rejectedAllocation safety empty (some 2305)).2.item.object = some (object empty) ∧
    (memory (rejectedAllocation safety empty (some 2305)).2).memory.nextId = backing empty := by
  cases safety <;> cases empty <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl,
    by insertion_kernel_rfl, by insertion_kernel_rfl⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.GrowingTests
