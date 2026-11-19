/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionAppendOwnership
import Compiler.Extraction.AssemblyCloneQueryRegistryTests
import Compiler.Extraction.InternerInsertionTests
import Compiler.Extraction.InsertionKernelTestSupport

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.AppendOwnershipTests
open Compiler.ZigAir.Memory Compiler.Algebraic Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray
open AssemblyClone.NativeFields.QueryTests (old ownerCell backing)
open AssemblyItem.Creation.NativeFields.Tests (input source copy expectedCells returned_pair)

def normalized : Storage.ArgumentSlice := ⟨8, [99]⟩
def operands : Storage.ArgumentSlice := ⟨1, [99]⟩
def normalizedCell : Compiler.ZigAir.Memory.Allocation := { Memory.Arguments.Tests.secondCell with base := 2048 }
/-- The retained old row owns argument allocation 0; the new row and outer
normalized buffer own distinct allocations 1 and 8. No old graph owner is freed. -/
def initial (safety : Bool) : Session (Publication.Effects Nat) :=
  let prior := AssemblyClone.NativeFields.QueryTests.initial safety false
  ⟨Memory.write (Memory.write prior.heap 1 (some ⟨7, .arguments [99]⟩)) 8 (some ⟨7, .arguments [99]⟩),
    ⟨(8, normalizedCell) :: prior.memory.heap, 9, 2052⟩, ⟨fun _ => none, 0⟩⟩

theorem initial_frame (safety : Bool) (id : Nat) (apart : id ≠ 8) :
    (initial safety).memory.heap.lookup id = (AssemblyClone.NativeFields.QueryTests.initial safety false).memory.heap.lookup id := by
  simp only [initial, Heap.lookup_cons, if_neg (Ne.symm apart)]

theorem initial_valid (safety : Bool) : Valid (initial safety) := by
  have prior := AssemblyClone.NativeFields.QueryTests.initial_valid safety false
  refine ⟨by cases safety <;> decide +kernel, ?_, ?_⟩
  · intro allocator id values nonempty stored
    by_cases eight : id = 8
    · subst id
      have same : allocator = 7 ∧ values = [99] := by simpa [initial, Memory.write] using stored.symm
      rcases same with ⟨rfl, rfl⟩
      refine ⟨⟨normalizedCell, rfl, rfl, rfl, rfl⟩, rfl, ?_⟩
      intro index inside
      have only : index = 0 := by simp only [List.length_cons, List.length_nil] at inside; omega
      subst index
      rfl'
    have old : ∃ originalAllocator, (AssemblyClone.NativeFields.QueryTests.initial safety false).heap id =
        some ⟨originalAllocator, .arguments values⟩ := by
      by_cases one : id = 1
      · subst id
        have same : allocator = 7 ∧ values = [99] := by simpa [initial, Memory.write] using stored.symm
        rw [same.2]
        exact ⟨11, rfl⟩
      · exact ⟨allocator, by simpa only [initial, Memory.write, if_neg eight, if_neg one] using stored⟩
    obtain ⟨originalAllocator, old⟩ := old
    obtain ⟨⟨cell, found, typed, writable, persistent⟩, represented⟩ := prior.related originalAllocator id values nonempty old
    exact ⟨⟨cell, (initial_frame safety id eight).trans found, typed, writable, persistent⟩,
      represented_frame _ _ represented (initial_frame safety id eight)⟩
  · intro id block stored
    by_cases eight : id = 8
    · subst id; exact ⟨normalizedCell, rfl, rfl⟩
    by_cases one : id = 1
    · subst id
      exact ⟨Memory.Arguments.Tests.secondCell, (initial_frame safety 1 (by decide)).trans rfl, rfl⟩
    obtain ⟨cell, found, persistent⟩ := prior.injected id block
      (by simpa only [initial, Memory.write, if_neg eight, if_neg one] using stored)
    exact ⟨cell, (initial_frame safety id eight).trans found, persistent⟩

def made (safety : Bool) := AssemblyItem.Creation.create (observe AssemblyItem.Creation.Insertion.Tests.allocate) 7 input.item (initial safety)
def cloned (safety : Bool) := AssemblyClone.Physical.run (observe (copy)) 7 input (made safety).2
def copied : AssemblyClone.NativeFields.ItemValue := { input with verbatim := some ⟨2, 3, ⟨10, [8, 9], 0⟩⟩ }
def ready (safety : Bool) : Session (Publication.Effects Nat) :=
  { (cloned safety).2 with memory := { (cloned safety).2.memory with
    heap := (cloned safety).2.memory.heap.replace 9 { AssemblyItem.Creation.cell 80 with cells := expectedCells 10 0 } } }
def compactReady (safety : Bool) : Session (Publication.Effects Nat) :=
  ⟨Memory.write (Memory.write (initial safety).heap 9 (some ⟨7, .item input.item⟩)) 10 (some ⟨7, .bytes 2⟩),
    ⟨(10, AssemblyClone.Physical.cell 2 320 (AssemblyClone.Physical.copiedCells ⟨3, [8, 9], 1⟩)) ::
      (9, { AssemblyItem.Creation.cell 80 with cells := expectedCells 10 0 }) :: (initial safety).memory.heap,
      11, 2052⟩, ⟨fun _ => none, 56⟩⟩
theorem ready_eq (safety : Bool) : ready safety = compactReady safety := by
  cases safety <;> insertion_kernel_rfl

def before (safety : Bool) : Frame Nat := ⟨⟨⟨⟨compactReady safety, false⟩, some copied⟩, some 9⟩, some operands⟩

theorem created_result (safety : Bool) : made safety = (.ok 9, (made safety).2) :=
  returned_pair _ _ (by cases safety <;> decide +kernel)
theorem cloned_result (safety : Bool) : cloned safety = (.ok copied, (cloned safety).2) := by
  cases safety <;> insertion_kernel_rfl

theorem installed (safety : Bool) : AssemblyClone.NativeFields.Installed 7 9 copied (cloned safety).2 (ready safety) := by
  have created := AssemblyItem.Creation.create_verified (observe AssemblyItem.Creation.Insertion.Tests.allocate) 7 9 input.item
    (initial safety) (made safety).2 (initial_valid safety) (created_result safety)
  have represented : AssemblyClone.NativeFields.Represents (initial safety).memory source input :=
    AssemblyItem.Creation.NativeFields.Tests.source_represented.frame
      ((initial_frame safety 5 (by decide)).trans (AssemblyClone.NativeFields.QueryTests.initial_frame safety false 5 (by decide)))
  have live := AssemblyItem.Creation.NativeFields.represented_after_create _ _ 7 9 source input
    (initial_valid safety) represented created
  obtain ⟨after, assigned, result⟩ := AssemblyClone.NativeFields.clone_install (observe (copy)) 7 9 source input copied
    (made safety).2 (cloned safety).2 created.valid live created.owned (cloned_result safety)
  have written : AssemblyItem.Fields.assign (AssemblyClone.NativeFields.values copied) 9 (cloned safety).2.memory =
      .ok (ready safety).memory := by cases safety <;> decide +kernel
  have stored := AssemblyClone.NativeFields.install_assigned copied 9 (cloned safety).2 (ready safety).memory written
  cases Except.ok.inj (assigned.symm.trans stored)
  exact result

def key : Key := ⟨input.item.kind, 254, input.item.data, normalized.items, 31⟩
def ownership : Storage.State := { owner := fun _ => .local, flag := fun _ => true, capturedId := true }
def handed := (((Storage.Command.append.success ⟨true, true, fun _ => false⟩ ownership).setFlag .arguments false).setFlag .allocation false).setFlag .value false
def graph (_ : Storage.State) (_ : Frame Nat) := Interner.observedHeap [old] (fun _ => none)
def allocate : Backing.Registry.Allocate Nat := fun _ _ _ effects => (none, effects + 999)
def ops : Operations Nat := { Insertion.Tests.ops with
  probe := fun _ reached =>
    (readItems reached.memory (Owner.headerAddress ⟨6, 0⟩) != .ok (.slice itemsType ⟨7, 0⟩ 2), reached.effects * 10 + 1)
  bytes := fun _ reached => reached.effects * 10 + 2
  objects := fun _ reached => reached.effects * 10 + 3
  arguments := { Insertion.Tests.ops.arguments with free := fun slice reached => reached.effects * 10 +
    (if slice.address = 1 then 4 else if readItems reached.memory (Owner.headerAddress ⟨6, 0⟩) ==
      .ok (.slice itemsType ⟨7, 0⟩ 1) && (reached.memory.heap.lookup 9).isNone then 5 else 9) } }
def calls (safety : Bool) := callbacks ops allocate safety 7 6 ⟨2, 0, 0⟩ source input key normalized [old] 0 graph
def appended (safety : Bool) := (calls safety |>.attempt .append ownership (before safety)).2
def failed (safety : Bool) := (calls safety |>.attempt .publish handed (appended safety)).2
def execute (safety : Bool) := (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).execute (calls safety) handed (failed safety)

theorem derived_contract (safety : Bool) : ∃ after,
    execute safety = ((.ok (), (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).run handed), after) ∧
    Valid (memory after) ∧ Memory.Vector 7 (memory after).heap 7 [old] ∧
    (memory after).memory.nextId = (memory (before safety)).memory.nextId ∧
    (memory after).memory.nextAddress = (memory (before safety)).memory.nextAddress := by
  have rows : DescriptorRelation.Prefix (compactReady safety).memory 7 [old] := by
    intro index cell found
    cases index with
    | zero => cases Option.some.inj found; unfold DescriptorRelation.Row; cases safety <;> decide +kernel
    | succ index => simp at found
  have publication : Publication.Input 7 ⟨2, 0, 0⟩ key normalized ⟨graph ownership (before safety), memory (before safety)⟩ :=
    ⟨rfl, (fun _ impossible => by cases impossible), (fun _ impossible => by cases impossible),
      (fun _ impossible => by cases impossible)⟩
  have installedBefore : AssemblyClone.NativeFields.Installed 7 9 copied (cloned safety).2 (memory (before safety)) := by
    change AssemblyClone.NativeFields.Installed 7 9 copied (cloned safety).2 (compactReady safety)
    rw [← ready_eq]
    exact installed safety
  obtain ⟨appendedState, failedState, _, after, appendRun, publishRun, _, _, cleaned, _, valid, vector,
      _, _, _, nextId, nextAddress, _⟩ :=
    spare_publication_oom_cleanup ops allocate safety 7 6 7 2 9 (ownerCell safety false) backing input copied key
      normalized operands [old] 0 ownership (cloned safety).2 (before safety) ⟨2, 0, 0⟩ source graph installedBefore
      rfl rfl rfl (by cases safety <;> decide +kernel) rfl rfl (by cases safety <;> decide +kernel) rfl rfl
      (by cases safety <;> decide +kernel) (by cases safety <;> decide +kernel) (by rfl') rows (by decide) (by decide)
      (by decide) (Or.inr (by rfl')) (Or.inr (by rfl')) (by decide) publication
      ((memory (before safety)).effects.allocator * 10 + 1) (by cases safety <;> decide +kernel)
  have sameAppended : appendedState = appended safety := (congrArg Prod.snd appendRun).symm
  subst appendedState
  have sameFailed : failedState = failed safety := (congrArg Prod.snd publishRun).symm
  subst failedState
  exact ⟨after, cleaned, valid, vector, nextId, nextAddress⟩

theorem observations (safety : Bool) :
    (calls safety |>.attempt .append ownership (before safety)).1 = .ok true ∧
    (calls safety |>.attempt .publish handed (appended safety)).1 = .ok false ∧
    (memory (execute safety).2).effects.allocator = (memory (before safety)).effects.allocator * 100000 + 12345 ∧
    (memory (execute safety).2).memory.heap.lookup 9 = none ∧
    (memory (execute safety).2).memory.heap.lookup 10 = none ∧
    (memory (execute safety).2).memory.heap.lookup 1 = none ∧
    (memory (execute safety).2).memory.heap.lookup 8 = none ∧
    (memory (execute safety).2).memory.heap.lookup 0 = (memory (before safety)).memory.heap.lookup 0 ∧
    (memory (execute safety).2).memory.heap.lookup 5 = some AssemblyItem.Creation.NativeFields.Tests.sourceCell := by
  cases safety <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl,
    by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

/-- Admission faults stay distinct from OOM and do not initiate rollback. -/
theorem admission_rejection (safety : Bool) :
    let rejected := (callbacks ops allocate safety 7 6 ⟨2, 0, 0⟩ source input { key with arguments := [] }
      normalized [old] 0 graph).attempt .publish handed (appended safety)
    rejected.1 = .error (.base (.publication (.language .safetyFault))) ∧
    (memory rejected.2).effects.allocator = (memory (appended safety)).effects.allocator ∧
    readItems (memory rejected.2).memory (Owner.headerAddress ⟨6, 0⟩) = .ok (.slice itemsType ⟨7, 0⟩ 2) := by
  cases safety <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem missing_clone_rejection (safety : Bool) :
    let prior := before safety
    let rejected := append safety allocate 7 6 [old] input key normalized 0 ownership
      { prior with item := { prior.item with clone := { prior.item.clone with value := none } } }
    rejected.1 = .error (.base .missingValue) ∧
    readItems (memory rejected.2).memory (Owner.headerAddress ⟨6, 0⟩) = .ok (.slice itemsType ⟨7, 0⟩ 1) := by
  cases safety <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.AppendOwnershipTests
