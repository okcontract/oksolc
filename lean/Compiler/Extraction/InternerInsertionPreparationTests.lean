/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionPreparedRollback
import Compiler.Extraction.InternerInsertionAppendOwnershipTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.PreparationTests
open Compiler.ZigAir.Memory Compiler.Algebraic Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray
open AssemblyClone.NativeFields.QueryTests (old ownerCell backing)
open AssemblyItem.Creation.NativeFields.Tests (input source copy expectedCells)
open AppendOwnershipTests (initial initial_valid key)

abbrev normalized := AppendOwnershipTests.normalized
abbrev allocate := AppendOwnershipTests.allocate

def operands : Storage.ArgumentSlice := ⟨9, [99]⟩
def copied : AssemblyClone.NativeFields.ItemValue := { input with verbatim := some ⟨2, 3, ⟨11, [8, 9], 0⟩⟩ }
def ops : Operations Nat := { Insertion.Tests.ops with
  create := AssemblyItem.Creation.Insertion.Tests.allocate
  copy := copy
  probe := fun _ reached =>
    (readItems reached.memory (Owner.headerAddress ⟨6, 0⟩) != .ok (.slice itemsType ⟨7, 0⟩ 2), reached.effects * 10 + 1)
  bytes := fun _ reached => reached.effects * 10 + 2
  objects := fun _ reached => reached.effects * 10 + 3
  arguments := { ExpressionDeinit.Tests.external with free := fun slice reached => reached.effects * 10 +
    (if slice.address = 9 then 4 else if readItems reached.memory (Owner.headerAddress ⟨6, 0⟩) ==
      .ok (.slice itemsType ⟨7, 0⟩ 1) && (reached.memory.heap.lookup 10).isNone then 5 else 9) } }
def world (safety : Bool) : World (Publication.Effects Nat) :=
  ⟨Interner.observedHeap [old] (fun _ => none), initial safety⟩
def handle : Handle := ⟨view normalized, normalized.items, none⟩
def taken (safety : Bool) := takeOwned normalizationOwnershipCode (Publication.external ops.arguments) 7 handle (initial safety)
def made (safety : Bool) := AssemblyItem.Creation.create (observe ops.create) 7 input.item (taken safety).2
def cloned (safety : Bool) := AssemblyClone.Physical.run (observe ops.copy) 7 input (made safety).2
def ready (safety : Bool) : Session (Publication.Effects Nat) :=
  { (cloned safety).2 with memory := { (cloned safety).2.memory with
    heap := (cloned safety).2.memory.heap.replace 10 { AssemblyItem.Creation.cell 80 with cells := expectedCells 11 0 } } }
def execute (safety : Bool) := execution ops allocate safety 7 6 ⟨2, 0, 0⟩ source Insertion.Tests.model input key normalized true [old] (world safety)

theorem preparation_results (safety : Bool) :
    taken safety = (.ok (operands, handle), (taken safety).2) ∧
    made safety = (.ok 10, (made safety).2) ∧
    cloned safety = (.ok copied, (cloned safety).2) ∧
    AssemblyClone.NativeFields.install copied 10 (cloned safety).2 = .ok (ready safety) := by
  cases safety <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem probe_result (safety : Bool) :
    ops.probe key (Publication.forget (memory (append safety allocate 7 6 [old] input key normalized
      ((key.eval Insertion.Tests.model (world safety).graph.read).getD 0) Storage.preparationOwnership
      (preparedFrame 10 copied operands (ready safety))).2)) = (false, 1561) := by
  cases safety <;> insertion_kernel_rfl

/-- Initial old-row geometry and normalized/source input facts suffice. The
complete production execution derives every later item, payload and argument
owner, including the separate outer cleanup. Both captured layouts are covered. -/
theorem derived_contract (safety : Bool) : ∃ after,
    execute safety = ((.ok (some .allocationFailure),
      (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).run Storage.publicationOwnership), after) ∧
    Valid (memory after) ∧ Memory.Vector 7 (memory after).heap 7 [old] ∧
    readHeader (memory after).memory (Owner.headerAddress ⟨6, 0⟩) =
      .ok (.slice itemsType ⟨7, 0⟩ 1, .scalar (.int false 64 2)) ∧
    after.item.object = none ∧ after.item.clone.value = none ∧ after.item.clone.execution.invalidated = true := by
  have represented : AssemblyClone.NativeFields.Represents (initial safety).memory source input :=
    AssemblyItem.Creation.NativeFields.Tests.source_represented.frame
      ((AppendOwnershipTests.initial_frame safety 5 (by decide)).trans
        (AssemblyClone.NativeFields.QueryTests.initial_frame safety false 5 (by decide)))
  have rows : DescriptorRelation.Prefix (initial safety).memory 7 [old] := by
    intro index cell found
    cases index with
    | zero => cases Option.some.inj found; unfold DescriptorRelation.Row; cases safety <;> decide +kernel
    | succ index => simp at found
  have publication : Publication.Input 7 ⟨2, 0, 0⟩ key normalized (world safety) :=
    ⟨rfl, (fun _ impossible => by cases impossible), (fun _ impossible => by cases impossible),
      (fun _ impossible => by cases impossible)⟩
  have observations := preparation_results safety
  exact deterministic_spare_oom ops allocate safety 7 6 7 2 10 (ownerCell safety false) backing ⟨2, 0, 0⟩ source
    Insertion.Tests.model input copied key normalized operands [old] (world safety)
    (taken safety).2 (made safety).2 (cloned safety).2 handle (initial_valid safety) (Or.inr (by rfl')) represented
    ExpressionDeinit.Tests.external_admitted (by cases safety <;> decide +kernel) rfl rfl
    (by cases safety <;> decide +kernel) rfl rfl (by cases safety <;> decide +kernel)
    (by cases safety <;> decide +kernel) (by rfl') rows (by decide) (by decide) publication
    observations.1 observations.2.1 observations.2.2.1 1561 (by
      intro installed assigned
      have same := Except.ok.inj (assigned.symm.trans observations.2.2.2)
      rw [same]
      exact probe_result safety)

/-- The probe sees the appended row; argument destruction sees it before pop;
the normalized free sees the shortened header and destroyed object. -/
theorem reached_observations (safety : Bool) :
    (memory (execute safety).2).effects.allocator = 15612345 ∧
    ([8, 9, 10, 11].map fun id => ((memory (execute safety).2).memory.heap.lookup id).isNone) = [true, true, true, true] ∧
    ([0, 1, 3, 5].map fun id => (memory (execute safety).2).memory.heap.lookup id) =
      ([0, 1, 3, 5].map fun id => (initial safety).memory.heap.lookup id) ∧
    (memory (execute safety).2).memory.nextId = 12 ∧
    (memory (execute safety).2).memory.nextAddress = 2060 := by
  cases safety <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl,
    by insertion_kernel_rfl, by insertion_kernel_rfl⟩

/-- An invalid source read is a semantic rejection after argument/object
allocation. It retains the reached state without pretending ordinary unwinding. -/
theorem source_rejection (safety : Bool) :
    let rejected := execution ops allocate safety 7 6 ⟨2, 0, 0⟩ ⟨999, 0⟩ Insertion.Tests.model input key normalized true [old] (world safety)
    rejected.1.1 = .error (.item (.source (.memory .kind .unallocated))) ∧
    (memory rejected.2).effects.allocator = 15 ∧
    (memory rejected.2).memory.nextId = 11 ∧
    (memory rejected.2).heap 9 = some ⟨7, .arguments [99]⟩ ∧
    rejected.2.item.object = some 10 := by
  cases safety <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl,
    by insertion_kernel_rfl, by insertion_kernel_rfl⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.PreparationTests
