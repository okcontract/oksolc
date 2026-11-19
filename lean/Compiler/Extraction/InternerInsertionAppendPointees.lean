/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionPointeeFrame

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open RepresentativeArray

/-- Shared pointee preservation for a native append into fresh or existing
representative storage. The caller derives the heap write and native frame from
its actual append. Registry kinds and typed owner geometry derive separation;
empty argument/payload sentinels do not require distinct allocations. -/
theorem append_pointees (allocator container lifetime object : Nat)
    (runtimeSafety : Bool) (ownerCell : Compiler.ZigAir.Memory.Allocation)
    (stored : AssemblyClone.NativeFields.ItemValue) (rows : List Storage.Cell)
    (middle before after : Session σ)
    (installed : AssemblyClone.NativeFields.Installed allocator object stored middle before)
    (ownerFound : before.memory.heap.lookup container = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety)
    (target : before.heap lifetime = none ∨ ∃ old, Memory.Vector allocator before.heap lifetime old)
    (heap : after.heap = Memory.write before.heap lifetime (some ⟨allocator, .representatives rows⟩))
    (frame : ∀ id, id ≠ container → id ≠ lifetime → after.memory.heap.lookup id = before.memory.heap.lookup id) :
    AssemblyItem.Owned allocator object after ∧
    AssemblyClone.NativeFields.Represents after.memory ⟨object, 0⟩ stored ∧
    (∀ slice, AssemblyClone.Physical.payload stored = some slice → AssemblyItemDeinit.Owned allocator slice after) ∧
    (∀ argumentAllocator slice, Memory.SliceValid argumentAllocator before.heap slice →
      Memory.SliceValid argumentAllocator after.heap slice) ∧
    (∀ payload, stored.verbatim = some payload → AssemblyClone.Physical.Reads after.memory payload.data) := by
  have preserved := representative_pointees allocator container object [lifetime] runtimeSafety ownerCell stored middle before after
    installed ownerFound ownerTyped (by intro id member; have same := List.mem_singleton.mp member; subst id; exact target)
    (by intro id outside; rw [heap, Memory.write_other _ _ _ _ (by simpa only [List.mem_singleton] using outside)])
    (fun id ownerApart outside => frame id ownerApart (by simpa only [List.mem_singleton] using outside))
  exact preserved

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
