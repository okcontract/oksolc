/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyItemCreationFields

namespace Compiler.Extraction.AssemblyClone.NativeFields
open Compiler.Extraction.Memory Compiler.Extraction.Storage
open Compiler.Extraction.Memory.Arguments.Normalization

/-- The exact registry item comes from actual creation and clone execution.
Complete installation retains that registry and the live argument slice. This
does not infer a key value from existential allocation ownership. -/
theorem created_resident (allocate : AssemblyItem.Creation.Allocate σ) (copy : Physical.Allocate σ)
    (allocator object : Nat) (input copied : ItemValue) (before allocated middle ready : Session σ)
    (logical : Storage.Cell) (initial : Valid before)
    (arguments : SliceValid allocator before.heap logical.argumentSlice)
    (address : logical.itemAddress = object) (item : logical.item = copied.item)
    (created : AssemblyItem.Creation.create allocate allocator input.item before = (.ok object, allocated))
    (cloned : Physical.run copy allocator input allocated = (.ok copied, middle))
    (installed : Installed allocator object copied middle ready) :
    Resident allocator ready.heap logical := by
  have made := AssemblyItem.Creation.create_verified allocate allocator object input.item before allocated initial created
  have copiedPost := Physical.run_valid copy allocator input copied allocated middle made.valid cloned
  have stored := AssemblyItem.Creation.create_registered allocate allocator object input.item before allocated created
  have retained := copiedPost.registered made.valid object _ stored
  have live := copiedPost.arguments made.valid logical.argumentSlice
    (made.arguments allocator object before allocated initial logical.argumentSlice arguments)
  refine ⟨?_, ?_⟩
  · simpa only [installed.heap, address, item, copiedPost.same.1] using retained
  · simpa only [installed.heap] using live

end Compiler.Extraction.AssemblyClone.NativeFields
