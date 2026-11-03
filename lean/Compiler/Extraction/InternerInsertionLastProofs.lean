/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionNative
import Compiler.Extraction.ExpressionDeinitNativeProofs

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open RepresentativeArray

/-- Initial backing ownership and native header contents derive the last-row
address. The native destructor derives cleanup from that row's initial owners;
neither a successful selector nor final memory validity is assumed. The full
native cleanup witness remains available to subsequent pop/frame composition. -/
theorem releaseLast_verified (ops : Operations σ) (allocator container lifetime capacity index object : Nat)
    (input : AssemblyClone.NativeFields.ItemValue) (arguments : Storage.ArgumentSlice) (before : Frame σ)
    (initial : Valid (memory before))
    (rowOwned : Backing.Release.Owned allocator ⟨lifetime, 0⟩ capacity (memory before))
    (inside : index < capacity)
    (header : readItems (memory before).memory (Owner.headerAddress ⟨container, 0⟩) =
      .ok (.slice itemsType ⟨lifetime, 0⟩ (index + 1)))
    (itemOwned : AssemblyItem.Owned allocator object (memory before))
    (itemRead : ExpressionDeinit.Native.Fields.item (memory before).memory ⟨lifetime, index * 32⟩ = .ok ⟨object, 0⟩)
    (argumentRead : Expression.readField (memory before).memory false ⟨lifetime, index * 32⟩ Expression.argumentsOffset =
      .ok (.slice Expression.argumentsType ⟨arguments.address, 0⟩ arguments.items.length))
    (live : Memory.SliceValid allocator (memory before).heap arguments)
    (represented : AssemblyClone.NativeFields.Represents (memory before).memory ⟨object, 0⟩ input)
    (payloadOwned : ∀ slice, AssemblyClone.Physical.payload input = some slice → AssemblyItemDeinit.Owned allocator slice (memory before)) :
    ∃ reached after,
      ExpressionDeinit.Native.run (release ops.bytes) (release ops.objects) (Publication.external ops.arguments)
        allocator ⟨lifetime, index * 32⟩ (memory before) = (.ok (), reached) ∧
      releaseLast ops allocator container before = (.ok (), after) ∧
      memory after = reached.memory ∧ Valid (memory after) ∧
      after.item.object = none ∧ after.item.clone.value = none ∧ after.item.clone.execution.invalidated = true ∧
      (memory after).heap lifetime = (memory before).heap lifetime := by
  obtain ⟨_, _, _, _, reached, ran, _, _, _, _, _, _, _, _, _, _, _, invalidated, valid, registry, _⟩ :=
    ExpressionDeinit.Native.run_verified (release ops.bytes) (release ops.objects) (Publication.external ops.arguments)
      allocator lifetime capacity index object input arguments (memory before) initial rowOwned inside itemOwned
      itemRead argumentRead live represented payloadOwned
  obtain ⟨_, _, backing, found, typed, writable, _⟩ := rowOwned
  have selected := Last.from_array (memory before).memory (Owner.headerAddress ⟨container, 0⟩)
    lifetime capacity index backing initial.memory found typed writable inside header
  refine ⟨reached, _, ran, releaseLast_success ops allocator container before _ reached selected ran,
    rfl, valid, rfl, rfl, invalidated, registry⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
