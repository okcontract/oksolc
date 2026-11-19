/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionCapacityCompletion

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- An actual allocation failure, including its reached cleanup ownership,
passes the native header check and leaves the logical graph unchanged. The
allocation theorem supplies this execution; no fixture allocator or debug
fields participate in the projection. -/
theorem CallerInput.insert_allocation_failure (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (allocator owner : Nat) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (meaning : Meaning) (request : Interner.Request) (values : List NodeId)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice) (lookup : Handle)
    (constructed : World (Publication.Effects σ)) (taken : OwnedCall.State (Publication.Effects σ))
    (rows : List Storage.Cell) (growth : Option (Growth.Registered.Callbacks σ))
    (entry : CallerInput allocator source address request values input key constructed taken normalized lookup)
    (ownerCell : Compiler.ZigAir.Memory.Allocation) (backing : Compiler.ZigAir.Memory.Address)
    (found : constructed.memory.memory.heap.lookup owner = some ownerCell)
    (header : readItems constructed.memory.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType backing rows.length))
    (projected : taken.world.graph.representatives = some rows)
    (reads : taken.world.graph.read = Storage.readValue rows) (after : Frame σ)
    (ran : execution ops allocate safety allocator owner source address meaning input key normalized true rows taken.world growth =
      ((.ok (some .allocationFailure), (Storage.Cleanup.sequence [.value, .allocation, .arguments, .normalized]).run preparationOwnership), after)) :
    insert ops allocate safety allocator owner source address meaning input key normalized true growth taken.world =
      (.error (.language .outOfMemory), { taken.world with memory := memory after }) := by
  have reached := (readField_eq_of_lookup constructed.memory.memory taken.world.memory.memory
    (Owner.headerAddress ⟨owner, 0⟩) itemsOffset (entry.native_frame owner ownerCell found)).trans header
  exact Native.insert_allocation_failure ops allocate safety allocator owner source address meaning input key normalized
    taken.world rows growth backing reached projected reads _ after rfl rfl ran

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
