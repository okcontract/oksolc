/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionCapacity
import Compiler.Extraction.InternerCallerTransferredCleanup

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

section Caller
variable (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
  (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
  (meaning : Meaning) (request : Interner.Request) (values : List NodeId)
  (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice) (lookup : Handle)
  (before : World (Publication.Effects σ)) (taken : OwnedCall.State (Publication.Effects σ))
  (deterministic : Bool) (cells : List Storage.Cell) (growth : Option (Growth.Registered.Callbacks σ))

/-- The actual caller prefix preserves the owner's native header. Its reached
read validates the row count and supplies the capacity input for every insertion
outcome. Native field correspondence is stated at entry, not assumed again after
normalization and take. -/
theorem CallerInput.checked_execution
    (entry : CallerInput allocator source itemSource request values input key before taken normalized lookup)
    (ownerCell : Compiler.ZigAir.Memory.Allocation) (backing : Compiler.ZigAir.Memory.Address)
    (owner : before.memory.memory.heap.lookup container = some ownerCell)
    (header : readItems before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType backing cells.length)) :
    checkedExecution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized deterministic cells taken.world growth =
      .ok (execution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized deterministic cells taken.world growth) := by
  have reached := (readField_eq_of_lookup before.memory.memory taken.world.memory.memory
    (Owner.headerAddress ⟨container, 0⟩) itemsOffset (entry.native_frame container ownerCell owner)).trans header
  exact checkedExecution_read ops allocate runtimeSafety allocator container source itemSource meaning input key normalized
    deterministic cells taken.world growth backing reached

/-- The second source capacity check consumes the actual incoming owner before
duplication or transfer. Both determinism settings follow the same normalized
defer, retaining all original native allocations, keys and reached history.
This entry specialization uses the same reached source execution as recursive
call frames. -/
theorem CallerInput.capacity_failure
    (entry : CallerInput allocator source itemSource request values input key before taken normalized lookup)
    (ownerCell : Compiler.ZigAir.Memory.Allocation) (backing : Compiler.ZigAir.Memory.Address)
    (owner : before.memory.memory.heap.lookup container = some ownerCell)
    (header : readItems before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType backing cells.length))
    (saturated : 2 ^ 32 - 1 ≤ cells.length) :
    ∃ after,
      checkedExecution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized deterministic cells taken.world growth =
        .ok ((.ok (some .capacityFailure), Storage.Release.normalized.run Storage.normalizedOwnership), after) ∧
      execution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized deterministic cells taken.world growth =
        ((.ok (some .capacityFailure), Storage.Release.normalized.run Storage.normalizedOwnership), after) ∧
      CallerPreparationFailure allocator normalized before taken.world.memory after ∧
      (memory after).effects = (if normalized.items.isEmpty then taken.world.memory.effects
        else (Publication.external ops.arguments).free normalized taken.world.memory) := by
  let start : Frame σ := ⟨⟨⟨⟨taken.world.memory, false⟩, none⟩, none⟩, none⟩
  obtain ⟨released, freed, post, effects, _⟩ := entry.free_incoming ops allocator source itemSource request values input key normalized lookup
    before taken start entry.origin.held.1.1 entry.origin.held.2.1 (fun _ _ found => found) (fun _ _ stored => stored) rfl ⟨rfl, rfl, rfl⟩
  let after := withMemory start released
  have ran := capacity_execution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized
    deterministic cells taken.world growth released saturated freed
  have checked := entry.checked_execution ops allocate runtimeSafety allocator container source itemSource meaning request values input key normalized lookup
    before taken deterministic cells growth ownerCell backing owner header
  rw [ran] at checked
  exact ⟨after, checked, ran, post, effects⟩

end Caller
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
