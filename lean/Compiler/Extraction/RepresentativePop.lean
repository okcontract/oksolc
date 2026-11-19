/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeGrowingAppend

namespace Compiler.Extraction.RepresentativeArray.Pop
open Compiler.ZigAir.Memory

/-- The insertion errdefer decrements only the native length leaf. Reading the
pointer or capacity first would incorrectly suppress this write on a malformed
header. Underflow is a semantic rejection, never an allocation failure. -/
def run (state : State) (header : Address) : Except Fault State := do
  let value ← readField state header Append.lengthOffset
  let .scalar (.int false 64 length) := value | .error .malformed
  if length ≤ 0 then .error .sourceBounds else
  Append.writeLength state header (length.toNat - 1)

theorem read_rejected (state : State) (header : Address) (reason : Fault)
    (rejected : readField state header Append.lengthOffset = .error reason) :
    run state header = .error reason := by
  simp only [run, rejected, bind, Except.bind]

theorem empty (state : State) (header : Address)
    (loaded : readField state header Append.lengthOffset = .ok (.scalar (.int false 64 0))) :
    run state header = .error .sourceBounds := by
  simp only [run, loaded, bind, Except.bind, Int.le_refl, ↓reduceIte]

theorem decrement (state : State) (header : Address) (length : Nat)
    (loaded : readField state header Append.lengthOffset = .ok (.scalar (.int false 64 (↑(length + 1))))) :
    run state header = Append.writeLength state header length := by
  have positive : ¬ (↑(length + 1) : Int) ≤ 0 := by omega
  simp only [run, loaded, bind, Except.bind, if_neg positive, Int.toNat_natCast, Nat.add_sub_cancel]

/-- Initial owner layout and contents derive the actual decrement and all
frames. This operation neither reads nor destroys the last row; the preceding
source statement owns that obligation. -/
theorem verified (runtimeSafety : Bool) (state : State) (owner : Nat) (cell : Allocation)
    (data : Address) (length capacity : Nat) (valid : state.valid = true)
    (found : state.heap.lookup owner = some cell) (typed : cell.type = Owner.viewType runtimeSafety)
    (writable : cell.writable = true)
    (loaded : readItems state (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType data (length + 1)))
    (capacityRead : readField state (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 capacity)))
    (bounded : length < addressLimit) :
    ∃ after, run state (Owner.headerAddress ⟨owner, 0⟩) = .ok after ∧ after.valid = true ∧
      state.heap.RetainsShape after.heap ∧
      readHeader after (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType data length, .scalar (.int false 64 capacity)) ∧
      after.nextId = state.nextId ∧ after.nextAddress = state.nextAddress ∧
      (∀ other, other ≠ owner → after.heap.lookup other = state.heap.lookup other) := by
  have lengthRead := Append.Execution.owner_length_from_items runtimeSafety state owner cell data (length + 1)
    valid found typed loaded
  obtain ⟨after, written, stored⟩ := Owner.length_store_total runtimeSafety state owner cell length valid found typed writable bounded
  have selectors := Owner.root_header_fields runtimeSafety state owner cell false valid found typed
  have items := Append.readItems_after_length_store_at state after (Owner.headerAddress ⟨owner, 0⟩) data (length + 1) length
    selectors.1 loaded stored
  have capacityKept := (Append.readCapacity_after_length_store_at state after (Owner.headerAddress ⟨owner, 0⟩) length
    selectors.2 stored).trans capacityRead
  have counters := store_keeps_counters _ _ _ _ stored
  refine ⟨after, (decrement state _ length lengthRead).trans written,
    store_preserves_valid _ _ _ _ valid stored, store_retains_shape _ _ _ _ stored,
    ?_, counters.1, counters.2, ?_⟩
  · simp only [readHeader, items, capacityKept, bind, Except.bind]
  · exact heap_after_store_other _ true false usize _ _ _ stored

end Compiler.Extraction.RepresentativeArray.Pop
