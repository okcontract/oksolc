/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InsertionSortCapturedResults
import Compiler.ZigAir.MemoryWordCopyProofs
import Compiler.ZigAir.MemoryWordCopyFrame

/-! Source-bound copy/sort control after selection of the destination. Copying
uses the typed specification; sorting calls captured swap AIR. Allocation and
native memcpy correspondence remain separate obligations. -/
namespace Compiler.Extraction.InsertionSort.Copied
open Compiler.Algebraic Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray

def copyTo (source target : View) (state : State) : Except Heap.Fault Unit × State :=
  let (result, after) := WordCopy.copy state source target
  (result.mapError Heap.Fault.memory, after)

def run (budget : Nat) (state : State) (source target : View) : Except Heap.Fault Unit × State :=
  copySortUsing (copyTo source target) (fun middle => Captured.run budget middle target) state

theorem run_after_copy (budget : Nat) (state middle : State) (source target : View)
    (copied : WordCopy.copy state source target = (.ok (), middle)) :
    run budget state source target = Captured.run budget middle target := by
  simp only [run, copySortUsing, copyTo, copied, Except.mapError]

/-- The selected destination starts unconstrained. Copy establishes the captured
sort's initialized-view premise; every admitted input has a finite uniform call
budget. Success sorts, exhaustion retains a permutation, and both retain the
source and frame. No allocation success or adequate-budget premise is assumed. -/
theorem run_refines (state : State) (source target : View) (items : List NodeId)
    (initial : state.valid = true) (cap : Writable state target) (represented : Represents state source items)
    (length : source.length = target.length) (separate : WordCopy.disjoint source target = true) :
    ∃ result after values, Captured.Settles (fun budget => run budget state source target) (result, after) ∧
      Heap.Related target after values ∧ values.Perm items ∧ Represents after source items ∧ HeapFrame target state after ∧
      ((result = .ok () ∧ values = sortIds items) ∨ result = .error (.memory .outOfMemory)) := by
  obtain ⟨middle, copied, valid, writable, preserved, initialized, copyFrame⟩ :=
    WordCopy.copy_refines state source target items initial cap represented length separate
  obtain ⟨result, after, values, ⟨budget, settled⟩, related, permutation, frame, effect⟩ :=
    Captured.run_refines target middle items ⟨valid, writable, initialized⟩
  refine ⟨result, after, values, ⟨budget, ?_⟩, related, permutation,
    WordCopy.source_frame middle after source target items preserved separate frame, copyFrame.heapFrame.trans frame, effect⟩
  intro fuel enough
  change run fuel state source target = _
  rw [run_after_copy fuel state middle source target copied]
  exact settled fuel enough

/-- Every observed budget is classified. An incomplete byte swap deliberately
carries no permutation or frame claim; its exact partial state is returned. -/
theorem run_result (budget : Nat) (state after : State) (source target : View) (items : List NodeId)
    (result : Except Heap.Fault Unit) (initial : state.valid = true) (cap : Writable state target)
    (represented : Represents state source items) (length : source.length = target.length)
    (separate : WordCopy.disjoint source target = true) (done : run budget state source target = (result, after)) :
    result = .error .incomplete ∨ ∃ values,
      Heap.Related target after values ∧ values.Perm items ∧ Represents after source items ∧ HeapFrame target state after ∧
      ((result = .ok () ∧ values = sortIds items) ∨ result = .error (.memory .outOfMemory)) := by
  obtain ⟨middle, copied, valid, writable, preserved, initialized, copyFrame⟩ :=
    WordCopy.copy_refines state source target items initial cap represented length separate
  rw [run_after_copy budget state middle source target copied] at done
  rcases Captured.run_result budget target middle after items result ⟨valid, writable, initialized⟩ done with
    incomplete | ⟨values, related, permutation, frame, effect⟩
  · exact Or.inl incomplete
  · exact Or.inr ⟨values, related, permutation, WordCopy.source_frame middle after source target items preserved separate frame,
      copyFrame.heapFrame.trans frame, effect⟩

end Compiler.Extraction.InsertionSort.Copied
