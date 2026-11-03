/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionCount
import Compiler.Extraction.InternerInsertionCaller

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Return the actual native execution's result and reached projection through
the existing caller interface. Count rejection precedes execution; native
semantic faults retain their reached memory and are not ordinary OOM. The raw
count/native reasons remain in checkedExecution. This adapter supplies no
universal graph, ownership or word-preservation premise. -/
def body (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (deterministic : Bool) (cells : List Storage.Cell) (before : World (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ) := none) : Except OwnedCall.Fault NodeId × World (Publication.Effects σ) :=
  match checkedExecution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized deterministic cells before growth with
  | .error _ => (.error (.language .safetyFault), before)
  | .ok ((result, owner), after) =>
    let value := (key.eval meaning before.graph.read).getD 0
    let reached := Insertion.projected cells before key (cell input key normalized value owner after) owner after
    let outcome := match result with
      | .error _ => .error (.language .safetyFault)
      | .ok outcome => (Interner.insertionOutcome cells outcome).mapError OwnedCall.Fault.language
    (outcome, reached)

/-- Select the rows from the reached graph, with explicit rejection when no
representative observation is available. Native field and ownership contracts
are still established by the calling proof, not by this wrapper. -/
def insert (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice) (deterministic : Bool)
    (growth : Option (Growth.Registered.Callbacks σ) := none) : GraphAction (Publication.Effects σ) NodeId := fun before =>
  match before.graph.representatives with
  | none => (.error (.language .safetyFault), before)
  | some cells => body ops allocate runtimeSafety allocator container source itemSource meaning input key normalized deterministic cells before growth

theorem body_rejected (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (deterministic : Bool) (cells : List Storage.Cell) (before : World (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (fault : CountFault)
    (rejected : checkedCount before.memory.memory container cells = .error fault) :
    body ops allocate runtimeSafety allocator container source itemSource meaning input key normalized deterministic cells before growth =
      (.error (.language .safetyFault), before) := by
  simp only [body, checkedExecution_rejected ops allocate runtimeSafety allocator container source itemSource meaning input key normalized
    deterministic cells before growth fault rejected]

/-- A semantic fault after insertion has begun retains the reached projection
and native memory. Its exact raw reason remains in the execution observation;
the existing caller interface classifies it as nonordinary. -/
theorem body_native_fault (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (deterministic : Bool) (cells : List Storage.Cell) (before : World (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (fault : Fault) (owner : Storage.State) (after : Frame σ)
    (failed : checkedExecution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized deterministic cells before growth =
      .ok ((.error fault, owner), after)) :
    body ops allocate runtimeSafety allocator container source itemSource meaning input key normalized deterministic cells before growth =
      (.error (.language .safetyFault), Insertion.projected cells before key
        (cell input key normalized ((key.eval meaning before.graph.read).getD 0) owner after) owner after) := by
  simp only [body, failed]

theorem insert_unrepresented (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice) (deterministic : Bool)
    (growth : Option (Growth.Registered.Callbacks σ)) (before : World (Publication.Effects σ))
    (missing : before.graph.representatives = none) :
    insert ops allocate runtimeSafety allocator container source itemSource meaning input key normalized deterministic growth before =
      (.error (.language .safetyFault), before) := by simp only [insert, missing]

/-- If the source neither appends nor publishes, its existing graph projection
retains every graph field, including the allocation-outcome cursor. The caller
supplies the initial row/read correspondence, never the final graph equality. -/
theorem projected_unchanged (cells : List Storage.Cell) (before : World (Publication.Effects σ)) (key : Key)
    (candidate : Storage.Cell) (owner : Storage.State) (after : Frame σ)
    (rows : before.graph.representatives = some cells) (reads : before.graph.read = Storage.readValue cells)
    (unappended : owner.appended = false) (unpublished : owner.published = false) :
    Insertion.projected cells before key candidate owner after = { before with memory := memory after } := by
  cases before with
  | mk graph session =>
    cases graph with
    | mk read table representatives cursor =>
      simp only at rows reads
      subst read
      subst representatives
      simp only [Insertion.projected, Interner.InsertionExecution.project, Interner.insertedHeap,
        Interner.storageHeap, Storage.nodesAfter, unappended, unpublished, Bool.false_eq_true, ↓reduceIte]

/-- Project an actual checked source outcome before append/publication. The
outcome and reached memory remain those of the execution, for either setting of
determinism. Capacity and preparation failure use the same projection. -/
theorem body_unpublished (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (allocator container : Nat) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (meaning : Meaning) (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (deterministic : Bool) (before : World (Publication.Effects σ)) (rows : List Storage.Cell)
    (growth : Option (Growth.Registered.Callbacks σ))
    (projected : before.graph.representatives = some rows) (reads : before.graph.read = Storage.readValue rows)
    (outcome : Option Storage.Outcome) (closed : Storage.State) (after : Frame σ)
    (unappended : closed.appended = false) (unpublished : closed.published = false)
    (checked : checkedExecution ops allocate safety allocator container source address meaning input key normalized
      deterministic rows before growth = .ok ((.ok outcome, closed), after)) :
    body ops allocate safety allocator container source address meaning input key normalized deterministic rows before growth =
      ((Interner.insertionOutcome rows outcome).mapError OwnedCall.Fault.language, { before with memory := memory after }) := by
  have projection := projected_unchanged rows before key
    (cell input key normalized ((key.eval meaning before.graph.read).getD 0) closed after)
    closed after projected reads unappended unpublished
  simp only [body, checked, projection]

theorem insert_unpublished (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (allocator container : Nat) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (meaning : Meaning) (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (deterministic : Bool) (before : World (Publication.Effects σ)) (rows : List Storage.Cell)
    (growth : Option (Growth.Registered.Callbacks σ)) (backing : Compiler.ZigAir.Memory.Address)
    (header : readItems before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType backing rows.length))
    (projected : before.graph.representatives = some rows) (reads : before.graph.read = Storage.readValue rows)
    (outcome : Option Storage.Outcome) (closed : Storage.State) (after : Frame σ)
    (unappended : closed.appended = false) (unpublished : closed.published = false)
    (ran : execution ops allocate safety allocator container source address meaning input key normalized deterministic rows before growth =
      ((.ok outcome, closed), after)) :
    insert ops allocate safety allocator container source address meaning input key normalized deterministic growth before =
      ((Interner.insertionOutcome rows outcome).mapError OwnedCall.Fault.language, { before with memory := memory after }) := by
  have checked := checkedExecution_read ops allocate safety allocator container source address meaning input key normalized
    deterministic rows before growth backing header
  rw [ran] at checked
  simpa only [insert, projected] using body_unpublished ops allocate safety allocator container source address meaning input key normalized
    deterministic before rows growth projected reads outcome closed after unappended unpublished checked

/-- The actual unpublished source projection restores rows and table without
assuming that the incoming logical read function already agrees with the rows.
Native frames do not need that separate semantic correspondence premise. -/
theorem insert_unpublished_projected (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (allocator container : Nat) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (meaning : Meaning) (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (deterministic : Bool) (before : World (Publication.Effects σ)) (rows : List Storage.Cell)
    (growth : Option (Growth.Registered.Callbacks σ)) (backing : Compiler.ZigAir.Memory.Address)
    (header : readItems before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType backing rows.length))
    (projected : before.graph.representatives = some rows)
    (outcome : Option Storage.Outcome) (closed : Storage.State) (after : Frame σ)
    (unappended : closed.appended = false) (unpublished : closed.published = false)
    (ran : execution ops allocate safety allocator container source address meaning input key normalized deterministic rows before growth =
      ((.ok outcome, closed), after)) :
    insert ops allocate safety allocator container source address meaning input key normalized deterministic growth before =
      ((Interner.insertionOutcome rows outcome).mapError OwnedCall.Fault.language,
        { before with graph := { before.graph with read := Storage.readValue rows }, memory := memory after }) := by
  have checked := checkedExecution_read ops allocate safety allocator container source address meaning input key normalized
    deterministic rows before growth backing header
  rw [ran] at checked
  simp only [insert, projected, body, checked, Insertion.projected, Interner.InsertionExecution.project,
    Interner.insertedHeap, Interner.storageHeap, Storage.nodesAfter, unappended, unpublished, Bool.false_eq_true, ↓reduceIte]

/-- An actual allocation failure whose cleanup clears append/publication passes
through the native count check and retains the reached graph. Cleanup prefixes can differ;
only their derived append/publication flags enter this common projection. -/
theorem insert_allocation_failure (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (allocator container : Nat) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (meaning : Meaning) (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (before : World (Publication.Effects σ)) (rows : List Storage.Cell)
    (growth : Option (Growth.Registered.Callbacks σ)) (backing : Compiler.ZigAir.Memory.Address)
    (header : readItems before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType backing rows.length))
    (projected : before.graph.representatives = some rows) (reads : before.graph.read = Storage.readValue rows)
    (closed : Storage.State) (after : Frame σ) (unappended : closed.appended = false) (unpublished : closed.published = false)
    (ran : execution ops allocate safety allocator container source address meaning input key normalized true rows before growth =
      ((.ok (some .allocationFailure), closed), after)) :
    insert ops allocate safety allocator container source address meaning input key normalized true growth before =
      (.error (.language .outOfMemory), { before with memory := memory after }) := by
  simpa only [Interner.insertionOutcome, Except.mapError] using insert_unpublished ops allocate safety allocator container source address
    meaning input key normalized true before rows growth backing header projected reads (some .allocationFailure) closed after
    unappended unpublished ran

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
