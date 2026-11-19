/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionPreparedRollback

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Native append changes shared storage, retaining the local descriptors used
by the existing logical graph projection on every reached outcome. -/
theorem append_cell (runtimeSafety : Bool) (allocate : Backing.Registry.Allocate σ) (allocator container : Nat)
    (cells : List Storage.Cell) (input : AssemblyClone.NativeFields.ItemValue) (key : Key)
    (normalized : ArgumentSlice) (value : Word) (owner projectedOwner : Storage.State) (before : Frame σ)
    (growth : Option (Growth.Registered.Callbacks σ)) :
    cell input key normalized value projectedOwner (append runtimeSafety allocate allocator container cells input key normalized value owner before growth).2 =
      cell input key normalized value projectedOwner before := by
  unfold append
  split
  · rfl
  · cases growth with
    | none =>
      generalize Append.Registered.run runtimeSafety (allocation allocate) allocator container cells
        (cell input key normalized value owner before) (memory before) = result
      obtain ⟨_, reached⟩ := result
      rfl
    | some calls =>
      generalize Append.Registered.runWithGrowth (growthCallbacks calls) runtimeSafety (allocation allocate) allocator container cells
        (cell input key normalized value owner before) (memory before) = result
      obtain ⟨_, reached⟩ := result
      rfl

/-- Publication's success, OOM and semantic rejection all retain insertion
locals. Only the reached shared memory changes. -/
theorem publication_cell (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (cells : List Storage.Cell) (value : Word) (graph : Storage.State → Frame σ → Interner.Heap)
    (growth : Option (Growth.Registered.Callbacks σ)) (owner projectedOwner : Storage.State) (before : Frame σ) :
    cell input key normalized value projectedOwner
      ((callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph growth).attempt .publish owner before).2 =
      cell input key normalized value projectedOwner before := by
  simp only [callbacks, Insertion.callbacks]
  generalize Publication.publish ops.probe ops.arguments allocator source key normalized (BitVec.ofNat 32 cells.length)
    ⟨graph owner before, memory before⟩ = result
  obtain ⟨result, reached⟩ := result
  cases result with
  | ok value => rfl
  | error fault => cases fault with
    | language error => cases error <;> rfl
    | memory failure => rfl
    | missingHandle => rfl
    | outsideOwnedContinuation => rfl

/-- The same append and publication calls determine the exact candidate used
in the reached graph, rather than accepting a separately supplied final row. -/
theorem prepared_publication_cell (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container object : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (input copied : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized operands : ArgumentSlice)
    (cells : List Storage.Cell) (value : Word) (graph : Storage.State → Frame σ → Interner.Heap)
    (growth : Option (Growth.Registered.Callbacks σ)) (installed : Session (Publication.Effects σ)) (appended after : Frame σ)
    (appendCall : append runtimeSafety allocate allocator container cells input key normalized value preparationOwnership
      (preparedFrame object copied operands installed) growth = (.ok true, appended))
    (publicationCall : (callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph growth).attempt
      .publish publicationOwnership appended = (.ok true, after)) :
    cell input key normalized value Storage.publishedOwnership after =
      ⟨copied.item, value, object, operands.items, key.sequence, operands.address⟩ := by
  have first := append_cell runtimeSafety allocate allocator container cells input key normalized value preparationOwnership
    Storage.publishedOwnership (preparedFrame object copied operands installed) growth
  have second := publication_cell ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph
    growth publicationOwnership Storage.publishedOwnership appended
  rw [appendCall] at first
  rw [publicationCall] at second
  exact second.trans first

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
