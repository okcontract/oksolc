/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeGrowthCoverage
import Compiler.Extraction.RepresentativeRegisteredGrowthAppend
import Compiler.Extraction.RepresentativeGrowingAppend

namespace Compiler.Extraction.RepresentativeArray.Append
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

/-- Ordinary append completion retains the selected capacity outcome. A later
descriptor rejection cannot turn an accepted allocation into ordinary OOM. -/
theorem Execution.capacity_completed (reject : Compiler.ZigAir.Memory.Fault → ε)
    (ensure : State → Address → Nat → σ → (Except ε (Option Unit) × State) × σ)
    (state : State) (header itemAddress argumentsAddress : Address)
    (length argumentsLength : Nat) (id sequence : Int) (effects : σ) (selected : Option Unit)
    (loaded : readField state header lengthOffset = .ok (.scalar (.int false 64 length)))
    (width : nextLength length < addressLimit)
    (completed : (Execution.runWithCapacity reject ensure state header itemAddress argumentsAddress argumentsLength
      id sequence effects).1.1 = .ok selected) :
    (ensure state header (nextLength length) effects).1.1 = .ok selected := by
  simp only [Execution.runWithCapacity, loaded, Int.toNat_natCast, if_neg (Nat.not_le.mpr width)] at completed
  cases called : ensure state header (nextLength length) effects with
  | mk native reached =>
    obtain ⟨result, memory⟩ := native
    rw [called] at completed
    dsimp only at completed
    cases result with
    | error fault => cases completed
    | ok value =>
      cases value with
      | none => exact completed
      | some value =>
        cases value
        dsimp only at completed
        split at completed
        · cases completed
        · exact completed

/-- The registry's successful finish always represents an accepted append.
It never maps failed field reads or ownership checks to allocation refusal. -/
theorem Registered.finish_accepted (allocator owner : Nat) (cells : List Storage.Cell) (cell : Storage.Cell)
    (before reached : Session σ) (registry : Compiler.Extraction.Memory.Heap) (accepted : Bool)
    (completed : (Registered.finish allocator owner cells cell before reached registry).1 = .ok accepted) :
    accepted = true := by
  unfold Registered.finish at completed
  repeat first
    | dsimp only at completed
    | exact (Except.ok.inj completed).symm
    | contradiction
    | split at completed

/-- The first/spare registry adapter retains the native append decision. -/
theorem Registered.ordinary_native (runtimeSafety : Bool) (allocate : Backing.Registry.Allocate σ)
    (allocator owner : Nat) (cells : List Storage.Cell) (cell : Storage.Cell) (before : Session σ)
    (accepted : Bool) (completed : (Registered.run runtimeSafety allocate allocator owner cells cell before).1 = .ok accepted) :
    (Execution.ownerRun runtimeSafety before.memory ⟨owner, 0⟩ ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩
      cell.arguments.length (Storage.idFor cells).toNat cell.sequence.toNat (allocate allocator) before.effects).1.1 =
        .ok (if accepted then some () else none) := by
  cases native : Execution.ownerRun runtimeSafety before.memory ⟨owner, 0⟩ ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩
      cell.arguments.length (Storage.idFor cells).toNat cell.sequence.toNat (allocate allocator) before.effects with
  | mk result effects =>
    obtain ⟨result, memory⟩ := result
    simp only [Registered.run, native] at completed
    cases result with
    | error fault => cases completed
    | ok value =>
      cases value with
      | none =>
        have same := (Except.ok.inj completed).symm
        simp only [same, Bool.false_eq_true, ↓reduceIte]
      | some value =>
        cases value
        have same := Registered.finish_accepted allocator owner cells cell before _ before.heap accepted completed
        simp only [same, ↓reduceIte]

/-- The captured-growth adapter uses the same decision and finish rule. -/
theorem Registered.ordinary_native_growth (calls : Growth.Registered.Callbacks σ) (runtimeSafety : Bool)
    (allocate : Backing.Registry.Allocate σ) (allocator owner : Nat) (cells : List Storage.Cell)
    (cell : Storage.Cell) (before : Session σ) (accepted : Bool)
    (completed : (Registered.runWithGrowth calls runtimeSafety allocate allocator owner cells cell before).1 = .ok accepted) :
    (Execution.ownerWithCapacity (fun fault => (.memory fault : Registered.Fault))
      (Registered.growingCapacity calls allocate allocator) runtimeSafety before.memory ⟨owner, 0⟩
      ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩ cell.arguments.length
      (Storage.idFor cells).toNat cell.sequence.toNat (before.heap, before.effects)).1.1 =
        .ok (if accepted then some () else none) := by
  cases native : Execution.ownerWithCapacity (fun fault => (.memory fault : Registered.Fault))
      (Registered.growingCapacity calls allocate allocator) runtimeSafety before.memory ⟨owner, 0⟩
      ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩ cell.arguments.length
      (Storage.idFor cells).toNat cell.sequence.toNat (before.heap, before.effects) with
  | mk result context =>
    obtain ⟨result, memory⟩ := result
    obtain ⟨heap, effects⟩ := context
    simp only [Registered.runWithGrowth, native] at completed
    cases result with
    | error fault => cases completed
    | ok value =>
      cases value with
      | none =>
        have same := (Except.ok.inj completed).symm
        simp only [same, Bool.false_eq_true, ↓reduceIte]
      | some value =>
        cases value
        have same := Registered.finish_accepted allocator owner cells cell before _ heap accepted completed
        simp only [same, ↓reduceIte]

end Compiler.Extraction.RepresentativeArray.Append

namespace Compiler.Extraction.RepresentativeArray
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

/-- The insertion count bound keeps the source-selected growth request below
usize byte overflow. This excludes synthetic overflow OOM from this branch. -/
theorem Capacity.grow_count_bytes (length : Nat) (room : length < 2 ^ 32 - 1) :
    Capacity.grow (Append.nextLength length) * 32 < addressLimit := by
  have bound : Capacity.grow (Append.nextLength length) ≤
      Append.nextLength length + (Append.nextLength length / 2 + 4) := by
    unfold Capacity.grow
    rw [Capacity.initial_capacity_checked]
    exact Nat.min_le_right _ _
  have count : length < 4294967295 := room
  dsimp only [Append.nextLength] at bound
  change Capacity.grow (length + 1) * 32 < 18446744073709551616
  omega

/-- Resolve the real owner's header and follow the shared append control to
the actual capacity call. Both adapters retain the same ordinary decision. -/
theorem Append.Registered.capacity_completed (growth : Option (Growth.Registered.Callbacks σ))
    (safety : Bool) (allocate : Backing.Registry.Allocate σ) (allocator owner : Nat)
    (cells : List Storage.Cell) (cell : Storage.Cell) (before : Session σ) (ownerCell : Allocation)
    (valid : before.memory.valid = true) (found : before.memory.heap.lookup owner = some ownerCell)
    (typed : ownerCell.type = Owner.viewType safety)
    (loaded : readField before.memory (Owner.headerAddress ⟨owner, 0⟩) lengthOffset =
      .ok (.scalar (.int false 64 cells.length)))
    (width : Append.nextLength cells.length < addressLimit) (accepted : Bool)
    (completed : (match growth with
      | none => Append.Registered.run safety allocate allocator owner cells cell before
      | some calls => Append.Registered.runWithGrowth calls safety allocate allocator owner cells cell before).1 = .ok accepted) :
    match growth with
    | none => (Capacity.ensure before.memory (Owner.headerAddress ⟨owner, 0⟩) (Append.nextLength cells.length)
        (allocate allocator) before.effects).1.1 = .ok (if accepted then some () else none)
    | some calls => (Capacity.Registered.ensure calls allocate allocator (Owner.headerAddress ⟨owner, 0⟩)
        (Append.nextLength cells.length) before).1 = .ok (if accepted then some () else none) := by
  have selected := Owner.root_header_pointer safety before.memory owner ownerCell true valid found typed
  cases growth with
  | none =>
    dsimp only
    have native := Append.Registered.ordinary_native safety allocate allocator owner cells cell before accepted completed
    apply Append.Execution.capacity_completed (fun fault => fault)
      (fun state header minimum effects => Capacity.ensure state header minimum (allocate allocator) effects)
      before.memory (Owner.headerAddress ⟨owner, 0⟩) ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩
      cells.length cell.arguments.length (Storage.idFor cells).toNat cell.sequence.toNat before.effects
      (if accepted then some () else none) loaded width
    simpa only [Append.Execution.ownerRun, Append.Execution.ownerWithCapacity, selected] using native
  | some calls =>
    dsimp only
    have native := Append.Registered.ordinary_native_growth calls safety allocate allocator owner cells cell before accepted completed
    have ensured := Append.Execution.capacity_completed (fun fault => (.memory fault : Append.Registered.Fault))
      (Append.Registered.growingCapacity calls allocate allocator) before.memory (Owner.headerAddress ⟨owner, 0⟩)
      ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩ cells.length cell.arguments.length
      (Storage.idFor cells).toNat cell.sequence.toNat (before.heap, before.effects)
      (if accepted then some () else none) loaded width
      (by simpa only [Append.Execution.ownerWithCapacity, selected] using native)
    cases called : Capacity.Registered.ensure calls allocate allocator (Owner.headerAddress ⟨owner, 0⟩)
        (Append.nextLength cells.length) before with
    | mk result reached =>
      simp only [Append.Registered.growingCapacity, called] at ensured
      cases result with
      | error fault => cases ensured
      | ok result => exact congrArg Except.ok (Except.ok.inj ensured)

/-- The actual capacity choice and raw allocator response, before descriptor
assignment or publication. Spare capacity performs no backing allocation;
growth records the checked lock and the admitted remap identity. -/
def Append.Registered.BackingObservation (growth : Option (Growth.Registered.Callbacks σ))
    (allocate : Backing.Registry.Allocate σ) (allocator owner length capacity : Nat)
    (before : Session σ) (accepted : Bool) : Prop :=
  (length < capacity ∧ accepted = true) ∨
  (Owner.NativeLock.checkHeader before.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok () ∧
    ((capacity = 0 ∧ Backing.AllocationObservation (allocate allocator) 5 before.memory before.effects accepted) ∨
      (capacity ≠ 0 ∧ capacity < Append.nextLength length ∧
        ∃ (context returnAddress : Nat) (release : Backing.Release.External σ), growth = some ⟨.noRemap context returnAddress, release⟩ ∧
          Backing.AllocationObservation (allocate allocator) (Capacity.grow (Append.nextLength length))
            before.memory before.effects accepted)))

/-- Ordinary native append derives its backing observation from the loaded
owner and live storage. Neither allocator success nor a post-state frame is
assumed; unsupported remap and malformed memory remain nonordinary. -/
theorem Append.Registered.backing_observation (growth : Option (Growth.Registered.Callbacks σ))
    (safety : Bool) (allocate : Backing.Registry.Allocate σ) (allocator owner : Nat)
    (cells : List Storage.Cell) (cell : Storage.Cell) (before : Session σ) (ownerCell : Allocation)
    (data : Address) (capacity : Nat) (valid : Valid before)
    (found : before.memory.heap.lookup owner = some ownerCell) (typed : ownerCell.type = Owner.viewType safety)
    (loaded : readHeader before.memory (Owner.headerAddress ⟨owner, 0⟩) =
      .ok (.slice itemsType data cells.length, .scalar (.int false 64 capacity)))
    (bounded : cells.length ≤ capacity)
    (storage : capacity ≠ 0 → Backing.Release.Owned allocator data capacity before)
    (room : cells.length < 2 ^ 32 - 1) (accepted : Bool)
    (completed : (match growth with
      | none => Append.Registered.run safety allocate allocator owner cells cell before
      | some calls => Append.Registered.runWithGrowth calls safety allocate allocator owner cells cell before).1 = .ok accepted) :
    Append.Registered.BackingObservation growth allocate allocator owner cells.length capacity before accepted := by
  have items := readHeader_items _ _ _ _ loaded
  have count := readHeader_capacity _ _ _ _ loaded
  have length := Append.Execution.owner_length_from_items safety before.memory owner ownerCell data cells.length
    valid.memory found typed items
  have width : Append.nextLength cells.length < addressLimit := by
    have bound : cells.length < 4294967295 := room
    change cells.length + 1 < 18446744073709551616
    omega
  have ensured := Append.Registered.capacity_completed growth safety allocate allocator owner cells cell before ownerCell
    valid.memory found typed length width accepted completed
  by_cases spare : cells.length < capacity
  · left
    refine ⟨spare, ?_⟩
    have enough : Append.nextLength cells.length ≤ capacity := by unfold Append.nextLength; omega
    cases growth with
    | none =>
      dsimp only at ensured
      rw [Capacity.ensure_unchanged before.memory (Owner.headerAddress ⟨owner, 0⟩) capacity
        (Append.nextLength cells.length) (allocate allocator) before.effects width count enough] at ensured
      cases accepted with
      | false => cases ensured
      | true => rfl
    | some calls =>
      dsimp only at ensured
      rw [Capacity.Registered.unchanged calls allocate allocator capacity (Append.nextLength cells.length)
        (Owner.headerAddress ⟨owner, 0⟩) before width count enough] at ensured
      cases accepted with
      | false => cases ensured
      | true => rfl
  · right
    have short : capacity < Append.nextLength cells.length := by unfold Append.nextLength; omega
    have pointer := readItemsData_from_loaded safety before.memory owner ownerCell data cells.length
      valid.memory found typed items
    have size := Capacity.grow_count_bytes cells.length room
    have positive := Capacity.grow_positive (Append.nextLength cells.length) width (by unfold Append.nextLength; omega)
    have wider : capacity < Capacity.grow (Append.nextLength cells.length) :=
      Nat.lt_of_lt_of_le short (Capacity.grow_sufficient _ width)
    have decision : (if accepted then some () else none).isSome = accepted := by cases accepted <;> rfl
    by_cases empty : capacity = 0
    · have zero : cells.length = 0 := by omega
      have saved := allocatedSlice_empty before.memory (Owner.headerAddress ⟨owner, 0⟩) data pointer (by simpa only [empty] using count)
      have target : Capacity.grow (Append.nextLength cells.length) = 5 := by
        rw [zero]; exact Capacity.first_capacity_checked
      have observed : Owner.NativeLock.checkHeader before.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok () ∧
          Backing.AllocationObservation (allocate allocator) (Capacity.grow (Append.nextLength cells.length))
            before.memory before.effects accepted := by
        cases growth with
        | none =>
          dsimp only at ensured
          rw [Capacity.ensure_growing before.memory (Owner.headerAddress ⟨owner, 0⟩) capacity
            (Append.nextLength cells.length) (allocate allocator) before.effects width count short] at ensured
          simpa only [decision] using Growth.first_observation before.memory (Owner.headerAddress ⟨owner, 0⟩)
            data _ (allocate allocator) before.effects _ positive size (by simpa only [empty] using count) saved ensured
        | some calls =>
          dsimp only at ensured
          rw [Capacity.Registered.growing calls allocate allocator capacity (Append.nextLength cells.length)
            (Owner.headerAddress ⟨owner, 0⟩) before width count short] at ensured
          simpa only [decision] using Growth.Registered.first_observation calls.remap allocate calls.release allocator
            (Owner.headerAddress ⟨owner, 0⟩) data _ before _ positive size (by simpa only [empty] using count) saved ensured
      exact ⟨observed.1, Or.inl ⟨empty, by simpa only [target] using observed.2⟩⟩
    · have owned := storage empty
      have root : data = ⟨data.allocation, 0⟩ := by
        have offset := owned.1
        cases data
        simp_all only
      obtain ⟨_, _, backing, backingFound, backingType, _, _⟩ := owned
      have saved := allocatedSlice_nonempty before.memory (Owner.headerAddress ⟨owner, 0⟩)
        data.allocation capacity backing valid.memory backingFound backingType empty (root ▸ pointer) count
      rw [← root] at saved
      cases growth with
      | none =>
        dsimp only at ensured
        rw [Capacity.ensure_growing before.memory (Owner.headerAddress ⟨owner, 0⟩) capacity
          (Append.nextLength cells.length) (allocate allocator) before.effects width count short] at ensured
        have unlocked := Growth.ordinary_unlocked before.memory (Owner.headerAddress ⟨owner, 0⟩) _
          (allocate allocator) before.effects _ ensured
        have prepared := Growth.prepare_growing before.memory (Owner.headerAddress ⟨owner, 0⟩) data capacity
          _ capacity (Capacity.grow_bounded _) wider count saved unlocked
        simp only [Growth.run, prepared, if_neg empty, reduceCtorEq] at ensured
      | some calls =>
        dsimp only at ensured
        rw [Capacity.Registered.growing calls allocate allocator capacity (Append.nextLength cells.length)
          (Owner.headerAddress ⟨owner, 0⟩) before width count short] at ensured
        obtain ⟨unlocked, context, returnAddress, remap, observed⟩ := Growth.Registered.growing_observation calls.remap
          allocate calls.release allocator (Owner.headerAddress ⟨owner, 0⟩) data capacity _ before _ valid
          (storage empty) empty wider size count saved ensured
        refine ⟨unlocked, Or.inr ⟨empty, short, context, returnAddress, calls.release, ?_, ?_⟩⟩
        · cases calls; cases remap; rfl
        · simpa only [decision] using observed

end Compiler.Extraction.RepresentativeArray
