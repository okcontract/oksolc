/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeFirstRegistry

namespace Compiler.Extraction.RepresentativeArray.Append.Registered
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

abbrev Fault := Backing.Registry.Fault

/-- A refinement-side ownership check, not a native compiler branch. Exact
old rows and their native correspondence remain initial invariant obligations.
An absent entry is admitted only for the first, freshly allocated backing. -/
def admit (allocator lifetime : Nat) (cells : List Storage.Cell) (before : Session σ) :
    Except Compiler.Extraction.Memory.Fault Unit :=
  match before.heap lifetime with
  | some ⟨owner, .representatives _⟩ =>
    if owner = allocator then .ok () else .error .wrongAllocator
  | some _ => .error .wrongType
  | none =>
    if cells.isEmpty && lifetime == before.memory.nextId then .ok () else .error .unallocated

/-- Register only a completed native append, using its reached slice identity.
Rejection retains every native write and allocator effect. This function does
not prove the caller's old vector or invent pointee residency from a descriptor.
The supplied registry retains growth's reached allocations and deaths; its
legacy default is the unchanged pre-append registry. -/
def finish (allocator owner : Nat) (cells : List Storage.Cell) (cell : Storage.Cell)
    (before reached : Session σ) (registry : Compiler.Extraction.Memory.Heap := before.heap) : Except Fault Bool × Session σ :=
  match readItems reached.memory (Owner.headerAddress ⟨owner, 0⟩) with
  | .error reason => (.error (.memory reason), reached)
  | .ok (.slice type data length) =>
    if type = itemsType ∧ data.offset = 0 ∧ length = cells.length + 1 then
      match admit allocator data.allocation cells {before with heap := registry} with
      | .error reason => (.error (.registry reason), reached)
      | .ok () => (.ok true, { reached with heap := (Compiler.Extraction.Memory.write registry data.allocation
          (some ⟨allocator, .representatives (cells ++ [cell])⟩)) })
    else (.error (.memory .malformed), reached)
  | .ok _ => (.error (.memory .malformed), reached)

/-- Execute the existing native append with reached insertion locals. The
registry is a ghost refinement of that same execution. Native OOM, memory
rejection and registration rejection remain separate outcomes. -/
def run (runtimeSafety : Bool) (allocate : Backing.Registry.Allocate σ) (allocator owner : Nat)
    (cells : List Storage.Cell) (cell : Storage.Cell) (before : Session σ) : Except Fault Bool × Session σ :=
  let ((result, memory), effects) := Execution.ownerRun runtimeSafety before.memory ⟨owner, 0⟩
    ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩ cell.arguments.length (Storage.idFor cells).toNat
    cell.sequence.toNat (allocate allocator) before.effects
  let reached : Session σ := { before with memory, effects }
  match result with
  | .error reason => (.error (.memory reason), reached)
  | .ok none => (.ok false, reached)
  | .ok (some ()) => finish allocator owner cells cell before reached

theorem finish_reached (allocator owner : Nat) (cells : List Storage.Cell) (cell : Storage.Cell)
    (before reached : Session σ) (registry : Compiler.Extraction.Memory.Heap := before.heap) :
    (finish allocator owner cells cell before reached registry).2.memory = reached.memory ∧
    (finish allocator owner cells cell before reached registry).2.effects = reached.effects := by
  unfold finish
  split
  · exact ⟨rfl, rfl⟩
  · split
    · split <;> exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- Every outcome retains the exact reached native state, including a length
or descriptor store made before rejection. Registry admission cannot rewind it. -/
theorem reached (runtimeSafety : Bool) (allocate : Backing.Registry.Allocate σ) (allocator owner : Nat)
    (cells : List Storage.Cell) (cell : Storage.Cell) (before : Session σ) :
    let native := Execution.ownerRun runtimeSafety before.memory ⟨owner, 0⟩ ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩
      cell.arguments.length (Storage.idFor cells).toNat cell.sequence.toNat (allocate allocator) before.effects
    (run runtimeSafety allocate allocator owner cells cell before).2.memory = native.1.2 ∧
    (run runtimeSafety allocate allocator owner cells cell before).2.effects = native.2 := by
  dsimp only
  unfold run
  generalize Execution.ownerRun runtimeSafety before.memory ⟨owner, 0⟩ ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩
    cell.arguments.length (Storage.idFor cells).toNat cell.sequence.toNat (allocate allocator) before.effects = outcome
  obtain ⟨⟨result, native⟩, effects⟩ := outcome
  cases result with
  | error reason => exact ⟨rfl, rfl⟩
  | ok value => cases value with
    | none => exact ⟨rfl, rfl⟩
    | some returned => cases returned; exact finish_reached allocator owner cells cell before _

theorem admit_vector (allocator lifetime : Nat) (cells : List Storage.Cell) (before : Session σ)
    (registered : Compiler.Extraction.Memory.Vector allocator before.heap lifetime cells) :
    admit allocator lifetime cells before = .ok () := by
  unfold Compiler.Extraction.Memory.Vector at registered
  simp only [admit, registered, ↓reduceIte]

theorem admit_first (allocator : Nat) (before : Session σ) (valid : Valid before) :
    admit allocator before.memory.nextId [] before = .ok () := by
  simp only [admit, valid.injected.fresh valid.memory, List.isEmpty_nil, beq_self_eq_true, Bool.and_self, ↓reduceIte]

/-- A registered append theorem supplies this executor's successful result.
Its final header and registry write must come from that very native execution;
the bridge neither assumes final Good nor changes a native result. -/
theorem completed (runtimeSafety : Bool) (allocate : Backing.Registry.Allocate σ) (allocator owner lifetime capacity : Nat)
    (cells : List Storage.Cell) (cell : Storage.Cell) (before after : Session σ)
    (executed : Execution.ownerRun runtimeSafety before.memory ⟨owner, 0⟩ ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩
      cell.arguments.length (Storage.idFor cells).toNat cell.sequence.toNat (allocate allocator) before.effects =
        ((.ok (some ()), after.memory), after.effects))
    (heap : after.heap = Compiler.Extraction.Memory.write before.heap lifetime (some ⟨allocator, .representatives (cells ++ [cell])⟩))
    (header : readHeader after.memory (Owner.headerAddress ⟨owner, 0⟩) =
      .ok (.slice itemsType ⟨lifetime, 0⟩ (cells.length + 1), .scalar (.int false 64 capacity)))
    (admitted : admit allocator lifetime cells before = .ok ()) :
    run runtimeSafety allocate allocator owner cells cell before = (.ok true, after) := by
  have items := readHeader_items _ _ _ _ header
  simp only [run, executed, finish, items, and_self, ↓reduceIte, admitted]
  cases after
  simp only [← heap]

theorem rejected (runtimeSafety : Bool) (allocate : Backing.Registry.Allocate σ) (allocator owner : Nat)
    (cells : List Storage.Cell) (cell : Storage.Cell) (before : Session σ) (memory : State) (effects : σ)
    (reason : Compiler.ZigAir.Memory.Fault)
    (executed : Execution.ownerRun runtimeSafety before.memory ⟨owner, 0⟩ ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩
      cell.arguments.length (Storage.idFor cells).toNat cell.sequence.toNat (allocate allocator) before.effects =
        ((.error reason, memory), effects)) :
    run runtimeSafety allocate allocator owner cells cell before = (.error (.memory reason), {before with memory, effects}) := by
  simp only [run, executed]

theorem oom (runtimeSafety : Bool) (allocate : Backing.Registry.Allocate σ) (allocator owner : Nat)
    (cells : List Storage.Cell) (cell : Storage.Cell) (before : Session σ) (memory : State) (effects : σ)
    (executed : Execution.ownerRun runtimeSafety before.memory ⟨owner, 0⟩ ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩
      cell.arguments.length (Storage.idFor cells).toNat cell.sequence.toNat (allocate allocator) before.effects =
        ((.ok none, memory), effects)) :
    run runtimeSafety allocate allocator owner cells cell before = (.ok false, {before with memory, effects}) := by
  simp only [run, executed]

end Compiler.Extraction.RepresentativeArray.Append.Registered
