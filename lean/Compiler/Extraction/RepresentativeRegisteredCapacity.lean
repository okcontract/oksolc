/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeArrayCapacity
import Compiler.Extraction.RepresentativeRemapGrowth

namespace Compiler.Extraction.RepresentativeArray
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

/-- Captured remap identity and the existing external free operation. Native
allocator-field/vtable correspondence remains an explicit caller obligation. -/
structure Growth.Registered.Callbacks (σ : Type) where
  remap : Remap.Callback
  release : Backing.Release.External σ

namespace Capacity.Registered

def ensure (calls : Growth.Registered.Callbacks σ) (allocate : Backing.Registry.Allocate σ)
    (allocator : Nat) (header : Address) (minimum : Nat) (before : Session σ) :
    Except Backing.Release.Fault (Option Unit) × Session σ :=
  match Capacity.prepare before.memory header minimum with
  | .error fault => (.error (.memory fault), before)
  | .ok none => (.ok (some ()), before)
  | .ok (some capacity) => Growth.Registered.run calls.remap allocate calls.release allocator header capacity before

theorem unchanged (calls : Growth.Registered.Callbacks σ) (allocate : Backing.Registry.Allocate σ)
    (allocator capacity minimum : Nat) (header : Address) (before : Session σ) (width : minimum < addressLimit)
    (loaded : readField before.memory header capacityOffset = .ok (.scalar (.int false 64 capacity)))
    (enough : minimum ≤ capacity) :
    ensure calls allocate allocator header minimum before = (.ok (some ()), before) := by
  simp only [ensure, Capacity.prepare, if_neg (Nat.not_le.mpr width), loaded, Int.toNat_natCast,
    Append.hasCapacity, decide_eq_true_eq, if_pos enough]

theorem growing (calls : Growth.Registered.Callbacks σ) (allocate : Backing.Registry.Allocate σ)
    (allocator capacity minimum : Nat) (header : Address) (before : Session σ) (width : minimum < addressLimit)
    (loaded : readField before.memory header capacityOffset = .ok (.scalar (.int false 64 capacity)))
    (short : capacity < minimum) :
    ensure calls allocate allocator header minimum before =
      Growth.Registered.run calls.remap allocate calls.release allocator header (Capacity.grow minimum) before := by
  simp only [ensure, Capacity.prepare, if_neg (Nat.not_le.mpr width), loaded, Int.toNat_natCast,
    Append.hasCapacity, decide_eq_true_eq, if_neg (Nat.not_le.mpr short)]

/-- The growth target is source-selected, including saturation. No result,
allocation or live-frame preservation of the capacity call is assumed. -/
theorem parent_borrow (runtimeSafety : Bool) (calls : Growth.Registered.Callbacks σ) (allocate : Backing.Registry.Allocate σ)
    (allocator owner minimum : Nat) (before : Session σ) (ownerCell : Allocation)
    (valid : Valid before) (ownerFound : before.memory.heap.lookup owner = some ownerCell)
    (ownerType : ownerCell.type = Owner.viewType runtimeSafety)
    (parent : WordArray.View) (values : List (BitVec 32)) (extent : Nat) (cell : Allocation)
    (found : before.memory.heap.lookup parent.allocation = some cell) (typed : cell.type = .array extent WordArray.word)
    (represented : WordArray.Represents before.memory parent values) :
    let after := (ensure calls allocate allocator (Owner.headerAddress ⟨owner, 0⟩) minimum before).2
    Valid after ∧ after.memory.heap.lookup parent.allocation = some cell ∧ WordArray.Represents after.memory parent values := by
  have positive : 0 < Capacity.grow minimum := by
    unfold Capacity.grow
    rw [Capacity.initial_capacity_checked]
    have : 0 < addressLimit - 1 := by decide
    omega
  unfold ensure
  cases selected : Capacity.prepare before.memory (Owner.headerAddress ⟨owner, 0⟩) minimum with
  | error reason => exact ⟨valid, found, represented⟩
  | ok target => cases target with
    | none => exact ⟨valid, found, represented⟩
    | some capacity =>
      have same := Capacity.prepare_selected before.memory (Owner.headerAddress ⟨owner, 0⟩) minimum capacity selected
      subst capacity
      exact Growth.Registered.parent_borrow runtimeSafety calls.remap allocate calls.release allocator owner
        (Capacity.grow minimum) before ownerCell valid positive ownerFound ownerType parent values extent cell found typed represented

end Capacity.Registered
end Compiler.Extraction.RepresentativeArray
