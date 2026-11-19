/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeOwnerLayout
import Compiler.Extraction.RepresentativeArray
import Compiler.ZigAir.MemoryRecordWrites

namespace Compiler.Extraction.RepresentativeArray.Owner
open Compiler.ZigAir.Memory

theorem layout_checked (runtimeSafety : Bool) : (allocationType runtimeSafety).layout = some (layout runtimeSafety) := by
  cases runtimeSafety <;> decide
theorem header_layout_checked : RepresentativeArray.allocationType.layout = some representativesLayout := by decide

theorem regions_checked (runtimeSafety : Bool) :
    (regions runtimeSafety).length = 3 ∧ (∀ entry ∈ regions runtimeSafety, 0 < entry.2.bytes ∧
      entry.1 + entry.2.bytes ≤ (layout runtimeSafety).bytes ∧ entry.1 % entry.2.alignment = 0 ∧
      (layout runtimeSafety).alignment % entry.2.alignment = 0) ∧
    (regions runtimeSafety).Pairwise (fun a b => a.1 + a.2.bytes ≤ b.1) := by
  cases runtimeSafety <;> decide

/-- Native field placement retains the enclosing allocation's lifetime. This
address arithmetic supplies no nested typed field or initialized header view. -/
def headerAddress (owner : Address) : Address :=
  ⟨owner.allocation, owner.offset + representativesOffset⟩

theorem header_address_identity (owner : Address) :
    (headerAddress owner).allocation = owner.allocation ∧
      (headerAddress owner).offset = owner.offset + 16 := ⟨rfl, rfl⟩

/-- Checked owner access derives bounds, alignment and the same permission for
its embedded header region. The allocation and initialized cells do not change. -/
theorem header_region_access (runtimeSafety : Bool) (state : State) (owner : Address) (cell : Allocation) (write : Bool)
    (accessed : access state owner (layout runtimeSafety) write = .ok cell) :
    access state (headerAddress owner) representativesLayout write = .ok cell :=
  access_subregion state owner (layout runtimeSafety) representativesLayout representativesOffset write cell accessed
    (by decide) (by cases runtimeSafety <;> decide) (by decide) (by cases runtimeSafety <;> decide)

theorem root_header_region (runtimeSafety : Bool) (state : State) (lifetime : Nat) (cell : Allocation) (write : Bool)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = allocationType runtimeSafety) (permitted : write = true → cell.writable = true) :
    access state (headerAddress ⟨lifetime, 0⟩) representativesLayout write = .ok cell :=
  header_region_access runtimeSafety state ⟨lifetime, 0⟩ cell write
    (root_access state lifetime cell (layout runtimeSafety) write initial found (typed ▸ layout_checked runtimeSafety)
      (by cases runtimeSafety <;> decide) permitted)

end Compiler.Extraction.RepresentativeArray.Owner
