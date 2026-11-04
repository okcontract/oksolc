/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionInvalidation
import Compiler.Extraction.ExpressionFieldTests

namespace Compiler.Extraction.Expression.InvalidationTests
open Compiler.ZigAir.Memory
open Tests (memory arrayMemory descriptor cells item arguments id sequence)

def after : State := { arrayMemory with heap := (arrayMemory.heap.replace 2
  { (descriptor cells) with type := .array 2 allocationType }) }

theorem array_execution : invalidate arrayMemory ⟨2, 32⟩ = .ok after := by decide

theorem array_from_geometry : ∃ reached, invalidate arrayMemory ⟨2, 32⟩ = .ok reached ∧
    reached.valid = true ∧ reached.nextId = arrayMemory.nextId ∧ reached.nextAddress = arrayMemory.nextAddress ∧
    reached.heap.lookup 2 = some { (descriptor cells) with type := .array 2 allocationType } ∧
    (∀ other, other ≠ 2 → reached.heap.lookup other = arrayMemory.heap.lookup other) := by
  exact invalidate_array arrayMemory 2 2 1 _ (by decide) rfl rfl rfl (by decide)

theorem every_leaf_uninitialized :
    readField after false ⟨2, 32⟩ itemOffset = .error .uninitialized ∧
    readField after false ⟨2, 32⟩ argumentsOffset = .error .uninitialized ∧
    load after (.pointer (.pointer false false usize) ⟨2, 48⟩) = .error .uninitialized ∧
    readField after false ⟨2, 32⟩ idOffset = .error .uninitialized ∧
    readField after false ⟨2, 32⟩ sequence_numberOffset = .error .uninitialized := by decide

theorem earlier_row_unchanged : readFields after false ⟨2, 0⟩ = .ok [item, arguments, id, sequence] := by decide

def threeRows : State := { arrayMemory with nextAddress := 608, heap := (arrayMemory.heap.replace 2
  { (descriptor cells) with type := .array 3 allocationType, cells := (cells ++
    cells.map (fun (offset, value) => (offset + 32, value)) ++ cells.map (fun (offset, value) => (offset + 64, value))) }) }

theorem later_row_unchanged :
    (do let reached ← invalidate threeRows ⟨2, 32⟩
        readFields reached false ⟨2, 64⟩) = .ok [item, arguments, id, sequence] := by decide

theorem pointees_and_history_retained : after.heap.lookup 0 = arrayMemory.heap.lookup 0 ∧
    after.heap.lookup 1 = arrayMemory.heap.lookup 1 ∧ after.nextId = 3 ∧ after.nextAddress = 576 ∧ after.valid = true := by decide

theorem root_execution : invalidate memory ⟨2, 0⟩ = .ok (memory []) := by decide

theorem already_uninitialized : invalidate (memory []) ⟨2, 0⟩ = .ok (memory []) := by decide

theorem readonly_rejected : Compiler.ZigAir.Memory.invalidate memory false allocationType ⟨2, 0⟩ = .error .readOnly ∧
    invalidate { memory with heap := memory.heap.replace 2 { descriptor with writable := false } } ⟨2, 0⟩ = .error .readOnly := by decide

theorem wrong_view_rejected : invalidate (memory [] (.array 8 idType)) ⟨2, 0⟩ = .error .unsupported ∧
    invalidate arrayMemory ⟨2, 8⟩ = .error .unsupported := by decide

theorem stale_and_bounds_rejected : invalidate Tests.reused ⟨2, 0⟩ = .error .unallocated ∧
    invalidate Tests.reused ⟨3, 0⟩ = .ok { Tests.reused with heap := Tests.reused.heap.replace 3 (descriptor []) } ∧
    invalidate arrayMemory ⟨2, 64⟩ = .error .memoryValidity ∧
    invalidate arrayMemory ⟨2, 1⟩ = .error .memoryValidity := by decide

theorem reinitialization_required :
    (do let reached ← store after (.pointer (.pointer true false itemType) ⟨2, 32⟩) item
        readFields reached false ⟨2, 32⟩) = .error .uninitialized := by decide

end Compiler.Extraction.Expression.InvalidationTests
