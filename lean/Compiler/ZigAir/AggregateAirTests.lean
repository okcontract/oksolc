/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.AggregateAirProofs

namespace Compiler.ZigAir.AggregateAir.Tests
open Memory
deriving instance DecidableEq for Except

def owner : Ty := .aggregate "fixture.Pair" ⟨16, 8⟩ [(0, .scalar (.int false 64)), (8, .scalar (.int false 64))]
def word (n : Nat) : Value := .scalar (.int false 64 n)
def cell : Allocation := ⟨16, owner, [(0, word 7), (8, word 9)], true, false⟩
def state : State := ⟨[(0, cell)], 1, 32⟩
def pointer : Value := .pointer (.pointer true false owner) ⟨0, 0⟩
def partialValue : Register := .aggregate owner [(0, word 3)]
def after : State := { state with heap := [(0, { cell with cells := [(0, word 3)] })] }

theorem fixture_valid : state.valid = true ∧ after.valid = true := by decide +kernel

theorem partial_assignment_forgets_absent_leaves :
    store state pointer partialValue = .ok after ∧
    Memory.load after (.pointer (.pointer true false usize) ⟨0, 8⟩) = .error .uninitialized := by decide +kernel

theorem snapshot_is_value_not_local_alias :
    load state pointer = .ok (.aggregate owner [(0, word 7), (8, word 9)]) ∧
    load after pointer = .ok partialValue := by decide +kernel

theorem readonly_and_dead_reject :
    store state (.pointer (.pointer false false owner) ⟨0, 0⟩) partialValue = .error .readOnly ∧
    store { state with heap := [(0, { cell with writable := false })] } pointer partialValue = .error .readOnly ∧
    load {} pointer = .error .unallocated := by decide +kernel

theorem nominal_and_field_identity_reject :
    load state (.pointer (.pointer true false (.aggregate "Other" ⟨16, 8⟩
      [(0, .scalar (.int false 64)), (8, .scalar (.int false 64))])) ⟨0, 0⟩) = .error .unsupported ∧
    store state pointer (.aggregate owner [(8, .scalar (.int false 8 1))]) = .error .malformed := by decide +kernel

def outer : Ty := .aggregate "Outer" ⟨32, 8⟩ [(8, .object owner)]
def nested : State := ⟨[(0, ⟨16, outer, [], true, false⟩)], 1, 48⟩

theorem nested_aggregate_copy_rejects_explicitly :
    nested.valid = true ∧
    load nested (.pointer (.pointer true false owner) ⟨0, 8⟩) = .error .unsupported ∧
    store nested (.pointer (.pointer true false owner) ⟨0, 8⟩) partialValue = .error .unsupported := by decide +kernel

theorem declared_array_bound_precedes_larger_heap :
    arrayElementPointer ⟨[(0, ⟨16, .array 4 usize, [], true, false⟩)], 1, 48⟩
      (.pointer (.pointer true false (.array 3 usize)) ⟨0, 0⟩) 3 = .error .sourceBounds := by decide +kernel

theorem forged_array_parent_rejects :
    arrayElementPointer state (.pointer (.pointer true false (.array 2 usize)) ⟨0, 0⟩) 0 =
      .error .unsupported := by decide +kernel

end Compiler.ZigAir.AggregateAir.Tests
