/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.SliceBytesAir
import Compiler.ZigAir.AggregateAirTests

namespace Compiler.ZigAir.SliceBytesAir.Tests
open Memory Memory.WordArray AggregateAir

def caller : State :=
  ⟨[(0, ⟨16, .array 3 word,
    [(0, .scalar (.int false 32 99)), (4, .scalar (.int false 32 0x12345678)),
     (8, .scalar (.int false 32 0x90abcdef))], false, false⟩)], 1, 28⟩

def run (state : State) (address : Address) (length : Nat) : Except Fault Register × State :=
  GeneratedExpressionHashSlice.arguments.run [.value (.slice wordSlice address length)] state

theorem readonly_subview :
    run caller ⟨0, 4⟩ 2 =
      (.ok (.value (.slice byteSlice ⟨0, 4⟩ 8)), { caller with nextId := 3, nextAddress := 56 }) := by decide +kernel

theorem empty_unused_pointer :
    run caller ⟨999, 3⟩ 0 = (.ok .emptyBytes, { caller with nextId := 2, nextAddress := 48 }) := by decide +kernel

theorem first_allocation_failure :
    let before := { caller with nextAddress := addressLimit - 16 }
    run before ⟨999, 3⟩ 0 = (.error .outOfMemory, before) := by decide +kernel

theorem second_allocation_failure :
    let before := { caller with nextAddress := addressLimit - 24 }
    run before ⟨0, 4⟩ 2 =
      (.error .outOfMemory, { caller with nextId := 2, nextAddress := addressLimit - 8 }) := by decide +kernel

theorem source_geometry_rejected :
    (run caller ⟨0, 5⟩ 1).1 = .error .memoryValidity ∧
    (run caller ⟨999, 0⟩ 1).1 = .error .unallocated ∧
    (run caller ⟨0, 4⟩ 3).1 = .error .memoryValidity := by decide +kernel

theorem multiplication_overflow_rejected :
    (run caller ⟨0, 4⟩ (addressLimit / 4)).1 = .error (.scalar .illegalBehavior) := by decide +kernel

theorem empty_storage_has_no_heap_capability :
    (Ref.constant .emptyBytes).value (fun _ => none) = .error .unsupported ∧
    AggregateAir.store caller (.pointer (.pointer true false byteSlice) ⟨0, 0⟩) .emptyBytes = .error .unsupported ∧
    values (Control.Env.set (fun _ => none) 0 .emptyBytes) 0 = none := by decide +kernel

end Compiler.ZigAir.SliceBytesAir.Tests
