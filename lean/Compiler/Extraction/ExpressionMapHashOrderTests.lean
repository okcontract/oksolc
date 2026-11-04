/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapHashBytesRun
import Compiler.Extraction.ExpressionMapHashBytesTests

namespace Compiler.Extraction.ExpressionMap.HashBytes.Ordered.Tests
open Compiler.ZigAir.Memory Compiler.Extraction.Cache

def caller (address : Nat := 4096) : State := ⟨[], 1, address⟩
def key (arguments : List (BitVec 32)) : Key := ⟨0, 0, 0, arguments, 0⟩

def failedRead := runRaw caller (key [7]) ⟨999, 0, 1⟩

/-- The first three update calls have already written the hasher when the
argument view encounters a stale pointer. Its local is cleaned, but the caller
hasher and its 37-byte prefix remain observable until outer cleanup. -/
theorem previous_updates_retained :
    failedRead.1 = .error .unallocated ∧ failedRead.2.nextId = 7 ∧ failedRead.2.nextAddress = 4400 ∧
    load failedRead.2 (.pointer (.pointer false false usize) ⟨2, 40⟩) = .ok (WyhashLocal.word 37) ∧
    load failedRead.2 (.pointer (.pointer false false usize) ⟨2, 48⟩) = .ok (WyhashLocal.word 37) := by decide +kernel

theorem failed_view_cleanup :
    HashBytes.run caller (key [7]) ⟨999, 0, 1⟩ =
      (.error .unallocated, ⟨[], 7, 4400⟩) := by decide +kernel

/-- Initializer exhaustion occurs before any argument view, even when that
later view would reject. The caller-owned empty hasher is retired by cleanup. -/
theorem initialization_precedes_invalid_view :
    HashBytes.run (caller (addressLimit - 176)) (key [7]) ⟨999, 0, 1⟩ =
      (.error .outOfMemory, ⟨[], 3, addressLimit - 8⟩) := by decide +kernel

/-- Even an empty argument view performs its captured descriptor allocation.
Failure at that point keeps the preceding scalar updates and their cursors. -/
theorem view_allocation_failure_retains_prefix :
    let executed := runRaw (caller (addressLimit - 304)) (key []) ⟨999, 0, 0⟩
    executed.1 = .error .outOfMemory ∧ executed.2.nextId = 6 ∧ executed.2.nextAddress = addressLimit - 16 ∧
    load executed.2 (.pointer (.pointer false false usize) ⟨2, 40⟩) = .ok (WyhashLocal.word 37) := by decide +kernel

end Compiler.Extraction.ExpressionMap.HashBytes.Ordered.Tests
