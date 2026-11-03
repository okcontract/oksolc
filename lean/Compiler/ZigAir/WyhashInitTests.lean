/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashInitRun
import Compiler.Extraction.WyhashUpdate
import Compiler.ZigAir.AggregateAirProofs

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Compiler.ZigAir.WyhashInitTests
open Memory AggregateAir Compiler.Extraction
deriving instance DecidableEq for Except

def expected (seed : BitVec 64) : Register :=
  .aggregate GeneratedWyhashInit.fn_init.returnType (WyhashUpdate.initialCells (WyhashUpdate.seedState seed))

theorem seed_zero : GeneratedWyhashInit.fn_init.run [.value (WyhashLocal.word 0)] {} =
    (.ok (expected 0), ⟨[], 3, 128⟩) := by decide +kernel

theorem seed_max : GeneratedWyhashInit.fn_init.run [.value (WyhashLocal.word (-1))] {} =
    (.ok (expected (-1)), ⟨[], 3, 128⟩) := by decide +kernel

/-- Each allocation can fail independently. Cleanup retains reached cursors. -/
theorem first_allocation_oom : GeneratedWyhashInit.fn_init.run [.value (WyhashLocal.word 0)]
    ⟨[], 0, addressLimit - 104⟩ = (.error .outOfMemory, ⟨[], 0, addressLimit - 104⟩) := by decide +kernel

theorem second_allocation_oom : GeneratedWyhashInit.fn_init.run [.value (WyhashLocal.word 0)]
    ⟨[], 0, addressLimit - 112⟩ = (.error .outOfMemory, ⟨[], 1, addressLimit - 8⟩) := by decide +kernel

theorem third_allocation_oom : GeneratedWyhashInit.fn_init.run [.value (WyhashLocal.word 0)]
    ⟨[], 0, addressLimit - 120⟩ = (.error .outOfMemory, ⟨[], 2, addressLimit - 8⟩) := by decide +kernel

end Compiler.ZigAir.WyhashInitTests
