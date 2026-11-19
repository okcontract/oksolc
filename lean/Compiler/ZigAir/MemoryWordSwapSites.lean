/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MachineCoverage
import Compiler.ZigAir.GeneratedWordSwap

/-! Complete data-operation site inventory for the captured swap. This proves
which operands every dynamic data-operation attempt uses, for every finite
execution prefix. Runtime pointer origins and physical access confinement are
separate obligations; site IDs alone cannot establish native noalias. -/
namespace Compiler.ZigAir.MemoryWordSwap
open Memory MemoryAir Control.Machine GeneratedMemory

/-- Every memory primitive is classified explicitly. Geometry/metadata checks
are retained as observations too, but are not data loads or stores. -/
def dataSite (site : Nat × Ty × Prim) : Prop :=
  match site.2.2 with
  | .alloc _ => site = (7, .pointer true false usize, .alloc usize)
  | .load _ => site = (13, usize, .load (.local 7))
  | .store .. => site = (8, .scalar .unit, .store (.local 7) (.constant (.scalar (.int false 64 0)))) ∨
      site = (28, .scalar .unit, .store (.local 7) (.local 27))
  | .wordByteLoad .. => site = (20, ByteAccess.byte, .wordByteLoad .little (.local 18)) ∨
      site = (21, ByteAccess.byte, .wordByteLoad .little (.local 19))
  | .wordByteStore .. => site = (22, .scalar .unit, .wordByteStore .little (.local 18) (.local 21)) ∨
      site = (23, .scalar .unit, .wordByteStore .little (.local 19) (.local 20))
  | .argument .. | .scalar .. | .pointerField .. | .pointerCast .. | .offsetPointer .. |
    .elementPointer .. | .wordByteCast .. | .sliceElementPointer .. | .slice .. | .sliceLen .. |
    .slicePtr .. | .checkBounds .. => True

theorem data_sites_checked : fn_swap_u32.program.body.Covered dataSite := by
  simp [Control.Code.Covered, Control.Code.bindings, fn_swap_u32, dataSite, usize, ByteAccess.byte]

/-- Arbitrary fuel, arguments, environments and states, including failing
executions: every attempted data operation has one of the exact sites above. -/
theorem data_sites_complete (fuel : Nat) (args : List Value) (env : Env) (state : State) :
    ∀ event ∈ (trace semantics args fuel (.suspended ⟨fn_swap_u32.program.body, env, state, []⟩)).1,
      dataSite event.site :=
  trace_covered semantics args dataSite fuel _ ⟨data_sites_checked, by simp⟩

end Compiler.ZigAir.MemoryWordSwap
