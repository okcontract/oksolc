/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryInvariant
import Compiler.ZigAir.MachineProofs

namespace Compiler.ZigAir.MemoryAir
open Control.Machine Memory

/-- The concrete heap invariant holds at every execution budget, including
suspension inside loops and every modeled source, memory and resource fault.
This is a control-model theorem, not a source-to-AIR or termination theorem. -/
theorem machine_preserves_valid (args : List Value) (fuel : Nat)
    (config : Config Memory.Ty Prim Ref Value State) (initial : config.state.valid = true) :
    (run semantics args fuel config).state.valid = true :=
  run_preserves semantics args (fun state => state.valid = true) Prim.preserves_valid fuel config initial

/-- No bound on the length of the finite execution appears in this statement. -/
theorem machine_steps_preserve_valid (args : List Value)
    (first last : Execution Memory.Ty Prim Ref Value Memory.Fault State)
    (execution : Steps semantics args first last) (initial : first.state.valid = true) :
    last.state.valid = true :=
  execution.preserves semantics args (fun state => state.valid = true) Prim.preserves_valid initial

end Compiler.ZigAir.MemoryAir
