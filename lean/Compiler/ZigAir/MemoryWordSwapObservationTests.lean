/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryWordSwapSites
import Compiler.ZigAir.MemoryWordSwapInvocationTests
import Compiler.ZigAir.MachineObservationTests

namespace Compiler.ZigAir.MemoryWordSwap.Tests
open Memory MemoryAir Control.Machine GeneratedMemory
open Memory.ByteExchange.Tests (caller)

def bodyObserved (fuel : Nat) (state : State) :=
  trace semantics args fuel (.suspended ⟨fn_swap_u32.program.body, fun _ => none, state, []⟩)

/-- This projection observes the actual byte-operation operands in each event's
own environment. Failed reference evaluation remains an explicit Except. -/
def byteAttempt (event : Observation Ty Prim Value State) : Option (Bool × Except Fault Value) :=
  match event.site.2.2 with
  | .wordByteLoad _ pointer => some (false, pointer.eval event.env)
  | .wordByteStore _ pointer _ => some (true, pointer.eval event.env)
  | _ => none

def expectedLane (index : Nat) : List (Bool × Except Fault Value) :=
  [(false, .ok (ByteAccess.pointer true false ⟨0, index⟩)),
   (false, .ok (ByteAccess.pointer true false ⟨0, 4 + index⟩)),
   (true, .ok (ByteAccess.pointer true false ⟨0, index⟩)),
   (true, .ok (ByteAccess.pointer true false ⟨0, 4 + index⟩))]

theorem complete_byte_attempts : (bodyObserved 160 caller).1.filterMap byteAttempt =
    expectedLane 0 ++ expectedLane 1 ++ expectedLane 2 ++ expectedLane 3 := by rfl'

theorem complete_binding_count : (bodyObserved 160 caller).1.length = 62 := by rfl'

theorem exhausted_attempts : (bodyObserved 160 exhausted).1.map (·.site.1) = [0, 1, 3, 4, 5, 6, 7] := by rfl'

theorem exhausted_no_byte_attempt : (bodyObserved 160 exhausted).1.filterMap byteAttempt = [] := by rfl'

theorem body_observation_erases (fuel : Nat) (state : State) :
    (bodyObserved fuel state).2 = run semantics args fuel ⟨fn_swap_u32.program.body, fun _ => none, state, []⟩ :=
  trace_erases semantics args fuel _

end Compiler.ZigAir.MemoryWordSwap.Tests
