/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirLoopExecution
import Compiler.ZigAir.WyhashUpdateAirTests

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Compiler.ZigAir.WyhashUpdateAirTests
open Memory AggregateAir Compiler.Extraction WyhashUpdateAir Control.Machine

def loopBase : State :=
  { caller initial (bytes 49) with
    heap := (3, ⟨8200, inputType,
      [(0, .pointer (.pointer false true ByteSlice.byte) ⟨1, 0⟩), (8, .scalar (.int false 64 49))], true, true⟩) ::
      (2, ⟨8192, .pointer true false objectType, [(0, selfPointer 0)], true, true⟩) ::
      (caller initial (bytes 49)).heap
    nextId := 4
    nextAddress := 8216 }

def loopContext : Loop.Context loopBase 0 where
  frame := ⟨⟨16, objectType, initial, true, false⟩, ⟨104, 8⟩, rfl, rfl, by decide +kernel⟩
  valid := by decide +kernel
  typed := rfl
  source := ByteSlice.cellsFrom (bytes 49) 0
  view := ByteSlice.imageView (bytes 49)
  address := ⟨1, 0⟩
  bytes := fun i => (bytes 49)[i]?.getD 0
  geometry := ByteSlice.array_geometry _
  represented := ByteSlice.image_represents _
  reads := by
    have all : ∀ i : Fin 49, ScalarBytes.readAt loopBase ⟨1, i.val⟩ = .ok ((bytes 49)[i.val]?.getD 0) := by
      decide +kernel
    intro i inside
    simpa only [Nat.zero_add] using all ⟨i, inside⟩
  apart := by decide
  selfSlot := 2
  inputSlot := 3
  indexSlot := 4
  selfApart := by decide
  inputApart := by decide
  selfRead := by decide +kernel
  inputRead := by decide +kernel
  countRead := by decide +kernel
  indexFresh := by decide
  budget := by decide
  total := 0

def loopState : State :=
  { loopBase with
    heap := (4, ⟨8216, usize, [(0, .scalar (.int false 64 0))], true, true⟩) :: loopBase.heap
    nextId := 5
    nextAddress := 8224 }

def loopEnv : Env :=
  let empty : Env := fun _ => none
  ((empty.set 4 (.value (slot false (.pointer true false objectType) 2))).set
    7 (.value (slot false inputType 3))).set 50 (.value (slot true usize 4))

/-- The native-loop admission has a concrete witness with a taken round.
The independent whole-update regressions observe successful 49-byte execution. -/
theorem loop_admitted : Loop.At loopContext initial 0 loopState := by
  refine ⟨(WyhashUpdate.init_invariant 0).core, ?_, ?_, by decide +kernel, by decide⟩
  · rw [show initial = loopContext.frame.cell.cells from rfl, loopContext.frame.install_current loopContext.valid]
    refine ⟨by decide +kernel, by decide +kernel, by decide,
      [(4, ⟨8216, usize, [(0, .scalar (.int false 64 0))], true, true⟩)], rfl, ?_⟩
    intro entry member
    simp only [List.mem_singleton] at member
    subst entry
    exact ⟨rfl, by decide⟩
  · exact ⟨⟨⟨8216, usize, [(0, .scalar (.int false 64 0))], true, true⟩,
      ⟨8, 8⟩, rfl, rfl, by decide +kernel⟩, rfl, by decide +kernel⟩

theorem loop_specializes : ∃ after, after.valid = true ∧
    (Steps AggregateCall.semantics [] (.suspended ⟨Loop.entry, loopEnv, loopState, []⟩)
      (.finished (.fault .outOfMemory after)) ∨
     ∃ cells stop env, WyhashUpdate.loop loopContext.source loopContext.view 0 initial = .ok (cells, stop) ∧
       WyhashUpdate.Core cells 0 ∧ StackFrame (loopContext.frame.install cells) after ∧
       Memory.load after (slot true usize 4) = .ok (.scalar (.int false 64 stop)) ∧
       Steps AggregateCall.semantics [] (.suspended ⟨Loop.entry, loopEnv, loopState, []⟩)
         (.suspended ⟨Loop.continuation, env, after, []⟩)) := by
  obtain ⟨after, ⟨cells, _, _, stack, path⟩ |
      ⟨cells, stop, env, ran, live, _, _, _, _, _, path, _⟩⟩ :=
    Loop.entry_steps loopContext initial loop_admitted [] loopEnv [] (by unfold Loop.Locals; decide +kernel)
  · exact ⟨after, stack.valid, Or.inl path⟩
  · exact ⟨after, live.stack.valid, Or.inr ⟨cells, stop, env, ran, live.core, live.stack, live.indexRead, path⟩⟩

end Compiler.ZigAir.WyhashUpdateAirTests
