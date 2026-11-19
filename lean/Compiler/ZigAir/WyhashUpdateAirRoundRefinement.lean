/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirRoundPreparation

namespace Compiler.ZigAir.WyhashUpdateAir.Round
open Memory AggregateAir Compiler.Extraction Control.Machine

/-- The fill round reads the actual initialized hasher buffer. Pointer
preparation, parameter saves and every lane are consumed in source order. -/
theorem buffer_steps {state : State} {id : Nat} (frame : CellFrame state id)
    (valid : state.valid = true) (typed : frame.cell.type = objectType) (total : Nat)
    (core : WyhashUpdate.Core frame.cell.cells total) (ready : WyhashUpdate.Input.buffer.Ready frame.cell.cells)
    (selfSlot : Nat)
    (selfRead : Memory.load state (slot false (.pointer true false objectType) selfSlot) = .ok (selfPointer id))
    (args : List Register) (env : Env) (frames : List (Frame Ty AggregateCall.Prim Ref))
    (foundSelf : env 4 = some (.value (slot false (.pointer true false objectType) selfSlot))) :
    ∃ after,
      (∃ completed cells, completed < 3 ∧ lanePrefix .buffer 0 completed frame.cell.cells = .ok cells ∧
        WyhashUpdate.Core cells total ∧ StackFrame (frame.install cells) after ∧
        Steps AggregateCall.semantics args (.suspended ⟨bufferSite, env, state, frames⟩)
          (.finished (.fault .outOfMemory after))) ∨
      ∃ cells afterEnv, WyhashUpdate.round .buffer 0 frame.cell.cells = .ok cells ∧
        WyhashUpdate.Core cells total ∧ WyhashUpdate.Input.buffer.Ready cells ∧
        (∀ query, query < 16 ∨ 40 ≤ query → cells.lookup query = frame.cell.cells.lookup query) ∧
        StackFrame (frame.install cells) after ∧
        Steps AggregateCall.semantics args (.suspended ⟨bufferSite, env, state, frames⟩)
          (.suspended ⟨lanesAt false 3, afterEnv, after, frames⟩) ∧
        ∀ query < 83, afterEnv query = env query := by
  have head := buffer_prepare_steps frame valid typed selfSlot selfRead args env frames foundSelf
  obtain ⟨after, ⟨completed, cells, bounded, ran, failedCore, stack, path⟩ |
      ⟨cells, afterEnv, ran, nextCore, nextReady, retained, stack, path, before⟩⟩ :=
    steps false frames frame valid typed .buffer 0 total core ready ⟨id, 56⟩ _ ready.represented
      (by decide) rfl args (bufferEnv env id)
      (by simp [bufferEnv, selfArgument, Control.Env.set])
      (by simp [bufferEnv, inputArgument, Control.Env.set])
  · exact ⟨after, Or.inl ⟨completed, cells, bounded, ran, failedCore, stack,
      head.trans AggregateCall.semantics args path⟩⟩
  · refine ⟨after, Or.inr ⟨cells, afterEnv, ran, nextCore, nextReady, retained, stack,
      head.trans AggregateCall.semantics args path, ?_⟩⟩
    intro query earlier
    apply (before query (by change query < 88; omega)).trans
    simp (disch := omega) only [bufferEnv, Control.Env.set, if_neg]

/-- The full-block round starts from the original external slice and current
index. Native offset arithmetic, source bounds and array casts are derived
before the same shared round executes. -/
theorem external_steps {state : State} {id : Nat} (frame : CellFrame state id)
    (valid : state.valid = true) (typed : frame.cell.type = objectType) (total : Nat)
    (core : WyhashUpdate.Core frame.cell.cells total) (source : Cells) (view : ByteSlice.View)
    (address : Address) (bytes : Nat → BitVec 8)
    (geometry : ByteSlice.Geometry view) (represented : ByteSlice.Represents source view bytes)
    (reads : ByteRange.Reads state address view.length bytes) (apart : address.allocation ≠ id)
    (index : Nat) (inside : index + 48 ≤ view.length) (bound : view.length < addressLimit)
    (selfSlot inputSlot indexSlot : Nat)
    (selfRead : Memory.load state (slot false (.pointer true false objectType) selfSlot) = .ok (selfPointer id))
    (inputRead : Memory.load state (slot false inputType inputSlot) = .ok (.slice inputType address view.length))
    (indexRead : Memory.load state (slot true usize indexSlot) = .ok (.scalar (.int false 64 index)))
    (args : List Register) (env : Env) (frames : List (Frame Ty AggregateCall.Prim Ref))
    (foundSelf : env 4 = some (.value (slot false (.pointer true false objectType) selfSlot)))
    (foundInput : env 7 = some (.value (slot false inputType inputSlot)))
    (foundIndex : env 50 = some (.value (slot true usize indexSlot))) :
    ∃ after,
      (∃ completed cells, completed < 3 ∧ lanePrefix (.external source view) index completed frame.cell.cells = .ok cells ∧
        WyhashUpdate.Core cells total ∧ StackFrame (frame.install cells) after ∧
        Steps AggregateCall.semantics args (.suspended ⟨loopBody, env, state, frames⟩)
          (.finished (.fault .outOfMemory after))) ∨
      ∃ cells afterEnv, WyhashUpdate.round (.external source view) index frame.cell.cells = .ok cells ∧
        WyhashUpdate.Core cells total ∧
        (∀ query, query < 16 ∨ 40 ≤ query → cells.lookup query = frame.cell.cells.lookup query) ∧
        StackFrame (frame.install cells) after ∧
        Steps AggregateCall.semantics args (.suspended ⟨loopBody, env, state, frames⟩)
          (.suspended ⟨lanesAt true 3, afterEnv, after, frames⟩) ∧
        ∀ query < 337, afterEnv query = env query := by
  have head := external_prepare_steps state id address index view.length bytes reads inside bound
    selfSlot inputSlot indexSlot selfRead inputRead indexRead args env frames foundSelf foundInput foundIndex
  have ready : (WyhashUpdate.Input.external source view).Ready frame.cell.cells :=
    ⟨geometry, fun i inside => ⟨bytes i, represented i inside⟩⟩
  obtain ⟨after, ⟨completed, cells, bounded, ran, failedCore, stack, path⟩ |
      ⟨cells, afterEnv, ran, nextCore, _, retained, stack, path, before⟩⟩ :=
    steps true frames frame valid typed (.external source view) index total core ready
      ⟨address.allocation, address.offset + index⟩ bytes represented inside
      ⟨apart, reads.window index 48 inside⟩ args (externalEnv env id address index view.length)
      (by simp [externalEnv, selfArgument, Control.Env.set])
      (by simp [externalEnv, inputArgument, Control.Env.set])
  · exact ⟨after, Or.inl ⟨completed, cells, bounded, ran, failedCore, stack,
      head.trans AggregateCall.semantics args path⟩⟩
  · refine ⟨after, Or.inr ⟨cells, afterEnv, ran, nextCore, retained, stack,
      head.trans AggregateCall.semantics args path, ?_⟩⟩
    intro query earlier
    apply (before query (by change query < 345; omega)).trans
    simp (disch := omega) only [externalEnv, Control.Env.set, if_neg]

end Compiler.ZigAir.WyhashUpdateAir.Round
