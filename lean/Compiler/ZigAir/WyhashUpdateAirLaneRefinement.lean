/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirLane

set_option maxRecDepth 8192

namespace Compiler.ZigAir.WyhashUpdateAir.Lane
open Memory AggregateAir Compiler.Extraction Control.Machine

/-- The native decoded operands are exactly those consumed by the existing
cell-level lane operation, for either external bytes or the hasher's buffer. -/
theorem model_eq (input : WyhashUpdate.Input) (offset : Nat) (index : Fin 3) (cells : Cells)
    (bytes : Nat → BitVec 8) (old : BitVec 64) (geometry : ByteSlice.Geometry input.view)
    (represented : ByteSlice.Represents (input.cells cells) input.view bytes)
    (inside : offset + 48 ≤ input.view.length)
    (found : cells.lookup (16 + index.val * 8) = some (WyhashLocal.word old)) :
    WyhashUpdate.lane input offset index cells = .ok
      (updatedCells cells index (word (fun i => bytes (offset + i)) index false)
        (word (fun i => bytes (offset + i)) index true) old) := by
  have bound := index.isLt
  have readA := ByteSlice.readLE_verified (input.cells cells) input.view bytes geometry represented
    (offset + 16 * index.val) 8 (by omega)
  have readB := ByteSlice.readLE_verified (input.cells cells) input.view bytes geometry represented
    (offset + 16 * index.val + 8) 8 (by omega)
  have readOld : WyhashLocal.nativeOps.read cells ⟨2 + index.val, by omega⟩ = .ok old := by
    apply WyhashUpdate.read_slot
    simpa only [show 8 * (2 + index.val) = 16 + index.val * 8 by omega] using found
  have member : 16 + 8 * index.val ∈ [16, 24, 32, 40, 48] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  simp only [WyhashUpdate.lane, readA, readB, readOld, bind, Except.bind, WyhashUpdate.store_eq _ _ _ member]
  simp only [updatedCells, word, Round.readOffset, Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
    ByteRange.decode_shift, Nat.add_assoc, Nat.mul_comm]

/-- General native lane preservation consumes the existing update invariant's
core and readiness facts. Its successful model result and preservation facts
are derived; the caller does not supply native reads, writes or allocations for
the lane's implementation. Original input-byte and saved-parameter admission
remain explicit until the enclosing captured round is composed. -/
theorem model_steps (loop : Bool) (index : Fin 3) (frames : List (Frame Ty AggregateCall.Prim Ref))
    {state : State} {id : Nat} (frame : CellFrame state id) (valid : state.valid = true)
    (typed : frame.cell.type = objectType) (input : WyhashUpdate.Input) (offset total : Nat)
    (core : WyhashUpdate.Core frame.cell.cells total) (ready : input.Ready frame.cell.cells)
    (address : Address) (bytes : Nat → BitVec 8)
    (represented : ByteSlice.Represents (input.cells frame.cell.cells) input.view bytes)
    (inside : offset + 48 ≤ input.view.length)
    (reads : ByteRange.Reads state address 48 (fun i => bytes (offset + i)))
    (inputSlot selfSlot : Nat)
    (inputRead : Memory.load state (slot false (WordRead.arrayPointer 48) inputSlot) =
      .ok (.pointer (WordRead.arrayPointer 48) address))
    (selfRead : Memory.load state (slot false (.pointer true false objectType) selfSlot) = .ok (selfPointer id))
    (args : List Register) (env : Env)
    (foundInput : env (inputReg loop) = some (.value (slot false (WordRead.arrayPointer 48) inputSlot)))
    (foundSelf : env (selfReg loop) = some (.value (slot false (.pointer true false objectType) selfSlot))) :
    ∃ after,
      (StackFrame state after ∧ Steps AggregateCall.semantics args
        (.suspended ⟨Round.readSite loop index false, env, state, frames⟩)
        (.finished (.fault .outOfMemory after))) ∨
      ∃ cells afterEnv, WyhashUpdate.lane input offset index frame.cell.cells = .ok cells ∧
        WyhashUpdate.Core cells total ∧ input.Ready cells ∧
        (∀ query, query < 16 ∨ 40 ≤ query → cells.lookup query = frame.cell.cells.lookup query) ∧
        StackFrame (frame.install cells) after ∧ Steps AggregateCall.semantics args
          (.suspended ⟨Round.readSite loop index false, env, state, frames⟩)
          (.suspended ⟨next loop index, afterEnv, after, frames⟩) ∧
        ∀ query < Round.readBase loop index false, afterEnv query = env query := by
  obtain ⟨old, found⟩ := core.lanes index
  have nativeFound : frame.cell.cells.lookup (16 + index.val * 8) = some (WyhashLocal.word old) := by
    simpa only [Nat.mul_comm] using found
  have model := model_eq input offset index frame.cell.cells bytes old ready.1 represented inside nativeFound
  obtain ⟨cells, ran, coreNext, readyNext, retained⟩ :=
    WyhashUpdate.lane_verified input offset index frame.cell.cells total core ready inside
  have same := Except.ok.inj (ran.symm.trans model)
  subst cells
  obtain ⟨after, failure | ⟨afterEnv, stack, path, before⟩⟩ := steps loop index frames frame valid typed core.valid
    address (fun i => bytes (offset + i)) reads old nativeFound inputSlot selfSlot inputRead selfRead args env foundInput foundSelf
  · exact ⟨after, Or.inl failure⟩
  · exact ⟨after, Or.inr ⟨_, afterEnv, model, coreNext, readyNext, retained, stack, path, before⟩⟩

end Compiler.ZigAir.WyhashUpdateAir.Lane
