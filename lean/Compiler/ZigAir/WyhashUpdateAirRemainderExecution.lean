/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirSuffixExecution

set_option maxRecDepth 8192

namespace Compiler.ZigAir.WyhashUpdateAir.Remainder
open Memory AggregateAir Compiler.Extraction Control.Machine

/-- Complete post-loop execution. Native allocation may fail before any tail
write; otherwise the original suffix, final copy, length store and return all
execute. Their cells equal the tail consumed by the existing update invariant. -/
theorem execute {state : State} {id : Nat} (frame : CellFrame state id)
    (valid : state.valid = true) (typed : frame.cell.type = objectType)
    (address : Address) (source : Cells) (view : ByteSlice.View) (bytes : Nat → BitVec 8)
    (geometry : ByteSlice.Geometry view) (represented : ByteSlice.Represents source view bytes)
    (reads : ByteRange.Reads state address view.length bytes) (apart : address.allocation ≠ id)
    (total index selfSlot inputSlot indexSlot : Nat) (core : WyhashUpdate.Core frame.cell.cells total)
    (inside : index < view.length) (ended : view.length ≤ index + 48) (budget : view.length < addressLimit)
    (selfApart : selfSlot ≠ id) (inputApart : inputSlot ≠ id) (indexApart : indexSlot ≠ id)
    (selfRead : Memory.load state (slot false (.pointer true false objectType) selfSlot) = .ok (selfPointer id))
    (inputRead : Memory.load state (slot false inputType inputSlot) = .ok (.slice inputType address view.length))
    (indexRead : Memory.load state (slot true usize indexSlot) = .ok (.scalar (.int false 64 index)))
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (foundSelf : env 4 = some (.value (slot false (.pointer true false objectType) selfSlot)))
    (foundInput : env 7 = some (.value (slot false inputType inputSlot)))
    (foundIndex : env 50 = some (.value (slot true usize indexSlot))) :
    ∃ after,
      (StackFrame state after ∧
        Steps AggregateCall.semantics args (.suspended ⟨Loop.continuation, env, state, outer⟩)
          (.finished (.fault .outOfMemory after))) ∨
      ∃ cells, WyhashUpdate.remainder source view index frame.cell.cells = .ok cells ∧
        WyhashUpdate.Core cells total ∧ StackFrame (frame.install cells) after ∧
        Steps AggregateCall.semantics args (.suspended ⟨Loop.continuation, env, state, outer⟩)
          (.finished (.returned (.value (.scalar .unit)) after)) := by
  obtain ⟨prepared, stack, failed | ⟨savedEnv, savedPath, countRead, strict, foundRest, foundSlice, before⟩⟩ :=
    save_steps state valid address index view.length inputSlot indexSlot bytes reads inside budget
      inputRead indexRead args env outer foundInput foundIndex
  · exact ⟨prepared, Or.inl ⟨stack, failed⟩⟩
  · let current := frame.extend stack
    have restApart : state.nextId ≠ id := by
      have old := (valid_lookup state id frame.cell valid frame.found).1
      omega
    have bound := end_bound current stack.valid typed strict
    have self := stack.old_load false false (.pointer true false objectType) ⟨selfSlot, 0⟩ _ selfRead
    have input := stack.old_load false false inputType ⟨inputSlot, 0⟩ _ inputRead
    have indexValue := stack.old_load true false usize ⟨indexSlot, 0⟩ _ indexRead
    obtain ⟨retained, suffixEnv, suffixPath, suffixRun, suffixCore, suffixBefore⟩ :=
      Suffix.execute current stack.valid typed bound address source frame.cell.cells view bytes geometry represented
        (reads.extend stack) apart total index (view.length - index) selfSlot inputSlot indexSlot state.nextId core
        inside (by omega) budget selfApart inputApart indexApart restApart self input indexValue countRead
        args savedEnv outer (by rw [before 4 (by decide)]; exact foundSelf)
        (by rw [before 7 (by decide)]; exact foundInput) (by rw [before 50 (by decide)]; exact foundIndex) foundRest
    obtain ⟨copied, finishPath, copiedRun, copiedCore, _, _⟩ := Finish.body_steps current stack.valid typed bound address source
      retained view bytes geometry represented (reads.extend stack) apart total index (view.length - index)
      selfSlot state.nextId suffixCore (by omega) (by omega) selfApart restApart self countRead args suffixEnv outer
      (by rw [suffixBefore 4 (by decide), before 4 (by decide)]; exact foundSelf)
      (by rw [suffixBefore 594 (by decide)]; exact foundRest)
      (by rw [suffixBefore 591 (by decide)]; exact foundSlice)
    let finalCells := copied.set 48 (WyhashLocal.word (BitVec.ofNat 64 (view.length - index)))
    have finalCore : WyhashUpdate.Core finalCells total := copiedCore.store_word 48 _ (by decide)
    have finalStack := stack.install_old frame finalCells (typed ▸ finalCore.valid)
    have model : WyhashUpdate.remainder source view index frame.cell.cells = .ok finalCells := by
      have closed : WyhashUpdate.store copied 48 (BitVec.ofNat 64 (view.length - index)) = .ok finalCells :=
        WyhashUpdate.store_eq copied 48 _ (by decide)
      unfold WyhashUpdate.remainder
      dsimp only
      split
      · rename_i selected
        exact WyhashLocal.bind_result _ _ retained finalCells (by simpa only [if_pos selected] using suffixRun)
          (WyhashLocal.bind_result _ _ copied finalCells copiedRun closed)
      · rename_i selected
        exact WyhashLocal.bind_result _ _ retained finalCells (by simpa only [if_neg selected] using suffixRun)
          (WyhashLocal.bind_result _ _ copied finalCells copiedRun closed)
    have currentEq : current.install frame.cell.cells = prepared := current.install_current stack.valid
    rw [currentEq] at suffixPath
    exact ⟨current.install finalCells, Or.inr ⟨finalCells, model, finalCore, finalStack,
      savedPath.trans AggregateCall.semantics args (suffixPath.trans AggregateCall.semantics args finishPath)⟩⟩

end Compiler.ZigAir.WyhashUpdateAir.Remainder
