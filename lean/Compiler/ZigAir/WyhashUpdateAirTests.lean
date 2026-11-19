/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.GeneratedWyhashUpdate
import Compiler.ZigAir.MemoryByteRangeTests
import Compiler.Extraction.WyhashUpdate
import Compiler.Extraction.WyhashHashVectors

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false

/-! Full generated-body regressions. These exercise the general interpreter;
they do not establish update preservation for arbitrary caller inputs. -/
namespace Compiler.ZigAir.WyhashUpdateAirTests
open Memory AggregateAir Compiler.Extraction

def bytes (length : Nat) : List (BitVec 8) :=
  (List.range length).map fun i => BitVec.ofNat 8 (i * 17 + 3)

def inputCell (input : List (BitVec 8)) : Allocation :=
  ⟨128, .array (max 1 input.length) ByteSlice.byte, ByteSlice.cellsFrom input 0, false, false⟩

def caller (cells : Cells) (input : List (BitVec 8)) : State :=
  ⟨[(0, ⟨16, WyhashLocal.objectType, cells, true, false⟩), (1, inputCell input)],
    2, 128 + max 1 input.length⟩

def arguments (length : Nat) : List Register :=
  [.value (.pointer (.pointer true false WyhashLocal.objectType) ⟨0, 0⟩),
   .value (.slice (.slice false ByteSlice.byte) ⟨1, 0⟩ length)]

def execute (cells : Cells) (input : List (BitVec 8)) (fuel : Nat := 10000) : AggregateCall.Invocation :=
  GeneratedWyhashUpdate.update.runFuel fuel (arguments input.length) (caller cells input)

def agrees (cells : Cells) (input : List (BitVec 8)) : Bool :=
  match execute cells input with
  | .suspended .. => false
  | .finished (.error _) _ => false
  | .finished (.ok value) after =>
    match after.heap.lookup 0 with
    | none => false
    | some cell =>
      decide (value = .value (.scalar .unit)) && after.valid &&
      decide (WyhashUpdate.update (ByteSlice.cellsFrom input 0) (ByteSlice.imageView input) cells = .ok cell.cells) &&
      decide (after.heap.lookup 1 = some (inputCell input)) && decide (after.heap.length = 2)

def initial : Cells := WyhashUpdate.initialCells (WyhashUpdate.seedState 0)

theorem buffered : agrees initial (bytes 4) = true := by decide +kernel

theorem assertion_body_both_outcomes :
    GeneratedWyhashUpdate.assertion.run [.value (.scalar (.bool true))] {} =
      (.ok (.value (.scalar .unit)), {}) ∧
    GeneratedWyhashUpdate.assertion.run [.value (.scalar (.bool false))] {} =
      (.error (.scalar .illegalBehavior), {}) := by decide +kernel

theorem block_boundaries_short : [0, 1, 16, 47].all
    (fun length => agrees initial (bytes length)) = true := by decide +kernel

theorem block_boundaries_middle : [48, 49, 63, 64].all
    (fun length => agrees initial (bytes length)) = true := by decide +kernel

private theorem boundary95 : agrees initial (bytes 95) = true := by decide +kernel
private theorem boundary96 : agrees initial (bytes 96) = true := by decide +kernel
private theorem boundary97 : agrees initial (bytes 97) = true := by decide +kernel
private theorem boundary145 : agrees initial (bytes 145) = true := by decide +kernel

theorem block_boundaries_long : [95, 96, 97, 145].all
    (fun length => agrees initial (bytes length)) = true := by
  simp only [List.all_cons, List.all_nil, boundary95, boundary96, boundary97, boundary145, Bool.true_and]

def prepared (length : Nat) : Cells :=
  match WyhashUpdate.update (ByteSlice.cellsFrom (bytes length) 0) (ByteSlice.imageView (bytes length)) initial with
  | .ok cells => cells
  | .error _ => []

theorem fills_existing_buffer : [(1, 48), (47, 2), (48, 1), (16, 113)].all
    (fun (before, count) => agrees (prepared before) (bytes count)) = true := by decide +kernel

/-- Reuse the existing native matrix rather than inventing another opcode or
hash fixture family. Each accepted comparison includes the complete live cells,
caller input and cleanup; the next input uses those equal cells. -/
def matchesChunks (cells : Cells) : List (List (BitVec 8)) → Bool
  | [] => true
  | input :: rest => agrees cells input &&
    match WyhashUpdate.update (ByteSlice.cellsFrom input 0) (ByteSlice.imageView input) cells with
    | .error _ => false
    | .ok next => matchesChunks next rest


def incomplete : State := { caller initial (bytes 4) with
  heap := [(0, ⟨16, WyhashLocal.objectType, initial, true, false⟩),
           (1, { inputCell (bytes 4) with cells := ByteSlice.cellsFrom (bytes 2) 0 })] }

def partialFailure : AggregateCall.Invocation :=
  GeneratedWyhashUpdate.update.runFuel 10000 (arguments 4) incomplete

theorem missing_input_retains_total_and_prefix :
    (match partialFailure with
    | .finished (.error .uninitialized) after =>
      decide (Memory.load after (.pointer (.pointer false false usize) ⟨0, 40⟩) = .ok (WyhashLocal.word 4) ∧
      ByteRange.read after ⟨0, 56⟩ 2 = .ok (bytes 2) ∧
      ScalarBytes.readAt after ⟨0, 58⟩ = .error .uninitialized ∧
      after.heap.length = 2 ∧ after.valid = true ∧ after.nextId > incomplete.nextId)
    | _ => false) = true := by decide +kernel

def exhausted : State := { caller initial (bytes 4) with nextAddress := addressLimit - 8 }

theorem stack_oom_is_explicit :
    (match GeneratedWyhashUpdate.update.runFuel 10000 (arguments 4) exhausted with
    | .finished (.error .outOfMemory) after => decide (after = exhausted)
    | _ => false) = true := by decide +kernel

theorem suspension_keeps_locals :
    (match execute initial (bytes 49) 20 with
    | .suspended _ mark _ config => decide (mark = 2 ∧ config.state.heap.length > 2)
    | _ => false) = true := by decide +kernel

/-- All four allocations within the first loop lane may fail. Earlier total
accounting survives, while the lane word is unchanged and invocation locals are
cleaned. These exercise the existing complete generated update. -/
theorem lane_allocation_failures : [(64, 5), (80, 6), (88, 7), (96, 8)].all
    (fun (headroom, allocations) =>
      let state := { caller initial (bytes 49) with nextAddress := addressLimit - headroom }
      match GeneratedWyhashUpdate.update.runFuel 10000 (arguments 49) state with
      | .finished (.error .outOfMemory) after =>
          after.valid && decide (after.heap.length = 2 ∧ after.nextId = state.nextId + allocations ∧
            (after.heap.lookup 0).map Allocation.cells = some (initial.set 40 (WyhashLocal.word 49)) ∧
            after.heap.lookup 1 = state.heap.lookup 1)
      | _ => false) = true := by decide +kernel

/-- Exhaustion in the next lane must preserve the already completed lane's
store. Treating OOM as rollback of the hasher would fail this observation. -/
theorem later_lane_oom_keeps_completed_store :
    (let state := { caller initial (bytes 49) with nextAddress := addressLimit - 112 }
    match GeneratedWyhashUpdate.update.runFuel 10000 (arguments 49) state with
    | .finished (.error .outOfMemory) after =>
        match after.heap.lookup 0 with
        | none => false
        | some cell => after.valid && decide (after.heap.length = 2 ∧ after.nextId = state.nextId + 9 ∧
            WyhashUpdate.lane (.external (ByteSlice.cellsFrom (bytes 49) 0) (ByteSlice.imageView (bytes 49)))
              0 0 (initial.set 40 (WyhashLocal.word 49)) = .ok cell.cells ∧
            cell.cells.lookup 16 ≠ initial.lookup 16 ∧ after.heap.lookup 1 = state.heap.lookup 1)
    | _ => false) = true := by decide +kernel

end Compiler.ZigAir.WyhashUpdateAirTests
