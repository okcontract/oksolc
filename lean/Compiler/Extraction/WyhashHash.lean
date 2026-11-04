/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.WyhashUpdate

namespace Compiler.Extraction.WyhashHash
open Compiler.ZigAir.Memory WyhashLocal WyhashUpdate

/-- Byte images describe already admitted inputs. They are read through typed
cells without claiming a new native allocation for the image representation. -/
def updates : List (List (BitVec 8)) → Cells → Except Fault Cells
  | [], cells => .ok cells
  | input :: rest, cells => do
      let cells ← update (ByteSlice.cellsFrom input 0) (ByteSlice.imageView input) cells
      updates rest cells

/-- Complete local long-key execution. Native heap admission of these locals
remains an enclosing obligation; faults are retained in the executable result. -/
def run (seed : BitVec 64) (inputs : List (List (BitVec 8))) : Except Fault (BitVec 64) := do
  let cells ← init seed
  let cells ← updates inputs cells
  WyhashBuffer.run cells

theorem updates_verified (inputs : List (List (BitVec 8))) (cells : Cells) (total length : Nat)
    (invariant : Invariant cells total length)
    (sumBound : total + inputs.flatten.length < addressLimit)
    (budgets : ∀ input ∈ inputs, input.length + 48 < addressLimit) :
    ∃ after buffered, updates inputs cells = .ok after ∧
      Invariant after (total + inputs.flatten.length) buffered := by
  induction inputs generalizing cells total length with
  | nil => exact ⟨cells, length, rfl, by simpa using invariant⟩
  | cons input rest ih =>
    have size : (input :: rest).flatten.length = input.length + rest.flatten.length := by simp
    have inputBudget := budgets input (by simp)
    obtain ⟨middle, buffered, updated, middleInv⟩ := update_verified (ByteSlice.cellsFrom input 0) cells
      (ByteSlice.imageView input) (fun i => input[i]?.getD 0) (ByteSlice.array_geometry input.length)
      (ByteSlice.image_represents input) total length invariant
      (by change total + input.length < addressLimit; rw [size] at sumBound; omega) inputBudget
    obtain ⟨after, finalLength, continued, final⟩ := ih middle (total + input.length) buffered middleInv
      (by rw [size] at sumBound; omega) (fun bytes inside => budgets bytes (by simp [inside]))
    refine ⟨after, finalLength, bind_result _ _ _ _ updated continued, ?_⟩
    simpa only [size, Nat.add_assoc] using final

theorem run_verified (seed : BitVec 64) (inputs : List (List (BitVec 8)))
    (long : 16 < inputs.flatten.length) (bounded : inputs.flatten.length < addressLimit)
    (budgets : ∀ input ∈ inputs, input.length + 48 < addressLimit) :
    ∃ value, run seed inputs = .ok value := by
  obtain ⟨cells, length, updated, invariant⟩ := updates_verified inputs (initialCells (seedState seed)) 0 0
    (init_invariant seed) (by simpa using bounded) budgets
  obtain ⟨value, finished⟩ := invariant.final (by simpa using long)
  refine ⟨value, ?_⟩
  unfold run
  refine bind_result _ _ (initialCells (seedState seed)) value (init_eq seed) ?_
  exact bind_result _ _ cells value updated finished

/-- Total mathematical routing function. Its default outside the admitted
domain is never a successful native result: run_digest derives actual success
before this function can be used by the native map consumer. -/
def digest (inputs : List (List (BitVec 8))) : BitVec 64 := (run 0 inputs).toOption.getD 0

theorem run_digest (inputs : List (List (BitVec 8)))
    (long : 16 < inputs.flatten.length) (bounded : inputs.flatten.length < addressLimit)
    (budgets : ∀ input ∈ inputs, input.length + 48 < addressLimit) :
    run 0 inputs = .ok (digest inputs) := by
  obtain ⟨value, ran⟩ := run_verified 0 inputs long bounded budgets
  simp only [digest, ran, Except.toOption, Option.getD_some]

end Compiler.Extraction.WyhashHash
