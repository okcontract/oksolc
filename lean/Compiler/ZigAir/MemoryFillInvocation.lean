/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryFillPrologue
import Compiler.ZigAir.MemoryExecutionProofs

/-! Whole-invocation refinement for the captured fill fixture, including its
allocation prologue, checked fault prefixes and cleanup at the original mark.
The incoming buffer lifetime predates the invocation. Native source validity,
the decoder and Zig backend remain separate obligations. -/
namespace Compiler.ZigAir.MemoryFill
open Memory MemoryAir Control.Machine GeneratedMemory

def specification (length : Nat) (value : Scalar.Value) (address : Address) (state : State) :
    Except Fault Value × State :=
  Program.finish (.scalar .unit) state.nextId (preparedOutcome length value address (prepare state address))

theorem fill_accepts (length : Nat) (value : Scalar.Value) (address : Address) (state : State)
    (initial : state.valid = true) (bound : length < addressLimit)
    (typed : (Value.scalar value).hasType word = true) :
    fn_fill.accepts (arguments length value address) state = true := by
  have parameters : fn_fill.parameters = [.pointer true true word, usize, word] := rfl
  simp only [Program.accepts, parameters, arguments, List.length_cons, List.length_nil,
    Nat.reduceAdd, List.zip_cons_cons, List.zip_nil_left, List.all_cons, List.all_nil,
    initial, size_typed length bound, typed]
  rfl

/-- A complete invocation reaches the checked specification for every admitted
input, including allocation exhaustion and buffer faults. No success or fuel
premise is required, and the scratch-slot assumptions are now discharged. -/
theorem fill_terminates (length : Nat) (value : Scalar.Value) (address : Address) (state : State)
    (initial : state.valid = true) (bound : length < addressLimit)
    (typed : (Value.scalar value).hasType word = true) (older : address.allocation < state.nextId) :
    ∃ fuel, fn_fill.runFuel fuel (arguments length value address) state =
      .finished (specification length value address state).1 (specification length value address state).2 := by
  obtain ⟨fuel, done⟩ := (steps_iff_fuel semantics (arguments length value address) _ _).mp
    (fill_body_steps length value address state bound typed older)
  refine ⟨fuel, ?_⟩
  simp only [Program.runFuel, Program.start, fill_accepts length value address state initial bound typed,
    ↓reduceIte, Invocation.resume]
  change (match run semantics (arguments length value address) fuel ⟨fn_fill.body, fun _ => none, state, []⟩ with
    | .finished result => Invocation.finish fn_fill.returnType state.nextId result
    | .suspended next => .suspended fn_fill.returnType state.nextId (arguments length value address) next) = _
  rw [show run semantics (arguments length value address) fuel ⟨fn_fill.body, fun _ => none, state, []⟩ =
    .finished (preparedOutcome length value address (prepare state address)) from done]
  rfl

theorem fill_result (length : Nat) (value : Scalar.Value) (address : Address) (state : State)
    (initial : state.valid = true) (bound : length < addressLimit)
    (typed : (Value.scalar value).hasType word = true) (older : address.allocation < state.nextId)
    (fuel : Nat) (result : Except Fault Value) (after : State)
    (observed : fn_fill.runFuel fuel (arguments length value address) state = .finished result after) :
    (result, after) = specification length value address state := by
  obtain ⟨budget, expected⟩ := fill_terminates length value address state initial bound typed older
  exact Invocation.finished_unique (fn_fill.start (arguments length value address) state) fuel budget
    result (specification length value address state).1 after (specification length value address state).2
    observed expected

theorem specification_cleanup (length : Nat) (value : Scalar.Value) (address : Address) (state : State) :
    (specification length value address state).2 =
      cleanup state.nextId (preparedOutcome length value address (prepare state address)).state := by
  unfold specification
  cases preparedOutcome length value address (prepare state address) <;> rfl

end Compiler.ZigAir.MemoryFill
