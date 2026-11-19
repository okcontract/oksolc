/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryWordSwapPrologue

/-! Complete captured u32 swap over distinct elements of an initialized writable
array view. Allocation exhaustion is explicit. Successful execution swaps the
words, removes the private counter and retains all other caller memory. These
typed-heap results do not establish Zig/LLVM or generic-specialization
preservation, nor all inputs of the broader word-pair entry contract. -/
namespace Compiler.ZigAir.MemoryWordSwap
open Memory MemoryAir Control.Machine GeneratedMemory
open Memory.WordArray (View Writable Represents Frame word)

theorem accepts (caller : State) (view : View) (left right : Nat) (initial : caller.valid = true) :
    fn_swap_u32.program.accepts (arguments view left right) caller = true := by
  have parameters : fn_swap_u32.program.parameters = [.pointer true false word, .pointer true false word] := rfl
  simp only [Program.accepts, initial, parameters, arguments, List.length_cons, List.length_nil,
    Nat.reduceAdd, List.zip_cons_cons, List.zip_nil_left, List.all_cons, List.all_nil]
  rfl

theorem finish_counter (caller after : State) (base : Nat) (initial : after.valid = true)
    (same : after.nextId = caller.nextId) :
    cleanup caller.nextId (withCounter base 4 after) = ⟨after.heap, caller.nextId + 1, base + 8⟩ := by
  have heap := counter_cleanup base 4 after initial
  rw [same] at heap
  change (⟨(cleanup caller.nextId (withCounter base 4 after)).heap, after.nextId + 1, base + 8⟩ : State) = _
  rw [heap, same]

/-- A complete terminal run exists for every admitted view. There are no fuel,
termination, allocation-success or intermediate memory-success premises. -/
theorem swap_refines (caller : State) (view : View) (items : List (BitVec 32)) (left right : Nat)
    (initial : caller.valid = true) (cap : Writable caller view) (represented : Represents caller view items)
    (hl : left < items.length) (hr : right < items.length) (apart : left ≠ right) :
    ∃ fuel result after, fn_swap_u32.runFuel fuel (arguments view left right) caller = .finished result after ∧
      after.valid = true ∧
      ((result = .error .outOfMemory ∧ after = caller) ∨ ∃ base direct,
        result = .ok (.scalar .unit) ∧ after = ⟨direct.heap, caller.nextId + 1, base + 8⟩ ∧
        direct.valid = true ∧ Writable after view ∧
        Represents after view ((items.set left items[right]).set right items[left]) ∧ Frame view caller direct) := by
  obtain ⟨outcome, steps, result⟩ := body_steps caller view items left right initial cap represented hl hr apart
  obtain ⟨fuel, ran⟩ := (steps_iff_fuel semantics (arguments view left right) _ _).mp steps
  change run semantics (arguments view left right) fuel ⟨fn_swap_u32.program.body, fun _ => none, caller, []⟩ =
    .finished outcome at ran
  have checked := WordPair.validate_view caller view items left right initial cap represented hl hr apart
  change WordPair.validate caller (arguments view left right) = .ok () at checked
  have finished : fn_swap_u32.runFuel fuel (arguments view left right) caller =
      Invocation.finish (.scalar .unit) caller.nextId outcome := by
    rw [WordPairProgram.accepted_run _ _ _ _ checked]
    simp only [Program.runFuel, Program.start, accepts caller view left right initial, ↓reduceIte, Invocation.resume]
    change (match run semantics (arguments view left right) fuel ⟨fn_swap_u32.program.body, fun _ => none, caller, []⟩ with
      | .finished value => Invocation.finish (.scalar .unit) caller.nextId value
      | .suspended next => .suspended (.scalar .unit) caller.nextId (arguments view left right) next) = _
    rw [ran]
  rcases result with fault | ⟨base, direct, success, valid, live, writable, rep, frame⟩
  · rw [fault] at finished
    have cleanup := cleanup_initial caller initial
    refine ⟨fuel, .error .outOfMemory, caller, ?_, initial, Or.inl ⟨rfl, rfl⟩⟩
    simpa only [Invocation.finish, Program.finish, cleanup] using finished
  · rw [success] at finished
    let after : State := ⟨direct.heap, caller.nextId + 1, base + 8⟩
    have cleaned := finish_counter caller direct base valid frame.nextId
    have afterValid : after.valid = true := by
      dsimp only [after]
      rw [← cleaned]
      exact cleanup_preserves_valid caller.nextId (withCounter base 4 direct) live
    refine ⟨fuel, .ok (.scalar .unit), after, ?_, afterValid, Or.inr ⟨base, direct, rfl, rfl, valid,
      WordArray.writable_heap_eq direct after view rfl writable,
      WordArray.represents_heap_eq direct after view _ rfl rep, frame⟩⟩
    simpa only [Invocation.finish, Program.finish, show (Value.scalar .unit).hasType (.scalar .unit) = true from rfl,
      ↓reduceIte, cleaned] using finished

end Compiler.ZigAir.MemoryWordSwap
