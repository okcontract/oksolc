/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryFill

/-! Unbounded functional correctness for the initialized loop in captured
`fill`. The allocator prologue and invocation cleanup are separate obligations.
The theorem includes every checked heap failure, with its partial effects. -/
namespace Compiler.ZigAir.MemoryFill
open Memory MemoryAir Control.Machine

def loopFrames (outer : List (Frame Ty Prim Ref)) : List (Frame Ty Prim Ref) :=
  .loop 9 body :: .block 8 (.scalar .unit) (.ret unitRef) :: outer

def loopConfig (env : Env) (state : State) (outer : List (Frame Ty Prim Ref)) :
    Config Ty Prim Ref Value State := ⟨body, env, state, loopFrames outer⟩

def outcome : Except Fault Unit × State → Control.Outcome Value Fault State
  | (.error fault, after) => .fault fault after
  | (.ok (), after) => .returned (.scalar .unit) after

theorem body_steps (args : List Value) (env : Env) (state : State) (outer : List (Frame Ty Prim Ref)) :
    Steps semantics args (.suspended (loopConfig env state outer))
      (continueOutcome semantics (head.eval semantics args env state)
        (.block 10 (.scalar .unit) (.repeat rfl 9) :: loopFrames outer)) := by
  apply Steps.step
  exact finite_steps semantics args head env state _

theorem body_fault (args : List Value) (env : Env) (state after : State) (outer : List (Frame Ty Prim Ref))
    (fault : Fault) (evaluated : head.eval semantics args env state = .fault fault after) :
    Steps semantics args (.suspended (loopConfig env state outer)) (.finished (.fault fault after)) := by
  have path := body_steps args env state outer
  rw [evaluated] at path
  exact path

theorem body_next (args : List Value) (env nextEnv : Env) (state after : State)
    (outer : List (Frame Ty Prim Ref))
    (evaluated : head.eval semantics args env state = .jumped 10 (.scalar .unit) nextEnv after) :
    Steps semantics args (.suspended (loopConfig env state outer))
      (.suspended (loopConfig (nextEnv.set 10 (.scalar .unit)) after outer)) := by
  have path := body_steps args env state outer
  rw [evaluated] at path
  apply path.trans semantics args
  exact .step _ (.refl _)

theorem body_stop (args : List Value) (env nextEnv : Env) (state : State)
    (outer : List (Frame Ty Prim Ref))
    (evaluated : head.eval semantics args env state = .jumped 8 (.scalar .unit) nextEnv state) :
    Steps semantics args (.suspended (loopConfig env state outer))
      (.finished (.returned (.scalar .unit) state)) := by
  have path := body_steps args env state outer
  rw [evaluated] at path
  apply path.trans semantics args
  exact .step _ (.refl _)

theorem Matches.fault_eq {length : Nat} {value : Scalar.Value} {pointerSlot indexSlot : Address}
    {reason : Fault} {after : State} {observed : Control.Outcome Value Fault State}
    (matched : Matches length value pointerSlot indexSlot (.error reason, after) observed) :
    observed = .fault reason after := by cases matched; rfl

theorem Matches.next_exists {length : Nat} {value : Scalar.Value} {pointerSlot indexSlot : Address}
    {after : State} {observed : Control.Outcome Value Fault State}
    (matched : Matches length value pointerSlot indexSlot (.ok (), after) observed) :
    ∃ env, observed = .jumped 10 (.scalar .unit) env after ∧ Locals env length value pointerSlot indexSlot := by
  cases matched with | next env _ locals => exact ⟨env, rfl, locals⟩

/-- For any number of remaining elements, the actual captured loop reaches the
ordered checked fill specification. Neither sufficient fuel nor a successful
whole-run premise is assumed. Only initialized, separate scratch slots and
valid scalar inputs are required; buffer accesses can fail. -/
theorem loop_effects (remaining index length : Nat) (args : List Value) (env : Env) (state : State)
    (value : Scalar.Value) (address pointerSlot indexSlot : Address) (outer : List (Frame Ty Prim Ref))
    (locals : Locals env length value pointerSlot indexSlot)
    (bound : length < addressLimit) (count : length = index + remaining)
    (typed : (Value.scalar value).hasType word = true)
    (readIndex : load state (counter indexSlot) = .ok (size index))
    (readPointer : load state (saved pointerSlot) = .ok (buffer address))
    (indexApart : indexSlot.allocation ≠ address.allocation)
    (pointerApart : pointerSlot.allocation ≠ address.allocation)
    (slotsApart : pointerSlot.allocation ≠ indexSlot.allocation) :
    Steps semantics args (.suspended (loopConfig env state outer))
      (.finished (outcome (effects address indexSlot value remaining index state))) := by
  induction remaining generalizing index env state with
  | zero =>
    obtain ⟨nextEnv, stopped⟩ := head_stop args env state length index value pointerSlot indexSlot
      locals (by omega) bound (by omega) readIndex
    exact body_stop args env nextEnv state outer stopped
  | succ remaining ih =>
    have matched := head_continue args env state length index value address pointerSlot indexSlot
      locals bound (by omega) typed readIndex readPointer indexApart
    cases h : step state address indexSlot index value with
    | mk result after =>
      rw [h] at matched
      cases result with
      | error reason =>
        simp only [effects, h, outcome]
        exact body_fault args env state after outer reason matched.fault_eq
      | ok done =>
        cases done
        obtain ⟨nextEnv, evaluated, nextLocals⟩ := matched.next_exists
        have reads := step_reads state after address pointerSlot indexSlot index value h
          readPointer pointerApart slotsApart
        have live : Locals (nextEnv.set 10 (.scalar .unit)) length value pointerSlot indexSlot := by
          simpa [Locals, Control.Env.set] using nextLocals
        simp only [effects, h]
        exact (body_next args env nextEnv state after outer evaluated).trans semantics args
          (ih (index + 1) _ after live (by omega) reads.1 reads.2)

/-- Entry to the actual captured loop, after its scratch-slot prologue. The
shape equality below certifies extraction; the fallback is never admitted. -/
def entry (env : Env) (state : State) (outer : List (Frame Ty Prim Ref)) :
    Config Ty Prim Ref Value State :=
  ⟨(GeneratedMemory.fn_fill.body.block? 8).getD (.ret unitRef), env, state, outer⟩

theorem entry_shape (env : Env) (state : State) (outer : List (Frame Ty Prim Ref)) :
    entry env state outer =
      ⟨.block 8 (.scalar .unit) (.loop rfl 9 body) (.ret unitRef), env, state, outer⟩ := by rfl

theorem initialized_fill_steps (length : Nat) (args : List Value) (env : Env) (state : State)
    (value : Scalar.Value) (address pointerSlot indexSlot : Address) (outer : List (Frame Ty Prim Ref))
    (locals : Locals env length value pointerSlot indexSlot)
    (bound : length < addressLimit) (typed : (Value.scalar value).hasType word = true)
    (readIndex : load state (counter indexSlot) = .ok (size 0))
    (readPointer : load state (saved pointerSlot) = .ok (buffer address))
    (indexApart : indexSlot.allocation ≠ address.allocation)
    (pointerApart : pointerSlot.allocation ≠ address.allocation)
    (slotsApart : pointerSlot.allocation ≠ indexSlot.allocation) :
    Steps semantics args (.suspended (entry env state outer))
      (.finished (outcome (effects address indexSlot value length 0 state))) := by
  rw [entry_shape]
  apply Steps.step
  apply Steps.step
  exact loop_effects length 0 length args env state value address pointerSlot indexSlot outer
    locals bound (by omega) typed readIndex readPointer indexApart pointerApart slotsApart

/-- There exists sufficient fuel for every admitted initialized fill, including
buffer faults. This is termination, not an assumption that a run has finished. -/
theorem initialized_fill_terminates (length : Nat) (args : List Value) (env : Env) (state : State)
    (value : Scalar.Value) (address pointerSlot indexSlot : Address) (outer : List (Frame Ty Prim Ref))
    (locals : Locals env length value pointerSlot indexSlot)
    (bound : length < addressLimit) (typed : (Value.scalar value).hasType word = true)
    (readIndex : load state (counter indexSlot) = .ok (size 0))
    (readPointer : load state (saved pointerSlot) = .ok (buffer address))
    (indexApart : indexSlot.allocation ≠ address.allocation)
    (pointerApart : pointerSlot.allocation ≠ address.allocation)
    (slotsApart : pointerSlot.allocation ≠ indexSlot.allocation) :
    ∃ fuel, run semantics args fuel (entry env state outer) =
      .finished (outcome (effects address indexSlot value length 0 state)) := by
  exact (steps_iff_fuel semantics args _ _).mp
    (initialized_fill_steps length args env state value address pointerSlot indexSlot outer
      locals bound typed readIndex readPointer indexApart pointerApart slotsApart)

/-- Every terminal fuel/resumption observation agrees with the fill effects;
the preceding theorem separately establishes existence of that terminal run. -/
theorem initialized_fill_result (length : Nat) (args : List Value) (env : Env) (state : State)
    (value : Scalar.Value) (address pointerSlot indexSlot : Address) (outer : List (Frame Ty Prim Ref))
    (locals : Locals env length value pointerSlot indexSlot)
    (bound : length < addressLimit) (typed : (Value.scalar value).hasType word = true)
    (readIndex : load state (counter indexSlot) = .ok (size 0))
    (readPointer : load state (saved pointerSlot) = .ok (buffer address))
    (indexApart : indexSlot.allocation ≠ address.allocation)
    (pointerApart : pointerSlot.allocation ≠ address.allocation)
    (slotsApart : pointerSlot.allocation ≠ indexSlot.allocation)
    (observed : Control.Outcome Value Fault State)
    (path : Steps semantics args (.suspended (entry env state outer)) (.finished observed)) :
    observed = outcome (effects address indexSlot value length 0 state) := by
  exact finished_unique semantics args _ _ _ path
    (initialized_fill_steps length args env state value address pointerSlot indexSlot outer
      locals bound typed readIndex readPointer indexApart pointerApart slotsApart)

end Compiler.ZigAir.MemoryFill
