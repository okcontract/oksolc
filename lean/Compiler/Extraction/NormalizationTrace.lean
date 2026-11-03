/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationPreparedTransport

namespace Compiler.Extraction.Cache.NormalizationOwnership.Trace

/-- Invocation-local protocol calls, in actual order. An empty duplication
may skip the native allocator inside its callback. Preparation retains semantic
failure, distinct from the Boolean ordinary-allocation response. Descriptors
belong to this invocation; these events alone do not bind a native trace. -/
inductive Event (ε : Type) where
  | allocate (site : Allocation) (succeeded : Bool)
  | prepare (lookup : State) (result : Except ε Unit)
  | release (lookup : State)
  /-- Another protocol occupies this cursor. A projected view retains the slot
  and rejects it; normalization recorders never emit this constructor. -/
  | foreign
  deriving Repr

structure Recorded (σ ε : Type) where
  effects : σ
  events : List (Event ε) := []

def record (p : PreparedPrimitives σ ε) : PreparedPrimitives (Recorded σ ε) ε := {
  allocate := fun site before =>
    let (result, after) := p.allocate site before.effects
    (result, ⟨after, before.events ++ [.allocate site result]⟩)
  prepare := fun lookup before =>
    let (result, after) := p.prepare lookup before.effects
    (result, ⟨after, before.events ++ [.prepare lookup result]⟩)
  release := fun lookup before =>
    ⟨p.release lookup before.effects, before.events ++ [.release lookup]⟩ }

theorem record_transport (p : PreparedPrimitives σ ε) : Transport (record p) p Recorded.effects := by
  constructor <;> intros <;> rfl

def prepend (events : List (Event ε)) (before : Recorded σ ε) : Recorded σ ε :=
  { before with events := events ++ before.events }

theorem prefix_transport (p : PreparedPrimitives σ ε) (events : List (Event ε)) :
    Transport (record p) (record p) (prepend events) := by
  constructor <;> intros <;> simp [record, prepend, List.append_assoc]

/-- Recording cannot change primitive outcomes, allocation/copy effects or
cleanup. The original private state remains available without encoding it. -/
theorem record_erases (code : Code) (p : PreparedPrimitives σ ε) (commutative : Bool)
    (length bufferLength : Nat) (exit : Exit) (before : σ) :
    code.runPrepared commutative length bufferLength p exit before =
      ((code.runPrepared commutative length bufferLength (record p) exit ⟨before, []⟩).1,
       (code.runPrepared commutative length bufferLength (record p) exit ⟨before, []⟩).2.effects) :=
  run_prepared_transport code (record p) p Recorded.effects (record_transport p) commutative length bufferLength exit ⟨before, []⟩

/-- The first cursor past the trace is exhausted, and the next is an absorbing
mismatch sentinel. Neither is a memory address or a physical lifetime ID. -/
def rejected (events : List (Event ε)) : Nat := events.length + 1

def allocate (events : List (Event ε)) (site : Allocation) (cursor : Nat) : Bool × Nat :=
  match events[cursor]? with
  | some (.allocate expected result) =>
    if expected = site then (result, cursor + 1) else (false, rejected events)
  | _ => (false, rejected events)

def prepare (events : List (Event ε)) (mismatch : ε) (lookup : State) (cursor : Nat) : Except ε Unit × Nat :=
  match events[cursor]? with
  | some (.prepare expected result) =>
    if expected = lookup then (result, cursor + 1) else (.error mismatch, rejected events)
  | _ => (.error mismatch, rejected events)

def release (events : List (Event ε)) (lookup : State) (cursor : Nat) : Nat :=
  match events[cursor]? with
  | some (.release expected) => if expected = lookup then cursor + 1 else rejected events
  | _ => rejected events

def replay (events : List (Event ε)) (mismatch : ε) : PreparedPrimitives Nat ε := {
  allocate := allocate events
  prepare := prepare events mismatch
  release := release events }

/-- Once a callback mismatch poisons the cursor, later callbacks cannot
restore acceptance by treating the mismatch as ordinary OOM or cleanup. -/
theorem rejected_absorbs (events : List (Event ε)) (mismatch : ε) (site : Allocation) (lookup : State) :
    allocate events site (rejected events) = (false, rejected events) ∧
    prepare events mismatch lookup (rejected events) = (.error mismatch, rejected events) ∧
    release events lookup (rejected events) = rejected events := by
  have absent : events[rejected events]? = none := by
    apply List.getElem?_eq_none
    simp [rejected]
  simp [allocate, prepare, release, absent]

/-- Replaying at an invocation's position in a larger trace gives the same
results and advances the same relative cursor. No state serialization is used. -/
theorem replay_prefix (events leading : List (Event ε)) (mismatch : ε) :
    Transport (replay events mismatch) (replay (leading ++ events) mismatch) (fun cursor => leading.length + cursor) := by
  have index (cursor : Nat) : (leading ++ events)[leading.length + cursor]? = events[cursor]? := by
    rw [List.getElem?_append_right (by omega)]
    simp
  constructor
  · intro site cursor
    simp only [replay, allocate, index]
    cases events[cursor]? with
    | none => simp [rejected, Nat.add_assoc]
    | some event =>
      cases event <;> simp [rejected, Nat.add_assoc]
      split <;> simp_all
  · intro lookup cursor
    simp only [replay, release, index]
    cases events[cursor]? with
    | none => simp [rejected, Nat.add_assoc]
    | some event =>
      cases event <;> simp [rejected, Nat.add_assoc]
      split <;> simp_all
  · intro lookup cursor
    simp only [replay, prepare, index]
    cases events[cursor]? with
    | none => simp [rejected, Nat.add_assoc]
    | some event =>
      cases event <;> simp [rejected, Nat.add_assoc]
      split <;> simp_all

end Compiler.Extraction.Cache.NormalizationOwnership.Trace
