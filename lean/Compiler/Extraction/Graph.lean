/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.Builder

namespace Compiler.Algebraic
open Contract.Yul

/-- Error results retain the heap actually reached. A failed second allocation
can leave a successful first allocation behind; rollback is not assumed. -/
abbrev Effect (Heap Error Result : Type) := Heap → Except Error Result × Heap

namespace Effect

def pure (value : α) : Effect Heap Error α := fun heap => (.ok value, heap)
def bind (action : Effect Heap Error α) (next : α → Effect Heap Error β) : Effect Heap Error β :=
  fun heap => match action heap with
    | (.error error, after) => (.error error, after)
    | (.ok value, after) => next value after

instance : Monad (Effect Heap Error) where
  pure := pure
  bind := bind

/-- Lift a read/arithmetic result without changing the reached heap. -/
instance : MonadLift (Except Error) (Effect Heap Error) where
  monadLift result := fun heap => (result, heap)

/-- A failed callback returns its exact error and heap without running the
continuation. Allocation failures are outcomes, never successful certificates. -/
theorem bind_failure (action : Effect Heap Error α) (next : α → Effect Heap Error β)
    (before after : Heap) (error : Error) (failed : action before = (.error error, after)) :
    bind action next before = (.error error, after) := by
  simp only [bind, failed]

/-- A successful phase supplies its returned value and reached heap to the
next phase. Keep callers abstract rather than unfolding their memory actions. -/
theorem bind_success (action : Effect Heap Error α) (next : α → Effect Heap Error β)
    (before after : Heap) (value : α) (returned : action before = (.ok value, after)) :
    bind action next before = next value after := by
  simp only [bind, returned]

/-- A successful bind reached both phases, with the first phase's actual
returned value and heap supplied to the continuation. -/
theorem bind_success_phases (action : Effect Heap Error α) (next : α → Effect Heap Error β)
    (before after : Heap) (value : β) (ran : bind action next before = (.ok value, after)) :
    ∃ first middle, action before = (.ok first, middle) ∧ next first middle = (.ok value, after) := by
  cases called : action before with
  | mk result middle =>
    cases result with
    | error fault => simp only [bind, called, Prod.mk.injEq] at ran; cases ran.1
    | ok first => exact ⟨first, middle, rfl, by simpa only [bind, called] using ran⟩

theorem bind_pure (action : Effect Heap Error α) : bind action pure = action := by
  funext before
  unfold bind
  obtain ⟨result, after⟩ := action before
  cases result <;> rfl

end Effect

/-- Observations of all existing valid IDs remain stable. This permits interning
and ID reuse for equal values, but excludes overwriting an old value. -/
def Preserves (read : Heap → NodeId → Option Word) (before after : Heap) : Prop :=
  ∀ id value, read before id = some value → read after id = some value

theorem Preserves.trans {read : Heap → NodeId → Option Word} {a b c : Heap}
    (ab : Preserves read a b) (bc : Preserves read b c) : Preserves read a c :=
  fun id value valid => bc id value (ab id value valid)

/-- Only success establishes a valid result ID and stable earlier nodes. Errors
remain explicit in Effect, with no assumption that their heap is unchanged. -/
def Ensures (read : Heap → NodeId → Option Word) (action : Effect Heap Error NodeId)
    (before : Heap) (value : Word) : Prop :=
  ∀ id after, action before = (.ok id, after) →
    Preserves read before after ∧ read after id = some value

theorem Ensures.pure {read : Heap → NodeId → Option Word} {before : Heap}
    {id : NodeId} {value : Word} (valid : read before id = some value) :
    Ensures read (pure id : Effect Heap Error NodeId) before value := by
  intro result after succeeded
  change (Except.ok id, before) = (Except.ok result, after) at succeeded
  cases succeeded
  exact ⟨fun _ _ h => h, valid⟩

theorem Ensures.bind {read : Heap → NodeId → Option Word}
    {action : Effect Heap Error NodeId} {next : NodeId → Effect Heap Error NodeId}
    {before : Heap} {a b : Word}
    (first : Ensures read action before a)
    (second : ∀ id middle, Preserves read before middle → read middle id = some a →
      Ensures read (next id) middle b) :
    Ensures read (action >>= next) before b := by
  intro result after succeeded
  change Effect.bind action next before = (.ok result, after) at succeeded
  unfold Effect.bind at succeeded
  cases step : action before with
  | mk outcome middle =>
    cases outcome with
    | error error => simp only [step] at succeeded; cases succeeded
    | ok id =>
      have intermediate := first id middle step
      have final := second id middle intermediate.1 intermediate.2 result after
        (by simpa only [step] using succeeded)
      exact ⟨intermediate.1.trans final.1, final.2⟩

/-- The native graph/interner is an explicit boundary. Its successful callbacks
must satisfy these obligations for each observation environment. Valid u32 IDs
alone do not establish valid graph references; `read` must return a value. -/
structure Builder.Valid {Heap Error Debug : Type}
    (classes : Builder (Effect Heap Error) Debug) (read : Heap → NodeId → Option Word) : Prop where
  constant : ∀ value debug before,
    Ensures read (classes.makeConstant value debug) before value
  operation : ∀ op ids values debug before value,
    ids.map (read before) = values.map some →
    op.eval values = some value →
    Ensures read (classes.makeOperation op ids debug) before value

namespace Builder.Valid

variable {Heap Error Debug : Type} {classes : Builder (Effect Heap Error) Debug}
  {read : Heap → NodeId → Option Word}

theorem bitnot (valid : classes.Valid read) (debug : Debug) (before : Heap)
    (id : NodeId) (a : Word) (ha : read before id = some a) :
    Ensures read (classes.makeOperation .NOT [id] debug) before (Unary.bitnot.eval a) :=
  valid.operation _ _ [a] _ _ _ (by simp only [List.map, ha]) rfl

theorem iszero (valid : classes.Valid read) (debug : Debug) (before : Heap)
    (id : NodeId) (a : Word) (ha : read before id = some a) :
    Ensures read (classes.makeOperation .ISZERO [id] debug) before (Unary.iszero.eval a) :=
  valid.operation _ _ [a] _ _ _ (by simp only [List.map, ha]) rfl

theorem sub (valid : classes.Valid read) (debug : Debug) (before : Heap)
    (left right : NodeId) (a b : Word)
    (ha : read before left = some a) (hb : read before right = some b) :
    Ensures read (classes.makeOperation .SUB [left, right] debug) before (Binary.sub.eval a b) :=
  valid.operation _ _ [a, b] _ _ _ (by simp only [List.map, ha, hb]) rfl

end Builder.Valid

/-- Successful replacement construction preserves old graph values and produces
a valid ID with the specified value, even if the interner reuses an old ID. -/
theorem replacement_build_sound {Heap Error Debug : Type}
    (classes : Builder (Effect Heap Error) Debug) (read : Heap → NodeId → Option Word)
    (valid : classes.Valid read) (replacement : Replacement) (before : Heap)
    (left right : NodeId) (a b : Word) (debug : Debug)
    (ha : read before left = some a) (hb : read before right = some b) :
    Ensures read (replacement.build classes left right debug) before (replacement.eval a b) := by
  cases replacement <;> simp only [Replacement.build, Replacement.eval]
  · exact Ensures.pure ha
  · exact Ensures.pure hb
  · exact valid.constant _ _ _
  · exact valid.constant _ _ _
  · exact valid.constant _ _ _
  · exact valid.bitnot _ _ _ _ hb
  · apply Ensures.bind (valid.constant 0 debug before)
    intro zero middle stable hz
    exact valid.sub _ _ _ _ _ _ hz (stable _ _ ha)
  · apply Ensures.bind (valid.constant 0 debug before)
    intro zero middle stable hz
    exact valid.sub _ _ _ _ _ _ hz (stable _ _ hb)
  · exact valid.iszero _ _ _ _ ha
  · exact valid.iszero _ _ _ _ hb
  · apply Ensures.bind (valid.iszero debug before left a ha)
    intro first middle _ hf
    exact valid.iszero _ _ _ _ hf
  · apply Ensures.bind (valid.iszero debug before right b hb)
    intro first middle _ hf
    exact valid.iszero _ _ _ _ hf

end Compiler.Algebraic
