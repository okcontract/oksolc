/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionNativeTrace
import Compiler.Extraction.InsertionExecutionAction

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

variable (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (safety : Bool)
    (allocator container : Nat) (source : View) (address : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (deterministic : Bool) (cells : List Storage.Cell) (before : World (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ))

/-- Replay supplies the interner action's exact result, reached graph and
advancing cursor from the actual native transcript. The candidate is read from
that same captured execution; its key/word contract remains separate. -/
theorem insert_replayed (mismatch : Fault) (leading trailing : List (Trace.Event Fault))
    (backing : Compiler.ZigAir.Memory.Address)
    (header : readItems before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType backing cells.length))
    (rows : before.graph.representatives = some cells) :
    let captured := recordExecution ops allocate safety allocator container source address meaning input key normalized deterministic cells before growth []
    let candidate := cell input key normalized ((key.eval meaning before.graph.read).getD 0) captured.1.2 captured.2.effects
    let replayed := Interner.InsertionExecution.action candidate key deterministic
      (Trace.replay (leading ++ captured.2.events ++ trailing) mismatch) { before.graph with allocationCursor := leading.length }
    let actual := insert ops allocate safety allocator container source address meaning input key normalized deterministic growth before
    actual.1 = replayed.1.mapError OwnedCall.Fault.language ∧
      replayed.2 = { actual.2.graph with allocationCursor := leading.length + captured.2.events.length } ∧
      actual.2.memory = memory captured.2.effects := by
  have recorded := execution_recorded ops allocate safety allocator container source address meaning input key normalized
    deterministic cells before growth mismatch [] leading trailing
  have projected := body_recorded ops allocate safety allocator container source address meaning input key normalized
    deterministic cells before growth mismatch leading trailing backing header
  dsimp only at recorded projected ⊢
  rw [insert, rows]
  simp only [Interner.InsertionExecution.action, Interner.InsertionExecution.transaction]
  rw [recorded.2.2] at projected ⊢
  rw [← recorded.1] at projected ⊢
  rw [projected.1]
  cases (recordExecution ops allocate safety allocator container source address meaning input key normalized
    deterministic cells before growth []).1.1 <;> exact ⟨rfl, rfl, rfl⟩

/-- The same action now enters the existing scoped graph lift. Insertion
advances its cursor while leaving the caller's normalization token, items and
phase intact. No independently supplied ending-cursor equation is needed. -/
theorem scoped_insert_replayed (mismatch : Fault) (leading trailing : List (Trace.Event Fault))
    (backing : Compiler.ZigAir.Memory.Address)
    (header : readItems before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType backing cells.length))
    (rows : before.graph.representatives = some cells) (scope : Interner.Scoped.Scope) :
    let captured := recordExecution ops allocate safety allocator container source address meaning input key normalized deterministic cells before growth []
    let candidate := cell input key normalized ((key.eval meaning before.graph.read).getD 0) captured.1.2 captured.2.effects
    let action := Interner.InsertionExecution.action candidate key deterministic
      (Trace.replay (leading ++ captured.2.events ++ trailing) mismatch)
    let actual := insert ops allocate safety allocator container source address meaning input key normalized deterministic growth before
    let logical := Interner.Scoped.liftGraph action ⟨scope, { before.graph with allocationCursor := leading.length }⟩
    actual.1 = logical.1.mapError OwnedCall.Fault.language ∧
      logical.2 = ⟨scope, { actual.2.graph with allocationCursor := leading.length + captured.2.events.length }⟩ ∧
      actual.2.memory = memory captured.2.effects := by
  have checked := insert_replayed ops allocate safety allocator container source address meaning input key normalized
    deterministic cells before growth mismatch leading trailing backing header rows
  exact ⟨checked.1, congrArg (fun graph => (⟨scope, graph⟩ : Interner.Scoped.Session)) checked.2.1, checked.2.2⟩

/-- The same recorded decisions now consume the existing universal word
proof. Initial semantic validity and the actual candidate's key/denotation are
local obligations; no final graph equality, preservation or allocation policy
is assumed. This semantic result does not certify native lifetimes or map buckets. -/
theorem insert_replayed_verified (mismatch : Fault) (leading trailing : List (Trace.Event Fault))
    (backing : Compiler.ZigAir.Memory.Address)
    (header : readItems before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType backing cells.length))
    (rows : before.graph.representatives = some cells) (valid : Interner.Invariant meaning before.graph)
    (outcome : Option Storage.Outcome)
    (completed : (execution ops allocate safety allocator container source address meaning input key normalized
      deterministic cells before growth).1.1 = .ok outcome) :
    let captured := recordExecution ops allocate safety allocator container source address meaning input key normalized deterministic cells before growth []
    let candidate := cell input key normalized ((key.eval meaning before.graph.read).getD 0) captured.1.2 captured.2.effects
    keyCode.run candidate.item candidate.arguments candidate.sequence = some key →
    key.eval meaning before.graph.read = some candidate.value →
    let actual := insert ops allocate safety allocator container source address meaning input key normalized deterministic growth before
    Interner.Invariant meaning actual.2.graph ∧ Interner.Stable before.graph actual.2.graph ∧
      match actual.1 with | .error _ => True | .ok id => actual.2.graph.read id = some candidate.value := by
  intro captured candidate binding denotation actual
  let calls := Trace.replay (leading ++ captured.2.events ++ trailing) mismatch
  let start := { before.graph with allocationCursor := leading.length }
  let modeled := Interner.InsertionExecution.action candidate key deterministic calls start
  have recorded := execution_recorded ops allocate safety allocator container source address meaning input key normalized
    deterministic cells before growth mismatch [] leading trailing
  have replayed : (insertProgram.execute ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩
      calls {} start.allocationCursor).1.1 = .ok outcome := by
    rw [recorded.2.2]
    exact completed
  have sound := Interner.InsertionExecution.action_verified meaning candidate key deterministic calls start cells outcome rows
    (valid.with_cursor leading.length) binding denotation replayed
  have related := insert_replayed ops allocate safety allocator container source address meaning input key normalized
    deterministic cells before growth mismatch leading trailing backing header rows
  change actual.1 = modeled.1.mapError OwnedCall.Fault.language ∧
    modeled.2 = { actual.2.graph with allocationCursor := leading.length + captured.2.events.length } ∧ _ at related
  change modeled.1 = _ ∧ Interner.Invariant meaning modeled.2 ∧ Interner.Stable start modeled.2 ∧ _ at sound
  have finalValid := sound.2.1.with_cursor actual.2.graph.allocationCursor
  rw [related.2.1] at finalValid
  refine ⟨finalValid, ?_, ?_⟩
  · intro id value found
    have retained := sound.2.2.1 id value found
    rw [related.2.1] at retained
    exact retained
  · rw [related.1]
    have word := sound.2.2.2
    rw [related.2.1] at word
    change (match modeled.1 with | .error _ => True | .ok id => actual.2.graph.read id = some candidate.value) at word
    cases selected : modeled.1 with
    | error _ => trivial
    | ok _ => simpa only [selected] using word

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
