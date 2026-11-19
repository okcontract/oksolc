/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionCandidateIdentity
import Compiler.Extraction.InternerInsertionNativeReplay
import Compiler.Extraction.InternerNativeFrames

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- One insertion model for a fixed stream and allocation identity. The input
heap supplies the key's denotation; no native execution or returned cell is
consulted when constructing this action. -/
def allocationReplay (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (meaning : Meaning) (deterministic : Bool) (nextId : Nat) (stream : List (Trace.Event Fault))
    (mismatch : Fault) : Interner.Action NodeId := fun before =>
  Interner.InsertionExecution.action
    (allocationCandidate input key normalized ((key.eval meaning before.read).getD 0) deterministic nextId)
    key deterministic (Trace.replay stream mismatch) before

variable (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (safety : Bool)
    (allocator container : Nat) (source : View) (address : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (deterministic : Bool) (cells : List Storage.Cell) (before : World (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ))

/-- Replay the actual native insertion with a candidate computed before
execution from its source inputs and allocation cursor. Success derives exact
candidate identities; ordinary failure uses the shared candidate-irrelevance
proof. Full event replay still supplies the allocation/publication decisions. -/
theorem insert_allocation_replayed (mismatch : Fault) (leading trailing : List (Trace.Event Fault))
    (backing : Compiler.ZigAir.Memory.Address)
    (header : readItems before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType backing cells.length))
    (rows : before.graph.representatives = some cells)
    (initial : Valid before.memory) (live : Memory.SliceValid allocator before.memory.heap normalized)
    (represented : AssemblyClone.NativeFields.Represents before.memory.memory address input)
    (admitted : Admitted ops.arguments) :
    let captured := recordExecution ops allocate safety allocator container source address meaning input key normalized deterministic cells before growth []
    let candidate := allocationCandidate input key normalized ((key.eval meaning before.graph.read).getD 0)
      deterministic before.memory.memory.nextId
    let replayed := Interner.InsertionExecution.action candidate key deterministic
      (Trace.replay (leading ++ captured.2.events ++ trailing) mismatch) { before.graph with allocationCursor := leading.length }
    let actual := insert ops allocate safety allocator container source address meaning input key normalized deterministic growth before
    ordinary actual.1 = true →
      actual.1 = replayed.1.mapError OwnedCall.Fault.language ∧
      replayed.2 = { actual.2.graph with allocationCursor := leading.length + captured.2.events.length } ∧
      actual.2.memory = memory captured.2.effects := by
  intro captured candidate replayed actual ordinaryResult
  have recorded := execution_recorded ops allocate safety allocator container source address meaning input key normalized
    deterministic cells before growth mismatch [] leading trailing
  have checked := checkedExecution_read ops allocate safety allocator container source address meaning input key normalized
    deterministic cells before growth backing header
  have original := insert_replayed ops allocate safety allocator container source address meaning input key normalized
    deterministic cells before growth mismatch leading trailing backing header rows
  let native := execution ops allocate safety allocator container source address meaning input key normalized deterministic cells before growth
  obtain ⟨outcome, completed⟩ : ∃ outcome, native.1.1 = .ok outcome := by
    cases ran : native with
    | mk result reached =>
      obtain ⟨result, owner⟩ := result
      cases result with
      | error fault =>
        have nativeEq : execution ops allocate safety allocator container source address meaning input key normalized
            deterministic cells before growth = ((.error fault, owner), reached) := ran
        change ordinary (insert ops allocate safety allocator container source address meaning input key normalized deterministic growth before).1 = true at ordinaryResult
        simp only [insert, rows, body, checked, nativeEq, ordinary, OwnedCall.Fault.recoverable, Bool.false_eq_true] at ordinaryResult
      | ok outcome => exact ⟨outcome, rfl⟩
  have safe := (Storage.insert_execution_safe
    ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩
    (observedCalls ops allocate safety allocator container source address meaning input key normalized cells before growth)
    (observedStart before) outcome (by simpa only [execution_observed] using completed)).1
  have capturedEq : (captured.1, captured.2.effects) = native := recorded.1
  have ownerEq : captured.1.2 = native.1.2 := congrArg (fun ran => ran.1.2) capturedEq
  change Storage.SafeResult deterministic (outcome, native.1.2) at safe
  rw [← ownerEq] at safe
  have candidateEq : Interner.InsertionExecution.project cells before.graph.table
      (cell input key normalized ((key.eval meaning before.graph.read).getD 0) captured.1.2 captured.2.effects) key captured.1.2 =
      Interner.InsertionExecution.project cells before.graph.table candidate key captured.1.2 := by
    apply Interner.InsertionExecution.project_candidate cells before.graph.table _ candidate key deterministic outcome captured.1.2
      safe
    intro success
    have actual := execution_allocation_candidate ops allocate safety allocator container source address meaning input key normalized
      deterministic cells before growth initial live represented admitted (success ▸ completed)
    change cell input key normalized ((key.eval meaning before.graph.read).getD 0) native.1.2 native.2 = candidate at actual
    rw [← capturedEq] at actual
    exact actual
  have same : Interner.InsertionExecution.action
      (cell input key normalized ((key.eval meaning before.graph.read).getD 0) captured.1.2 captured.2.effects) key deterministic
      (Trace.replay (leading ++ captured.2.events ++ trailing) mismatch) { before.graph with allocationCursor := leading.length } = replayed := by
    dsimp only [replayed, Interner.InsertionExecution.action]
    rw [rows]
    dsimp only [Interner.InsertionExecution.transaction]
    rw [recorded.2.2]
    dsimp only
    have ownerActual : (execution ops allocate safety allocator container source address meaning input key normalized
        deterministic cells before growth).1.2 = captured.1.2 := ownerEq.symm
    rw [ownerActual, candidateEq]
  change actual.1 = (Interner.InsertionExecution.action
      (cell input key normalized ((key.eval meaning before.graph.read).getD 0) captured.1.2 captured.2.effects) key deterministic
      (Trace.replay (leading ++ captured.2.events ++ trailing) mismatch) { before.graph with allocationCursor := leading.length }).1.mapError OwnedCall.Fault.language ∧
    (Interner.InsertionExecution.action
      (cell input key normalized ((key.eval meaning before.graph.read).getD 0) captured.1.2 captured.2.effects) key deterministic
      (Trace.replay (leading ++ captured.2.events ++ trailing) mismatch) { before.graph with allocationCursor := leading.length }).2 =
      { actual.2.graph with allocationCursor := leading.length + captured.2.events.length } ∧
    actual.2.memory = memory captured.2.effects at original
  rw [same] at original
  exact original

/-- A captured prefix in one fixed stream suffices for replay. The suffix is
derived from admission, and the model uses only the reached allocation identity
and observed input heap. Success and ordinary allocation/capacity failure share
this result; malformed native execution remains outside ordinary completion. -/
theorem insert_allocation_stream (mismatch : Fault) (leading stream : List (Trace.Event Fault))
    (backing : Compiler.ZigAir.Memory.Address)
    (header : readItems before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType backing cells.length))
    (rows : before.graph.representatives = some cells)
    (initial : Valid before.memory) (live : Memory.SliceValid allocator before.memory.heap normalized)
    (represented : AssemblyClone.NativeFields.Represents before.memory.memory address input)
    (admitted : Admitted ops.arguments)
    (inside : leading ++ (recordExecution ops allocate safety allocator container source address meaning input key normalized
      deterministic cells before growth []).2.events <+: stream) :
    let captured := recordExecution ops allocate safety allocator container source address meaning input key normalized deterministic cells before growth []
    let actual := insert ops allocate safety allocator container source address meaning input key normalized deterministic growth before
    let logical := allocationReplay input key normalized meaning deterministic before.memory.memory.nextId stream mismatch
      { before.graph with allocationCursor := leading.length }
    ordinary actual.1 = true →
      (actual.1, { actual.2.graph with allocationCursor := leading.length + captured.2.events.length }) =
        (logical.1.mapError OwnedCall.Fault.language, logical.2) := by
  obtain ⟨trailing, rfl⟩ := inside
  intro captured actual logical completed
  have related := insert_allocation_replayed ops allocate safety allocator container source address meaning input key normalized
    deterministic cells before growth mismatch leading trailing backing header rows initial live represented admitted completed
  exact Prod.ext related.1 related.2.1.symm

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Insertion.Native

/-- The existing live caller frame supplies native insertion inputs. Its
resource stream and entry allocation identity are the only remaining replay
bindings; no candidate correspondence or final graph equality is assumed. -/
theorem CallFrame.allocation_insert_stream
    {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {input : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {before : World (Publication.Effects σ)}
    (frame : CallFrame safety allocator owner rows source values normalized address input parent before)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning) (key : Key) (deterministic : Bool)
    (mismatch : Insertion.Native.Fault) (leading stream : List (Trace.Event Insertion.Native.Fault))
    (admitted : Admitted ops.arguments)
    (inside : leading ++ (recordExecution ops allocate safety allocator owner source address meaning input key normalized
      deterministic (before.graph.representatives.getD []) before growth []).2.events <+: stream) :
    let captured := recordExecution ops allocate safety allocator owner source address meaning input key normalized
      deterministic (before.graph.representatives.getD []) before growth []
    let actual := insert ops allocate safety allocator owner source address meaning input key normalized deterministic growth before
    let logical := allocationReplay input key normalized meaning deterministic before.memory.memory.nextId stream mismatch
      { before.graph with allocationCursor := leading.length }
    ordinary actual.1 = true →
      (actual.1, { actual.2.graph with allocationCursor := leading.length + captured.2.events.length }) =
        (logical.1.mapError Fault.language, logical.2) := by
  obtain ⟨added, data, capacity, facts, _, _⟩ := frame.1.1
  have exactRows : before.graph.representatives = some (before.graph.representatives.getD []) := by
    rw [facts.projected]; rfl
  exact insert_allocation_stream ops allocate safety allocator owner source address meaning input key normalized
    deterministic (before.graph.representatives.getD []) before growth mismatch leading stream data
    (by simpa only [facts.projected, Option.getD_some] using readHeader_items _ _ _ _ facts.header)
    exactRows facts.valid frame.1.2.2.1 frame.2.1 admitted inside

/-- Equal observed inputs and allocation identities determine one insertion
result and observed graph on a fixed admitted stream. Native private effects
may differ. This is the insertion portion of uniform body replay, not a claim
that the complete recursive constructor or its admission has been derived. -/
theorem CallFrame.allocation_insert_agrees
    {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {input : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {left right : World (Publication.Effects σ)}
    (one : CallFrame safety allocator owner rows source values normalized address input parent left)
    (two : CallFrame safety allocator owner rows source values normalized address input parent right)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning) (key : Key) (deterministic : Bool)
    (mismatch : Insertion.Native.Fault) (leading stream : List (Trace.Event Insertion.Native.Fault))
    (admitted : Admitted ops.arguments)
    (identity : left.memory.memory.nextId = right.memory.memory.nextId)
    (same : { left.graph with allocationCursor := leading.length } = { right.graph with allocationCursor := leading.length })
    (insideLeft : leading ++ (recordExecution ops allocate safety allocator owner source address meaning input key normalized
      deterministic (left.graph.representatives.getD []) left growth []).2.events <+: stream)
    (insideRight : leading ++ (recordExecution ops allocate safety allocator owner source address meaning input key normalized
      deterministic (right.graph.representatives.getD []) right growth []).2.events <+: stream) :
    let leftCapture := recordExecution ops allocate safety allocator owner source address meaning input key normalized
      deterministic (left.graph.representatives.getD []) left growth []
    let rightCapture := recordExecution ops allocate safety allocator owner source address meaning input key normalized
      deterministic (right.graph.representatives.getD []) right growth []
    let first := insert ops allocate safety allocator owner source address meaning input key normalized deterministic growth left
    let second := insert ops allocate safety allocator owner source address meaning input key normalized deterministic growth right
    ordinary first.1 = true → ordinary second.1 = true →
      (first.1, { first.2.graph with allocationCursor := leading.length + leftCapture.2.events.length }) =
        (second.1, { second.2.graph with allocationCursor := leading.length + rightCapture.2.events.length }) := by
  intro leftCapture rightCapture first second firstDone secondDone
  have firstSame := one.allocation_insert_stream ops allocate growth meaning key deterministic mismatch leading stream admitted insideLeft firstDone
  have secondSame := two.allocation_insert_stream ops allocate growth meaning key deterministic mismatch leading stream admitted insideRight secondDone
  dsimp only at firstSame secondSame
  rw [identity, same] at firstSame
  exact firstSame.trans secondSame.symm

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
