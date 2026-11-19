/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.StorageExecutionEffects
import Compiler.Extraction.InternerItemPreparationEffects
import Compiler.Extraction.InternerInsertionNativeBody

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

namespace Native

/-- Compiler obligations still open after deriving item/clone transport. Each
equation is for a local callback at its reached frame, including faults; none
assumes the enclosing insertion result or its final memory/graph projection. -/
structure PendingTransport (physical : Storage.Operations (Frame σ) Fault)
    (original : Storage.Operations (Frame τ) Fault) (project : σ → τ) : Prop where
  arguments : ∀ owner, Effect.Transport (State.mapEffects project) (physical.attempt .arguments owner) (original.attempt .arguments owner)
  append : ∀ owner, Effect.Transport (State.mapEffects project) (physical.attempt .append owner) (original.attempt .append owner)
  publish : ∀ owner, Effect.Transport (State.mapEffects project) (physical.attempt .publish owner) (original.attempt .publish owner)
  release : ∀ action owner, Effect.Transport (State.mapEffects project) (physical.release action owner) (original.release action owner)

theorem callbacks_transport {project : σ → τ} {left : Operations σ} {right : Operations τ}
    (creation : HostTransport project left.create right.create) (cloning : HostTransport project left.copy right.copy)
    (leftAllocate : Backing.Registry.Allocate σ) (rightAllocate : Backing.Registry.Allocate τ)
    (runtimeSafety : Bool) (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (cells : List Storage.Cell) (value : Contract.Yul.Word)
    (leftGraph : Storage.State → Frame σ → Interner.Heap) (rightGraph : Storage.State → Frame τ → Interner.Heap)
    (leftGrowth : Option (Growth.Registered.Callbacks σ)) (rightGrowth : Option (Growth.Registered.Callbacks τ))
    (pending : PendingTransport
      (callbacks left leftAllocate runtimeSafety allocator container source itemSource input key normalized cells value leftGraph leftGrowth)
      (callbacks right rightAllocate runtimeSafety allocator container source itemSource input key normalized cells value rightGraph rightGrowth) project) :
    Storage.Operations.Transport
      (callbacks left leftAllocate runtimeSafety allocator container source itemSource input key normalized cells value leftGraph leftGrowth)
      (callbacks right rightAllocate runtimeSafety allocator container source itemSource input key normalized cells value rightGraph rightGrowth)
      (State.mapEffects project) := by
  constructor
  · intro site owner
    cases site with
    | arguments => exact pending.arguments owner
    | append => exact pending.append owner
    | publish => exact pending.publish owner
    | item =>
      exact preparation_callback_transport creation cloning leftAllocate rightAllocate runtimeSafety allocator container
        source itemSource input key normalized cells value leftGraph rightGraph leftGrowth rightGrowth .item (Or.inl rfl) owner
    | clone =>
      exact preparation_callback_transport creation cloning leftAllocate rightAllocate runtimeSafety allocator container
        source itemSource input key normalized cells value leftGraph rightGraph leftGrowth rightGrowth .clone (Or.inr rfl) owner
  · exact pending.release

/-- Index the remaining local obligations by the actual callback inputs. Graph
observation agreement is supplied by the insertion projection below. These are
compiler proof obligations, not additional trusted host contracts. -/
def CallbackObligations (project : σ → τ) (left : Operations σ) (right : Operations τ)
    (leftAllocate : Backing.Registry.Allocate σ) (rightAllocate : Backing.Registry.Allocate τ)
    (runtimeSafety : Bool) (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (leftGrowth : Option (Growth.Registered.Callbacks σ)) (rightGrowth : Option (Growth.Registered.Callbacks τ)) : Prop :=
  ∀ cells value (leftGraph : Storage.State → Frame σ → Interner.Heap) (rightGraph : Storage.State → Frame τ → Interner.Heap),
    (∀ owner before, rightGraph owner (before.mapEffects project) = leftGraph owner before) →
    PendingTransport
      (callbacks left leftAllocate runtimeSafety allocator container source itemSource input key normalized cells value leftGraph leftGrowth)
      (callbacks right rightAllocate runtimeSafety allocator container source itemSource input key normalized cells value rightGraph rightGrowth) project

variable {project : σ → τ} {left : Operations σ} {right : Operations τ}
  (creation : HostTransport project left.create right.create) (cloning : HostTransport project left.copy right.copy)
  (leftAllocate : Backing.Registry.Allocate σ) (rightAllocate : Backing.Registry.Allocate τ)
  (runtimeSafety : Bool) (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
  (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
  (leftGrowth : Option (Growth.Registered.Callbacks σ)) (rightGrowth : Option (Growth.Registered.Callbacks τ))
  (remaining : CallbackObligations project left right leftAllocate rightAllocate runtimeSafety allocator container
    source itemSource input key normalized leftGrowth rightGrowth)
include creation cloning remaining

theorem executionWithRoom_transport (meaning : Meaning) (deterministic room : Bool) (cells : List Storage.Cell)
    (before : World (Publication.Effects σ)) :
    executionWithRoom right rightAllocate runtimeSafety allocator container source itemSource meaning input key normalized
      deterministic room cells (before.mapEffects (Publication.Effects.mapAllocator project)) rightGrowth =
    ((executionWithRoom left leftAllocate runtimeSafety allocator container source itemSource meaning input key normalized
      deterministic room cells before leftGrowth).1,
     (executionWithRoom left leftAllocate runtimeSafety allocator container source itemSource meaning input key normalized
      deterministic room cells before leftGrowth).2.mapEffects project) := by
  let value := (key.eval meaning before.graph.read).getD 0
  let leftGraph : Storage.State → Frame σ → Interner.Heap := fun owner state =>
    Interner.InsertionExecution.project cells before.graph.table (cell input key normalized value owner state) key owner
  let rightGraph : Storage.State → Frame τ → Interner.Heap := fun owner state =>
    Interner.InsertionExecution.project cells before.graph.table (cell input key normalized value owner state) key owner
  have pending := remaining cells value leftGraph rightGraph (fun _ _ => rfl)
  have mapped := callbacks_transport creation cloning leftAllocate rightAllocate runtimeSafety allocator container source itemSource
    input key normalized cells value leftGraph rightGraph leftGrowth rightGrowth pending
  exact mapped.execute ⟨deterministic, room, fun _ => false⟩ insertProgram {} ⟨⟨⟨⟨before.memory, false⟩, none⟩, none⟩, none⟩

theorem execution_transport (meaning : Meaning) (deterministic : Bool) (cells : List Storage.Cell)
    (before : World (Publication.Effects σ)) :
    execution right rightAllocate runtimeSafety allocator container source itemSource meaning input key normalized
      deterministic cells (before.mapEffects (Publication.Effects.mapAllocator project)) rightGrowth =
    ((execution left leftAllocate runtimeSafety allocator container source itemSource meaning input key normalized
      deterministic cells before leftGrowth).1,
     (execution left leftAllocate runtimeSafety allocator container source itemSource meaning input key normalized
      deterministic cells before leftGrowth).2.mapEffects project) :=
  executionWithRoom_transport creation cloning leftAllocate rightAllocate runtimeSafety allocator container source itemSource input key normalized
    leftGrowth rightGrowth remaining meaning deterministic _ cells before

theorem checkedExecution_transport (meaning : Meaning) (deterministic : Bool) (cells : List Storage.Cell)
    (before : World (Publication.Effects σ)) :
    checkedExecution right rightAllocate runtimeSafety allocator container source itemSource meaning input key normalized
      deterministic cells (before.mapEffects (Publication.Effects.mapAllocator project)) rightGrowth =
    (checkedExecution left leftAllocate runtimeSafety allocator container source itemSource meaning input key normalized
      deterministic cells before leftGrowth).map (fun ran => (ran.1, ran.2.mapEffects project)) := by
  unfold checkedExecution
  simp only [show (before.mapEffects (Publication.Effects.mapAllocator project)).memory.memory = before.memory.memory from rfl]
  cases checkedCount before.memory.memory container cells with
  | error fault => rfl
  | ok count =>
    dsimp only [bind, Except.bind, pure, Except.pure, Except.map]
    rw [executionWithRoom_transport creation cloning leftAllocate rightAllocate runtimeSafety allocator container source itemSource
      input key normalized leftGrowth rightGrowth remaining]

/-- Derive exact body/world transport from the actual count check, source
executor and projection. Capacity, ordinary failure and stopped native faults
all retain the reached graph, ownership and memory selected by that execution. -/
theorem body_transport (meaning : Meaning) (deterministic : Bool) (cells : List Storage.Cell) :
    Effect.Transport (World.mapEffects (Publication.Effects.mapAllocator project))
      (fun before => body left leftAllocate runtimeSafety allocator container source itemSource meaning input key normalized deterministic cells before leftGrowth)
      (fun before => body right rightAllocate runtimeSafety allocator container source itemSource meaning input key normalized deterministic cells before rightGrowth) := by
  intro before
  unfold body
  dsimp only
  rw [checkedExecution_transport creation cloning leftAllocate rightAllocate runtimeSafety allocator container source itemSource
    input key normalized leftGrowth rightGrowth remaining]
  cases checkedExecution left leftAllocate runtimeSafety allocator container source itemSource meaning input key normalized deterministic cells before leftGrowth with
  | error fault => rfl
  | ok ran =>
    rcases ran with ⟨⟨result, owner⟩, after⟩
    rfl

theorem insert_transport (meaning : Meaning) (deterministic : Bool) :
    Effect.Transport (World.mapEffects (Publication.Effects.mapAllocator project))
      (insert left leftAllocate runtimeSafety allocator container source itemSource meaning input key normalized deterministic leftGrowth)
      (insert right rightAllocate runtimeSafety allocator container source itemSource meaning input key normalized deterministic rightGrowth) := by
  intro before
  unfold insert
  simp only [show (before.mapEffects (Publication.Effects.mapAllocator project)).graph = before.graph from rfl]
  cases before.graph.representatives with
  | none => rfl
  | some cells =>
    exact body_transport creation cloning leftAllocate rightAllocate runtimeSafety allocator container source itemSource
      input key normalized leftGrowth rightGrowth remaining meaning deterministic cells before

end Native
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion
