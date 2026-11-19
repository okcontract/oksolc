/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionPayload
import Compiler.Extraction.AssemblyItemAllocation

namespace Compiler.Extraction.ExpressionDeinit.Lifetime
open Compiler.Extraction.Memory Compiler.Extraction.Storage
open Compiler.Extraction.Memory.Arguments.Normalization

abbrev ItemFault := Payload.ItemFault Arguments.ReleaseFault

def operations (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ) (allocator : Nat)
    (payloads : Nat → Option AssemblyItemDeinit.Bytes) : Operations σ ItemFault :=
  Payload.operationsWith bytes allocator payloads (AssemblyItem.destroy objects allocator)

def run (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ) (external : External σ)
    (allocator : Nat) (payloads : Nat → Option AssemblyItemDeinit.Bytes) (descriptor : Descriptor) (before : Session σ) :=
  execute (operations bytes objects allocator payloads) external allocator descriptor expressionDeinitCode ⟨before, false⟩

structure Post (payload : Option AssemblyItemDeinit.Bytes) (descriptor : Descriptor) (before : Session σ)
    (after : State σ) : Prop where
  valid : Valid after.memory
  invalidated : after.invalidated = true
  nextId : after.memory.memory.nextId = before.memory.nextId
  nextAddress : after.memory.memory.nextAddress = before.memory.nextAddress
  frame : ∀ id, id ≠ descriptor.item → id ≠ descriptor.arguments.address → ¬AssemblyItemDeinit.Touches payload id →
    after.memory.heap id = before.heap id ∧ after.memory.memory.heap.lookup id = before.memory.heap.lookup id
  itemDead : after.memory.heap descriptor.item = none ∧ after.memory.memory.heap.lookup descriptor.item = none
  payloadDead : ∀ id, AssemblyItemDeinit.Touches payload id →
    after.memory.heap id = none ∧ after.memory.memory.heap.lookup id = none
  argumentsConsumed : Consumed descriptor.arguments after.memory

/-- Complete expression destruction in one registry: payload cleanup preserves
item ownership, object destruction preserves argument ownership, then argument
cleanup retains both earlier lifetime deaths. Native field projection and caller
ownership admission remain explicit preconditions, not verified by this theorem. -/
theorem run_verified (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ) (external : External σ)
    (allocator : Nat) (payloads : Nat → Option AssemblyItemDeinit.Bytes) (descriptor : Descriptor) (before : Session σ)
    (valid : Valid before) (itemOwned : AssemblyItem.Owned allocator descriptor.item before)
    (live : SliceValid allocator before.heap descriptor.arguments)
    (payloadOwned : ∀ slice, payloads descriptor.item = some slice → AssemblyItemDeinit.Owned allocator slice before) :
    ∃ after, run bytes objects external allocator payloads descriptor before = (.ok (), after) ∧
      Post (payloads descriptor.item) descriptor before after := by
  obtain ⟨valueState, valueCall, valuePost, _⟩ := AssemblyItemDeinit.run_verified bytes allocator
    (payloads descriptor.item) before valid payloadOwned
  have stillOwned := AssemblyItem.after_payload allocator descriptor.item (payloads descriptor.item) before
    valueState itemOwned payloadOwned valuePost
  obtain ⟨objectState, objectCall, objectPost, _⟩ := AssemblyItem.destroy_verified objects allocator descriptor.item
    valueState.memory valuePost.valid stillOwned
  have argumentsLive := objectPost.arguments descriptor.item valueState.memory objectState allocator stillOwned allocator
    descriptor.arguments (valuePost.arguments allocator descriptor.arguments live)
  obtain ⟨after, argumentCall, afterValid, argumentPost, _⟩ := free_valid external allocator descriptor.arguments
    objectState objectPost.valid argumentsLive
  refine ⟨⟨after, true⟩, ?_, ⟨afterValid, rfl, argumentPost.nextId.trans (objectPost.nextId.trans valuePost.nextId),
    argumentPost.nextAddress.trans (objectPost.nextAddress.trans valuePost.nextAddress), ?_, ?_, ?_, released_consumed argumentPost⟩⟩
  · dsimp only [run]
    rw [execute_equation]
    simp only [operations, Payload.operationsWith, valueCall, objectCall, argumentCall, Except.mapError]
  · intro id objectApart argumentsApart untouched
    exact ⟨(argumentPost.frame id argumentsApart).1.trans ((objectPost.frame id objectApart).1.trans (valuePost.frame id untouched).1),
      (argumentPost.frame id argumentsApart).2.trans ((objectPost.frame id objectApart).2.trans (valuePost.frame id untouched).2)⟩
  · exact Payload.free_keeps_dead external allocator descriptor.arguments objectState after descriptor.item argumentCall argumentPost objectPost.dead
  · intro id touched
    exact Payload.free_keeps_dead external allocator descriptor.arguments objectState after id argumentCall argumentPost
      (objectPost.keeps_dead descriptor.item valueState.memory objectState id (valuePost.dead id touched))

def insertionOperations (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ) (external : External σ)
    (allocator : Nat) (payloads : Nat → Option AssemblyItemDeinit.Bytes)
    (last : Storage.State → State σ → Descriptor) (rest : Storage.Operations (State σ) (Fault ItemFault)) :=
  insertionWith (operations bytes objects allocator payloads) external allocator last rest

theorem last_value_preserved (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ) (external : External σ)
    (allocator : Nat) (payloads : Nat → Option AssemblyItemDeinit.Bytes)
    (last : Storage.State → State σ → Descriptor) (rest : Storage.Operations (State σ) (Fault ItemFault))
    (ownership : Storage.State) (before : State σ) (ready : before.invalidated = false)
    (valid : Valid before.memory) (itemOwned : AssemblyItem.Owned allocator (last ownership before).item before.memory)
    (live : SliceValid allocator before.memory.heap (last ownership before).arguments)
    (payloadOwned : ∀ slice, payloads (last ownership before).item = some slice → AssemblyItemDeinit.Owned allocator slice before.memory) :
    let executed := Storage.Release.lastValue.execute (insertionOperations bytes objects external allocator payloads last rest) ownership before
    executed.1.1 = .ok () ∧ Post (payloads (last ownership before).item) (last ownership before) before.memory executed.2 := by
  rcases before with ⟨memory, invalidated⟩
  cases ready
  obtain ⟨after, executed, post⟩ := run_verified bytes objects external allocator payloads (last ownership ⟨memory, false⟩)
    memory valid itemOwned live payloadOwned
  dsimp only [insertionOperations]
  rw [last_value_memory_equation]
  change execute _ _ _ _ _ _ = _ at executed
  rw [executed]
  exact ⟨rfl, post⟩

open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul

/-- The same complete insertion execution retains word preservation and calls
the destructor which consumes all three owned extents at admitted rollback sites. -/
theorem insertion_verified (meaning : Meaning) (cells : List Cell) (table : Table)
    (cell : Cell) (key : Key) (deterministic : Bool) (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ) (external : External σ)
    (allocator : Nat) (payloads : Nat → Option AssemblyItemDeinit.Bytes) (last : Storage.State → State σ → Descriptor)
    (rest : Storage.Operations (State σ) (Fault ItemFault)) (before : State σ) (outcome : Option Storage.Outcome)
    (valid : Interner.Invariant meaning (Interner.observedHeap cells table))
    (binding : keyCode.run cell.item cell.arguments cell.sequence = some key)
    (denotation : key.eval meaning (readValue cells) = some cell.value)
    (completed : (insertProgram.execute ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩
      (insertionOperations bytes objects external allocator payloads last rest) {} before).1.1 = .ok outcome) :
    (let executed := insertProgram.execute ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩
        (insertionOperations bytes objects external allocator payloads last rest) {} before;
      SafeResult deterministic (outcome, executed.1.2) ∧
        Interner.Invariant meaning (Interner.InsertionExecution.project cells table cell key executed.1.2) ∧
        Interner.Stable (Interner.observedHeap cells table) (Interner.InsertionExecution.project cells table cell key executed.1.2) ∧
        match Interner.insertionOutcome cells outcome with
        | .error _ => True
        | .ok id => (Interner.InsertionExecution.project cells table cell key executed.1.2).read id = some cell.value) ∧
    (∀ ownership reached, reached.invalidated = false → Valid reached.memory →
      AssemblyItem.Owned allocator (last ownership reached).item reached.memory →
      SliceValid allocator reached.memory.heap (last ownership reached).arguments →
      (∀ slice, payloads (last ownership reached).item = some slice → AssemblyItemDeinit.Owned allocator slice reached.memory) →
      let executed := Storage.Release.lastValue.execute (insertionOperations bytes objects external allocator payloads last rest) ownership reached
      executed.1.1 = .ok () ∧ Post (payloads (last ownership reached).item) (last ownership reached) reached.memory executed.2) :=
  ⟨Interner.InsertionExecution.verified meaning cells table cell key deterministic
      (insertionOperations bytes objects external allocator payloads last rest) before outcome valid binding denotation completed,
    last_value_preserved bytes objects external allocator payloads last rest⟩


end Compiler.Extraction.ExpressionDeinit.Lifetime
