/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionDeinitInsertion
import Compiler.Extraction.AssemblyItemDeinitProofs

namespace Compiler.Extraction.ExpressionDeinit.Payload
open Compiler.Extraction.Memory Compiler.Extraction.Storage
open Compiler.Extraction.Memory.Arguments.Normalization

abbrev ItemFault (ε : Type) := Sum AssemblyItemDeinit.Fault ε
abbrev Destroy (σ ε : Type) := Nat → Session σ → Except ε Unit × σ

/-- Both stages can change the shared registry. The value destructor uses its
actual extracted body; callers supply the allocation-release implementation. -/
def operationsWith (release : AssemblyItemDeinit.Release σ) (allocator : Nat)
    (payloads : Nat → Option AssemblyItemDeinit.Bytes) (destroy : Nat → Session σ → Except ε Unit × Session σ) : Operations σ (ItemFault ε) where
  deinit id before :=
    let (result, after) := AssemblyItemDeinit.run release allocator (payloads id) before
    (result.mapError Sum.inl, after.memory)
  destroy id before :=
    let (result, reached) := destroy id before
    (result.mapError Sum.inr, reached)

/-- Compatibility adapter for the earlier framed allocation callback. Its native
allocation lifetime remains a caller obligation; Lifetime supplies checked release. -/
def operations (release : AssemblyItemDeinit.Release σ) (allocator : Nat)
    (payloads : Nat → Option AssemblyItemDeinit.Bytes) (destroy : Destroy σ ε) : Operations σ (ItemFault ε) :=
  operationsWith release allocator payloads fun id before =>
    let (result, effects) := destroy id before
    (result, { before with effects })

def run (release : AssemblyItemDeinit.Release σ) (external : External σ) (allocator : Nat)
    (payloads : Nat → Option AssemblyItemDeinit.Bytes) (destroy : Destroy σ ε)
    (descriptor : Descriptor) (before : Session σ) :=
  execute (operations release allocator payloads destroy) external allocator descriptor expressionDeinitCode ⟨before, false⟩

/-- Argument cleanup cannot revive a payload lifetime already released by the
preceding item operation, even when an empty argument sentinel aliases its ID. -/
theorem free_keeps_dead (external : External σ) (allocator : Nat) (slice : ArgumentSlice)
    (before after : Session σ) (id : Nat)
    (executed : free external allocator slice before = (.ok (), after))
    (post : Arguments.ReleasePost before.heap before.memory allocator slice after.heap after.memory)
    (dead : before.heap id = none ∧ before.memory.heap.lookup id = none) :
    after.heap id = none ∧ after.memory.heap.lookup id = none := by
  by_cases empty : slice.items = []
  · cases before
    simp [free, Arguments.release, empty] at executed
    cases executed
    exact dead
  · by_cases same : id = slice.address
    · subst id; exact post.dead empty
    · exact ⟨(post.frame id same).1.trans dead.1, (post.frame id same).2.trans dead.2⟩

structure Post (allocator : Nat) (payload : Option AssemblyItemDeinit.Bytes) (descriptor : Descriptor) (before : Session σ)
    (execution : Except (Fault (ItemFault ε)) Unit × State σ) : Prop where
  valid : Valid execution.2.memory
  nextId : execution.2.memory.memory.nextId = before.memory.nextId
  nextAddress : execution.2.memory.memory.nextAddress = before.memory.nextAddress
  frame : ∀ id, id ≠ descriptor.arguments.address → ¬AssemblyItemDeinit.Touches payload id →
    execution.2.memory.heap id = before.heap id ∧ execution.2.memory.memory.heap.lookup id = before.memory.heap.lookup id
  payloadDead : ∀ id, AssemblyItemDeinit.Touches payload id →
    execution.2.memory.heap id = none ∧ execution.2.memory.memory.heap.lookup id = none
  outcome : match execution.1 with
    | .ok () => Consumed descriptor.arguments execution.2.memory ∧ execution.2.invalidated = true
    | .error (.item (.inr _)) => SliceValid allocator execution.2.memory.heap descriptor.arguments ∧
        execution.2.invalidated = false
    | .error _ => False

/-- Same execution: source-bound item cleanup changes memory, allocation cleanup
receives that state, then checked argument free consumes its still-live slice.
A later item-allocation fault retains the completed payload release and effects.
The native allocation destructor and descriptor admission are not proved here. -/
theorem run_verified (release : AssemblyItemDeinit.Release σ) (external : External σ) (allocator : Nat)
    (payloads : Nat → Option AssemblyItemDeinit.Bytes) (destroy : Destroy σ ε)
    (descriptor : Descriptor) (before : Session σ) (valid : Valid before)
    (live : SliceValid allocator before.heap descriptor.arguments)
    (owned : ∀ slice, payloads descriptor.item = some slice → AssemblyItemDeinit.Owned allocator slice before) :
    ∃ prepared, AssemblyItemDeinit.run release allocator (payloads descriptor.item) before = (.ok (), prepared) ∧
      AssemblyItemDeinit.Post (payloads descriptor.item) before prepared ∧
      Post (allocator := allocator) (payloads descriptor.item) descriptor before
        (run release external allocator payloads destroy descriptor before) := by
  obtain ⟨prepared, valueCall, valuePost, _⟩ := AssemblyItemDeinit.run_verified release allocator
    (payloads descriptor.item) before valid owned
  refine ⟨prepared, valueCall, valuePost, ?_⟩
  have argumentsLive := valuePost.arguments allocator descriptor.arguments live
  dsimp only [run]
  rw [execute_equation]
  simp only [operations, operationsWith, valueCall, Except.mapError]
  cases allocationCall : destroy descriptor.item prepared.memory with
  | mk result effects =>
    cases result with
    | error fault =>
      refine ⟨⟨valuePost.valid.memory, valuePost.valid.related, valuePost.valid.injected⟩,
        valuePost.nextId, valuePost.nextAddress, ?_, valuePost.dead, argumentsLive, rfl⟩
      intro id _ untouched
      exact valuePost.frame id untouched
    | ok returned =>
      cases returned
      obtain ⟨after, freed, afterValid, argumentPost, _⟩ := free_valid external allocator descriptor.arguments
        { prepared.memory with effects } ⟨valuePost.valid.memory, valuePost.valid.related, valuePost.valid.injected⟩ argumentsLive
      simp only [freed]
      refine ⟨afterValid, argumentPost.nextId.trans valuePost.nextId, argumentPost.nextAddress.trans valuePost.nextAddress,
        ?_, ?_, released_consumed argumentPost, rfl⟩
      · intro id separate untouched
        exact ⟨(argumentPost.frame id separate).1.trans (valuePost.frame id untouched).1,
          (argumentPost.frame id separate).2.trans (valuePost.frame id untouched).2⟩
      · intro id touched
        exact free_keeps_dead external allocator descriptor.arguments { prepared.memory with effects }
          after id freed argumentPost (valuePost.dead id touched)

theorem Post.preserves_borrow (allocator : Nat) (payload : Option AssemblyItemDeinit.Bytes)
    (descriptor : Descriptor) (before : Session σ) (execution : Except (Fault (ItemFault ε)) Unit × State σ)
    (post : Post allocator payload descriptor before execution) (source : Compiler.ZigAir.Memory.WordArray.View)
    (values : List Compiler.Algebraic.NodeId)
    (represented : Compiler.ZigAir.Memory.WordArray.Represents before.memory source values)
    (separate : values ≠ [] → source.allocation ≠ descriptor.arguments.address)
    (untouched : values ≠ [] → ¬AssemblyItemDeinit.Touches payload source.allocation) :
    Compiler.ZigAir.Memory.WordArray.Represents execution.2.memory.memory source values := by
  by_cases empty : values = []
  · subst values
    exact ⟨represented.1, fun _ impossible => False.elim (by simp at impossible)⟩
  · exact represented_frame source values represented (post.frame _ (separate empty) (untouched empty)).2

/-- Install the same memory-changing destructor in insertion's lastValue action;
all other production insertion operations retain their explicit obligations. -/
def insertionOperations (release : AssemblyItemDeinit.Release σ) (external : External σ) (allocator : Nat)
    (payloads : Nat → Option AssemblyItemDeinit.Bytes) (destroy : Destroy σ ε)
    (last : Storage.State → State σ → Descriptor) (rest : Storage.Operations (State σ) (Fault (ItemFault ε))) :=
  insertionWith (operations release allocator payloads destroy) external allocator last rest

theorem last_value_preserved (release : AssemblyItemDeinit.Release σ) (external : External σ) (allocator : Nat)
    (payloads : Nat → Option AssemblyItemDeinit.Bytes) (destroy : Destroy σ ε)
    (last : Storage.State → State σ → Descriptor) (rest : Storage.Operations (State σ) (Fault (ItemFault ε)))
    (ownership : Storage.State) (before : State σ) (ready : before.invalidated = false)
    (valid : Valid before.memory) (live : SliceValid allocator before.memory.heap (last ownership before).arguments)
    (owned : ∀ slice, payloads (last ownership before).item = some slice → AssemblyItemDeinit.Owned allocator slice before.memory) :
    let executed := Storage.Release.lastValue.execute (insertionOperations release external allocator payloads destroy last rest) ownership before
    Post (allocator := allocator) (payloads (last ownership before).item) (last ownership before) before.memory (executed.1.1, executed.2) := by
  rcases before with ⟨memory, invalidated⟩
  cases ready
  obtain ⟨_, _, _, post⟩ := run_verified release external allocator payloads destroy (last ownership ⟨memory, false⟩)
    memory valid live owned
  dsimp only [insertionOperations]
  rw [last_value_memory_equation]
  cases executed : execute (operations release allocator payloads destroy) external allocator
      (last ownership ⟨memory, false⟩) expressionDeinitCode ⟨memory, false⟩ with
  | mk result reached =>
    change Post (allocator := allocator) _ _ memory (run release external allocator payloads destroy (last ownership ⟨memory, false⟩) memory) at post
    rw [show run release external allocator payloads destroy (last ownership ⟨memory, false⟩) memory = (result, reached) from executed] at post
    exact post

open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul

/-- Word preservation and the checked payload/argument callback concern the same
complete insertion execution. Reached descriptor admission is still explicit. -/
theorem insertion_verified (meaning : Meaning) (cells : List Cell) (table : Table)
    (cell : Cell) (key : Key) (deterministic : Bool) (release : AssemblyItemDeinit.Release σ) (external : External σ)
    (allocator : Nat) (payloads : Nat → Option AssemblyItemDeinit.Bytes) (destroy : Destroy σ ε) (last : Storage.State → State σ → Descriptor)
    (rest : Storage.Operations (State σ) (Fault (ItemFault ε))) (before : State σ) (outcome : Option Storage.Outcome)
    (valid : Interner.Invariant meaning (Interner.observedHeap cells table))
    (binding : keyCode.run cell.item cell.arguments cell.sequence = some key)
    (denotation : key.eval meaning (readValue cells) = some cell.value)
    (completed : (insertProgram.execute ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩
      (insertionOperations release external allocator payloads destroy last rest) {} before).1.1 = .ok outcome) :
    (let executed := insertProgram.execute ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩
        (insertionOperations release external allocator payloads destroy last rest) {} before;
      SafeResult deterministic (outcome, executed.1.2) ∧
        Interner.Invariant meaning (Interner.InsertionExecution.project cells table cell key executed.1.2) ∧
        Interner.Stable (Interner.observedHeap cells table) (Interner.InsertionExecution.project cells table cell key executed.1.2) ∧
        match Interner.insertionOutcome cells outcome with
        | .error _ => True
        | .ok id => (Interner.InsertionExecution.project cells table cell key executed.1.2).read id = some cell.value) ∧
    (∀ ownership reached, reached.invalidated = false → Valid reached.memory →
      SliceValid allocator reached.memory.heap (last ownership reached).arguments →
      (∀ slice, payloads (last ownership reached).item = some slice → AssemblyItemDeinit.Owned allocator slice reached.memory) →
      let executed := Storage.Release.lastValue.execute (insertionOperations release external allocator payloads destroy last rest) ownership reached
      Post allocator (payloads (last ownership reached).item) (last ownership reached) reached.memory (executed.1.1, executed.2)) :=
  ⟨Interner.InsertionExecution.verified meaning cells table cell key deterministic
      (insertionOperations release external allocator payloads destroy last rest) before outcome valid binding denotation completed,
    last_value_preserved release external allocator payloads destroy last rest⟩


end Compiler.Extraction.ExpressionDeinit.Payload
