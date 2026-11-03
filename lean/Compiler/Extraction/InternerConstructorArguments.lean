/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorItem
import Compiler.Extraction.InternerTemporaryTernary

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.Arguments
open Compiler.Algebraic Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

-- Each phase already has a checked contract. Compare its actual arguments at
-- the forwarding boundary instead of unfolding an entire memory execution.
attribute [local irreducible] TemporaryUnary.prepare TemporaryArguments.prepare TemporaryTernary.prepare
  TemporaryArguments.unwind ConstructorItem.operation

/-- The already evaluated elements of an admitted source literal use the
existing allocation/store programs. This is not a replacement for evaluating
those elements at their source call sites, including recursive initializers. -/
def prepare (values : List NodeId) : GraphAction σ View :=
  match values with
  | [] => fun before => (.ok ⟨0, 0, 0⟩, before)
  | [a] => TemporaryUnary.prepare a
  | [a, b] => TemporaryArguments.prepare a b
  | [a, b, c] => TemporaryTernary.prepare a b c
  | _ => fun before => (.error .outsideOwnedContinuation, before)

/-- Storage metadata follows allocation and the actual reached stores, not
the logical list or a postulated stack flag. Empty input has no native buffer. -/
theorem prepare_storage (values : List NodeId) (before after : World σ) (source : View)
    (ran : prepare values before = (.ok source, after)) (nonempty : values ≠ []) :
    ∃ cell, after.memory.memory.heap.lookup source.allocation = some cell ∧
      cell.type = .array values.length word ∧ cell.writable = true ∧ cell.stack = true := by
  rcases values with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, tail⟩⟩⟩⟩
  · exact (nonempty rfl).elim
  · cases allocation : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 1 word) with
    | error fault => simp only [prepare, TemporaryUnary.prepare, allocation, Prod.mk.injEq] at ran; cases ran.1
    | ok pair =>
      have stored := TemporaryUnary.writeOne_success ⟨before.memory.memory.nextId, 0, 1⟩ source a
        { before with memory := { before.memory with memory := pair.2 } } after
        (by simpa only [prepare, TemporaryUnary.prepare, allocation] using ran)
      rw [stored.1]
      exact TemporaryMemory.allocated_array _ _ _ 1 pair.1 allocation stored.2
  · cases allocation : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) with
    | error fault => simp only [prepare, TemporaryArguments.prepare, allocation, Prod.mk.injEq] at ran; cases ran.1
    | ok pair =>
      have stored := TemporaryArguments.writePair_success ⟨before.memory.memory.nextId, 0, 2⟩ source a b
        { before with memory := { before.memory with memory := pair.2 } } after
        (by simpa only [prepare, TemporaryArguments.prepare, allocation] using ran)
      rw [stored.1]
      exact TemporaryMemory.allocated_array _ _ _ 2 pair.1 allocation stored.2
  · cases allocation : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 3 word) with
    | error fault => simp only [prepare, TemporaryTernary.prepare, allocation, Prod.mk.injEq] at ran; cases ran.1
    | ok pair =>
      have stored := TemporaryTernary.writeTriple_success ⟨before.memory.memory.nextId, 0, 3⟩ source a b c
        { before with memory := { before.memory with memory := pair.2 } } after
        (by simpa only [prepare, TemporaryTernary.prepare, allocation] using ran)
      rw [stored.1]
      exact TemporaryMemory.allocated_array _ _ _ 3 pair.1 allocation stored.2
  · cases (Prod.mk.inj ran).1

structure Prepared (values : List NodeId) (before : World σ) (source : View) (after : World σ) : Prop where
  address : source = if values.isEmpty then ⟨0, 0, 0⟩ else ⟨before.memory.memory.nextId, 0, values.length⟩
  good : Good source values after
  graph : after.graph = before.graph
  heap : after.memory.heap = before.memory.heap
  effects : after.memory.effects = before.memory.effects
  counter : after.memory.memory.nextId = before.memory.memory.nextId + (if values.isEmpty then 0 else 1)
  frame : ∀ id cell, before.memory.memory.heap.lookup id = some cell → after.memory.memory.heap.lookup id = some cell
  storage : values ≠ [] → ∃ cell, after.memory.memory.heap.lookup source.allocation = some cell ∧
    cell.type = .array values.length word ∧ cell.writable = true ∧ cell.stack = true

/-- Returning the source scope retires its actual stack lifetime after any
continuation that retains that allocation. The mark comes from preparation. -/
theorem Prepared.retire (values : List NodeId) (before after : World σ) (source : View)
    (ready : Prepared values before source after) (nonempty : values ≠ [])
    (reached : Compiler.ZigAir.Memory.State) (valid : reached.valid = true)
    (frame : reached.heap.lookup source.allocation = after.memory.memory.heap.lookup source.allocation) :
    (Compiler.ZigAir.Memory.cleanup before.memory.memory.nextId reached).heap.lookup source.allocation = none := by
  obtain ⟨cell, found, _, _, stack⟩ := ready.storage nonempty
  have recent : before.memory.memory.nextId ≤ source.allocation := by
    rw [ready.address]
    simp only [List.isEmpty_eq_false_iff.mpr nonempty, Bool.false_eq_true, ↓reduceIte, Nat.le_refl]
  exact Compiler.ZigAir.Memory.cleanup_lookup_stack _ _ _ cell valid (frame.trans found) stack recent

/-- A successful actual initializer discharges the native constructor's input
contents and lifetime premises. Neither allocation success nor final Good is
assumed independently of the observed initializer execution. -/
theorem prepare_success (values : List NodeId) (before after : World σ) (source : View)
    (valid : Valid before.memory) (ran : prepare values before = (.ok source, after)) :
    Prepared values before source after := by
  have storage := prepare_storage values before after source ran
  rcases values with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, tail⟩⟩⟩⟩
  · have same := Prod.mk.inj ran
    cases Except.ok.inj same.1
    cases same.2
    exact ⟨rfl, ⟨valid, rfl, by intro index inside; simp at inside⟩, rfl, rfl, rfl, by simp, fun _ _ found => found, storage⟩
  · cases allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 1 word) with
    | error fault => simp only [prepare, TemporaryUnary.prepare, allocated, Prod.mk.injEq] at ran; cases ran.1
    | ok pair =>
      obtain ⟨reached, called, good, graph, heap, effects, counter, frame⟩ :=
        TemporaryUnary.prepare_verified a before pair.1 pair.2 valid allocated
      have same := Prod.mk.inj (called.symm.trans ran)
      cases Except.ok.inj same.1
      cases same.2
      exact ⟨rfl, good, graph, heap, effects, counter, frame, storage⟩
  · cases allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) with
    | error fault => simp only [prepare, TemporaryArguments.prepare, allocated, Prod.mk.injEq] at ran; cases ran.1
    | ok pair =>
      obtain ⟨reached, called, good, graph, heap, effects, counter, frame⟩ :=
        TemporaryArguments.prepare_verified a b before pair.1 pair.2 valid allocated
      have same := Prod.mk.inj (called.symm.trans ran)
      cases Except.ok.inj same.1
      cases same.2
      exact ⟨rfl, good, graph, heap, effects, counter, frame, storage⟩
  · cases allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 3 word) with
    | error fault => simp only [prepare, TemporaryTernary.prepare, allocated, Prod.mk.injEq] at ran; cases ran.1
    | ok pair =>
      obtain ⟨reached, called, good, graph, heap, effects, counter, frame⟩ :=
        TemporaryTernary.prepare_verified a b c before pair.1 pair.2 valid allocated
      have same := Prod.mk.inj (called.symm.trans ran)
      cases Except.ok.inj same.1
      cases same.2
      exact ⟨rfl, good, graph, heap, effects, counter, frame, storage⟩
  · cases (Prod.mk.inj ran).1

/-- Literal and named-local initialization select a new native lifetime, not
an address in an existing container. Empty input has no allocation to separate.
This applies to stack allocations as well as registered allocator storage. -/
theorem Prepared.native_apart (values : List NodeId) (before after : World σ)
    (source : View) (ready : Prepared values before source after) (valid : Valid before.memory)
    (id : Nat) (cell : Compiler.ZigAir.Memory.Allocation)
    (found : before.memory.memory.heap.lookup id = some cell) (nonempty : source.length ≠ 0) :
    source.allocation ≠ id := by
  have older := (Compiler.ZigAir.Memory.valid_lookup _ _ _ valid.memory found).1
  by_cases empty : values.isEmpty = true
  · have length : source.length = 0 := by rw [ready.address]; simp only [empty, ↓reduceIte]
    exact (nonempty length).elim
  · rw [ready.address]
    simpa only [empty, Bool.false_eq_true, ↓reduceIte] using (Nat.ne_of_lt older).symm

/-- A fresh literal cannot borrow an existing nonempty map key. Empty keys
and empty literals keep their explicit no-backing guards. -/
theorem Prepared.key_apart (values : List NodeId) (before after : World (Publication.Effects σ))
    (source : View) (ready : Prepared values before source after) (valid : Valid before.memory)
    (allocator : Nat) (key : Key)
    (live : OwnedKeys.Live allocator ⟨before.memory.effects.keys, before.memory.heap⟩) :
    ∀ old, before.memory.effects.keys key = some old → key.arguments ≠ [] →
      source.length ≠ 0 → source.allocation ≠ old.address := by
  intro old found nonempty nonemptySource
  have stored := (live key old found).resolve_left nonempty
  obtain ⟨cell, backed, _⟩ := valid.injected _ _ stored
  exact ready.native_apart values before after source valid old.address cell backed nonemptySource

/-- Both anonymous literals and the named local array establish Prepared from
their actual stores. Share the subsequent item/init/take ownership connection. -/
theorem Prepared.caller_input (host : External σ) (budget allocator : Nat) (opcode : Opcode)
    (arguments : List NodeId) (debug : AssemblyItem.Fields.Values)
    (before prepared constructed : World (Publication.Effects σ)) (source : View)
    (address : Compiler.ZigAir.Memory.Address) (memory : Compiler.ZigAir.Memory.State)
    (pointer : Compiler.ZigAir.Memory.Value) (values : List NodeId)
    (normalized taken : State (Publication.Effects σ)) (key : Key)
    (valid : Valid before.memory)
    (ready : Prepared arguments before source prepared)
    (typed : AssemblyItem.Initializers.DebugTyped debug) (admitted : Admitted host)
    (made : ConstructorItem.prepare (Interner.constructorCode.operationRequest opcode arguments).item debug prepared =
      (.ok address, constructed))
    (allocated : Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) = .ok (pointer, memory))
    (initialized : Caller.initLookup (Publication.external host) budget allocator source
      ⟨constructed.memory.memory.nextId, 0, 2⟩ (Interner.constructorCode.operationRequest opcode arguments)
      ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩ = (.ok values, normalized))
    (transferred : take (Publication.external host) allocator normalized = (.ok (), taken))
    (keyed : Interner.makeKey (Interner.constructorCode.operationRequest opcode arguments) values = .ok key)
    (live : OwnedKeys.Live allocator ⟨before.memory.effects.keys, before.memory.heap⟩)
    (unique : OwnedKeys.Unique before.memory.effects.keys) :
    ∃ owned remaining, Insertion.Native.CallerInput allocator source address
      (Interner.constructorCode.operationRequest opcode arguments) values
      (input (Interner.constructorCode.operationRequest opcode arguments).item debug) key constructed taken owned remaining := by
  apply ConstructorItem.caller_input host budget allocator source (Interner.constructorCode.operationRequest opcode arguments)
    debug prepared constructed address memory pointer values normalized taken key ready.good
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) typed admitted made allocated initialized transferred keyed
  · rw [ready.effects, ready.heap]; exact live
  · rw [ready.effects]; exact unique
  · rw [ready.effects]
    exact Prepared.key_apart arguments before prepared source ready valid allocator key live

/-- Literal stores derive the shared native input contract. -/
theorem caller_input (host : External σ) (budget allocator : Nat) (opcode : Opcode)
    (arguments : List NodeId) (debug : AssemblyItem.Fields.Values)
    (before prepared constructed : World (Publication.Effects σ)) (source : View)
    (address : Compiler.ZigAir.Memory.Address) (memory : Compiler.ZigAir.Memory.State)
    (pointer : Compiler.ZigAir.Memory.Value) (values : List NodeId)
    (normalized taken : State (Publication.Effects σ)) (key : Key)
    (valid : Valid before.memory)
    (literal : prepare arguments before = (.ok source, prepared))
    (typed : AssemblyItem.Initializers.DebugTyped debug) (admitted : Admitted host)
    (made : ConstructorItem.prepare (Interner.constructorCode.operationRequest opcode arguments).item debug prepared =
      (.ok address, constructed))
    (allocated : Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) = .ok (pointer, memory))
    (initialized : Caller.initLookup (Publication.external host) budget allocator source
      ⟨constructed.memory.memory.nextId, 0, 2⟩ (Interner.constructorCode.operationRequest opcode arguments)
      ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩ = (.ok values, normalized))
    (transferred : take (Publication.external host) allocator normalized = (.ok (), taken))
    (keyed : Interner.makeKey (Interner.constructorCode.operationRequest opcode arguments) values = .ok key)
    (live : OwnedKeys.Live allocator ⟨before.memory.effects.keys, before.memory.heap⟩)
    (unique : OwnedKeys.Unique before.memory.effects.keys) :
    ∃ owned remaining, Insertion.Native.CallerInput allocator source address
      (Interner.constructorCode.operationRequest opcode arguments) values
      (input (Interner.constructorCode.operationRequest opcode arguments).item debug) key constructed taken owned remaining :=
  Prepared.caller_input host budget allocator opcode arguments debug before prepared constructed source address memory
    pointer values normalized taken key valid (prepare_success arguments before prepared source valid literal)
    typed admitted made allocated initialized transferred keyed live unique

/-- Empty literals have no array frame. Every nonempty literal is retired only
after the complete constructor returns ordinarily; rejection retains its world. -/
def returned (values : List NodeId) (mark : Nat) (ran : Except Fault NodeId × State σ) : Except Fault NodeId × World σ :=
  if values.isEmpty then (ran.1, ran.2.world) else TemporaryArguments.unwind mark ran

theorem returned_nonempty (values : List NodeId) (mark : Nat) (ran : Except Fault NodeId × State σ)
    (nonempty : values.isEmpty = false) : returned values mark ran = TemporaryArguments.unwind mark ran := by
  simp only [returned, nonempty, Bool.false_eq_true, ↓reduceIte]

theorem returned_rejected (values : List NodeId) (mark : Nat) (ran : Except Fault NodeId × State σ)
    (rejected : ordinary ran.1 = false) : returned values mark ran = (ran.1, ran.2.world) := by
  simp only [returned, TemporaryArguments.unwind, rejected, Bool.false_eq_true, ↓reduceIte]
  split <;> rfl

def operation (external : External σ) (budget allocator : Nat)
    (p : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives σ)
    (q : Caller.Queries) (opcode : Opcode) (values : List NodeId) (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId :=
  fun before => match prepare values before with
  | (.error fault, reached) => (.error fault, reached)
  | (.ok source, prepared) => returned values before.memory.memory.nextId
      (ConstructorItem.operation external budget allocator (p source) q source opcode values debug prepared)

theorem operation_prepared (external : External σ) (budget allocator : Nat)
    (p : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives σ)
    (q : Caller.Queries) (opcode : Opcode) (values : List NodeId) (debug : AssemblyItem.Fields.Values)
    (before prepared : World σ) (source : View) (ran : prepare values before = (.ok source, prepared)) :
    operation external budget allocator p q opcode values debug before = returned values before.memory.memory.nextId
      (ConstructorItem.operation external budget allocator (p source) q source opcode values debug prepared) := by
  simp only [operation, ran]

theorem operation_rejected (external : External σ) (budget allocator : Nat)
    (p : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives σ)
    (q : Caller.Queries) (opcode : Opcode) (values : List NodeId) (debug : AssemblyItem.Fields.Values)
    (before reached : World σ) (fault : Fault) (ran : prepare values before = (.error fault, reached)) :
    operation external budget allocator p q opcode values debug before = (.error fault, reached) := by
  simp only [operation, ran]

theorem operation_item_rejected (external : External σ) (budget allocator : Nat)
    (p : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives σ)
    (q : Caller.Queries) (opcode : Opcode) (values : List NodeId) (debug : AssemblyItem.Fields.Values)
    (before prepared reached : World σ) (source : View) (fault : Fault)
    (literal : prepare values before = (.ok source, prepared))
    (item : ConstructorItem.prepare (Interner.constructorCode.operationRequest opcode values).item debug prepared = (.error fault, reached))
    (rejected : ordinary (.error fault : Except Fault NodeId) = false) :
    operation external budget allocator p q opcode values debug before = (.error fault, reached) := by
  rw [operation_prepared _ _ _ _ _ _ _ _ _ _ _ literal]
  unfold ConstructorItem.operation
  rw [ConstructorItem.invoke_rejected _ _ _ _ _ _ _ _ _ _ _ item]
  exact returned_rejected values before.memory.memory.nextId _ rejected

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.Arguments
