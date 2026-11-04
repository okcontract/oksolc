/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorItem

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- Both locals return in their actual nesting order. Marks are taken from
entry and reached preparation, not reconstructed from fixture allocation IDs. -/
def returnWorld (itemMark scratchMark : Nat) (world : World σ) : World σ :=
  let memory := Compiler.ZigAir.Memory.cleanup itemMark
    (Compiler.ZigAir.Memory.cleanup scratchMark world.memory.memory)
  { world with memory := { world.memory with memory } }

theorem returnWorld_valid (itemMark scratchMark : Nat) (world : World σ) (valid : Valid world.memory) :
    Valid (returnWorld itemMark scratchMark world).memory :=
  (valid.cleanup _ scratchMark).cleanup _ itemMark

theorem returnWorld_cell (before world : World σ) (scratchMark : Nat)
    (valid : Valid before.memory) (ordered : before.memory.memory.nextId ≤ scratchMark)
    (id : Nat) (native : Compiler.ZigAir.Memory.Allocation)
    (found : before.memory.memory.heap.lookup id = some native)
    (kept : world.memory.memory.heap.lookup id = some native) :
    (returnWorld before.memory.memory.nextId scratchMark world).memory.memory.heap.lookup id = some native := by
  have older := (Compiler.ZigAir.Memory.valid_lookup _ _ _ valid.memory found).1
  exact (Compiler.ZigAir.Memory.cleanup_lookup_older _ _ id older).trans
    ((Compiler.ZigAir.Memory.cleanup_lookup_older _ _ id (Nat.lt_of_lt_of_le older ordered)).trans kept)

/-- Existing parent allocations are older than both reached local frames.
This keeps every old cell, including stack borrows; registry/effects/graph
retention follows definitionally from the same return. -/
theorem returnWorld_frame (before world : World σ) (scratchMark : Nat)
    (valid : Valid before.memory) (ordered : before.memory.memory.nextId ≤ scratchMark)
    (frame : ∀ id native, before.memory.memory.heap.lookup id = some native →
      world.memory.memory.heap.lookup id = some native) :
    ∀ id native, before.memory.memory.heap.lookup id = some native →
      (returnWorld before.memory.memory.nextId scratchMark world).memory.memory.heap.lookup id = some native :=
  fun id native found => returnWorld_cell before world scratchMark valid ordered id native found (frame id native found)

/-- Share the actual constructor-local and scratch return around every caller
outcome. Only ordinary results retire the reached locals; rejection retains
the complete reached state. -/
theorem invoke_after_scratch (external : External σ) (budget allocator : Nat)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives σ)
    (q : Caller.Queries) (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before constructed : World σ) (address : Compiler.ZigAir.Memory.Address)
    (pointer : Compiler.ZigAir.Memory.Value) (memory : Compiler.ZigAir.Memory.State)
    (made : prepare request.item debug before = (.ok address, constructed))
    (room : q.atCapacity constructed.graph = false)
    (allocated : Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) = .ok (pointer, memory)) :
    invoke external budget allocator p q source request debug before =
      (let ran := Caller.find external budget allocator (p address (input request.item debug)) q source
         ⟨constructed.memory.memory.nextId, 0, 2⟩ request
         { constructed with memory := { constructed.memory with memory } }
       if ordinary ran.1 then
         (ran.1, { ran.2 with world := returnWorld before.memory.memory.nextId constructed.memory.memory.nextId ran.2.world })
       else ran) := by
  rw [invoke_prepared _ _ _ _ _ _ _ _ _ _ _ made]
  simp only [ConstructorFrame.find, room, Bool.false_eq_true, ↓reduceIte, allocated]
  generalize Caller.find external budget allocator (p address (input request.item debug)) q source
    ⟨constructed.memory.memory.nextId, 0, 2⟩ request
    { constructed with memory := { constructed.memory with memory } } = ran
  rcases ran with ⟨result, reached⟩
  cases completed : ordinary result with
  | false => simp only [completed, Bool.false_eq_true, ↓reduceIte]
  | true => simp only [completed, ↓reduceIte]; rfl

/-- A cache hit shares constructor-local return with a taken miss, but never
calls take, recursive simplification or insertion. The optional normalization
owner still passes through the actual outer cleanup. -/
theorem invoke_cached (external : External σ) (budget allocator : Nat)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives σ)
    (q : Caller.Queries) (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before constructed : World σ) (address : Compiler.ZigAir.Memory.Address)
    (pointer : Compiler.ZigAir.Memory.Value) (memory : Compiler.ZigAir.Memory.State)
    (values : List NodeId) (prepared : State σ) (key : Key) (id : NodeId)
    (made : prepare request.item debug before = (.ok address, constructed))
    (room : q.atCapacity constructed.graph = false)
    (allocated : Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) = .ok (pointer, memory))
    (initialized : Caller.initLookup external budget allocator source ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))
    (classified : q.deterministic request.item = .ok true)
    (keyed : Interner.makeKey request values = .ok key) (found : constructed.graph.table key = some id) :
    invoke external budget allocator p q source request debug before =
      (let done := OwnedCall.finish external allocator (.ok id) prepared
       if ordinary done.1 then
         (done.1, { done.2 with world := returnWorld before.memory.memory.nextId constructed.memory.memory.nextId done.2.world })
       else done) := by
  rw [invoke_after_scratch _ _ _ _ _ _ _ _ _ _ _ _ _ made room allocated,
    Caller.find_cached external budget allocator (p address (input request.item debug)) q source
      ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      { constructed with memory := { constructed.memory with memory } }
      values prepared key id room initialized classified keyed found]

/-- Route the actual constructor-local and caller prefix for arbitrary debug,
host, budget and allocator inputs. Ordinary return cleans the two reached local
frames; rejection retains the exact reached result, ownership and memory. -/
theorem invoke_after_take (external : External σ) (budget allocator : Nat)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives σ)
    (q : Caller.Queries) (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before constructed : World σ) (address : Compiler.ZigAir.Memory.Address)
    (pointer : Compiler.ZigAir.Memory.Value) (memory : Compiler.ZigAir.Memory.State)
    (values : List NodeId) (prepared taken : State σ) (key : Key) (deterministic : Bool)
    (made : prepare request.item debug before = (.ok address, constructed))
    (room : q.atCapacity constructed.graph = false)
    (allocated : Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) = .ok (pointer, memory))
    (initialized : Caller.initLookup external budget allocator source ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))
    (classified : q.deterministic request.item = .ok deterministic)
    (keyed : Interner.makeKey request values = .ok key)
    (missed : deterministic = true → constructed.graph.table key = none)
    (transferred : take external allocator prepared = (.ok (), taken)) :
    invoke external budget allocator p q source request debug before =
      (let ran := Interner.findCode.controlMiss
         (Caller.execution external budget allocator (p address (input request.item debug)) q source
           ⟨constructed.memory.memory.nextId, 0, 2⟩) request key deterministic taken
       let done := OwnedCall.finish external allocator ran.1 ran.2
       if ordinary done.1 then
         (done.1, { done.2 with world := { done.2.world with memory := { done.2.world.memory with
           memory := Compiler.ZigAir.Memory.cleanup before.memory.memory.nextId
             (Compiler.ZigAir.Memory.cleanup constructed.memory.memory.nextId done.2.world.memory.memory) } } })
       else done) := by
  have routed := Caller.find_after_take external budget allocator (p address (input request.item debug)) q source
    ⟨constructed.memory.memory.nextId, 0, 2⟩ request { constructed with memory := { constructed.memory with memory } }
    values prepared taken key deterministic room initialized classified keyed missed transferred
  rw [invoke_after_scratch _ _ _ _ _ _ _ _ _ _ _ _ _ made room allocated, routed]
  rfl

open Insertion Insertion.Native RepresentativeArray

/-- A constant bypasses recursive simplification. Its actual native insertion
outcome drives handoff, deferred cleanup and both constructor-local returns.
No successful insertion, ordinary result or final ownership is assumed. -/
theorem invoke_native_constant (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (budget allocator owner : Nat) (source : View) (meaning : Meaning)
    (seed : Primitives (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (q : Caller.Queries) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before constructed : World (Publication.Effects σ)) (address : Compiler.ZigAir.Memory.Address)
    (pointer : Compiler.ZigAir.Memory.Value) (memory : Compiler.ZigAir.Memory.State)
    (values : List NodeId) (prepared taken : State (Publication.Effects σ))
    (key : Key) (normalized : ArgumentSlice) (lookup : Handle)
    (entry : CallerInput allocator source address request values (input request.item debug) key constructed taken normalized lookup)
    (made : prepare request.item debug before = (.ok address, constructed))
    (room : q.atCapacity constructed.graph = false)
    (allocated : Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) = .ok (pointer, memory))
    (initialized : Caller.initLookup (Publication.external ops.arguments) budget allocator source
      ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))
    (classified : q.deterministic request.item = .ok true)
    (keyed : Interner.makeKey request values = .ok key)
    (missed : constructed.graph.table key = none)
    (transferred : take (Publication.external ops.arguments) allocator prepared = (.ok (), taken))
    (kind : request.item.kind = 2) :
    invoke (Publication.external ops.arguments) budget allocator
      (fun address native => callerPrimitives ops allocate safety allocator owner source address meaning native seed growth)
      q source request debug before =
      (let ran := Native.insert ops allocate safety allocator owner source address meaning
         (input request.item debug) key normalized true growth taken.world
       if ordinary ran.1 then
         let returned := Compiler.ZigAir.Memory.cleanup before.memory.memory.nextId
           (Compiler.ZigAir.Memory.cleanup constructed.memory.memory.nextId ran.2.memory.memory)
         (ran.1, ⟨{ ran.2 with memory := { ran.2.memory with memory := returned } },
           ⟨none, some normalized, true⟩⟩)
       else (ran.1, ⟨ran.2, ⟨some lookup, some normalized, true⟩⟩)) := by
  let p := fun address native => callerPrimitives ops allocate safety allocator owner source address meaning native seed growth
  have routed := invoke_after_take (Publication.external ops.arguments) budget allocator p q source request debug
    before constructed address pointer memory values prepared taken key true made room allocated initialized classified
    keyed (fun _ => missed) transferred
  have continued :
      (let ran := Interner.findCode.controlMiss
         (Caller.execution (Publication.external ops.arguments) budget allocator
           (p address (input request.item debug)) q source ⟨constructed.memory.memory.nextId, 0, 2⟩)
         request key true taken
       OwnedCall.finish (Publication.external ops.arguments) allocator ran.1 ran.2) =
      finishInsertion ops allocate safety allocator owner source address meaning (input request.item debug) key true taken growth := by
    simp only [Interner.FindCode.controlMiss, Caller.execution, OwnedCall.execution, kind,
      BitVec.reduceBEq, Bool.false_eq_true, Bool.true_and, ↓reduceIte, handoff, graph, entry.origin.scope,
      bind, Effect.bind, pure, Effect.pure, p, callerPrimitives, finishInsertion]
  dsimp only at routed continued
  rw [continued, entry.finish_native ops allocate safety allocator owner source address meaning request values
    (input request.item debug) key normalized lookup constructed taken true growth] at routed
  generalize Native.insert ops allocate safety allocator owner source address meaning (input request.item debug)
    key normalized true growth taken.world = ran at routed ⊢
  rcases ran with ⟨result, reached⟩
  cases completed : ordinary result <;> simpa only [completed, Bool.false_eq_true, ↓reduceIte] using routed

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem
