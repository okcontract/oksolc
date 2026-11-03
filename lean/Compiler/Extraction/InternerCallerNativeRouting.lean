/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionCapacityCompletion
import Compiler.Extraction.InternerConstructorFrame
import Compiler.Extraction.InternerQueries
import Compiler.Extraction.InternerCallerLookupRouting

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- Execute the complete caller prefix, including the actual cache decision,
before entering the owned miss branch. The take and normalization observations
are for this execution; no frame or recursive preservation premise is used. -/
theorem find_after_take (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Queries)
    (source buffer : View) (request : Interner.Request) (before : World σ) (values : List NodeId)
    (prepared taken : State σ) (key : Key) (deterministic : Bool)
    (room : q.atCapacity before.graph = false)
    (initialized : initLookup external budget allocator source buffer request ⟨before, { lookup := none }⟩ = (.ok values, prepared))
    (classified : q.deterministic request.item = .ok deterministic)
    (made : Interner.makeKey request values = .ok key)
    (missed : deterministic = true → before.graph.table key = none)
    (transferred : take external allocator prepared = (.ok (), taken)) :
    find external budget allocator p q source buffer request before =
      (let ran := Interner.findCode.controlMiss (execution external budget allocator p q source buffer)
         request key deterministic taken
       finish external allocator ran.1 ran.2) := by
  obtain ⟨selected, keyed, routed⟩ := find_initialized external budget allocator p q source buffer request before values prepared room initialized
  have same : selected = key := Except.ok.inj (keyed.symm.trans made)
  subst selected
  rw [classified] at routed
  cases deterministic with
  | false => simpa only [Bool.false_eq_true, ↓reduceIte, Interner.FindCode.controlOwned, execution, OwnedCall.execution,
      pure, Effect.pure, transferred, made, bind, Effect.bind, Except.mapError] using routed
  | true => simpa only [↓reduceIte, missed rfl, Interner.FindCode.controlOwned, execution, OwnedCall.execution,
      pure, Effect.pure, transferred, made, bind, Effect.bind, Except.mapError] using routed

/-- A cache hit returns before take, simplification and insertion, but still
runs the normalizer's actual outer cleanup. -/
theorem find_cached (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Queries)
    (source buffer : View) (request : Interner.Request) (before : World σ) (values : List NodeId)
    (prepared : State σ) (key : Key) (id : NodeId)
    (room : q.atCapacity before.graph = false)
    (initialized : initLookup external budget allocator source buffer request ⟨before, { lookup := none }⟩ = (.ok values, prepared))
    (classified : q.deterministic request.item = .ok true)
    (made : Interner.makeKey request values = .ok key) (found : before.graph.table key = some id) :
    find external budget allocator p q source buffer request before = finish external allocator (.ok id) prepared := by
  obtain ⟨selected, keyed, routed⟩ := find_initialized external budget allocator p q source buffer request before values prepared room initialized
  have same : selected = key := Except.ok.inj (keyed.symm.trans made)
  subst selected
  simpa only [classified, ↓reduceIte, found] using routed

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Supply the checked native insertion to the existing caller. Simplification
and publication retain their supplied production implementations. -/
def callerPrimitives (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (seed : Primitives (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ) := none) : Primitives (Publication.Effects σ) :=
  { seed with insert := fun key slice deterministic => insert ops allocate runtimeSafety allocator container source itemSource meaning input key slice deterministic growth }

/-- A completed simplifier miss passes its exact reached world to native
insertion, retaining the caller's local normalized descriptor. This equation
allows recursive mutations; it does not require the graph to remain unchanged. -/
theorem find_after_simplify (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (budget allocator container : Nat) (source buffer : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (meaning : Meaning) (input : AssemblyClone.NativeFields.ItemValue) (seed : Primitives (Publication.Effects σ))
    (q : Caller.Queries) (request : Interner.Request) (before reached : World (Publication.Effects σ))
    (values : List NodeId) (prepared taken : OwnedCall.State (Publication.Effects σ)) (key : Key) (normalized : ArgumentSlice)
    (growth : Option (Growth.Registered.Callbacks σ))
    (room : q.atCapacity before.graph = false)
    (initialized : Caller.initLookup (Publication.external ops.arguments) budget allocator source buffer request
      ⟨before, { lookup := none }⟩ = (.ok values, prepared))
    (classified : q.deterministic request.item = .ok true)
    (made : Interner.makeKey request values = .ok key) (missed : before.graph.table key = none)
    (transferred : take (Publication.external ops.arguments) allocator prepared = (.ok (), taken))
    (slice : taken.scope.slice = some normalized) (operation : request.item.kind = 1)
    (simplified : seed.simplify key normalized taken.world = (.ok none, reached)) :
    Caller.find (Publication.external ops.arguments) budget allocator
      (callerPrimitives ops allocate runtimeSafety allocator container source itemSource meaning input seed growth)
      q source buffer request before =
        finishInsertion ops allocate runtimeSafety allocator container source itemSource meaning input key true
          ⟨reached, taken.scope⟩ growth := by
  rw [Caller.find_after_take _ _ _ _ _ _ _ _ _ values prepared taken key true room initialized classified made (fun _ => missed) transferred]
  simp only [Interner.FindCode.controlMiss, Caller.execution, OwnedCall.execution, operation, beq_self_eq_true,
    Bool.and_self, ↓reduceIte, callerPrimitives, graph, slice, simplified, bind, Effect.bind,
    pure, Effect.pure, finishInsertion, handoff]

/-- Connect source scratch allocation, cache miss, normalization and the actual
simplifier result to the native insertion suffix and constructor-frame return.
Ordinary results unwind stack locals; rejection retains the reached state. The
simplifier may have changed any part of the graph and memory. -/
theorem CallerInput.find_after_simplify
    (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (budget allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (meaning : Meaning) (input : AssemblyClone.NativeFields.ItemValue) (seed : Primitives (Publication.Effects σ))
    (q : Caller.Queries) (request : Interner.Request) (before reached : World (Publication.Effects σ))
    (native : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (values : List NodeId) (prepared taken : OwnedCall.State (Publication.Effects σ))
    (key : Key) (normalized : ArgumentSlice) (lookup : Handle) (growth : Option (Growth.Registered.Callbacks σ))
    (entry : CallerInput allocator source itemSource request values input key before taken normalized lookup)
    (room : q.atCapacity before.graph = false)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, native))
    (initialized : Caller.initLookup (Publication.external ops.arguments) budget allocator source
      ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨{ before with memory := { before.memory with memory := native } }, { lookup := none }⟩ = (.ok values, prepared))
    (classified : q.deterministic request.item = .ok true)
    (made : Interner.makeKey request values = .ok key) (missed : before.graph.table key = none)
    (transferred : take (Publication.external ops.arguments) allocator prepared = (.ok (), taken))
    (operation : request.item.kind = 1)
    (simplified : seed.simplify key normalized taken.world = (.ok none, reached)) :
    ConstructorFrame.find (Publication.external ops.arguments) budget allocator
      (callerPrimitives ops allocate runtimeSafety allocator container source itemSource meaning input seed growth)
      q source request before =
        (let ran := finishInsertion ops allocate runtimeSafety allocator container source itemSource meaning input key true
           ⟨reached, taken.scope⟩ growth
         if ordinary ran.1 then
           (ran.1, { ran.2 with world := { ran.2.world with memory := { ran.2.world.memory with
             memory := Compiler.ZigAir.Memory.cleanup before.memory.memory.nextId ran.2.world.memory.memory } } })
         else ran) := by
  have routed := Native.find_after_simplify ops allocate runtimeSafety budget allocator container source
    ⟨before.memory.memory.nextId, 0, 2⟩ itemSource meaning input seed q request
    { before with memory := { before.memory with memory := native } } reached values prepared taken key normalized growth
    room initialized classified made missed transferred (by rw [entry.origin.scope]) operation simplified
  unfold ConstructorFrame.find
  simp only [room, Bool.false_eq_true, ↓reduceIte, allocated, routed]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
