/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerOrigin
import Compiler.Extraction.InternerOwnedProofs
import Compiler.Extraction.InternerCallerLookupRouting

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- An admitted initialized take can fail only while duplicating a borrow.
Its failed allocation preserves native storage and registry, while allocator
effects remain the actual reached effects. -/
theorem take_failed (external : External σ) (allocator : Nat) (source : View)
    (request : Interner.Request) (values : List NodeId) (prepared reached : State σ) (fault : Fault)
    (initialized : Initialized allocator source request (.ok values, prepared))
    (admitted : Admitted external) (failed : take external allocator prepared = (.error fault, reached)) :
    fault = .language .outOfMemory ∧ reached.world.graph = prepared.world.graph ∧
      reached.world.memory.memory = prepared.world.memory.memory ∧ reached.world.memory.heap = prepared.world.memory.heap ∧
      reached.scope = prepared.scope ∧ reached.scope.slice = none ∧
      ReadyToClose allocator source request.arguments reached := by
  obtain ⟨handle, scope, ready, _, _⟩ := initialized
  obtain ⟨result, memory, taken, post⟩ := take_refines external allocator source request.arguments handle prepared.world.memory ready admitted
  have lookup : prepared.scope.lookup = some handle := congrArg Local.lookup scope
  simp only [take, lookup, taken] at failed
  cases result with
  | ok pair => cases failed
  | error failure =>
    cases failure with
    | outOfMemory =>
      have same := Prod.mk.inj failed
      have errorEq := Except.error.inj same.1
      have stateEq := same.2
      subst reached
      cases errorEq
      refine ⟨rfl, rfl, post.2.2.1, post.2.1, rfl, congrArg Local.slice scope, ?_⟩
      refine ⟨⟨post.2.2.2.valid, post.2.2.2.source⟩, ⟨handle, lookup, post.1⟩, ?_, ?_⟩
      · intro slice impossible
        rw [scope] at impossible
        cases impossible
      · intro slice impossible
        rw [scope] at impossible
        cases impossible
    | allocation | preparation | release => exact False.elim post

/-- The initializer's original storage frame survives failed duplication.
Detached cleanup retains the reached world, including the allocation attempt's
effects. No recursive or insertion callback is reached. -/
theorem finish_take_failed (external : External σ) (budget allocator : Nat) (source : View)
    (request : Interner.Request) (before : World σ) (memory : Compiler.ZigAir.Memory.State)
    (pointer : Compiler.ZigAir.Memory.Value) (values : List NodeId) (prepared reached : State σ) (fault : Fault)
    (good : Good source request.arguments before) (admitted : Admitted external)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (initialized : initLookup external budget allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))
    (failed : take external allocator prepared = (.error fault, reached)) :
    ∃ after, fault = .language .outOfMemory ∧
      finish external allocator (.error fault : Except Fault NodeId) reached = (.error fault, after) ∧
      after.world = reached.world ∧ Good source request.arguments after.world ∧ Closed after.scope ∧
      after.world.graph = before.graph ∧
      (∀ id cell, before.memory.memory.heap.lookup id = some cell → after.world.memory.memory.heap.lookup id = some cell) ∧
      (∀ id block, before.memory.heap id = some block → after.world.memory.heap id = some block) ∧
      normalizeCode.run InsertionSort.sortIds request.item request.arguments = some values := by
  obtain ⟨ready, graph, native, registry⟩ := initialize_origin external budget allocator source request before memory pointer
    values prepared good admitted allocated initialized
  obtain ⟨oom, sameGraph, sameNative, sameRegistry, _, noSlice, close⟩ :=
    take_failed external allocator source request values prepared reached fault ready admitted failed
  subst fault
  obtain ⟨after, finished, afterGood, closed, _, kept, _⟩ := finish_ready external allocator source request.arguments reached
    (.error (.language .outOfMemory) : Except Fault NodeId) close rfl
  have same := kept noSlice
  obtain ⟨_, _, _, _, normalized⟩ := ready
  refine ⟨after, rfl, finished, same, afterGood, closed,
    (congrArg World.graph same).trans (sameGraph.trans graph), ?_, ?_, normalized⟩
  · intro id cell found
    rw [same, sameNative]
    exact native id cell found
  · intro id block found
    rw [same, sameRegistry]
    exact registry id block found

theorem find_take_failed (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Queries)
    (source buffer : View) (request : Interner.Request) (before : World σ)
    (values : List NodeId) (prepared reached : State σ) (fault : Fault) (key : Key) (deterministic : Bool)
    (room : q.atCapacity before.graph = false)
    (initialized : initLookup external budget allocator source buffer request ⟨before, { lookup := none }⟩ = (.ok values, prepared))
    (classified : q.deterministic request.item = .ok deterministic)
    (keyed : Interner.makeKey request values = .ok key)
    (missed : deterministic = true → before.graph.table key = none)
    (failed : take external allocator prepared = (.error fault, reached)) :
    find external budget allocator p q source buffer request before =
      finish external allocator (.error fault : Except Fault NodeId) reached := by
  obtain ⟨selected, made, routed⟩ := find_initialized external budget allocator p q source buffer request before values prepared room initialized
  have same : selected = key := Except.ok.inj (made.symm.trans keyed)
  subst selected
  rw [classified] at routed
  cases deterministic with
  | false => simpa only [Bool.false_eq_true, ↓reduceIte, Interner.FindCode.controlOwned, execution, OwnedCall.execution,
      failed, bind, Effect.bind] using routed
  | true => simpa only [↓reduceIte, missed rfl, Interner.FindCode.controlOwned, execution, OwnedCall.execution,
      failed, bind, Effect.bind] using routed

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller
