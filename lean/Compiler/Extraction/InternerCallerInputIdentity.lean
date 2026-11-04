/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerQueries
import Compiler.Extraction.InternerCallerOrigin

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- The closed nondeterministic classifier skips normalization allocations.
Successful take therefore derives its exact slice from the original allocation
cursor, including the empty case. No completed descriptor is assumed. -/
theorem nondeterministic_taken (external : External σ) (budget allocator : Nat)
    (source buffer : View) (request : Interner.Request) (before : World σ)
    (values : List NodeId) (prepared called : State σ)
    (good : Good source request.arguments before) (admitted : Admitted external)
    (classified : Interner.Queries.queries.deterministic request.item = .ok false)
    (initialized : initLookup external budget allocator source buffer request
      ⟨before, { lookup := none }⟩ = (.ok values, prepared))
    (transferred : take external allocator prepared = (.ok (), called)) :
    called.scope.slice = some ⟨before.memory.memory.nextId, request.arguments⟩ := by
  have unsorted := Interner.Queries.nondeterministic_noncommutative request.item classified
  simp only [initLookup, unsorted, init, Bool.not_false, Bool.true_or, ↓reduceIte,
    Except.ok.injEq, Prod.mk.injEq] at initialized
  rcases initialized with ⟨rfl, rfl⟩
  obtain ⟨result, middle, ran, post⟩ := init_refines external budget allocator false source buffer request.arguments before.memory
    good.1 good.2 (by intro impossible; cases impossible) admitted
  simp only [init, Bool.not_false, Bool.true_or, ↓reduceIte, Prod.mk.injEq] at ran
  rcases ran with ⟨rfl, rfl⟩
  obtain ⟨result, after, ran, ready⟩ := take_refines external allocator source request.arguments
    ⟨source, request.arguments, none⟩ before.memory post.1 admitted
  simp only [take, ran] at transferred
  cases result with
  | error fault => cases transferred
  | ok pair =>
    rcases pair with ⟨slice, remaining⟩
    cases transferred
    have identity : slice = ⟨before.memory.memory.nextId, request.arguments⟩ := by
      cases slice
      simp only [ArgumentSlice.mk.injEq]
      exact ⟨ready.freshBorrow rfl, ready.values⟩
    exact congrArg some identity

/-- Actual scratch allocation, initialization, take and key construction bind
the entry replay inputs. A sorted slice may have another address; that address
is irrelevant to deterministic insertion and is not constrained here. -/
theorem taken_replay_inputs (external : External σ) (budget allocator : Nat)
    (source : View) (request : Interner.Request) (before : World σ)
    (memory : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (values : List NodeId) (prepared called : State σ) (key : Key) (slice : ArgumentSlice) (deterministic : Bool)
    (good : Good source request.arguments before) (admitted : Admitted external)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (initialized : initLookup external budget allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))
    (transferred : take external allocator prepared = (.ok (), called))
    (classified : Interner.Queries.queries.deterministic request.item = .ok deterministic)
    (made : Interner.makeKey request values = .ok key) (present : called.scope.slice = some slice) :
    slice.items = key.arguments ∧
      (deterministic = false → slice.address = before.memory.memory.nextId + 1) := by
  obtain ⟨actual, remaining, origin⟩ := take_origin external budget allocator source request before memory pointer values prepared called
    good admitted allocated initialized transferred
  have same : actual = slice := Option.some.inj ((congrArg Local.slice origin.scope).symm.trans present)
  subst actual
  refine ⟨origin.aligned.trans (key_arguments request values key made).symm, ?_⟩
  intro notDeterministic
  subst deterministic
  have scratch := caller_buffer before.memory memory pointer source request.arguments good.1 good.2 allocated
  have descriptor := nondeterministic_taken external budget allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request
    { before with memory := { before.memory with memory } } values prepared called ⟨scratch.1, scratch.2.1⟩
    admitted classified initialized transferred
  have exactSlice := Option.some.inj (present.symm.trans descriptor)
  have next := (Compiler.ZigAir.Memory.allocate_pointer before.memory.memory (.array 2 word) pointer memory allocated).2
  exact (congrArg ArgumentSlice.address exactSlice).trans next

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller
