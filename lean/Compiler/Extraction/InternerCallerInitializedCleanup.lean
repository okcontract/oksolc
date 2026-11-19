/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerOrigin

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- Before take, the actual optional normalization owner is fresh relative to
all pre-scratch allocations. Close it once, retaining the original graph and
native/registry frame, including when initialization allocated a temporary. -/
theorem finish_initialized (external : External σ) (budget allocator : Nat) (source : View)
    (request : Interner.Request) (before : World σ) (memory : Compiler.ZigAir.Memory.State)
    (pointer : Compiler.ZigAir.Memory.Value) (values : List NodeId) (prepared : State σ)
    (result : Except Fault α) (good : Good source request.arguments before) (admitted : Admitted external)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (initialized : initLookup external budget allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))
    (completed : ordinary result = true) :
    ∃ after, finish external allocator result prepared = (result, after) ∧
      Good source request.arguments after.world ∧ OwnedCall.Closed after.scope ∧
      after.world.graph = before.graph ∧
      (∀ id cell, before.memory.memory.heap.lookup id = some cell → after.world.memory.memory.heap.lookup id = some cell) ∧
      (∀ id block, before.memory.heap id = some block → after.world.memory.heap id = some block) ∧
      normalizeCode.run InsertionSort.sortIds request.item request.arguments = some values := by
  obtain ⟨ready, graph, origin⟩ := initialize_origin_frame external budget allocator source request before memory pointer
    values prepared good admitted allocated initialized
  obtain ⟨handle, scope, ready, _, normalized⟩ := ready
  obtain ⟨closedMemory, closed, valid, represented, consumed, frame⟩ :=
    deinit_refines external allocator source request.arguments handle prepared.world.memory ready
  have post : Normalization.Closed external allocator source request.arguments .lookup handle prepared.world.memory
      (.ok .lookup) closedMemory :=
    ⟨valid, represented, ⟨rfl, consumed⟩, fun id _ found apart => ⟨(frame id apart).1.trans found, (frame id apart).2⟩⟩
  have kept := closed_frame external allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request.arguments .lookup
    handle before.memory prepared.world.memory closedMemory (.ok .lookup) good.1 ready (origin handle scope) post
  let after : State σ := ⟨{ prepared.world with memory := closedMemory }, { lookup := none }⟩
  refine ⟨after, ?_, ⟨valid, represented⟩, ⟨rfl, Or.inr rfl⟩, graph, ?_, kept.registry, normalized⟩
  · rcases prepared with ⟨world, locals⟩
    cases scope
    simp only [finish, completed, ↓reduceIte, cleanup, Bool.false_eq_true, deinit, closed]
    rfl
  · intro id cell found
    have older := (Compiler.ZigAir.Memory.valid_lookup _ _ _ good.1.memory found).1
    exact kept.memory id cell found (by dsimp only; omega)


end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller
