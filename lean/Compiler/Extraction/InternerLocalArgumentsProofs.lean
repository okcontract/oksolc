/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.LocalArgumentsProgram

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.LocalArguments
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul Compiler.ZigAir.Memory.WordArray

theorem first_error (source : View) (selected : Nat) (repeated : NodeId) (repeatedIsFirst : Bool)
    (before reached : World σ) (fault : Fault) (failed : copy source before = (.error fault, reached)) :
    zigLocal source selected repeated repeatedIsFirst before = (.error fault, reached) := by
  simp only [zigLocal, failed]

theorem after_copy (source target : View) (selected : Nat) (repeated : NodeId) (repeatedIsFirst : Bool)
    (before initialized : World σ) (copied : copy source before = (.ok target, initialized)) :
    zigLocal source selected repeated repeatedIsFirst before =
      if repeatedIsFirst then overwrite target selected repeated initialized else (.ok target, initialized) := by
  simp only [zigLocal, copied]

/-- Both the aggregate initializer and optional overwrite retain the actual
local allocation's type, permission and stack lifetime. -/
theorem prepare_storage (source target : View) (selected : Nat) (repeated : NodeId)
    (repeatedIsFirst : Bool) (before after : World σ)
    (ran : zigLocal source selected repeated repeatedIsFirst before = (.ok target, after)) :
    ∃ cell, after.memory.memory.heap.lookup target.allocation = some cell ∧
      cell.type = .array 2 word ∧ cell.writable = true ∧ cell.stack = true := by
  cases copied : copy source before with
  | mk result initialized =>
    cases result with
    | error fault => simp only [zigLocal, copied, Prod.mk.injEq] at ran; cases ran.1
    | ok view =>
      have storage := (copy_storage source view before initialized copied).2
      cases repeatedIsFirst with
      | false =>
        simp only [zigLocal, copied, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq, Except.ok.injEq] at ran
        cases ran.1
        cases ran.2
        exact storage
      | true =>
        simp only [zigLocal, copied, ↓reduceIte] at ran
        have written := overwrite_success view target selected repeated initialized after ran
        obtain ⟨cell, found, typed, writable, stack⟩ := storage
        obtain ⟨updated, kept, shape⟩ := written.2 view.allocation cell found
        rw [written.1]
        exact ⟨updated, kept, shape.2.1.trans typed, shape.2.2.1.trans writable, shape.2.2.2.trans stack⟩

/-- All initialization, private identity and optional-write permission follow
the same reached allocation and stores. Source/query correctness is an initial
borrow obligation; no final Good, writable or initialized-local premise is used. -/
theorem prepare_verified (source : View) (left right repeated : NodeId) (selected : Nat) (repeatedIsFirst : Bool)
    (before : World σ) (pointer : Compiler.ZigAir.Memory.Value) (allocated : Compiler.ZigAir.Memory.State)
    (valid : Valid before.memory) (represented : Represents before.memory.memory source [left, right])
    (inside : selected < 2)
    (allocation : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, allocated)) :
    ∃ after, zigLocal source selected repeated repeatedIsFirst before = (.ok ⟨before.memory.memory.nextId, 0, 2⟩, after) ∧
      Good ⟨before.memory.memory.nextId, 0, 2⟩ (if repeatedIsFirst then [left, right].set selected repeated else [left, right]) after ∧
      after.graph = before.graph ∧ after.memory.heap = before.memory.heap ∧ after.memory.effects = before.memory.effects ∧
      after.memory.memory.nextId = before.memory.memory.nextId + 1 ∧
      (∀ id cell, before.memory.memory.heap.lookup id = some cell → after.memory.memory.heap.lookup id = some cell) := by
  let target : View := ⟨before.memory.memory.nextId, 0, 2⟩
  obtain ⟨initialized, copied, good, graph, heap, effects, counter, frame, cap, unregistered⟩ :=
    copy_verified source left right before pointer allocated valid represented allocation
  cases repeatedIsFirst with
  | false =>
    exact ⟨initialized, by simp only [after_copy _ _ _ _ _ _ _ copied, Bool.false_eq_true, ↓reduceIte],
      good, graph, heap, effects, counter, frame⟩
  | true =>
    obtain ⟨after, written, finalGood, finalGraph, finalHeap, finalEffects, finalCounter, kept⟩ :=
      overwrite_verified target [left, right] selected repeated initialized good unregistered cap inside
    refine ⟨after, ?_, finalGood, finalGraph.trans graph, finalHeap.trans heap, finalEffects.trans effects,
      finalCounter.trans counter, ?_⟩
    · simpa only [after_copy _ _ _ _ _ _ _ copied, ↓reduceIte] using written
    · intro id cell found
      have older := (Compiler.ZigAir.Memory.valid_lookup _ _ _ valid.memory found).1
      exact (kept id (by dsimp [target]; omega)).trans (frame id cell found)

/-- The logical IDs annotate the source view; preparation still reads and
copies the native words. Their agreement is discharged from the initial borrow
in invoke_verified, rather than assumed for the completed local. -/
def invoke (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries)
    (opcode : Opcode) (source : View) (left right repeated : NodeId) (selected : Nat) (repeatedIsFirst : Bool) :
    GraphAction σ NodeId := fun before =>
  match zigLocal source selected repeated repeatedIsFirst before with
  | (.error fault, reached) => (.error fault, reached)
  | (.ok target, prepared) => TemporaryArguments.unwind before.memory.memory.nextId
    (ConstructorFrame.operation external budget allocator p q target opcode
      (if repeatedIsFirst then [left, right].set selected repeated else [left, right]) prepared)

theorem invoke_preparation_error (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Caller.Queries) (opcode : Opcode) (source : View) (left right repeated : NodeId)
    (selected : Nat) (repeatedIsFirst : Bool) (before reached : World σ) (fault : Fault)
    (failed : zigLocal source selected repeated repeatedIsFirst before = (.error fault, reached)) :
    invoke external budget allocator p q opcode source left right repeated selected repeatedIsFirst before =
      (.error fault, reached) := by
  simp only [invoke, failed]

theorem invoke_verified (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries)
    (opcode : Opcode) (source : View) (left right repeated : NodeId) (selected : Nat) (repeatedIsFirst : Bool)
    (before : World σ) (pointer : Compiler.ZigAir.Memory.Value) (allocated : Compiler.ZigAir.Memory.State)
    (other : Meaning) (value : Word) (initial : Valid before.memory)
    (represented : Represents before.memory.memory source [left, right]) (inside : selected < 2)
    (allocation : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, allocated))
    (admitted : Admitted external) (ownership : ∀ source values, OwnedCall.Contracts allocator source values p)
    (contracts : ∀ source values, Semantic.Contracts allocator source values (Folding.wordMeaning other) p)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (evaluated : (Interner.constructorCode.operationRequest opcode
      (if repeatedIsFirst then [left, right].set selected repeated else [left, right])).item.eval
        (Folding.wordMeaning other) before.graph.read
        (if repeatedIsFirst then [left, right].set selected repeated else [left, right])
        Interner.constructorCode.sequence = some value) :
    ordinary (invoke external budget allocator p q opcode source left right repeated selected repeatedIsFirst before).1 = true →
      Valid (invoke external budget allocator p q opcode source left right repeated selected repeatedIsFirst before).2.memory ∧
      Semantic.Ensures (Folding.wordMeaning other) before.graph
        (invoke external budget allocator p q opcode source left right repeated selected repeatedIsFirst before).1
        (invoke external budget allocator p q opcode source left right repeated selected repeatedIsFirst before).2.graph
        (fun id graph => graph.read id = some value) := by
  obtain ⟨prepared, initialized, good, graph, _⟩ :=
    prepare_verified source left right repeated selected repeatedIsFirst before pointer allocated initial represented inside allocation
  have checked := ConstructorFrame.operation_verified external budget allocator p q
    ⟨before.memory.memory.nextId, 0, 2⟩ opcode
    (if repeatedIsFirst then [left, right].set selected repeated else [left, right]) prepared other value
    good admitted (ownership _ _) (contracts _ _) (graph.symm ▸ valid) (graph.symm ▸ evaluated)
  simp only [invoke, initialized]
  intro completed
  have post := TemporaryArguments.unwind_verified before.memory.memory.nextId (Folding.wordMeaning other)
    ⟨before.memory.memory.nextId, 0, 2⟩
    (if repeatedIsFirst then [left, right].set selected repeated else [left, right]) prepared _ value checked completed
  exact ⟨post.1, graph ▸ post.2.2⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.LocalArguments
