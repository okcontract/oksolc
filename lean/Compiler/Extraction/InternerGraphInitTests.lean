/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.GraphInitProgram
import Compiler.Extraction.InternerConstructorFrameTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.GraphInit.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul

theorem source_initializer (allocator : Nat) (before : Session σ) (meaning : Meaning)
    (valid : Valid before) :
    (zigInit allocator before).1 = allocator ∧ (zigInit allocator before).2.memory = before ∧
    Valid (zigInit allocator before).2.memory ∧ Interner.Invariant meaning (zigInit allocator before).2.graph ∧
    Memory.GraphResident allocator (zigInit allocator before).2.memory.heap [] ∧
    (zigInit allocator before).2.graph.representatives = some [] :=
  initialize_verified allocator before meaning valid

theorem source_queries (allocator : Nat) (before : Session σ) (id : NodeId) (opcode : Opcode) (key : Key) :
    Interner.Queries.queries.atCapacity (zigInit allocator before).2.graph = false ∧
    Interner.Queries.queries.validate id (zigInit allocator before).2.graph = .error .invalidId ∧
    (Interner.representativeReads (zigInit allocator before).2.graph).constant id = .ok none ∧
    BorrowedQuery.observe allocator id opcode (zigInit allocator before).2 = .ok none ∧
    (zigInit allocator before).2.graph.table key = none :=
  initial_queries allocator before id opcode key

def caller := Normalization.Tests.original
def initialized := (zigInit 7 caller).2

theorem existing_storage_is_unchanged :
    initialized.memory = caller ∧ initialized.memory.memory.nextId = caller.memory.nextId ∧
    initialized.memory.memory.nextAddress = caller.memory.nextAddress ∧
    initialized.memory.heap 2 = caller.heap 2 ∧ initialized.memory.effects = caller.effects :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem graph_starts_empty : initialized.graph.representatives = some [] ∧
    initialized.graph.allocationCursor = 0 ∧ initialized.graph.read 0 = none ∧
    initialized.graph.read 0xFFFFFFFF = none := ⟨rfl, rfl, rfl, rfl⟩

def root (effects : σ) : Session σ := ⟨fun _ => none, {}, effects⟩

theorem root_valid (effects : σ) : Valid (root effects) := by
  refine ⟨by rfl, ?_, ?_⟩
  · intro allocator id values nonempty impossible
    cases impossible
  · intro id block impossible
    cases impossible

theorem root_initialized (allocator : Nat) (effects : σ) (meaning : Meaning) :
    Valid (zigInit allocator (root effects)).2.memory ∧
    Interner.Invariant meaning (zigInit allocator (root effects)).2.graph ∧
    (zigInit allocator (root effects)).2.memory.effects = effects :=
  ⟨(source_initializer allocator (root effects) meaning (root_valid effects)).2.2.1,
    (source_initializer allocator (root effects) meaning (root_valid effects)).2.2.2.1, rfl⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.GraphInit.Tests
