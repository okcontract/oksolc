/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerBorrowedQuery

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.GraphInit
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul

/-- The source's empty containers have no backing allocation or graph entry.
The existing representative, cache and typed-memory representations are reused.
The allocation cursor starts at zero; the caller's memory/effects are untouched. -/
def emptyGraph : Interner.Heap :=
  { read := Storage.readValue [], table := fun _ => none, representatives := some [] }

/-- Retain the supplied allocator identity, as the native object does. Native
initialization allocates nothing; it cannot reset the caller's lifetime history. -/
def run (allocator : Nat) (before : Session σ) : Nat × World σ :=
  (allocator, ⟨emptyGraph, before⟩)

theorem empty_invariant (meaning : Meaning) : Interner.Invariant meaning emptyGraph := by
  refine ⟨?_, rfl, coherent_empty meaning⟩
  intro key id impossible
  cases impossible

theorem initialize_verified (allocator : Nat) (before : Session σ) (meaning : Meaning)
    (valid : Valid before) :
    (run allocator before).1 = allocator ∧
    (run allocator before).2.memory = before ∧
    Valid (run allocator before).2.memory ∧
    Interner.Invariant meaning (run allocator before).2.graph ∧
    Memory.GraphResident allocator (run allocator before).2.memory.heap [] ∧
    (run allocator before).2.graph.representatives = some [] := by
  refine ⟨rfl, rfl, valid, empty_invariant meaning, ?_, rfl⟩
  intro cell impossible
  cases impossible

theorem initial_queries (allocator : Nat) (before : Session σ) (id : NodeId) (opcode : Opcode) (key : Key) :
    Interner.Queries.queries.atCapacity (run allocator before).2.graph = false ∧
    Interner.Queries.queries.validate id (run allocator before).2.graph = .error .invalidId ∧
    (Interner.representativeReads (run allocator before).2.graph).constant id = .ok none ∧
    BorrowedQuery.observe allocator id opcode (run allocator before).2 = .ok none ∧
    (run allocator before).2.graph.table key = none := by
  simp [run, emptyGraph, Interner.Queries.queries, Interner.representativeReads,
    Nested.storageReads, representativeProgram, constantProgram, operationProgram,
    Lookup.run, Bound.reject, ConstantRead.run, OperationRead.run, BorrowedQuery.observe,
    Except.map, Except.mapError, bind, Except.bind]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.GraphInit
