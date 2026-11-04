/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerTemporaryUnary

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryUnary.BorrowedInput
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul Compiler.ZigAir.Memory.WordArray

/-- An anonymous initializer reads its borrowed operand before allocating the
temporary. Bounds and memory failures reject without an allocation or call. -/
def invoke (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries)
    (opcode : Opcode) (source : View) (index : Nat) : GraphAction σ NodeId := fun before =>
  if index < source.length then
    match TemporaryMemory.readId before.memory.memory source index with
    | .error fault => (.error (.memory (.preparation (.memory fault))), before)
    | .ok operand => TemporaryUnary.invoke external budget allocator p q opcode operand before
  else (.error (.memory (.preparation (.memory .sourceBounds))), before)

theorem invoke_of_load (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries)
    (opcode : Opcode) (source : View) (index : Nat) (operand : NodeId) (before : World σ)
    (inside : index < source.length)
    (loaded : Compiler.ZigAir.Memory.load before.memory.memory (source.pointer index) = .ok (number operand)) :
    invoke external budget allocator p q opcode source index before =
      TemporaryUnary.invoke external budget allocator p q opcode operand before := by
  simp only [invoke, inside, ↓reduceIte, TemporaryMemory.readId_of_load _ _ _ _ loaded]

theorem invoke_read_error (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries)
    (opcode : Opcode) (source : View) (index : Nat) (before : World σ) (fault : Compiler.ZigAir.Memory.Fault)
    (inside : index < source.length) (failed : TemporaryMemory.readId before.memory.memory source index = .error fault) :
    invoke external budget allocator p q opcode source index before =
      (.error (.memory (.preparation (.memory fault))), before) := by
  simp only [invoke, inside, ↓reduceIte, failed]

theorem invoke_verified (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries)
    (opcode : Opcode) (source : View) (values : List NodeId) (index : Nat) (inside : index < values.length)
    (before : World σ) (pointer : Compiler.ZigAir.Memory.Value) (allocated : Compiler.ZigAir.Memory.State)
    (other : Meaning) (value : Word) (initial : Valid before.memory)
    (represented : Represents before.memory.memory source values)
    (allocation : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 1 word) = .ok (pointer, allocated))
    (admitted : Admitted external) (ownership : ∀ source values, OwnedCall.Contracts allocator source values p)
    (contracts : ∀ source values, Semantic.Contracts allocator source values (Folding.wordMeaning other) p)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (evaluated : (Interner.constructorCode.operationRequest opcode [values[index]]).item.eval
      (Folding.wordMeaning other) before.graph.read [values[index]] Interner.constructorCode.sequence = some value) :
    ordinary (invoke external budget allocator p q opcode source index before).1 = true →
      Valid (invoke external budget allocator p q opcode source index before).2.memory ∧
      Semantic.Ensures (Folding.wordMeaning other) before.graph
        (invoke external budget allocator p q opcode source index before).1
        (invoke external budget allocator p q opcode source index before).2.graph
        (fun id graph => graph.read id = some value) := by
  rw [invoke_of_load external budget allocator p q opcode source index values[index] before
    (represented.1 ▸ inside) (represented.2 index inside)]
  exact TemporaryUnary.invoke_verified external budget allocator p q opcode values[index] before pointer allocated
    other value initial allocation admitted ownership contracts valid evaluated

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryUnary.BorrowedInput
