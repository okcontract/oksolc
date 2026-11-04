/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeGraph
import Compiler.Extraction.InternerNativeRecursion

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ConstructorItem

/-- A source operation query and the same reached native graph derive every
indexed initializer load. The reader ignores its logical annotation; a wrong
annotation therefore cannot supply the result. -/
theorem Facts.operand {safety : Bool} {allocator owner capacity : Nat} {data : Compiler.ZigAir.Memory.Address}
    {world : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity world rows) (id : NodeId) (opcode : Opcode)
    (source : ArgumentSlice) (query : Storage.operationProgram.run rows id opcode = .ok (some source))
    (index : Nat) (inside : index < source.items.length) (annotation : NodeId) :
    Operation.run world.memory.memory (Owner.headerAddress ⟨owner, 0⟩) id opcode =
      .ok (.ok (some (Operation.returned source))) ∧
    NativeRecursion.operand source index annotation world = (.ok source.items[index], world) := by
  have observed := BorrowedQuery.Native.observed allocator id opcode world rows facts.projected facts.valid facts.resident
  rw [query] at observed
  have good := BorrowedQuery.accepted_good allocator id opcode world source facts.valid observed
  refine ⟨?_, ShiftInput.operand_good _ _ _ good index inside⟩
  exact (facts.operations id opcode).trans (by rw [query]; rfl)

/-- Proper children can append representatives and relocate their backing.
The reached graph facts and exact row prefix derive later loads through the
original operand allocation; no final Good or cached native read is assumed. -/
theorem Facts.operand_after_append {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {world : World (Publication.Effects σ)}
    (before added : List Storage.Cell)
    (facts : Facts safety allocator owner data capacity world (before ++ added))
    (id : NodeId) (opcode : Opcode) (source : ArgumentSlice)
    (query : Storage.operationProgram.run before id opcode = .ok (some source))
    (index : Nat) (inside : index < source.items.length) (annotation : NodeId) :
    NativeRecursion.operand source index annotation world = (.ok source.items[index], world) := by
  have retained := Storage.operation_after_append before added id opcode source query
  exact (facts.operand id opcode source retained index inside annotation).2

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
