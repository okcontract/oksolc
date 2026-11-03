/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeInput
import Compiler.Extraction.InternerCallerGraphCustody
import Compiler.Extraction.InternerConstructorSource

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray

/-- A query-selected operand supplies the actual borrowed constructor's source
admission after arbitrary representative appends. Native residency supplies its
contents and array provenance; graph/key separation supplies source privacy. -/
theorem Facts.source_after_append {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {world : World (Publication.Effects σ)}
    (before added : List Storage.Cell)
    (facts : Facts safety allocator owner data capacity world (before ++ added))
    (id : NodeId) (opcode : Opcode) (source : ArgumentSlice)
    (query : Storage.operationProgram.run before id opcode = .ok (some source)) :
    Represents world.memory.memory (view source) source.items ∧
      Caller.SourcePrivate (view source) world.memory.effects.keys ∧
      ArraySource (view source) world.memory.memory := by
  have retained := Storage.operation_after_append before added id opcode source query
  have observed := BorrowedQuery.Native.observed allocator id opcode world (before ++ added)
    facts.projected facts.valid facts.resident
  rw [retained] at observed
  have checked := BorrowedQuery.accepted allocator id opcode world source observed
  obtain ⟨live, represented, _⟩ := BorrowedQuery.slice_sound allocator source world.memory checked.2
  refine ⟨represented, ?_, ArraySource.registered facts.valid live⟩
  obtain ⟨row, found, _, _, returned⟩ := Storage.operation_found (before ++ added) id opcode source retained
  intro key old owned nonempty length alias
  apply facts.apart key old owned nonempty
  refine ⟨row, List.mem_of_getElem? found, ?_, ?_⟩
  · intro empty
    apply length
    rw [← returned]
    simp only [view, Storage.Cell.argumentSlice, empty, List.length_nil]
  · exact alias.symm.trans (congrArg ArgumentSlice.address returned).symm

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
