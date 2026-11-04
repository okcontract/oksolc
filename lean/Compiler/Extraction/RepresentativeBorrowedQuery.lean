/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerBorrowedQuery
import Compiler.Extraction.RepresentativeOperationProofs

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.BorrowedQuery.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- Residency and the reached typed session make the existing checker complete
for every logical query outcome. Misses and optional faults keep their distinct
source results; no unbacked hit is silently turned into a miss. -/
theorem observed (allocator : Nat) (id : NodeId) (opcode : BitVec 8) (before : World σ)
    (cells : List Storage.Cell) (present : before.graph.representatives = some cells)
    (valid : Valid before.memory) (resident : Memory.GraphResident allocator before.memory.heap cells) :
    observe allocator id opcode before = (operationProgram.run cells id opcode).mapError Rejection.query := by
  have reads : (Interner.representativeReads before.graph).operation id opcode = operationProgram.run cells id opcode := by
    simp only [Interner.representativeReads, present, Nested.storageReads]
  cases result : operationProgram.run cells id opcode with
  | error fault => simp only [observe, reads, result, Except.mapError, bind, Except.bind]
  | ok found =>
    cases found with
    | none => simp only [observe, reads, result, Except.mapError, bind, Except.bind]
    | some slice =>
      have accepted := resident_accepted allocator id opcode before cells slice present valid resident (reads.trans result)
      simpa only [result, Except.mapError] using accepted

/-- A native descriptor does not determine its contents by itself. The proved
native/logical query correspondence identifies the graph slice; residency and
the same reached session then derive its checked contents and constructor Good.
The agreement premise is supplied by the actual append/query theorems. -/
theorem accepted (allocator : Nat) (header : Compiler.ZigAir.Memory.Address) (id : NodeId) (opcode : BitVec 8)
    (before : World σ) (cells : List Storage.Cell) (value : Compiler.ZigAir.Memory.Value)
    (present : before.graph.representatives = some cells) (valid : Valid before.memory)
    (resident : Memory.GraphResident allocator before.memory.heap cells)
    (agreement : RepresentativeArray.Operation.run before.memory.memory header id opcode =
      .ok ((operationProgram.run cells id opcode).map (Option.map RepresentativeArray.Operation.returned)))
    (native : RepresentativeArray.Operation.run before.memory.memory header id opcode = .ok (.ok (some value))) :
    ∃ slice, value = RepresentativeArray.Operation.returned slice ∧
      observe allocator id opcode before = .ok (some slice) ∧ Good (view slice) slice.items before := by
  have mapped := Except.ok.inj (agreement.symm.trans native)
  cases result : operationProgram.run cells id opcode with
  | error fault => simp only [result, Except.map] at mapped; contradiction
  | ok found =>
    cases found with
    | none => simp only [result, Except.map, Option.map_none] at mapped; cases Except.ok.inj mapped
    | some slice =>
      have same : RepresentativeArray.Operation.returned slice = value := by
        simpa only [result, Except.map, Option.map_some, Except.ok.injEq, Option.some.injEq] using mapped
      have checked := observed allocator id opcode before cells present valid resident
      rw [result, Except.mapError] at checked
      exact ⟨slice, same.symm, checked, accepted_good allocator id opcode before slice valid checked⟩

/-- A proposition over the existing registry, native memory and logical rows.
It adds no graph snapshot or memory representation. Every matching source-world
projection observes the same results and obtains Good for actual native hits. -/
def AcceptedQueries (allocator : Nat) (header : Compiler.ZigAir.Memory.Address) (cells : List Storage.Cell)
    (memory : Session σ) : Prop :=
  (∀ id opcode, RepresentativeArray.Operation.run memory.memory header id opcode =
    .ok ((operationProgram.run cells id opcode).map (Option.map RepresentativeArray.Operation.returned))) ∧
  ∀ graph : Interner.Heap, graph.representatives = some cells →
    (∀ id opcode, observe allocator id opcode (⟨graph, memory⟩ : World σ) =
      (operationProgram.run cells id opcode).mapError Rejection.query) ∧
    ∀ id opcode value, RepresentativeArray.Operation.run memory.memory header id opcode = .ok (.ok (some value)) →
      ∃ slice, value = RepresentativeArray.Operation.returned slice ∧
        observe allocator id opcode (⟨graph, memory⟩ : World σ) = .ok (some slice) ∧
        Good (view slice) slice.items (⟨graph, memory⟩ : World σ)

theorem of_resident (allocator : Nat) (header : Compiler.ZigAir.Memory.Address) (cells : List Storage.Cell)
    (memory : Session σ) (valid : Valid memory) (resident : Memory.GraphResident allocator memory.heap cells)
    (agreement : ∀ id opcode, RepresentativeArray.Operation.run memory.memory header id opcode =
      .ok ((operationProgram.run cells id opcode).map (Option.map RepresentativeArray.Operation.returned))) :
    AcceptedQueries allocator header cells memory := by
  refine ⟨agreement, fun graph present => ⟨fun id opcode => ?_, fun id opcode value hit => ?_⟩⟩
  · exact observed allocator id opcode ⟨graph, memory⟩ cells present valid resident
  · exact accepted allocator header id opcode ⟨graph, memory⟩ cells value present valid resident (agreement id opcode) hit

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.BorrowedQuery.Native
