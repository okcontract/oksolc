/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeGraphFrame
import Compiler.Extraction.InternerNativeGraphMapWrites

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

namespace PrivateRegion

/-- Lift the existing native region reservation without inventing a logical
argument/vector entry. Actual typed memory, lifetime counters and allocator
effects are retained on success, OOM and verification rejection. Bucket layout,
initialization, ownership by a map and eventual release remain separate. -/
def reserve (type : Compiler.ZigAir.Memory.Ty) (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ)
    (before : World (Publication.Effects σ)) :
    Except Compiler.ZigAir.Memory.Fault (Option Compiler.ZigAir.Memory.Address) × World (Publication.Effects σ) :=
  let ((result, memory), effects) := Compiler.ZigAir.Memory.RegionAllocation.reserve
    before.memory.memory type allocate before.memory.effects.allocator
  (result, { before with memory := ⟨before.memory.heap, memory, ⟨before.memory.effects.keys, effects⟩⟩ })

end PrivateRegion

/-- All reservation outcomes preserve the existing graph and key ownership.
The region allocator derives validity and retention of old objects; no final
query, allocator-success, region-fit or unchanged-lifetime-counter premise is
needed. Invalid host responses remain explicit verification rejections. -/
theorem Facts.reserve_private {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (type : Compiler.ZigAir.Memory.Ty) (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ) :
    Facts safety allocator owner data capacity (PrivateRegion.reserve type allocate before).2 rows := by
  let result := Compiler.ZigAir.Memory.RegionAllocation.reserve before.memory.memory type allocate before.memory.effects.allocator
  have retained (id : Nat) (cell : Compiler.ZigAir.Memory.Allocation)
      (found : before.memory.memory.heap.lookup id = some cell) :
      result.1.2.heap.lookup id = some cell := by
    have older := (Compiler.ZigAir.Memory.valid_lookup _ _ _ facts.valid.memory found).1
    exact (Compiler.ZigAir.Memory.RegionAllocation.reserve_heap_other _ _ _ _ id (by omega)).trans found
  have shape : before.memory.memory.heap.RetainsShape result.1.2.heap :=
    fun id cell found => ⟨cell, retained id cell found, Compiler.ZigAir.Memory.Allocation.SameShape.refl _⟩
  have valid := facts.valid.private_memory_frame before.memory result.1.2 before.memory.memory.nextId
    (facts.valid.injected.fresh facts.valid.memory)
    (Compiler.ZigAir.Memory.RegionAllocation.reserve_preserves_valid _ _ _ _ facts.valid.memory)
    shape (Compiler.ZigAir.Memory.RegionAllocation.reserve_heap_other _ _ _ _)
  exact facts.frame ⟨valid.memory, valid.related, valid.injected⟩ facts.projected rfl rfl
    (fun id cell found _ => retained id cell found) (fun _ _ found => found)

/-- Ordinary OOM leaves native memory and the registry unchanged while retaining
the allocator's actual reached effects. It does not become a malformed-state
fault or erase an allocation attempt. -/
theorem PrivateRegion.oom (before : World (Publication.Effects σ)) (type : Compiler.ZigAir.Memory.Ty)
    (layout : Compiler.ZigAir.Memory.Layout) (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ)
    (effects : σ) (valid : before.memory.memory.valid = true) (shaped : type.layout = some layout)
    (nonzero : layout.bytes ≠ 0) (bounded : layout.bytes < Compiler.ZigAir.Memory.addressLimit)
    (response : allocate layout.bytes layout.alignment before.memory.effects.allocator = (none, effects)) :
    reserve type allocate before = (.ok none, { before with memory := { before.memory with
      effects := { before.memory.effects with allocator := effects } } }) := by
  simp only [reserve, Compiler.ZigAir.Memory.RegionAllocation.reserve_failed _ _ _ _ _ _ valid shaped nonzero bounded response]

/-- Successful nonempty reservation binds the actual returned base and fresh
lifetime. The logical registry has no entry for that lifetime; map ownership
must account for it separately rather than misclassifying it as arguments. -/
theorem Facts.reserve_private_success {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (type : Compiler.ZigAir.Memory.Ty) (layout : Compiler.ZigAir.Memory.Layout) (base : Nat)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ) (effects : σ)
    (shaped : type.layout = some layout) (nonzero : layout.bytes ≠ 0)
    (bounded : layout.bytes < Compiler.ZigAir.Memory.addressLimit)
    (response : allocate layout.bytes layout.alignment before.memory.effects.allocator = (some base, effects))
    (fits : Compiler.ZigAir.Memory.RegionAllocation.Fits before.memory.memory layout base) :
    ∃ after, PrivateRegion.reserve type allocate before = (.ok (some ⟨before.memory.memory.nextId, 0⟩), after) ∧
      Facts safety allocator owner data capacity after rows ∧
      after.memory.memory.heap.lookup before.memory.memory.nextId = some ⟨base, type, [], true, false⟩ ∧
      after.memory.heap before.memory.memory.nextId = none ∧
      after.memory.memory.nextId = before.memory.memory.nextId + 1 ∧
      after.memory.memory.nextAddress = max before.memory.memory.nextAddress (base + layout.bytes) ∧
      after.memory.effects.allocator = effects := by
  have ran := Compiler.ZigAir.Memory.RegionAllocation.reserve_admitted _ _ _ _ _ _ _
    facts.valid.memory shaped nonzero bounded response fits
  refine ⟨(PrivateRegion.reserve type allocate before).2, ?_, facts.reserve_private type allocate, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [PrivateRegion.reserve, ran]
  · simp only [PrivateRegion.reserve, ran, Compiler.ZigAir.Memory.RegionAllocation.extend_lookup,
      ↓reduceIte, Compiler.ZigAir.Memory.RegionAllocation.cell]
  · exact facts.valid.injected.fresh facts.valid.memory
  all_goals simp only [PrivateRegion.reserve, ran, Compiler.ZigAir.Memory.RegionAllocation.extend]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
