/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorArguments

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray

/-- Nonempty constructor sources have an actual word-array allocation. Empty
views need no allocation; offsets, extent, writability and values are unrestricted
here. Reading words alone would also admit interior views into graph storage. -/
def ArraySource (source : View) (memory : Compiler.ZigAir.Memory.State) : Prop :=
  source.length ≠ 0 → ∃ extent cell, memory.heap.lookup source.allocation = some cell ∧
    cell.type = .array extent word

theorem ArraySource.empty {source : View} {memory : Compiler.ZigAir.Memory.State}
    (empty : source.length = 0) : ArraySource source memory :=
  fun nonempty => False.elim (nonempty empty)

/-- A registered borrowed operand has its actual word-array allocation through
the existing session relation. Empty operands need no registered allocation. -/
theorem ArraySource.registered {allocator : Nat} {slice : ArgumentSlice} {session : Session σ}
    (valid : Valid session) (live : SliceValid allocator session.heap slice) :
    ArraySource (view slice) session.memory := by
  intro nonempty
  have valuesNonempty : slice.items ≠ [] := by
    intro empty
    exact nonempty (by simp [view, empty])
  obtain ⟨⟨cell, found, typed, _⟩, _⟩ := valid.related allocator slice.address slice.items valuesNonempty
    (live.resolve_left valuesNonempty)
  exact ⟨slice.items.length, cell, found, typed⟩

theorem ArraySource.frame {source : View} {before after : Compiler.ZigAir.Memory.State}
    (array : ArraySource source before)
    (retained : source.length ≠ 0 → ∀ cell, before.heap.lookup source.allocation = some cell →
      after.heap.lookup source.allocation = some cell) :
    ArraySource source after := by
  intro nonempty
  obtain ⟨extent, cell, found, typed⟩ := array nonempty
  exact ⟨extent, cell, retained nonempty _ found, typed⟩

/-- Successful literal/local preparation supplies source provenance from its
existing native storage fact, without a final insertion-frame premise. -/
theorem ConstructorItem.Arguments.Prepared.arraySource {values : List NodeId}
    {before after : World σ} {source : View} (prepared : ConstructorItem.Arguments.Prepared values before source after) :
    ArraySource source after.memory.memory := by
  intro nonempty
  have valuesNonempty : values ≠ [] := by
    intro empty
    have length := prepared.good.2.1
    simp only [empty, List.length_nil] at length
    exact nonempty length.symm
  obtain ⟨cell, found, typed, _⟩ := prepared.storage valuesNonempty
  exact ⟨values.length, cell, found, typed⟩

/-- Cleanup retains an older source's actual allocation type, including offset
views. Empty sources impose no allocation or age requirement. -/
theorem ArraySource.cleanup {source : View} {memory : Compiler.ZigAir.Memory.State}
    (array : ArraySource source memory) (mark : Nat)
    (older : source.length ≠ 0 → source.allocation < mark) :
    ArraySource source (Compiler.ZigAir.Memory.cleanup mark memory) :=
  array.frame (fun nonempty _ found =>
    (Compiler.ZigAir.Memory.cleanup_lookup_older _ mark source.allocation (older nonempty)).trans found)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
