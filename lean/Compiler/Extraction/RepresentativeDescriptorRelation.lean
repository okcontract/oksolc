/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeBackingCopy

namespace Compiler.Extraction.RepresentativeArray.DescriptorRelation
open Compiler.ZigAir.Memory
open Compiler.Algebraic

/-- Project the existing logical cell into the captured assignment schedule.
An owned graph descriptor has root item/argument pointers; offset borrowed
inputs remain separate views. The stored ID is its vector index, and sequence
metadata is retained even when it does not affect a query. No pointee payload,
registry entry, denotation or map correspondence follows from these fields. -/
def values (index : Nat) (cell : Storage.Cell) : List Value :=
  (descriptorFields ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩ cell.arguments.length index cell.sequence.toNat).map Prod.snd

def Row (state : State) (lifetime index : Nat) (cell : Storage.Cell) : Prop :=
  Expression.readFields state false ⟨lifetime, index * 32⟩ = .ok (values index cell)

/-- Relate the actual initialized prefix to the existing cells, without a
second descriptor list or a native snapshot. Capacity and the loaded header
remain separate geometric facts; empty prefixes need no live sentinel. -/
def Prefix (state : State) (lifetime : Nat) (cells : List Storage.Cell) : Prop :=
  ∀ index cell, cells[index]? = some cell → Row state lifetime index cell

theorem empty (state : State) (lifetime : Nat) : Prefix state lifetime [] := by
  intro index cell found
  simp at found

/-- Extend the existing cell list only after both its old rows and the new row
have been established in the same memory. -/
theorem extend (state : State) (lifetime : Nat) (cells : List Storage.Cell) (cell : Storage.Cell)
    (old : Prefix state lifetime cells) (newRow : Row state lifetime cells.length cell) :
    Prefix state lifetime (cells ++ [cell]) := by
  intro index record entry
  by_cases inside : index < cells.length
  · exact old index record (by simpa only [List.getElem?_append_left inside] using entry)
  · rw [List.getElem?_append_right (by omega)] at entry
    have indexEq : index = cells.length := by
      by_cases same : index = cells.length
      · exact same
      · have past : 1 ≤ index - cells.length := by omega
        rw [List.getElem?_eq_none past] at entry
        contradiction
    subst index
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at entry
    subst record
    exact newRow

theorem row_frame (before after : State) (lifetime index : Nat) (cell : Storage.Cell)
    (row : Row before lifetime index cell) (same : after.heap.lookup lifetime = before.heap.lookup lifetime) :
    Row after lifetime index cell :=
  (Copy.readFields_eq_of_slots _ _ _ _ (fun slot _ => Backing.RegisteredCopy.read_field_frame _ _ _ slot.1 same)).trans row

theorem frame (before after : State) (lifetime : Nat) (cells : List Storage.Cell)
    (represented : Prefix before lifetime cells) (same : after.heap.lookup lifetime = before.heap.lookup lifetime) :
    Prefix after lifetime cells :=
  fun index cell found => row_frame before after lifetime index cell (represented index cell found) same

/-- All four copy preconditions follow from the initial descriptor relation,
including the slice descriptor's complete pointer/length pair. -/
theorem source_ready (state : State) (lifetime : Nat) (cells : List Storage.Cell) (represented : Prefix state lifetime cells) :
    ∀ index, index < cells.length → ∀ slot ∈ expressionSlots,
      ∃ value, Expression.readField state false ⟨lifetime, index * 32⟩ slot.1 = .ok value := by
  intro index inside slot member
  have row := represented index cells[index] (List.getElem?_eq_getElem inside)
  have parts := Expression.readFields_parts state false ⟨lifetime, index * 32⟩ _ _ _ _ row
  rcases slot with ⟨offset, type⟩
  simp only [expressionSlots, Expression.allocationType, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false, Field.type, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨_, parts.1⟩
  · exact ⟨_, parts.2.1⟩
  · exact ⟨_, parts.2.2.1⟩
  · exact ⟨_, parts.2.2.2⟩

/-- Relocation preserves the relation exactly when its existing field theorem
preserves every row. This lemma transports observations, not logical storage. -/
theorem copied (before after : State) (source target : Nat) (cells : List Storage.Cell)
    (represented : Prefix before source cells)
    (fields : ∀ index, index < cells.length → Expression.readFields after false ⟨target, index * 32⟩ =
      Expression.readFields before false ⟨source, index * 32⟩) : Prefix after target cells := by
  intro index cell found
  have inside : index < cells.length := by
    by_cases inside : index < cells.length
    · exact inside
    · rw [List.getElem?_eq_none (by omega)] at found
      contradiction
  exact (fields index inside).trans (represented index cell found)

/-- The source-bound native representative reader agrees with the existing
logical lookup for every ID, including invalid IDs. The descriptor relation
supplies complete field values; actual header/backing geometry supplies access. -/
theorem query (state : State) (header : Address) (lifetime capacity : Nat) (backing : Allocation)
    (cells : List Storage.Cell) (id : NodeId) (valid : state.valid = true)
    (loaded : readItems state header = .ok (.slice itemsType ⟨lifetime, 0⟩ cells.length))
    (found : state.heap.lookup lifetime = some backing) (typed : backing.type = .array capacity Expression.allocationType)
    (writable : backing.writable = true) (extent : cells.length ≤ capacity) (represented : Prefix state lifetime cells) :
    representativeFields state header id = .ok ((Storage.representativeProgram.run cells id).map (values id.toNat)) := by
  by_cases inside : id.toNat < cells.length
  · have pointer := representative_from_array state header lifetime capacity cells.length backing id valid loaded found typed writable extent inside
    have row := represented id.toNat cells[id.toNat] (List.getElem?_eq_getElem inside)
    simp only [Row] at row
    simp only [representativeFields, pointer, bind, Except.bind, ne_self_iff_false, ↓reduceIte, row,
      pure, Except.pure, Storage.Lookup.run, Storage.representativeProgram, Storage.Bound.reject, Storage.Index.eval,
      show ¬id.toNat ≥ cells.length by omega, decide_false, Bool.false_eq_true, List.getElem?_eq_getElem inside, Except.map]
  · have rejected := invalid_from_loaded_header state header ⟨lifetime, 0⟩ cells.length id loaded (by omega)
    simp only [representativeFields, rejected, bind, Except.bind, pure, Except.pure, Storage.Lookup.run,
      Storage.representativeProgram, Storage.Bound.reject, show id.toNat ≥ cells.length by omega, decide_true, ↓reduceIte, Except.map]

end Compiler.Extraction.RepresentativeArray.DescriptorRelation
