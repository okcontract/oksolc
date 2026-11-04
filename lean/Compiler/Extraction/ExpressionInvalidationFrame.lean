/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionInvalidation
import Compiler.Extraction.RepresentativeDescriptorRelation
import Compiler.ZigAir.MemoryInvalidationFrame

namespace Compiler.Extraction.Expression
open Compiler.ZigAir.Memory

/-- Earlier descriptor fields survive last-row invalidation. Geometry and
every read leaf come from the existing typed selector and captured field types. -/
theorem readField_before_invalidate (before after : State) (lifetime index other offset : Nat)
    (executed : invalidate before ⟨lifetime, index * 32⟩ = .ok after) (earlier : other < index)
    (slot : (offset, fieldType allocationType offset) ∈
      [(itemOffset, some itemType), (argumentsOffset, some argumentsType), (idOffset, some idType), (sequence_numberOffset, some idType)]) :
    readField after false ⟨lifetime, other * 32⟩ offset = readField before false ⟨lifetime, other * 32⟩ offset := by
  have rowBound : (other + 1) * 32 ≤ index * 32 := Nat.mul_le_mul_right 32 earlier
  have selected := fieldPointer_after_invalidate before after true allocationType ⟨lifetime, index * 32⟩
    false false allocationType ⟨lifetime, other * 32⟩ offset executed
  unfold readField
  rw [selected]
  cases called : fieldPointer before (.pointer (.pointer false false allocationType) ⟨lifetime, other * 32⟩) offset with
  | error fault => rfl
  | ok pointer =>
    obtain ⟨field, typed, rfl⟩ := fieldPointer_address before false false allocationType ⟨lifetime, other * 32⟩ offset pointer called
    apply load_disjoint_after_invalidate before after true allocationType ⟨lifetime, index * 32⟩ ⟨32, 8⟩ false false field
      (other * 32 + offset) layout_checked executed
    intro position member
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at slot
    rcases slot with ⟨rfl, typeEq⟩ | ⟨rfl, typeEq⟩ | ⟨rfl, typeEq⟩ | ⟨rfl, typeEq⟩
    all_goals
      have same := Option.some.inj (typed.symm.trans typeEq)
      subst field
      simp only [Ty.readOffsets, itemType, argumentsType, idType, List.mem_cons, List.not_mem_nil, or_false, itemOffset,
        argumentsOffset, idOffset, sequence_numberOffset] at member
      dsimp only
      omega

theorem prefix_before_invalidate (before after : State) (lifetime : Nat) (cells : List Storage.Cell)
    (executed : invalidate before ⟨lifetime, cells.length * 32⟩ = .ok after)
    (rows : RepresentativeArray.DescriptorRelation.Prefix before lifetime cells) :
    RepresentativeArray.DescriptorRelation.Prefix after lifetime cells := by
  intro index cell found
  have inside : index < cells.length := by
    by_cases inside : index < cells.length
    · exact inside
    · rw [List.getElem?_eq_none (by omega)] at found; contradiction
  have frame := readField_before_invalidate before after lifetime cells.length index
  have item := frame itemOffset executed inside (by decide)
  have arguments := frame argumentsOffset executed inside (by decide)
  have id := frame idOffset executed inside (by decide)
  have sequence := frame sequence_numberOffset executed inside (by decide)
  unfold RepresentativeArray.DescriptorRelation.Row readFields
  rw [item, arguments, id, sequence]
  exact rows index cell found

end Compiler.Extraction.Expression
