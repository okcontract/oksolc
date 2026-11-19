/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryShapePreservation
import Compiler.ZigAir.MemoryShapeRegions
import Compiler.ZigAir.MemoryWordSwapConfinement

/-! Stable physical intervals in the typed allocation model, for every captured
swap prefix. Native address injection, LLVM noalias and native allocator
correspondence remain separate obligations. -/
namespace Compiler.ZigAir.MemoryWordSwap
open Memory MemoryAir Control.Machine
open Memory.WordArray (View Writable Represents)

/-- Every original allocation remains live with its original metadata, even
when the trace is suspended or ends at allocation exhaustion. -/
theorem captured_retains_shape (caller : State) (view : View) (left right fuel : Nat)
    (initial : caller.valid = true) (event : Observation Ty Prim Value State)
    (present : event ∈ (trace semantics (arguments view left right) fuel
      (.suspended ⟨GeneratedMemory.fn_swap_u32.program.body, fun _ => none, caller, []⟩)).1) :
    caller.heap.RetainsShape event.state.heap :=
  observed_retains_shape _ fuel _ initial event present

/-- The two fixed, bounded, disjoint argument intervals persist at every
observed step. Contents may change; base, layout, permission and stack lifetime
do not. The universal trace claim needs no initialized-content premise. -/
theorem captured_regions (caller : State) (view : View) (left right : Nat)
    (initial : caller.valid = true) (cap : Writable caller view)
    (hl : left < view.length) (hr : right < view.length) (apart : left ≠ right) :
    ∃ cell, caller.heap.lookup view.allocation = some cell ∧
      0 < cell.base + (view.address left).offset ∧
      cell.base + (view.address left).offset + 4 ≤ addressLimit ∧
      0 < cell.base + (view.address right).offset ∧
      cell.base + (view.address right).offset + 4 ≤ addressLimit ∧
      (cell.base + (view.address left).offset + 4 ≤ cell.base + (view.address right).offset ∨
       cell.base + (view.address right).offset + 4 ≤ cell.base + (view.address left).offset) ∧
      ∀ fuel event, event ∈ (trace semantics (arguments view left right) fuel
          (.suspended ⟨GeneratedMemory.fn_swap_u32.program.body, fun _ => none, caller, []⟩)).1 →
        ∃ updated, event.state.heap.lookup view.allocation = some updated ∧ cell.SameShape updated := by
  obtain ⟨cell, found, regions⟩ := WordArray.element_regions caller view left right initial cap hl hr apart
  refine ⟨cell, found, regions.1, regions.2.1, regions.2.2.1, regions.2.2.2.1, regions.2.2.2.2, ?_⟩
  intro fuel event present
  exact captured_retains_shape caller view left right fuel initial event present view.allocation cell found

/-- Every actual byte operation resolves inside one of the original physical
word intervals. Whole-word read/modify/write has the same original word base.
This is stronger than an allocation-ID comparison, but still model-relative. -/
theorem captured_byte_regions (caller : State) (view : View) (items : List (BitVec 32)) (left right : Nat)
    (initial : caller.valid = true) (cap : Writable caller view) (represented : Represents caller view items)
    (hl : left < items.length) (hr : right < items.length) (apart : left ≠ right)
    (fuel : Nat) (event : Observation Ty Prim Value State) (order : WordBytes.Order) (pointer : Ref)
    (present : event ∈ (trace semantics (arguments view left right) fuel
      (.suspended ⟨GeneratedMemory.fn_swap_u32.program.body, fun _ => none, caller, []⟩)).1)
    (kind : event.site.2.2 = .wordByteLoad order pointer ∨ ∃ value, event.site.2.2 = .wordByteStore order pointer value) :
    ∃ original current address word,
      caller.heap.lookup view.allocation = some original ∧
      event.state.heap.lookup address.allocation = some current ∧ original.SameShape current ∧
      pointer.eval event.env = .ok (ByteAccess.pointer true false address) ∧
      ((pointer = .local 18 ∧ word = left) ∨ (pointer = .local 19 ∧ word = right)) ∧
      ByteAccess.wordAddress address = view.address word ∧
      current.base + (ByteAccess.wordAddress address).offset = original.base + (view.address word).offset ∧
      original.base + (view.address word).offset ≤ current.base + address.offset ∧
      current.base + address.offset < original.base + (view.address word).offset + 4 := by
  have confined := (captured_confinement caller view items left right initial cap represented hl hr apart).2 fuel event present
  have borrowed := Footprint.byte_access view left right _ event order pointer kind confined.1
  obtain ⟨extent, original, found, _, _, _⟩ := cap
  obtain ⟨current, lookup, shape⟩ := captured_retains_shape caller view left right fuel initial event present _ original found
  obtain ⟨address, resolved, first | second⟩ := borrowed_word view left right event.env pointer borrowed
  · have id : address.allocation = view.allocation := congrArg Address.allocation first.2.1
    refine ⟨original, current, address, left, found, by simpa only [id] using lookup,
      shape, resolved, Or.inl ⟨first.1, rfl⟩, first.2.1, ?_, ?_, ?_⟩
    · rw [first.2.1, shape.1]
    · rw [shape.1]; omega
    · rw [shape.1]; omega
  · have id : address.allocation = view.allocation := congrArg Address.allocation second.2.1
    refine ⟨original, current, address, right, found, by simpa only [id] using lookup,
      shape, resolved, Or.inr ⟨second.1, rfl⟩, second.2.1, ?_, ?_, ?_⟩
    · rw [second.2.1, shape.1]
    · rw [shape.1]; omega
    · rw [shape.1]; omega

end Compiler.ZigAir.MemoryWordSwap
