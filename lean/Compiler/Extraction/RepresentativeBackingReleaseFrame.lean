/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeBackingRelease

namespace Compiler.Extraction.RepresentativeArray.Backing.Release
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

theorem Post.frame {id : Nat} {before after : Session σ} (post : Post id before after) (query : Nat) (apart : query ≠ id) :
    after.heap query = before.heap query ∧ after.memory.heap.lookup query = before.memory.heap.lookup query := by
  simp [post.registry, post.memory, Compiler.Extraction.Memory.write, apart, erase_lookup]

theorem Post.dead {id : Nat} {before after : Session σ} (post : Post id before after) : after.heap id = none ∧ after.memory.heap.lookup id = none := by
  simp [post.registry, post.memory, Compiler.Extraction.Memory.write, erase_lookup]

/-- Every well-shaped alias into the released lifetime fails, including aliases
at nonzero offsets. Lifetime history is retained even if a later allocation
reuses the native base. -/
theorem Post.stale_alias {id : Nat} {before after : Session σ} (post : Post id before after) (offset : Nat) (writable many : Bool)
    (child : Ty) (layout : Layout) (shaped : child.layout = some layout) :
    load after.memory (.pointer (.pointer writable many child) ⟨id, offset⟩) = .error .unallocated := by
  rw [post.memory]
  exact erase_load_dead before.memory id offset writable many child layout shaped

/-- Rejection, the empty no-op, and successful release all preserve validity,
history and every other allocation at both existing heap levels. -/
theorem run_storage (external : External σ) (allocator : Nat) (data : Address) (capacity : Nat)
    (before : Session σ) (valid : Valid before) :
    let after := (run external allocator data capacity before).2
    Valid after ∧ after.memory.nextId = before.memory.nextId ∧ after.memory.nextAddress = before.memory.nextAddress ∧
      ∀ query, query ≠ data.allocation → after.heap query = before.heap query ∧ after.memory.heap.lookup query = before.memory.heap.lookup query := by
  unfold run
  split
  · exact ⟨valid, rfl, rfl, fun _ _ => ⟨rfl, rfl⟩⟩
  · cases checked : check allocator data capacity before with
    | error fault => exact ⟨valid, rfl, rfl, fun _ _ => ⟨rfl, rfl⟩⟩
    | ok result =>
      rcases result with ⟨heap, memory, base⟩
      obtain ⟨_, _, rfl, rfl, _⟩ := check_shape allocator data capacity before heap memory base checked
      have post := erased_post before data.allocation (external allocator base (capacity * 32) 8 before.effects) valid
      exact ⟨post.valid, post.nextId, post.nextAddress, post.frame⟩

/-- Checked representative storage has a different declared element type from
parent arguments. Separation therefore follows from the reached checker, even
when the parent is readonly or on the stack. -/
theorem run_word_frame (external : External σ) (allocator : Nat) (data : Address) (capacity : Nat)
    (before : Session σ) (id extent : Nat) (cell : Allocation)
    (found : before.memory.heap.lookup id = some cell) (typed : cell.type = .array extent WordArray.word) :
    (run external allocator data capacity before).2.memory.heap.lookup id = some cell := by
  unfold run
  split
  · exact found
  · cases checked : check allocator data capacity before with
    | error fault => exact found
    | ok result =>
      rcases result with ⟨heap, memory, base⟩
      obtain ⟨owned, _, _, rfl, _⟩ := check_shape allocator data capacity before heap memory base checked
      obtain ⟨owner, ownerFound, ownerType, _, _⟩ := owned.2.2
      have apart := before.memory.heap.lookup_ne_of_type_ne id data.allocation cell owner found ownerFound
        (by simp [typed, ownerType, Backing.type, Expression.allocationType, WordArray.word])
      simpa only [erase_lookup, if_neg apart] using found

theorem parent_borrow (external : External σ) (allocator : Nat) (data : Address) (capacity : Nat)
    (before : Session σ) (parent : WordArray.View) (values : List (BitVec 32)) (extent : Nat) (cell : Allocation)
    (found : before.memory.heap.lookup parent.allocation = some cell) (typed : cell.type = .array extent WordArray.word)
    (represented : WordArray.Represents before.memory parent values) :
    let after := (run external allocator data capacity before).2.memory
    after.heap.lookup parent.allocation = some cell ∧ WordArray.Represents after parent values ∧
      ∀ writable many child offset, load after (.pointer (.pointer writable many child) ⟨parent.allocation, offset⟩) =
        load before.memory (.pointer (.pointer writable many child) ⟨parent.allocation, offset⟩) := by
  have framed := run_word_frame external allocator data capacity before parent.allocation extent cell found typed
  have same := framed.trans found.symm
  refine ⟨framed, ⟨represented.1, ?_⟩, ?_⟩
  · intro index inside
    exact (load_eq_of_lookup before.memory _ true false WordArray.word (parent.address index) same).trans (represented.2 index inside)
  · intro writable many child offset
    exact load_eq_of_lookup before.memory _ writable many child ⟨parent.allocation, offset⟩ same

/-- Release of the container does not destroy the separately owned graph item
or arguments. This frames the existing logical registry; complete native graph
field correspondence is still a separate obligation. -/
theorem run_graph_frame (external : External σ) (allocator : Nat) (data : Address) (capacity : Nat)
    (before : Session σ) (cells : List Compiler.Extraction.Storage.Cell)
    (resident : Compiler.Extraction.Memory.GraphResident allocator before.heap cells) :
    Compiler.Extraction.Memory.GraphResident allocator (run external allocator data capacity before).2.heap cells := by
  unfold run
  split
  · exact resident
  · cases checked : check allocator data capacity before with
    | error fault => exact resident
    | ok result =>
      rcases result with ⟨heap, memory, base⟩
      obtain ⟨owned, _, rfl, _, _⟩ := check_shape allocator data capacity before heap memory base checked
      obtain ⟨stored, vector⟩ := owned.2.1
      intro cell present
      exact Compiler.Extraction.Memory.resident_vector_write allocator before.heap cell (resident cell present)
        data.allocation stored vector none

/-- Header acquisition only reads pointer and capacity. All of its faults, and
all following release outcomes, preserve independent word allocations. -/
theorem fromHeader_word_frame (external : External σ) (allocator : Nat) (header : Address)
    (before : Session σ) (id extent : Nat) (cell : Allocation)
    (found : before.memory.heap.lookup id = some cell) (typed : cell.type = .array extent WordArray.word) :
    (fromHeader external allocator header before).2.memory.heap.lookup id = some cell := by
  unfold fromHeader
  cases acquired : allocatedSlice before.memory header with
  | error fault => exact found
  | ok value =>
    cases value with
    | slice declared data capacity =>
      simp only
      split
      · exact found
      · exact run_word_frame external allocator data capacity before id extent cell found typed
    | _ => exact found

end Compiler.Extraction.RepresentativeArray.Backing.Release
