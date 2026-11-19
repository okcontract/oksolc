/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeBackingRegistry

namespace Compiler.Extraction.RepresentativeArray.Backing.Registry
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

/-- Every outcome retains the actual typed reservation, including collision
rejection after allocation. Registration changes only the fresh lifetime. -/
theorem storage (allocate : Allocate σ) (allocator capacity : Nat) (before : Session σ) (valid : Valid before) :
    let after := (run allocate allocator capacity before).2
    Valid after ∧ (after.heap = before.heap ∨ after.heap = Compiler.Extraction.Memory.write before.heap before.memory.nextId
      (some ⟨allocator, .representatives []⟩)) ∧
      ∀ query, query ≠ before.memory.nextId → after.memory.heap.lookup query = before.memory.heap.lookup query := by
  have privateValid := reservation_valid before capacity (allocate allocator) valid
  have frame := reservation_frame before capacity (allocate allocator)
  unfold run
  generalize reserved : Backing.reserve before.memory capacity (allocate allocator) before.effects = result at privateValid frame ⊢
  rcases result with ⟨⟨outcome, memory⟩, effects⟩
  cases outcome with
  | error fault => exact ⟨privateValid, Or.inl rfl, frame⟩
  | ok target =>
    cases target with
    | none => exact ⟨privateValid, Or.inl rfl, frame⟩
    | some data =>
      dsimp only
      split
      · exact ⟨privateValid, Or.inl rfl, frame⟩
      · rename_i nonempty
        obtain ⟨base, rfl, rfl, _, _⟩ := reservation_shape before memory capacity (allocate allocator) effects data nonempty reserved
        have fresh := valid.injected.fresh valid.memory
        have registered : Compiler.Extraction.Memory.allocate before.heap allocator before.memory.nextId (.representatives []) true =
            .ok (Compiler.Extraction.Memory.write before.heap before.memory.nextId (some ⟨allocator, .representatives []⟩)) := by
          simp [Compiler.Extraction.Memory.allocate, fresh]
        simp only [registered]
        refine ⟨register_valid _ allocator before.memory.nextId (RegionAllocation.cell (Backing.type capacity) base) privateValid ?_ rfl,
          Or.inr trivial, frame⟩
        simp [RegionAllocation.extend_lookup]

theorem frame (allocate : Allocate σ) (allocator capacity : Nat) (before : Session σ) (valid : Valid before)
    (query : Nat) (apart : query ≠ before.memory.nextId) :
    (run allocate allocator capacity before).2.heap query = before.heap query ∧
      (run allocate allocator capacity before).2.memory.heap.lookup query = before.memory.heap.lookup query := by
  have post := storage allocate allocator capacity before valid
  refine ⟨?_, post.2.2 query apart⟩
  rcases post.2.1 with unchanged | registered
  · rw [unchanged]
  · simp only [registered, Compiler.Extraction.Memory.write, if_neg apart]

/-- Invert an actual successful nonempty reservation. Both the fresh root and
its release permission follow from execution, including registration. -/
theorem success_owned (allocate : Allocate σ) (allocator capacity : Nat) (before after : Session σ) (data : Address)
    (valid : Valid before) (nonempty : capacity ≠ 0)
    (executed : run allocate allocator capacity before = (.ok (some data), after)) :
    data = ⟨before.memory.nextId, 0⟩ ∧ Release.Owned allocator data capacity after := by
  unfold run at executed
  cases reserved : Backing.reserve before.memory capacity (allocate allocator) before.effects with
  | mk result effects =>
    rcases result with ⟨outcome, memory⟩
    rw [reserved] at executed
    cases outcome with
    | error fault => simp at executed
    | ok target =>
      cases target with
      | none => simp at executed
      | some target =>
        obtain ⟨base, rfl, rfl, _, _⟩ := reservation_shape before memory capacity (allocate allocator) effects target nonempty reserved
        have fresh := valid.injected.fresh valid.memory
        simp only [if_neg nonempty] at executed
        have registered : Compiler.Extraction.Memory.allocate before.heap allocator before.memory.nextId (.representatives []) true =
            .ok (Compiler.Extraction.Memory.write before.heap before.memory.nextId (some ⟨allocator, .representatives []⟩)) := by
          simp [Compiler.Extraction.Memory.allocate, fresh]
        rw [registered] at executed
        have same := Prod.mk.inj executed
        cases Option.some.inj (Except.ok.inj same.1)
        cases same.2
        exact ⟨rfl, rfl, ⟨[], by simp [Compiler.Extraction.Memory.Vector, Compiler.Extraction.Memory.write]⟩,
          RegionAllocation.cell (Backing.type capacity) base, by simp [RegionAllocation.extend_lookup], rfl, rfl, rfl⟩

/-- The existing logical graph's separately allocated payloads survive every
reservation outcome. No initialized descriptor correspondence is manufactured. -/
theorem graph_frame (allocate : Allocate σ) (allocator capacity owner : Nat) (before : Session σ) (valid : Valid before)
    (cells : List Compiler.Extraction.Storage.Cell) (resident : Compiler.Extraction.Memory.GraphResident owner before.heap cells) :
    Compiler.Extraction.Memory.GraphResident owner (run allocate allocator capacity before).2.heap cells := by
  rcases (storage allocate allocator capacity before valid).2.1 with unchanged | registered
  · rw [unchanged]; exact resident
  · rw [registered]
    intro cell present
    exact Compiler.Extraction.Memory.resident_fresh_write owner before.heap cell (resident cell present)
      before.memory.nextId (valid.injected.fresh valid.memory) _

theorem parent_borrow (allocate : Allocate σ) (allocator capacity : Nat) (before : Session σ) (valid : Valid before)
    (parent : WordArray.View) (values : List (BitVec 32)) (cell : Allocation)
    (found : before.memory.heap.lookup parent.allocation = some cell) (represented : WordArray.Represents before.memory parent values) :
    let after := (run allocate allocator capacity before).2.memory
    after.heap.lookup parent.allocation = some cell ∧ WordArray.Represents after parent values ∧
      ∀ writable many child offset, load after (.pointer (.pointer writable many child) ⟨parent.allocation, offset⟩) =
        load before.memory (.pointer (.pointer writable many child) ⟨parent.allocation, offset⟩) := by
  have older := (valid_lookup before.memory parent.allocation cell valid.memory found).1
  have same := (frame allocate allocator capacity before valid parent.allocation (by omega)).2
  refine ⟨same.trans found, ⟨represented.1, ?_⟩, ?_⟩
  · intro index inside
    exact (load_eq_of_lookup before.memory _ true false WordArray.word (parent.address index) same).trans (represented.2 index inside)
  · intro writable many child offset
    exact load_eq_of_lookup before.memory _ writable many child ⟨parent.allocation, offset⟩ same

/-- The actual reservation discharges the release permission. This composition
checks matching allocator, native base, full extent and private-effect order;
the empty provisional vector is never treated as copied or published graph data. -/
theorem release_derived (allocate : Allocate σ) (release : Release.External σ) (allocator capacity base : Nat)
    (before : Session σ) (effects : σ) (valid : Valid before) (nonempty : capacity ≠ 0) (size : capacity * 32 < addressLimit)
    (response : allocate allocator (capacity * 32) 8 before.effects = (some base, effects))
    (fits : RegionAllocation.Fits before.memory ⟨capacity * 32, 8⟩ base) :
    ∃ ready after, run allocate allocator capacity before = (.ok (some ⟨before.memory.nextId, 0⟩), ready) ∧
      Release.run release allocator ⟨before.memory.nextId, 0⟩ capacity ready = (.ok (), after) ∧
      Release.Post before.memory.nextId ready after ∧ after.heap = before.heap ∧
      (∀ query, after.memory.heap.lookup query = before.memory.heap.lookup query) ∧
      after.memory.nextId = before.memory.nextId + 1 ∧
      after.memory.nextAddress = max before.memory.nextAddress (base + capacity * 32) ∧
      after.effects = release allocator base (capacity * 32) 8 effects := by
  obtain ⟨ready, allocated, readyValid, owned, memory, registry, reached⟩ :=
    verified allocate allocator capacity base before effects valid nonempty size response fits
  obtain ⟨cell, after, found, freed, post, privateEffects, _⟩ :=
    Release.verified release allocator ⟨before.memory.nextId, 0⟩ capacity ready readyValid owned nonempty
  have typed : cell = RegionAllocation.cell (Backing.type capacity) base := by
    rw [memory, RegionAllocation.extend_lookup] at found
    exact (Option.some.inj (by simpa only [↓reduceIte] using found)).symm
  subst cell
  refine ⟨ready, after, allocated, freed, post, ?_, ?_, ?_, ?_, ?_⟩
  · funext query
    have fresh := valid.injected.fresh valid.memory
    by_cases same : query = before.memory.nextId <;>
      simp [post.registry, registry, Compiler.Extraction.Memory.write, same, fresh]
  · intro query
    by_cases same : query = before.memory.nextId
    · subst query
      exact post.dead.2.trans (WordAllocation.next_id_fresh before.memory valid.memory).symm
    · rw [(post.frame query same).2, memory]
      simp only [RegionAllocation.extend_lookup, if_neg (Ne.symm same)]
  · rw [post.nextId, memory]; rfl
  · rw [post.nextAddress, memory]; rfl
  · simpa only [RegionAllocation.cell, reached] using privateEffects

end Compiler.Extraction.RepresentativeArray.Backing.Registry
