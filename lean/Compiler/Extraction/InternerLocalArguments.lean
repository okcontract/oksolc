/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerTemporaryArguments

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.LocalArguments
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray

/-- Decode the actual readonly u32 load. No graph/list observation supplies the
copied value. Unsupported or invalid memory remains an explicit rejection. -/
abbrev readId := TemporaryMemory.readId

theorem readId_of_load (memory : Compiler.ZigAir.Memory.State) (source : View) (index : Nat) (value : NodeId)
    (loaded : Compiler.ZigAir.Memory.load memory (source.pointer index) = .ok (number value)) :
    readId memory source index = .ok value := TemporaryMemory.readId_of_load _ _ _ _ loaded

/-- Model the aggregate store by its existing scalar leaf transformers, with
one commit point. No intermediate prefix is exposed on failure, and no callback
runs between the writes. Under the fresh typed-array contract both are total. -/
private def commitPair (before : World σ) (ran : Except Fault View × World σ) : Except Fault View × World σ :=
  match ran with
  | (.error fault, _) => (.error fault, before)
  | (.ok source, after) => (.ok source, after)

def initPair (target : View) (left right : NodeId) : GraphAction σ View := fun before =>
  commitPair before (TemporaryArguments.writePair target left right before)

theorem initPair_of_success (target : View) (left right : NodeId) (before after : World σ)
    (written : TemporaryArguments.writePair target left right before = (.ok target, after)) :
    initPair target left right before = (.ok target, after) := by
  exact congrArg (commitPair before) written

theorem initPair_of_error (target : View) (left right : NodeId) (before reached : World σ) (fault : Fault)
    (failed : TemporaryArguments.writePair target left right before = (.error fault, reached)) :
    initPair target left right before = (.error fault, before) := by
  exact congrArg (commitPair before) failed

private theorem commitPair_success (before after : World σ) (outcome : Except Fault View × World σ)
    (target : View) (ran : commitPair before outcome = (.ok target, after)) : outcome = (.ok target, after) := by
  rcases outcome with ⟨result, reached⟩
  cases result with
  | error fault => cases (Prod.mk.inj ran).1
  | ok source => exact ran

theorem initPair_success (source target : View) (left right : NodeId) (before after : World σ)
    (ran : initPair source left right before = (.ok target, after)) :
    target = source ∧ before.memory.memory.heap.RetainsShape after.memory.memory.heap :=
  TemporaryArguments.writePair_success source target left right before after
    (commitPair_success before after _ target ran)

/-- The mutable named local is allocated before evaluating its typed array
initializer (pinned AstGen.varDecl). Then two readonly loads feed a single
aggregate initialization. Anonymous literal allocation has a different order. -/
def copy (source : View) : GraphAction σ View := fun before =>
  if source.length != 2 then (.error (.memory (.preparation (.memory .sourceBounds))), before) else
  let target : View := ⟨before.memory.memory.nextId, 0, 2⟩
  match Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) with
  | .error fault => (.error (.memory (.preparation (.memory fault))), before)
  | .ok (_, memory) =>
    let allocated := { before with memory := { before.memory with memory } }
    match readId memory source 0 with
    | .error fault => (.error (.memory (.preparation (.memory fault))), allocated)
    | .ok left => match readId memory source 1 with
      | .error fault => (.error (.memory (.preparation (.memory fault))), allocated)
      | .ok right => initPair target left right allocated

theorem copy_storage (source target : View) (before after : World σ)
    (ran : copy source before = (.ok target, after)) :
    target = ⟨before.memory.memory.nextId, 0, 2⟩ ∧
      ∃ cell, after.memory.memory.heap.lookup target.allocation = some cell ∧
        cell.type = .array 2 word ∧ cell.writable = true ∧ cell.stack = true := by
  unfold copy at ran
  split at ran
  · cases (Prod.mk.inj ran).1
  · cases allocation : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) with
    | error fault => simp only [allocation, Prod.mk.injEq] at ran; cases ran.1
    | ok pair =>
      simp only [allocation] at ran
      cases first : readId pair.2 source 0 with
      | error fault => simp only [first, Prod.mk.injEq] at ran; cases ran.1
      | ok left =>
        simp only [first] at ran
        cases second : readId pair.2 source 1 with
        | error fault => simp only [second, Prod.mk.injEq] at ran; cases ran.1
        | ok right =>
          simp only [second] at ran
          have stored := initPair_success _ target left right _ after ran
          refine ⟨stored.1, ?_⟩
          rw [stored.1]
          exact TemporaryMemory.allocated_array _ _ _ 2 pair.1 allocation stored.2

theorem copy_of_reads (source : View) (left right : NodeId) (before : World σ)
    (pointer : Compiler.ZigAir.Memory.Value) (memory : Compiler.ZigAir.Memory.State) (after : World σ)
    (length : source.length = 2)
    (allocation : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (first : Compiler.ZigAir.Memory.load memory (source.pointer 0) = .ok (number left))
    (second : Compiler.ZigAir.Memory.load memory (source.pointer 1) = .ok (number right))
    (prepared : TemporaryArguments.prepare left right before = (.ok ⟨before.memory.memory.nextId, 0, 2⟩, after)) :
    copy source before = (.ok ⟨before.memory.memory.nextId, 0, 2⟩, after) := by
  have written : TemporaryArguments.writePair ⟨before.memory.memory.nextId, 0, 2⟩ left right
      { before with memory := { before.memory with memory } } = (.ok ⟨before.memory.memory.nextId, 0, 2⟩, after) := by
    simpa only [TemporaryArguments.prepare, allocation] using prepared
  simp only [copy, length, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, allocation,
    readId_of_load _ _ _ _ first, readId_of_load _ _ _ _ second]
  exact initPair_of_success _ _ _ _ _ written

theorem copy_first_error (source : View) (before : World σ) (pointer : Compiler.ZigAir.Memory.Value)
    (memory : Compiler.ZigAir.Memory.State) (fault : Compiler.ZigAir.Memory.Fault)
    (length : source.length = 2)
    (allocation : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (failed : readId memory source 0 = .error fault) :
    copy source before = (.error (.memory (.preparation (.memory fault))),
      { before with memory := { before.memory with memory } }) := by
  simp only [copy, length, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, allocation, failed]

theorem copy_second_error (source : View) (left : NodeId) (before : World σ) (pointer : Compiler.ZigAir.Memory.Value)
    (memory : Compiler.ZigAir.Memory.State) (fault : Compiler.ZigAir.Memory.Fault)
    (length : source.length = 2)
    (allocation : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (first : readId memory source 0 = .ok left) (failed : readId memory source 1 = .error fault) :
    copy source before = (.error (.memory (.preparation (.memory fault))),
      { before with memory := { before.memory with memory } }) := by
  simp only [copy, length, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, allocation, first, failed]

theorem copy_verified (source : View) (left right : NodeId) (before : World σ)
    (pointer : Compiler.ZigAir.Memory.Value) (allocated : Compiler.ZigAir.Memory.State)
    (valid : Valid before.memory) (represented : Represents before.memory.memory source [left, right])
    (allocation : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, allocated)) :
    ∃ after, copy source before = (.ok ⟨before.memory.memory.nextId, 0, 2⟩, after) ∧
      Good ⟨before.memory.memory.nextId, 0, 2⟩ [left, right] after ∧ after.graph = before.graph ∧
      after.memory.heap = before.memory.heap ∧ after.memory.effects = before.memory.effects ∧
      after.memory.memory.nextId = before.memory.memory.nextId + 1 ∧
      (∀ id cell, before.memory.memory.heap.lookup id = some cell → after.memory.memory.heap.lookup id = some cell) ∧
      Writable after.memory.memory ⟨before.memory.memory.nextId, 0, 2⟩ ∧
      after.memory.heap before.memory.memory.nextId = none := by
  have length : source.length = 2 := represented.1.symm
  obtain ⟨_, kept, _⟩ := caller_buffer before.memory allocated pointer source [left, right] valid represented allocation
  obtain ⟨after, ran, good, graph, heap, effects, counter, frame, cap, unregistered⟩ :=
    TemporaryArguments.prepare_with_writable left right before pointer allocated valid allocation
  exact ⟨after, copy_of_reads source left right before pointer allocated after length allocation
    (kept.2 0 (by simp)) (kept.2 1 (by simp)) ran, good, graph, heap, effects, counter, frame, cap, unregistered⟩

/-- This is the actual optional third store, into the same caller buffer. -/
def overwrite (source : View) (index : Nat) (value : NodeId) : GraphAction σ View := fun before =>
  TemporaryArguments.orderedStores
    (Compiler.ZigAir.Memory.store before.memory.memory (source.pointer index) (number value))
    (fun written => .ok written) source before

theorem overwrite_success (source target : View) (index : Nat) (value : NodeId) (before after : World σ)
    (ran : overwrite source index value before = (.ok target, after)) :
    target = source ∧ before.memory.memory.heap.RetainsShape after.memory.memory.heap :=
  TemporaryArguments.orderedStores_success _ _ source target before after
    (fun memory stored => Compiler.ZigAir.Memory.store_retains_shape _ _ _ memory stored)
    (fun written memory same => by cases Except.ok.inj same; exact Compiler.ZigAir.Memory.Heap.RetainsShape.refl _) ran

theorem overwrite_of_store (source : View) (index : Nat) (value : NodeId) (before : World σ)
    (memory : Compiler.ZigAir.Memory.State)
    (stored : Compiler.ZigAir.Memory.store before.memory.memory (source.pointer index) (number value) = .ok memory) :
    overwrite source index value before = (.ok source, { before with memory := { before.memory with memory } }) := by
  exact TemporaryArguments.orderedStores_of_success _ _ source before memory memory stored rfl

theorem overwrite_verified (source : View) (values : List NodeId) (index : Nat) (value : NodeId)
    (before : World σ) (good : Good source values before)
    (unregistered : before.memory.heap source.allocation = none)
    (writable : Writable before.memory.memory source) (inside : index < source.length) :
    ∃ after, overwrite source index value before = (.ok source, after) ∧ Good source (values.set index value) after ∧
      after.graph = before.graph ∧ after.memory.heap = before.memory.heap ∧ after.memory.effects = before.memory.effects ∧
      after.memory.memory.nextId = before.memory.memory.nextId ∧
      (∀ id, id ≠ source.allocation → after.memory.memory.heap.lookup id = before.memory.memory.heap.lookup id) := by
  obtain ⟨memory, stored⟩ := write_total before.memory.memory source index value good.1.memory writable inside
  refine ⟨{ before with memory := { before.memory with memory } }, overwrite_of_store source index value before memory stored,
    ⟨TemporaryMemory.stored_valid before.memory memory source index value good.1 unregistered inside stored,
      write_represents _ _ source values index value good.2 stored⟩, rfl, rfl, rfl, ?_, ?_⟩
  · exact (write_allocation_frame _ _ source index value stored).1
  · exact (write_allocation_frame _ _ source index value stored).2.2

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.LocalArguments
