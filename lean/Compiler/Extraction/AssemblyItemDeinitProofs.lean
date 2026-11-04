/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyItemDeinitProgram

namespace Compiler.Extraction.AssemblyItemDeinit
open Compiler.Extraction.Memory Compiler.Extraction.Storage
open Compiler.Extraction.Memory.Arguments.Normalization

structure Released (slice : Bytes) (before after : Session σ) : Prop where
  valid : Valid after
  nextId : after.memory.nextId = before.memory.nextId
  nextAddress : after.memory.nextAddress = before.memory.nextAddress
  frame : ∀ id, slice.length = 0 ∨ id ≠ slice.address →
    after.heap id = before.heap id ∧ after.memory.heap.lookup id = before.memory.heap.lookup id
  dead : slice.length ≠ 0 → after.heap slice.address = none ∧ after.memory.heap.lookup slice.address = none

theorem free_verified (external : Release σ) (allocator : Nat) (slice : Bytes) (before : Session σ)
    (valid : Valid before) (owned : Owned allocator slice before) :
    ∃ after, free external allocator slice before = (.ok (), after) ∧ Released slice before after ∧
      after.effects = if slice.length = 0 then before.effects else external slice before := by
  by_cases empty : slice.length = 0
  · exact ⟨before, by simp [free, empty],
      ⟨valid, rfl, rfl, fun _ _ => ⟨rfl, rfl⟩, fun nonempty => False.elim (nonempty empty)⟩,
      by simp [empty]⟩
  · obtain ⟨stored, cell, found, typed, writable, stack, offset⟩ := owned.resolve_left empty
    refine ⟨⟨write before.heap slice.address none, Compiler.ZigAir.Memory.erase before.memory slice.address,
      external slice before⟩, ?_, ?_, by simp [empty]⟩
    · simp [free, empty, offset, stored, Memory.release, Compiler.ZigAir.Memory.releaseOwned,
        valid.memory, found, typed, writable, stack, Except.mapError, bind, Except.bind]
    · refine ⟨⟨Compiler.ZigAir.Memory.erase_preserves_valid _ _ valid.memory,
        Arguments.related_erase _ _ _ valid.related, valid.injected.erased _⟩, rfl, rfl, ?_, ?_⟩
      · intro id separate
        have apart := separate.resolve_left empty
        exact ⟨by simp [write, apart], by simp [Compiler.ZigAir.Memory.erase_lookup, apart]⟩
      · intro _
        exact ⟨by simp [write], by simp [Compiler.ZigAir.Memory.erase_lookup]⟩

namespace Released

/-- A byte payload cannot own an argument allocation in the same registry.
Consequently payload cleanup establishes the argument-free precondition of
Expression.deinit rather than assuming a blanket frame for item destruction. -/
theorem arguments (slice : Bytes) (before after : Session σ) (post : Released slice before after)
    (allocator : Nat) (owned : Owned allocator slice before) (argumentAllocator : Nat) (arguments : ArgumentSlice)
    (live : SliceValid argumentAllocator before.heap arguments) : SliceValid argumentAllocator after.heap arguments := by
  rcases live with empty | stored
  · exact Or.inl empty
  · apply Or.inr
    by_cases empty : slice.length = 0
    · exact (post.frame arguments.address (Or.inl empty)).1.trans stored
    · obtain ⟨payload, _⟩ := owned.resolve_left empty
      have separate : arguments.address ≠ slice.address := by
        intro same
        rw [same, payload] at stored
        cases stored
      exact (post.frame arguments.address (Or.inr separate)).1.trans stored

end Released

def run (external : Release σ) (allocator : Nat) (payload : Option Bytes) (before : Session σ) :=
  execute external allocator payload assemblyItemDeinitCode ⟨before, false⟩

theorem run_equation (external : Release σ) (allocator : Nat) (payload : Option Bytes) (before : Session σ) :
    run external allocator payload before = match payload with
      | none => (.ok (), ⟨before, true⟩)
      | some slice =>
        let (result, reached) := free external allocator slice before
        match result with
        | .error fault => (.error (.release fault), ⟨reached, false⟩)
        | .ok () => (.ok (), ⟨reached, true⟩) := by
  cases payload with
  | none => rfl
  | some slice =>
    cases called : free external allocator slice before with
    | mk result reached => cases result with
      | error fault => simp [run, execute, assemblyItemDeinitCode, Stage.execute, called, Except.mapError]
      | ok returned => cases returned; simp [run, execute, assemblyItemDeinitCode, Stage.execute, called, Except.mapError]

def Touches (payload : Option Bytes) (id : Nat) : Prop :=
  ∃ slice, payload = some slice ∧ slice.length ≠ 0 ∧ id = slice.address

structure Post (payload : Option Bytes) (before : Session σ) (after : State σ) : Prop where
  valid : Valid after.memory
  invalidated : after.invalidated = true
  nextId : after.memory.memory.nextId = before.memory.nextId
  nextAddress : after.memory.memory.nextAddress = before.memory.nextAddress
  frame : ∀ id, ¬Touches payload id →
    after.memory.heap id = before.heap id ∧ after.memory.memory.heap.lookup id = before.memory.heap.lookup id
  dead : ∀ id, Touches payload id → after.memory.heap id = none ∧ after.memory.memory.heap.lookup id = none
  arguments : ∀ allocator arguments, SliceValid allocator before.heap arguments →
    SliceValid allocator after.memory.heap arguments

/-- Complete source-bound optional-payload destruction, relative to the supplied
native descriptor and frozen allocation/layout/free contracts. The value's own
allocation stays live; allocator.destroy is a distinct caller operation. -/
theorem run_verified (external : Release σ) (allocator : Nat) (payload : Option Bytes) (before : Session σ)
    (valid : Valid before) (owned : ∀ slice, payload = some slice → Owned allocator slice before) :
    ∃ after, run external allocator payload before = (.ok (), after) ∧ Post payload before after ∧
      after.memory.effects = match payload with
        | none => before.effects
        | some slice => if slice.length = 0 then before.effects else external slice before := by
  rw [run_equation]
  cases payload with
  | none =>
    refine ⟨⟨before, true⟩, rfl, ⟨valid, rfl, rfl, rfl, fun _ _ => ⟨rfl, rfl⟩, ?_, fun _ _ h => h⟩, rfl⟩
    intro id impossible
    obtain ⟨_, impossible, _⟩ := impossible
    cases impossible
  | some slice =>
    obtain ⟨after, executed, post, effects⟩ := free_verified external allocator slice before valid (owned slice rfl)
    simp only [executed]
    refine ⟨⟨after, true⟩, rfl, ⟨post.valid, rfl, post.nextId, post.nextAddress, ?_, ?_,
      post.arguments slice before after allocator (owned slice rfl)⟩, effects⟩
    · intro id untouched
      apply post.frame
      by_cases empty : slice.length = 0
      · exact Or.inl empty
      · exact Or.inr (fun same => untouched ⟨slice, rfl, empty, same⟩)
    · intro id touched
      obtain ⟨selected, same, nonempty, address⟩ := touched
      cases Option.some.inj same
      subst id
      exact post.dead nonempty

end Compiler.Extraction.AssemblyItemDeinit
