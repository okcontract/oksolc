/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.OwnedKeysProofs

namespace Compiler.Extraction.OwnedKeys.Tests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage

def key : Key := ⟨1, 3, 0, [7, 9], 17⟩
def other : Key := { key with sequence := 18 }
def incoming : Entry := ⟨30, 5⟩
def cell : Cell := {
  item := ⟨2, none, 11⟩, otherValue := 0, itemAddress := 20,
  arguments := [7, 9], argumentsAddress := 21 }

def before : State := {
  table := store (store (fun _ => none) other ⟨40, 3⟩) key ⟨10, 2⟩
  memory := fun address =>
    if address = 20 then some ⟨1, .item cell.item⟩
    else if address = 10 ∨ address = 21 ∨ address = 30 ∨ address = 40 ∨ address = 50 then
      some ⟨1, .arguments [7, 9]⟩ else none }

structure Trace where
  attempts : Nat := 0
  frees : List Nat := []
  deriving DecidableEq, Repr

def getOrPut (_ : Key) (trace : Trace) : Bool × Trace :=
  (trace.attempts == 0, { trace with attempts := trace.attempts + 1 })

def onFree (borrow : ArgumentSlice) (trace : Trace) : Trace :=
  if borrow.items.isEmpty then trace else { trace with frees := trace.frees ++ [borrow.address] }

def run (code := publicationCode) (state := before) (entry := incoming) (trace : Trace := {}) :=
  code.run getOrPut onFree 1 key entry state trace

def nominal := run (trace := {})

theorem initial_live : Live 1 before := by
  intro query entry found
  by_cases first : query = key
  · subst query
    have eq : (⟨10, 2⟩ : Entry) = entry := by simpa [before, store] using found
    subst entry
    exact Or.inr rfl
  · by_cases second : query = other
    · subst query
      have eq : (⟨40, 3⟩ : Entry) = entry := by simpa [before, store, first] using found
      subst entry
      exact Or.inr rfl
    · simp [before, store, first, second] at found

theorem initial_unique : Unique before.table := by
  apply store_unique
  · apply store_unique
    · intro _ _ _ _ absent
      cases absent
    · intro _ _ absent
      cases absent
  · intro query entry found _ _
    by_cases same : query = other
    · subst query
      have eq : (⟨40, 3⟩ : Entry) = entry := by simpa [store] using found
      subst entry
      decide
    · simp [store, same] at found

theorem incoming_fresh : Fresh before.table key incoming := by
  intro query entry found _ _
  by_cases first : query = key
  · subst query
    have eq : (⟨10, 2⟩ : Entry) = entry := by simpa [before, store] using found
    subst entry
    decide
  · by_cases second : query = other
    · subst query
      have eq : (⟨40, 3⟩ : Entry) = entry := by simpa [before, store, first] using found
      subst entry
      decide
    · simp [before, store, first, second] at found

theorem replacement : nominal.1.1 = .ok () ∧ nominal.1.2.table key = some incoming ∧
    nominal.1.2.memory 10 = none ∧ nominal.2 = ⟨1, [10]⟩ := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem other_key_preserved : nominal.1.2.table other = some ⟨40, 3⟩ ∧
    nominal.1.2.memory 40 = before.memory 40 := by exact ⟨rfl, rfl⟩

theorem incoming_and_graph_live : Memory.SliceValid 1 nominal.1.2.memory (slice key incoming) ∧
    Memory.Resident 1 nominal.1.2.memory cell := by
  exact ⟨Or.inr rfl, rfl, Or.inr rfl⟩

theorem ownership_preserved : Live 1 nominal.1.2 ∧ Unique nominal.1.2.table := by
  have checked := run_preserves getOrPut onFree 1 key incoming before ({} : Trace)
    (fun _ => False) initial_live initial_unique (Or.inr rfl) incoming_fresh
    (fun _ _ _ _ impossible => impossible) (fun _ impossible => impossible)
  exact ⟨checked.1, checked.2.1⟩

theorem repeated_failure :
    (run (state := nominal.1.2) (trace := nominal.2)).1 = (.error .outOfMemory, nominal.1.2) ∧
    (run (state := nominal.1.2) (trace := nominal.2)).2 = ⟨2, [10]⟩ := by
  exact ⟨rfl, rfl⟩

def releaseSensitive (_ : Key) (trace : Trace) : Bool × Trace :=
  (trace.frees.contains 10, { trace with attempts := trace.attempts + 1 })

def reused := publicationCode.run releaseSensitive onFree 1 key ⟨50, 8⟩ nominal.1.2 nominal.2

theorem release_effect_controls_later_attempt : reused.1.1 = .ok () ∧
    reused.1.2.table key = some ⟨50, 8⟩ ∧ reused.2 = ⟨2, [10, 30]⟩ := by
  exact ⟨rfl, rfl, rfl⟩

def emptyKey : Key := { key with arguments := [] }
def emptyState : State := { before with table := store (fun _ => none) emptyKey ⟨20, 2⟩ }
def emptyRun := publicationCode.run getOrPut onFree 1 emptyKey ⟨20, 5⟩ emptyState ({} : Trace)

theorem empty_sentinel : emptyRun.1.1 = .ok () ∧ emptyRun.1.2.memory = before.memory ∧
    emptyRun.1.2.table emptyKey = some ⟨20, 5⟩ ∧ emptyRun.2 = ⟨1, []⟩ := by
  exact ⟨rfl, rfl, rfl, rfl⟩

def absentState : State := { before with table := fun _ => none }

theorem new_key : (run (state := absentState)).1.1 = .ok () ∧
    (run (state := absentState)).1.2.table key = some incoming ∧
    (run (state := absentState)).1.2.memory = before.memory ∧
    (run (state := absentState)).2 = ⟨1, []⟩ := by exact ⟨rfl, rfl, rfl, rfl⟩

def missingFree : Code := { publicationCode with releaseExisting := false }
def missingStore : Code := { publicationCode with replaceKey := false }

theorem missing_free_leaks : (run (code := missingFree)).1.2.memory 10 = before.memory 10 := rfl

theorem missing_store_dangles : (run (code := missingStore)).1.2.table key = some ⟨10, 5⟩ ∧
    (run (code := missingStore)).1.2.memory 10 = none := by exact ⟨rfl, rfl⟩

theorem aliased_input_dangles : (run (entry := ⟨10, 5⟩)).1.2.table key = some ⟨10, 5⟩ ∧
    (run (entry := ⟨10, 5⟩)).1.2.memory 10 = none := by exact ⟨rfl, rfl⟩

theorem wrong_allocator_fault :
    (publicationCode.run getOrPut onFree 2 key incoming before ({} : Trace)).1.1 = .error .wrongAllocator ∧
    (publicationCode.run getOrPut onFree 2 key incoming before ({} : Trace)).2 = ⟨1, [10]⟩ := by
  exact ⟨rfl, rfl⟩

end Compiler.Extraction.OwnedKeys.Tests
