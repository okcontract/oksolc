/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.OwnedKeysPhysical
import Compiler.Extraction.OwnedKeysTests

namespace Compiler.Extraction.OwnedKeys.Physical.Tests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.Extraction.Memory.Arguments
open Compiler.ZigAir.Memory.WordArray

def key : Key := ⟨1, 1, 0, [7], 0⟩
def incoming : Entry := ⟨1, 5⟩
def cell (base : Nat) : Compiler.ZigAir.Memory.Allocation :=
  ⟨base, .array 1 word, [(0, number 7)], true, false⟩
def scratch : Compiler.ZigAir.Memory.Allocation := ⟨16, .array 1 word, [], true, true⟩
def before : State Nat := {
  table := store (fun _ => none) key ⟨0, 2⟩
  memory := ⟨(fun id => if id < 3 then some ⟨7, .arguments [7]⟩ else none),
    ⟨[(0, cell 4), (1, cell 8), (2, cell 12), (3, scratch)], 4, 20⟩, 10⟩ }

def external : Normalization.External Nat where
  allocate _ _ _ effects := (none, effects)
  free owned state := state.effects + 100 + owned.address

def probe (fail : Bool) : Probe Nat := fun _ state => (!fail, state.effects + 1)
def observed (fail := false) (code := publicationCode) (state := before) (allocator := 7) :=
  code.execute (operations (probe fail) external allocator) key incoming state

theorem initial_valid : Normalization.Valid before.memory := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · intro allocator id values _ stored
    by_cases inside : id < 3
    · have same : 7 = allocator ∧ [7] = values := by simpa [before, inside] using stored
      rcases same with ⟨rfl, rfl⟩
      have cases : id = 0 ∨ id = 1 ∨ id = 2 := by omega
      rcases cases with rfl | rfl | rfl
      all_goals
        refine ⟨⟨_, by rfl', rfl, rfl, rfl⟩, rfl, ?_⟩
        intro index bound
        have only : index = 0 := by simp only [List.length_cons, List.length_nil] at bound; omega
        subst index
        rfl'
    · simp [before, inside] at stored
  · intro id block stored
    have inside : id < 3 := by
      by_cases inside : id < 3
      · exact inside
      · simp [before, inside] at stored
    have cases : id = 0 ∨ id = 1 ∨ id = 2 := by omega
    rcases cases with rfl | rfl | rfl <;> exact ⟨_, by rfl', rfl⟩

theorem initial_live : Live 7 before.logical := by
  intro query entry found
  by_cases same : query = key
  · subst query
    have entryEq : entry = ⟨0, 2⟩ := by simpa [State.logical, before, store] using found.symm
    subst entry; exact Or.inr rfl
  · simp [State.logical, before, store, same] at found

theorem initial_unique : Unique before.table := by
  exact store_unique _ key ⟨0, 2⟩ (fun _ _ _ _ absent => by cases absent)
    (fun _ _ absent => by cases absent)

theorem incoming_fresh : Fresh before.table key incoming := by
  intro query entry found _ _
  by_cases same : query = key
  · subst query
    have entryEq : entry = ⟨0, 2⟩ := by simpa [before, store] using found.symm
    subst entry; decide
  · simp [before, store, same] at found

theorem borrowed_apart : Apart before.table (fun id => 2 ≤ id) := by
  intro query entry found _
  by_cases same : query = key
  · subst query
    have entryEq : entry = ⟨0, 2⟩ := by simpa [before, store] using found.symm
    subst entry; decide
  · simp [before, store, same] at found

/-- Inhabited contracts with live incoming, old, borrowed and uninitialized
allocations. This fixture does not claim native hash-map refinement. -/
theorem complete_ownership (fail : Bool) :
    Preserved 7 (fun id => 2 ≤ id) (slice key incoming) before (observed fail).2 :=
  run_preserves (probe fail) external 7 key incoming before _ initial_valid initial_live initial_unique
    (Or.inr rfl) incoming_fresh borrowed_apart (fun _ => by decide)

theorem replacement : (observed).1 = .ok () ∧ (observed).2.table key = some incoming ∧
    (observed).2.memory.heap 0 = none ∧ (observed).2.memory.memory.heap.lookup 0 = none ∧
    (observed).2.memory.effects = 111 := ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩

theorem borrowed_contents :
    Compiler.ZigAir.Memory.load (observed).2.memory.memory ((⟨2, 0, 1⟩ : View).pointer 0) = .ok (number 7) ∧
    Compiler.ZigAir.Memory.load (observed).2.memory.memory ((⟨3, 0, 1⟩ : View).pointer 0) = .error .uninitialized ∧
    (observed).2.memory.memory.nextId = 4 ∧ (observed).2.memory.memory.nextAddress = 20 :=
  ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem oom : observed true = (.error .outOfMemory,
    { before with memory := { before.memory with effects := 11 } }) := by rfl'

theorem wrong_allocator : observed (allocator := 8) =
    (.error (.release (.ownership .wrongAllocator)),
      { before with memory := { before.memory with effects := 11 } }) := by rfl'

def missing : State Nat := { before with memory := { before.memory with
  memory := Compiler.ZigAir.Memory.erase before.memory.memory 0 } }
theorem missing_typed_lifetime : observed (state := missing) =
    (.error (.release (.memory .unallocated)),
      { missing with memory := { missing.memory with effects := 11 } }) := by rfl'

def stack : State Nat := { before with memory := { before.memory with memory :=
  { before.memory.memory with heap := [(0, { cell 4 with stack := true }), (1, cell 8), (2, cell 12), (3, scratch)] } } }
theorem stack_rejected : observed (state := stack) =
    (.error (.release (.memory .memoryValidity)),
      { stack with memory := { stack.memory with effects := 11 } }) := by rfl'

def emptyKey : Key := { key with arguments := [] }
def empty : State Nat := { before with table := store (fun _ => none) emptyKey ⟨2, 2⟩ }
theorem empty_sentinel : run (probe false) external 7 emptyKey ⟨2, 5⟩ empty =
    (.ok (), ⟨store empty.table emptyKey ⟨2, 5⟩, { before.memory with effects := 11 }⟩) := by rfl'

def absent : State Nat := { before with table := fun _ => none }
theorem new_entry : observed (state := absent) = (.ok (),
    { table := store absent.table key incoming, memory := { absent.memory with effects := 11 } }) := by rfl'

theorem omitted_release_leaks :
    (observed (code := { publicationCode with releaseExisting := false })).2.memory.memory.heap.lookup 0 = some (cell 4) := by rfl'
theorem omitted_key_store_dangles :
    (observed (code := { publicationCode with replaceKey := false })).2.table key = some ⟨0, 5⟩ ∧
    (observed (code := { publicationCode with replaceKey := false })).2.memory.memory.heap.lookup 0 = none := ⟨by rfl', by rfl'⟩

end Compiler.Extraction.OwnedKeys.Physical.Tests
