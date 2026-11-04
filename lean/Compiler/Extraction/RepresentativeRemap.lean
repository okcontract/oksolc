/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeRemapProgram
import Compiler.Extraction.RepresentativeBackingRelease

namespace Compiler.Extraction.RepresentativeArray.Remap
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

/-- This identifies a captured callback body, not an allocator brand. Deriving
the vtable target and evaluated arguments at a compiler caller remains required. -/
inductive Callback where
  | noRemap (context returnAddress : Nat)
  | unsupported
  deriving DecidableEq

/-- The positive-size Expression specialization of Allocator.remap. Zero new
length frees first; zero old length and byte-count overflow skip rawRemap.
The shared full-extent checker validates rawRemap's ownership precondition;
its computed erased heap is discarded, since checking never executes a free.
Unknown callbacks reject explicitly without inventing their reached state. -/
def run (callback : Callback) (release : Backing.Release.External σ) (allocator : Nat)
    (data : Address) (oldCapacity capacity : Nat) (before : Session σ) :
    Except Backing.Release.Fault (Option Address) × Session σ :=
  if capacity ≥ addressLimit then (.error (.memory .malformed), before) else
  if capacity = 0 then
    let (result, after) := Backing.Release.run release allocator data oldCapacity before
    (result.map (fun _ => some data), after)
  else if oldCapacity = 0 then (.ok none, before)
  else if capacity * 32 ≥ addressLimit then (.ok none, before)
  else match Backing.Release.check allocator data oldCapacity before with
    | .error reason => (.error reason, before)
    | .ok (_, _, base) => match callback with
      | .unsupported => (.error (.memory .unsupported), before)
      | .noRemap context returnAddress =>
        match noRemap context base (oldCapacity * 32) 8 (capacity * 32) returnAddress with
        | none => (.ok none, before)
        | some _ => (.error (.memory .unsupported), before)

theorem zero_new (callback : Callback) (release : Backing.Release.External σ) (allocator : Nat)
    (data : Address) (oldCapacity : Nat) (before : Session σ) :
    run callback release allocator data oldCapacity 0 before =
      let (result, after) := Backing.Release.run release allocator data oldCapacity before
      (result.map (fun _ => some data), after) := by
  simp only [run, show ¬0 ≥ addressLimit by decide, ↓reduceIte]

theorem empty_old (callback : Callback) (release : Backing.Release.External σ) (allocator capacity : Nat)
    (data : Address) (before : Session σ) (positive : 0 < capacity) (width : capacity < addressLimit) :
    run callback release allocator data 0 capacity before = (.ok none, before) := by
  simp only [run, if_neg (Nat.not_le.mpr width), if_neg (by omega : capacity ≠ 0), ↓reduceIte]

theorem byte_overflow (callback : Callback) (release : Backing.Release.External σ) (allocator oldCapacity capacity : Nat)
    (data : Address) (before : Session σ) (positive : 0 < capacity) (width : capacity < addressLimit)
    (overflow : addressLimit ≤ capacity * 32) :
    run callback release allocator data oldCapacity capacity before = (.ok none, before) := by
  simp only [run, if_neg (Nat.not_le.mpr width), if_neg (by omega : capacity ≠ 0), if_pos overflow]
  split <;> rfl

/-- Derive the raw callback precondition from the existing owner and native
complete extent. The admitted body then returns null without any heap or
private-effect mutation; it supplies the saved-view frame needed by fallback. -/
theorem refuses (release : Backing.Release.External σ) (allocator context returnAddress oldCapacity capacity : Nat)
    (data : Address) (before : Session σ) (valid : Valid before)
    (owned : Backing.Release.Owned allocator data oldCapacity before)
    (positive : 0 < capacity) (width : capacity < addressLimit) :
    run (.noRemap context returnAddress) release allocator data oldCapacity capacity before = (.ok none, before) := by
  obtain ⟨base, checked⟩ := Backing.Release.checked_of_owned allocator data oldCapacity before valid owned
  simp only [run, if_neg (Nat.not_le.mpr width), if_neg (by omega : capacity ≠ 0)]
  split
  · rfl
  · split
    · rfl
    · simp only [checked, noRemap]

theorem positive_reached (callback : Callback) (release : Backing.Release.External σ) (allocator oldCapacity capacity : Nat)
    (data : Address) (before : Session σ) (positive : 0 < capacity) :
    (run callback release allocator data oldCapacity capacity before).2 = before := by
  unfold run
  split
  · rfl
  · rw [if_neg (by omega : capacity ≠ 0)]
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · cases callback <;> rfl

theorem positive_no_success (callback : Callback) (release : Backing.Release.External σ) (allocator oldCapacity capacity : Nat)
    (data : Address) (before : Session σ) (positive : 0 < capacity) (target : Address) :
    (run callback release allocator data oldCapacity capacity before).1 ≠ .ok (some target) := by
  unfold run
  split
  · simp
  · rw [if_neg (by omega : capacity ≠ 0)]
    split
    · simp
    · split
      · simp
      · split
        · simp
        · cases callback <;> simp [noRemap]

end Compiler.Extraction.RepresentativeArray.Remap
