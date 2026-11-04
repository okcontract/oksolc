/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeRelocationFrame

namespace Compiler.Extraction.RepresentativeArray.Backing.Fallback
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

/-- Enter the allocation branch with the previously evaluated old view.
Ordinary OOM precedes the items read; later rejection retains the suffix's
reached memory and effects. This does not model remap or claim
that the saved pre-remap view is preserved by an arbitrary remap callback. -/
def run (allocate : Registry.Allocate σ) (release : Release.External σ) (allocator : Nat)
    (header oldData : Address) (oldCapacity capacity : Nat) (before : Session σ) :
    Except Release.Fault (Option Unit) × Session σ :=
  let (allocated, reserved) := Registry.run allocate allocator capacity before
  match allocated with
  | .error (.memory fault) => (.error (.memory fault), reserved)
  | .error (.registry fault) => (.error (.ownership fault), reserved)
  | .ok none => (.ok none, reserved)
  | .ok (some data) =>
    let (relocated, reached) := Relocation.run release allocator header oldData data oldCapacity capacity reserved
    (relocated.map some, reached)

theorem of_steps (allocate : Registry.Allocate σ) (release : Release.External σ) (allocator : Nat)
    (header oldData data : Address) (oldCapacity capacity : Nat) (before reserved after : Session σ)
    (allocated : Registry.run allocate allocator capacity before = (.ok (some data), reserved))
    (relocated : Relocation.run release allocator header oldData data oldCapacity capacity reserved = (.ok (), after)) :
    run allocate release allocator header oldData oldCapacity capacity before = (.ok (some ()), after) := by
  simp only [run, allocated, relocated, Except.map]

/-- OOM is propagated before evaluating even a malformed or unreadable header.
The allocator's reached private effects are retained. -/
theorem oom (allocate : Registry.Allocate σ) (release : Release.External σ) (allocator : Nat)
    (header oldData : Address) (oldCapacity capacity : Nat) (before reserved : Session σ)
    (allocated : Registry.run allocate allocator capacity before = (.ok none, reserved)) :
    run allocate release allocator header oldData oldCapacity capacity before = (.ok none, reserved) := by
  simp only [run, allocated]

end Compiler.Extraction.RepresentativeArray.Backing.Fallback
