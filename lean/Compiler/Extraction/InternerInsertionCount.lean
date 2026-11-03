/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionNative

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

inductive CountFault where
  | memory (reason : Compiler.ZigAir.Memory.Fault)
  | mismatch (native logical : Nat)
  deriving DecidableEq, Repr

/-- Read the reached items slice through its native owner fields. This read
does not dereference the backing or inspect rows; malformed/uninitialized fields
remain semantic rejection, not the source's ExpressionCapacity outcome. -/
def headerCount (state : Compiler.ZigAir.Memory.State) (container : Nat) : Except Compiler.ZigAir.Memory.Fault Nat := do
  let items ← readItems state (Owner.headerAddress ⟨container, 0⟩)
  let .slice _ _ length := items | .error .malformed
  return length

/-- Bind the supplied logical rows to the native count before executing any
allocation or cleanup. This is a validation check, not a new Zig branch. -/
def checkedCount (state : Compiler.ZigAir.Memory.State) (container : Nat) (cells : List Storage.Cell) : Except CountFault Nat := do
  let count ← (headerCount state container).mapError CountFault.memory
  if count = cells.length then return count else .error (.mismatch count cells.length)

theorem headerCount_read (state : Compiler.ZigAir.Memory.State) (container count : Nat) (backing : Compiler.ZigAir.Memory.Address)
    (loaded : readItems state (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType backing count)) :
    headerCount state container = .ok count := by simp only [headerCount, loaded, bind, Except.bind, pure, Except.pure]

theorem checkedCount_read (state : Compiler.ZigAir.Memory.State) (container : Nat) (cells : List Storage.Cell)
    (backing : Compiler.ZigAir.Memory.Address)
    (loaded : readItems state (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType backing cells.length)) :
    checkedCount state container cells = .ok cells.length := by
  simp only [checkedCount, headerCount_read state container cells.length backing loaded, Except.mapError,
    bind, Except.bind, ↓reduceIte, pure, Except.pure]

theorem checkedCount_mismatch (state : Compiler.ZigAir.Memory.State) (container count : Nat) (cells : List Storage.Cell)
    (observed : headerCount state container = .ok count) (different : count ≠ cells.length) :
    checkedCount state container cells = .error (.mismatch count cells.length) := by
  simp only [checkedCount, observed, Except.mapError, bind, Except.bind, different, ↓reduceIte]

/-- The admitted insertion uses a u32 Id and rejects an items length at its maximum. -/
def roomForCount (count : Nat) : Bool := decide (count < 2 ^ 32 - 1)

/-- The existing source executor receives its capacity input from the native
header. Acceptance also checks row-count correspondence. Other field, payload,
map and allocator obligations remain separate; this adapter does not assert them. -/
def checkedExecution (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (deterministic : Bool) (cells : List Storage.Cell) (before : World (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ) := none) := do
  let count ← checkedCount before.memory.memory container cells
  return executionWithRoom ops allocate runtimeSafety allocator container source itemSource meaning input key normalized
    deterministic (roomForCount count) cells before growth

/-- Every existing execution theorem lifts at the reached native read, including
its exact result and memory. No supplied Boolean capacity oracle is accepted. -/
theorem checkedExecution_read (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (deterministic : Bool) (cells : List Storage.Cell) (before : World (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (backing : Compiler.ZigAir.Memory.Address)
    (loaded : readItems before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType backing cells.length)) :
    checkedExecution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized deterministic cells before growth =
      .ok (execution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized deterministic cells before growth) := by
  simp only [checkedExecution, checkedCount_read _ _ _ backing loaded, bind, Except.bind, pure, Except.pure, execution, roomForCount]

/-- A failed native count binding never executes insertion or converts the
rejection to an ordinary capacity/OOM outcome. The input world is still the
reached world supplied by the caller. -/
theorem checkedExecution_rejected (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (deterministic : Bool) (cells : List Storage.Cell) (before : World (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (fault : CountFault)
    (rejected : checkedCount before.memory.memory container cells = .error fault) :
    checkedExecution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized deterministic cells before growth =
      .error fault := by simp only [checkedExecution, rejected, bind, Except.bind]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
