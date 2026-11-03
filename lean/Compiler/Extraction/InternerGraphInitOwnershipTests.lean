/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerGraphInitMemoryTests
import Compiler.ZigAir.MemoryOptionalPointerTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.GraphInit.Ownership.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray
open OwnerMemory.Tests

def owned (runtimeSafety : Bool) : World (Publication.Effects Nat) :=
  ⟨emptyGraph, ⟨(after runtimeSafety).heap, (after runtimeSafety).memory, ⟨fun _ => none, (after runtimeSafety).effects⟩⟩⟩

theorem native_empty (runtimeSafety : Bool) :
    Compiler.Extraction.ExpressionMap.Initialization.observeEmpty runtimeSafety (after runtimeSafety).memory ⟨3, 0⟩ = .ok () := by
  cases runtimeSafety <;> decide +kernel

theorem source_initializer (runtimeSafety : Bool) :
    zigInitOwned runtimeSafety 7 (before runtimeSafety true) ⟨3, 0⟩ sentinel = .ok (7, owned runtimeSafety) := by
  have executed := actual_source_initializer runtimeSafety
  change OwnerMemory.run runtimeSafety 7 (before runtimeSafety true) ⟨3, 0⟩ sentinel = _ at executed
  simp only [zigInitOwned, Ownership.run, executed, initialized, keys, native_empty, bind, Except.bind, owned]

theorem initial_ownership_from_execution (runtimeSafety : Bool) (meaning : Meaning) :
    Established runtimeSafety 7 (before runtimeSafety true) (owned runtimeSafety) 3 sentinel meaning := by
  obtain ⟨result, executed, established⟩ := Ownership.initialize_verified runtimeSafety 7 (before runtimeSafety true)
    3 (ownerCell runtimeSafety true) sentinel meaning (initial_valid runtimeSafety true) rfl rfl rfl rfl
  have equal : result = owned runtimeSafety :=
    (Prod.mk.inj (Except.ok.inj (executed.symm.trans (source_initializer runtimeSafety)))).2
  exact equal ▸ established

theorem allocator_effects_registry_and_parent_retained (runtimeSafety : Bool) (meaning : Meaning) :
    Publication.forget (owned runtimeSafety).memory = after runtimeSafety ∧
      (owned runtimeSafety).memory.effects.allocator = 5 ∧
      (owned runtimeSafety).memory.heap 2 = original.heap 2 ∧
      Represents (owned runtimeSafety).memory.memory ⟨0, 1, 2⟩ [1, 2] :=
  ⟨rfl, by cases runtimeSafety <;> rfl, by cases runtimeSafety <;> rfl, parent_offset_borrow_survives runtimeSafety meaning⟩

/-- Count-only lookup remains insufficient to establish ownership: missing
metadata and availability cannot enter the owned publication path. -/
theorem count_only_rejects (runtimeSafety : Bool) :
    Compiler.Extraction.ExpressionMap.Initialization.observeEmpty runtimeSafety (countOnly runtimeSafety).memory ⟨3, 0⟩ =
      .error .uninitialized := by cases runtimeSafety <;> decide +kernel

def changed (runtimeSafety : Bool) (offset : Nat) (value : Value) : Compiler.ZigAir.Memory.State :=
  withCells runtimeSafety ((mapCells runtimeSafety).set offset value)

inductive Corruption where
  | metadata | size | available | locked | missingLock
  deriving DecidableEq

def corruptValue : Value := .optionalObject Compiler.Extraction.ExpressionMap.metadataPointerType ⟨8, 8⟩
  (some (.leaf (.pointer Compiler.Extraction.ExpressionMap.metadataPointerType ⟨88, 0⟩)))

def sample (runtimeSafety : Bool) : Corruption → Compiler.ZigAir.Memory.State
  | .metadata => changed runtimeSafety (if runtimeSafety then 48 else 40) corruptValue
  | .size => changed runtimeSafety (if runtimeSafety then 64 else 48) (.scalar (.int false 32 1))
  | .available => changed runtimeSafety (if runtimeSafety then 68 else 52) (.scalar (.int false 32 1))
  | .locked => changed runtimeSafety 56 (.scalar (.int false 64 1))
  | .missingLock => withCells runtimeSafety ((mapCells runtimeSafety).filter (fun entry => entry.1 != 56))

def nativeValue : Compiler.Extraction.ExpressionMap.Initialization.Slot → Value
  | .metadata => .optionalObject Compiler.Extraction.ExpressionMap.metadataPointerType ⟨8, 8⟩ none
  | .size | .available => .scalar (.int false 32 0)
  | .lock => .scalar (.int false 64 0)

theorem captured_default_values (slot : Compiler.Extraction.ExpressionMap.Initialization.Slot) :
    slot.value = nativeValue slot := by cases slot <;> rfl

def expected (corruption : Corruption) (slot : Compiler.Extraction.ExpressionMap.Initialization.Slot) :
    Except Compiler.ZigAir.Memory.Fault Value := match corruption, slot with
  | .metadata, .metadata => .ok corruptValue
  | .size, .size | .available, .available => .ok (.scalar (.int false 32 1))
  | .locked, .lock => .ok (.scalar (.int false 64 1))
  | .missingLock, .lock => .error .uninitialized
  | _, _ => .ok (nativeValue slot)

/-- Closed field observations keep rejection diagnostics small without changing
the decision procedure, proof limits or the mutation acceptance rules. -/
theorem sample_reads (runtimeSafety : Bool) (corruption : Corruption)
    (slot : Compiler.Extraction.ExpressionMap.Initialization.Slot) (active : slot.Active runtimeSafety) :
    Compiler.Extraction.ExpressionMap.Initialization.read runtimeSafety (sample runtimeSafety corruption) ⟨3, 0⟩ slot =
      expected corruption slot := by
  cases runtimeSafety <;> cases corruption <;> cases slot <;>
    simp_all only [Compiler.Extraction.ExpressionMap.Initialization.Slot.Active,
      reduceCtorEq, false_implies, true_implies, Bool.false_eq_true]
  all_goals decide +kernel

theorem nonnull_metadata_rejects (runtimeSafety : Bool) :
    Compiler.Extraction.ExpressionMap.Initialization.observeEmpty runtimeSafety (sample runtimeSafety .metadata) ⟨3, 0⟩ =
      .error .unsupported :=
  Compiler.Extraction.ExpressionMap.Initialization.rejects_metadata _ _ _ corruptValue
    (sample_reads runtimeSafety .metadata .metadata (by intro impossible; cases impossible)) (by intro impossible; cases impossible)

theorem inconsistent_size_or_available_rejects (runtimeSafety : Bool) :
    Compiler.Extraction.ExpressionMap.Initialization.observeEmpty runtimeSafety (sample runtimeSafety .size) ⟨3, 0⟩ = .error .unsupported ∧
    Compiler.Extraction.ExpressionMap.Initialization.observeEmpty runtimeSafety (sample runtimeSafety .available) ⟨3, 0⟩ = .error .unsupported := by
  constructor
  · exact Compiler.Extraction.ExpressionMap.Initialization.rejects_size _ _ _ (.scalar (.int false 32 1))
      (sample_reads runtimeSafety .size .metadata (by intro impossible; cases impossible))
      (sample_reads runtimeSafety .size .size (by intro impossible; cases impossible)) (by decide)
  · exact Compiler.Extraction.ExpressionMap.Initialization.rejects_available _ _ _ (.scalar (.int false 32 1))
      (sample_reads runtimeSafety .available .metadata (by intro impossible; cases impossible))
      (sample_reads runtimeSafety .available .size (by intro impossible; cases impossible))
      (sample_reads runtimeSafety .available .available (by intro impossible; cases impossible)) (by decide)

theorem locked_or_missing_lock_rejects :
    Compiler.Extraction.ExpressionMap.Initialization.observeEmpty true (sample true .locked) ⟨3, 0⟩ = .error .unsupported ∧
    Compiler.Extraction.ExpressionMap.Initialization.observeEmpty true (sample true .missingLock) ⟨3, 0⟩ = .error .uninitialized := by
  constructor
  · exact Compiler.Extraction.ExpressionMap.Initialization.rejects_lock _ _ (.scalar (.int false 64 1))
      (sample_reads true .locked .metadata (by intro _; rfl))
      (sample_reads true .locked .size (by intro _; rfl))
      (sample_reads true .locked .available (by intro _; rfl))
      (sample_reads true .locked .lock (by intro _; rfl)) (by decide)
  · exact Compiler.Extraction.ExpressionMap.Initialization.missing_lock _ _ .uninitialized
      (sample_reads true .missingLock .metadata (by intro _; rfl))
      (sample_reads true .missingLock .size (by intro _; rfl))
      (sample_reads true .missingLock .available (by intro _; rfl))
      (sample_reads true .missingLock .lock (by intro _; rfl))

theorem no_owner_allocator_or_sentinel_is_manufactured (runtimeSafety : Bool) :
    ((owned runtimeSafety).memory.memory.heap.lookup 3).map (fun cell => cell.cells.lookup 0) = some none ∧
      (owned runtimeSafety).memory.memory.heap.lookup 99 = none ∧
      (owned runtimeSafety).memory.memory.nextId = (before runtimeSafety true).memory.nextId := by
  cases runtimeSafety <;> decide +kernel

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.GraphInit.Ownership.Tests
