/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.MemoryProofs
import Compiler.Extraction.StorageOperationTests

namespace Compiler.Extraction.Memory.Tests
open Compiler.Extraction.Storage Compiler.Extraction.Storage.OperationTests

def heap : Heap := fun address =>
  if address = 0 then some ⟨3, .representatives cells⟩
  else if address = 4 then some ⟨3, .item left.item⟩
  else if address = 8 then some ⟨3, .item right.item⟩
  else if address = 12 then some ⟨3, .item nested.item⟩
  else if address = 16 then some ⟨3, .arguments nested.arguments⟩
  else none

def moved : Heap := write (write heap 20 (some ⟨3, .representatives cells⟩)) 0 none

theorem resident : GraphResident 3 heap cells := by
  simp [GraphResident, cells, Resident, SliceValid, Cell.argumentSlice,
    left, right, nested, heap]

example : Vector 3 heap 0 cells := rfl
example : moveVector heap 3 0 20 true = .ok moved := by rfl
example : moveVector heap 3 0 0 true = .ok heap := by rfl
example : moveVector heap 3 0 20 false = .error .outOfMemory := by rfl
example : moveVector heap 3 0 16 true = .error .notFresh := by rfl
example : readRepresentative moved 0 2 = .error .unallocated := by rfl
example : readRepresentative moved 20 2 = .ok nested := by rfl
example : readArgument moved nested.argumentSlice 0 = .ok 0 := by rfl
example : readArgument moved nested.argumentSlice 1 = .ok 1 := by rfl
example : readArgument moved nested.argumentSlice 2 = .error .bounds := by rfl
example : releaseSlice heap 3 ⟨0, []⟩ = .ok heap := by rfl
example : release heap 9 16 = .error .wrongAllocator := by rfl
example : release heap 3 16 = .ok (write heap 16 none) := by rfl
example : readArgument (write heap 16 none) nested.argumentSlice 0 = .error .unallocated := by rfl
example : readArgument heap ⟨0, [0]⟩ 0 = .error .wrongType := by rfl
-- A forged ghost payload does not change the actual memory read.
example : readArgument heap ⟨16, [9, 9]⟩ 0 = .ok 0 := by rfl

end Compiler.Extraction.Memory.Tests
