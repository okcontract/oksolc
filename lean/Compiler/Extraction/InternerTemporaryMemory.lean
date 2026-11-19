/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorFrame
import Compiler.ZigAir.MemoryWordCopy

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryMemory
open Compiler.Algebraic Compiler.ZigAir.Memory.WordArray

/-- Decode the actual readonly u32 load used by argument initializers. No
logical graph observation supplies the loaded ID. -/
def readId (memory : Compiler.ZigAir.Memory.State) (source : View) (index : Nat) :
    Except Compiler.ZigAir.Memory.Fault NodeId :=
  match Compiler.ZigAir.Memory.load memory (Compiler.ZigAir.Memory.WordCopy.readPointer source index) with
  | .error fault => .error fault
  | .ok (.scalar (.int false 32 value)) => .ok (BitVec.ofInt 32 value)
  | .ok _ => .error .unsupported

theorem readId_of_load (memory : Compiler.ZigAir.Memory.State) (source : View) (index : Nat) (value : NodeId)
    (loaded : Compiler.ZigAir.Memory.load memory (source.pointer index) = .ok (number value)) :
    readId memory source index = .ok value := by
  simp only [readId, Compiler.ZigAir.Memory.WordCopy.load_readonly, loaded, number]
  simp

/-- A reached initializer store preserves the existing semantic registry,
physical allocation invariant and lifetime injection. Its stack buffer must be
unregistered, so this cannot certify writes to a graph-owned argument buffer. -/
theorem stored_valid (before : Session σ) (memory : Compiler.ZigAir.Memory.State)
    (target : View) (index : Nat) (value : NodeId) (valid : Valid before)
    (unregistered : before.heap target.allocation = none) (inside : index < target.length)
    (stored : Compiler.ZigAir.Memory.store before.memory (target.pointer index) (number value) = .ok memory) :
    Valid ({ before with memory } : Session σ) :=
  ⟨Compiler.ZigAir.Memory.store_preserves_valid _ _ _ _ valid.memory stored,
    related_frame before.heap before.memory memory target valid.related unregistered
      (frame_store _ _ target index value inside stored).heapFrame,
    valid.injected.retained (Compiler.ZigAir.Memory.store_retains_shape _ _ _ _ stored)⟩

/-- Actual array allocation establishes the lifetime and storage metadata;
initializer stores preserve them while filling the contents. -/
theorem allocated_array (before allocated after : Compiler.ZigAir.Memory.State)
    (extent : Nat) (pointer : Compiler.ZigAir.Memory.Value)
    (allocation : Compiler.ZigAir.Memory.allocate before (.array extent word) = .ok (pointer, allocated))
    (retained : allocated.heap.RetainsShape after.heap) :
    ∃ cell, after.heap.lookup before.nextId = some cell ∧ cell.type = .array extent word ∧
      cell.writable = true ∧ cell.stack = true := by
  obtain ⟨layout, base, _, _, rfl⟩ := Compiler.ZigAir.Memory.allocate_shape _ _ _ _ allocation
  obtain ⟨cell, found, shape⟩ := retained before.nextId ⟨base, .array extent word, [], true, true⟩
    (by simp only [Compiler.ZigAir.Memory.Heap.lookup_cons, ↓reduceIte])
  exact ⟨cell, found, shape.2.1, shape.2.2.1, shape.2.2.2⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryMemory
