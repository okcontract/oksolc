/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyItemConstructorLocal

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem
open Compiler.Algebraic Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- Successful typed item preparation leaves room for the two-word scratch
array: its 224-byte, 16-aligned model layout leaves at least 16 address bytes.
Derive the actual scratch allocation without a separate capacity witness. -/
theorem prepare_scratch (item : Item) (debug : AssemblyItem.Fields.Values)
    (before constructed : World σ) (address : Compiler.ZigAir.Memory.Address)
    (valid : Valid before.memory) (domain : (item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (typed : AssemblyItem.Initializers.DebugTyped debug)
    (made : prepare item debug before = (.ok address, constructed)) :
    ∃ memory, Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) =
      .ok (.pointer (.pointer true false (.array 2 word)) ⟨constructed.memory.memory.nextId, 0⟩, memory) := by
  have prepared := (prepare_success item debug before constructed address valid domain typed made).2
  obtain ⟨pointer, allocated, allocation, counter⟩ := prepared.allocation
  have layout : AssemblyItem.viewType.layout = some ⟨224, 16⟩ := rfl
  simp only [Compiler.ZigAir.Memory.allocate, valid.memory, Bool.not_true, Bool.false_eq_true, ↓reduceIte, layout] at allocation
  split at allocation
  · contradiction
  · rename_i room
    have shaped := (Prod.mk.inj (Except.ok.inj allocation)).2
    have next := counter.trans (congrArg Compiler.ZigAir.Memory.State.nextAddress shaped.symm)
    dsimp only at next room
    have aligned : constructed.memory.memory.nextAddress % 4 = 0 := by omega
    have fits : constructed.memory.memory.nextAddress + 8 < Compiler.ZigAir.Memory.addressLimit := by
      unfold Compiler.ZigAir.Memory.addressLimit at room ⊢
      omega
    have positive : constructed.memory.memory.nextAddress ≠ 0 := by omega
    simp only [Compiler.ZigAir.Memory.allocate, prepared.valid.memory, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    change ∃ memory, (if constructed.memory.memory.nextAddress + (4 - constructed.memory.memory.nextAddress % 4) % 4 = 0 ∨
        constructed.memory.memory.nextAddress + (4 - constructed.memory.memory.nextAddress % 4) % 4 + 8 ≥ Compiler.ZigAir.Memory.addressLimit
      then _ else _) = Except.ok (_, memory)
    simp only [aligned, Nat.sub_zero, Nat.mod_self, Nat.add_zero, positive, Nat.not_le.mpr fits, or_self, ↓reduceIte]
    exact ⟨_, rfl⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem
