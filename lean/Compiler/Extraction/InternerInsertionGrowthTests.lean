/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeRegisteredGrowthAppendTests
import Compiler.Extraction.InternerInsertionNative
import Compiler.Extraction.AssemblyItemCreationFieldTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.GrowthTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray


def copied : AssemblyClone.NativeFields.ItemValue := {AssemblyItem.Creation.NativeFields.Tests.input with item := Append.Registered.GrowthTests.fourth.item, verbatim := none}
def incoming : ArgumentSlice := ⟨1, Append.Registered.GrowthTests.fourth.arguments⟩
def key : Key := ⟨Append.Registered.GrowthTests.fourth.item.kind, 0, Append.Registered.GrowthTests.fourth.item.data, Append.Registered.GrowthTests.fourth.arguments, Append.Registered.GrowthTests.fourth.sequence⟩
def lift (state : Session Nat) : Session (Publication.Effects Nat) := ⟨state.heap, state.memory, ⟨fun _ => none, state.effects⟩⟩
def frame (safety : Bool) : Frame Nat := ⟨⟨⟨⟨lift (Append.Registered.GrowthTests.before safety), false⟩, some copied⟩, some 0⟩, some incoming⟩
def execute (safety : Bool) := append safety Append.Registered.GrowthTests.request 7 3 DescriptorRelation.AppendTests.cells copied key incoming 0 {} (frame safety) (some Append.Registered.GrowthTests.calls)

/-- Reached insertion locals feed the same growing append. The lifted release
changes only private effects; it retains the exact publication key table. -/
theorem forwarded (safety : Bool) :
    execute safety = let (result, after) := Append.Registered.GrowthTests.execute safety
      (result.mapError Fault.append, withMemory (frame safety) (lift after)) := by
  cases safety <;> insertion_kernel_rfl

theorem derived_queries (safety : Bool) :
    (execute safety).1 = .ok true ∧ (memory (execute safety).2).heap 2 = none ∧
    (memory (execute safety).2).effects.allocator = 78 ∧
    (∀ query, (memory (execute safety).2).effects.keys query = none) ∧
    (∀ id, representativeFields (memory (execute safety).2).memory ⟨3, 16⟩ id =
      .ok ((Storage.representativeProgram.run (DescriptorRelation.AppendTests.cells ++ [Append.Registered.GrowthTests.fourth]) id).map (DescriptorRelation.values id.toNat))) := by
  obtain ⟨after, executed, _, _, _, dead, _, effects, _, _, queries⟩ := Append.Registered.GrowthTests.derived_contract safety
  rw [forwarded]
  rw [executed]
  exact ⟨rfl, dead, effects, fun _ => rfl, queries⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.GrowthTests
