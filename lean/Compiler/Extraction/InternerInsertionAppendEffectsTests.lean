/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionAppendRecursionEffects
import Compiler.Extraction.RepresentativeBackingTrace
import Compiler.Extraction.InternerInsertionReleaseEffectsTests
import Compiler.Extraction.InternerInsertionGrowthTests
import Compiler.Extraction.RepresentativeBackingRegistryTests
import Compiler.Extraction.AssemblyCloneQueryTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.AppendEffectTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Normalization.HostTrace

def history : List Event := [.itemFree 99]
def recordFrame (before : Frame σ) : Frame (Recorded σ) := before.mapEffects (fun effects => ⟨effects, history⟩)
def grow (safety : Bool) (response : Option Nat := some 2048)
    (state : Session Nat := Append.Registered.GrowthTests.before safety)
    (calls : Growth.Registered.Callbacks Nat := Append.Registered.GrowthTests.calls) :=
  append safety (recordBacking (Append.Registered.GrowthTests.request response)) 7 3 DescriptorRelation.AppendTests.cells
    GrowthTests.copied GrowthTests.key GrowthTests.incoming 0 {}
    (recordFrame (withMemory (GrowthTests.frame safety) (GrowthTests.lift state))) (some (recordGrowth calls))

/-- Existing relocation execution specializes the general native theorem. -/
theorem growth_erases (safety : Bool) (before : Frame (Recorded Nat)) :
    append safety Append.Registered.GrowthTests.request 7 3 DescriptorRelation.AppendTests.cells
        GrowthTests.copied GrowthTests.key GrowthTests.incoming 0 {} (before.mapEffects Recorded.effects) (some Append.Registered.GrowthTests.calls) =
      ((append safety (recordBacking Append.Registered.GrowthTests.request) 7 3 DescriptorRelation.AppendTests.cells
        GrowthTests.copied GrowthTests.key GrowthTests.incoming 0 {} before (some (recordGrowth Append.Registered.GrowthTests.calls))).1,
       (append safety (recordBacking Append.Registered.GrowthTests.request) 7 3 DescriptorRelation.AppendTests.cells
        GrowthTests.copied GrowthTests.key GrowthTests.incoming 0 {} before (some (recordGrowth Append.Registered.GrowthTests.calls))).2.mapEffects Recorded.effects) :=
  HostTrace.append_erases _ _ safety 7 3 GrowthTests.copied GrowthTests.key GrowthTests.incoming _ _ _ before

theorem growth_order (safety : Bool) :
    (grow safety).1 = .ok true ∧ (memory (grow safety).2).effects.allocator =
      ⟨78, history ++ [.backingAllocate 7 320 8 (some 2048), .backingFree 7 512 96 8]⟩ ∧
    (memory (grow safety).2).heap 2 = none := by
  cases safety <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem growth_oom (safety : Bool) :
    (grow safety none).1 = .ok false ∧ (memory (grow safety none).2).effects.allocator =
      ⟨7, history ++ [.backingAllocate 7 320 8 none]⟩ ∧
    (memory (grow safety none).2).memory = (Append.Registered.GrowthTests.before safety).memory := by
  cases safety <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem rejected_region (safety : Bool) :
    (grow safety (some 2049)).1 = .error (.append (.memory .memoryValidity)) ∧
    (memory (grow safety (some 2049)).2).effects.allocator = ⟨7, history ++ [.backingAllocate 7 320 8 (some 2049)]⟩ := by
  cases safety <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem unsupported_remap_skips_host (safety : Bool) :
    let result := grow safety (calls := ⟨.unsupported, Append.Registered.GrowthTests.release⟩)
    result.1 = .error (.append (.memory .unsupported)) ∧ (memory result.2).effects.allocator = ⟨0, history⟩ := by
  cases safety <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem partial_copy_keeps_allocation (safety : Bool) :
    let result := grow safety (state := Append.Registered.GrowthTests.damaged safety)
    result.1 = .error (.append (.memory .uninitialized)) ∧
    (memory result.2).effects.allocator = ⟨7, history ++ [.backingAllocate 7 320 8 (some 2048)]⟩ ∧
    (memory result.2).heap 2 = some ⟨7, .representatives DescriptorRelation.AppendTests.cells⟩ ∧
    (memory result.2).heap 4 = some ⟨7, .representatives []⟩ := by
  cases safety <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem partial_publication_keeps_free (safety : Bool) :
    let result := grow safety (state := Append.Registered.GrowthTests.readonly safety)
    result.1 = .error (.append (.memory .readOnly)) ∧
    (memory result.2).effects.allocator = ⟨78, history ++ [.backingAllocate 7 320 8 (some 2048), .backingFree 7 512 96 8]⟩ ∧
    (memory result.2).heap 2 = none ∧ (memory result.2).heap 4 = some ⟨7, .representatives []⟩ := by
  cases safety <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem missing_local_skips_host :
    let before := recordFrame { GrowthTests.frame false with duplicate := none }
    append false (recordBacking Append.Registered.GrowthTests.request) 7 3 DescriptorRelation.AppendTests.cells GrowthTests.copied
      GrowthTests.key GrowthTests.incoming 0 {} before (some (recordGrowth Append.Registered.GrowthTests.calls)) =
      (.error (.base .missingValue), before) := by dsimp only; insertion_kernel_rfl

def reserve (capacity : Nat) (before : Session Backing.Release.Tests.Effects) :=
  Backing.Registry.run (recordBacking Backing.Registry.Tests.request) 7 capacity (before.mapEffects (fun effects => ⟨effects, history⟩))

theorem registry_collision_keeps_request :
    (reserve 7 Backing.Registry.Tests.collision).1 = .error (.registry .notFresh) ∧
    (reserve 7 Backing.Registry.Tests.collision).2.effects.events = history ++ [.backingAllocate 7 224 8 (some 800)] ∧
    (reserve 7 Backing.Registry.Tests.collision).2.memory = Backing.Registry.Tests.ready.memory :=
  ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem empty_and_invalid_skip_host :
    (reserve 0 Backing.Registry.Tests.invalid).1 = .ok (some ⟨0, 0⟩) ∧
    (reserve 0 Backing.Registry.Tests.invalid).2.effects.events = history ∧
    (reserve 7 Backing.Registry.Tests.invalid).1 = .error (.memory .malformed) ∧
    (reserve 7 Backing.Registry.Tests.invalid).2.effects.events = history :=
  ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

open AssemblyClone.NativeFields.QueryTests (ready copied incoming old request)

def legacyFrame (safety first : Bool) : Frame (Recorded Nat) := recordFrame
  ⟨⟨⟨⟨GrowthTests.lift (ready safety first), false⟩, some copied⟩, some 8⟩, some incoming⟩
def legacy (safety first : Bool) := append safety (recordBacking (fun _ => request)) 7 6
  (if first then [] else [old]) copied ⟨copied.item.kind, 254, copied.item.data, incoming.items, 31⟩ incoming 0 {} (legacyFrame safety first)

theorem first_records_request (safety : Bool) :
    (legacy safety true).1 = .ok true ∧ (memory (legacy safety true).2).effects.allocator.events =
      history ++ [.backingAllocate 7 160 8 (some 2048)] := by
  cases safety <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem spare_skips_host (safety : Bool) :
    (legacy safety false).1 = .ok true ∧ (memory (legacy safety false).2).effects.allocator.events = history := by
  cases safety <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.AppendEffectTests
