/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstantNegationChildInputTests
import Compiler.Extraction.InternerRecursiveGrowingFailureTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ConstantNegationTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops growth GraphFacts)
open RecursiveTests (Call debug)

attribute [local irreducible] ConstantPublicationTests.ready rootArguments Call.constructed Call.stack

theorem child_duplicate (safety : Bool) (value : Word) :
    (child safety value).duplicate =
      (.ok ((child safety value).normalized, ⟨view (child safety value).normalized, [], none⟩),
        (child safety value).taken.2.world.memory) :=
  (child safety value).duplicate_empty rfl rfl rfl (child_prepared safety value).2.1 (child_prepared safety value).2.2.1

theorem child_creation_fits (safety : Bool) (value : Word) (apart : 0 - value ≠ value) :
    Compiler.ZigAir.Memory.RegionAllocation.Fits (child safety value).duplicate.2.memory AssemblyItem.Creation.layout
      (((child safety value).duplicate.2.memory.nextAddress / AssemblyItem.Creation.layout.alignment + 1) *
        AssemblyItem.Creation.layout.alignment) := by
  have counter : (child safety value).duplicate.2.memory.nextAddress = (childScratchReference safety).nextAddress := by
    rw [child_duplicate, (child_normalized safety value).2.2.2]
    exact (child_prepared safety value).2.2.2
  have valid : (child safety value).duplicate.2.memory.valid = true := by
    rw [child_duplicate]; exact (child_established safety value apart).taken.valid.memory
  apply Compiler.ZigAir.Memory.RegionAllocation.fits_above _ _ _ valid <;>
    rw [counter] <;> cases safety <;> apply of_decide_eq_true <;> insertion_kernel_rfl

theorem child_unlocked (safety : Bool) (value : Word) :
    Owner.NativeLock.checkHeader (child safety value).constructed.memory.memory (Owner.headerAddress ⟨6, 0⟩) = .ok () := by
  have prior := ConstantPublicationTests.contract safety value RecursiveNonemptyTests.failing (some growth)
  have parentFacts := established safety value
  have childReady := (child_prepared safety value).2.1
  obtain ⟨owner, found, typed, _⟩ := prior.2.1.owner
  have kept := childReady.memory 6 owner (parentFacts.entry.origin.memory 6 owner
    (parentFacts.item.memory 6 owner ((literal safety value).2.1.frame 6 owner found)))
  exact (Owner.NativeLock.checkHeader_eq_of_lookup safety (old safety value).memory.memory
    (child safety value).constructed.memory.memory 6 owner childReady.valid.memory found typed
    (kept.trans found.symm)).trans prior.2.2.2.2.2.2.2.2.2


end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ConstantNegationTests
