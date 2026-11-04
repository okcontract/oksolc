/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeFrameInduction
import Compiler.Extraction.InternerNativeAllocationIdentityTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeFrameInductionTests
open NativeRecursion Insertion.Native
open RecursiveTests (debug)
open NativeAllocationAdmissionTests

attribute [local irreducible] ConstantPublicationTests.ready ConstantFoldTests.rootArguments
  RecursiveTests.Call.constructed RecursiveTests.Call.stack

/-- The same proved family preserves the live ISZERO parent through both the
existing successful constant child and its actual allocator refusal. -/
theorem parent_retained (safety permitted : Bool) :
    frame safety (child safety (before safety permitted)).2 := by
  have family := Enclosing.unfold_frames ops ReachablePrefixTests.allocate safety 6 64
    (ReachablePrefixTests.base safety) (some CallerGrowingChainTests.growth) Insertion.Tests.model debug
    1 (ConstantPublicationTests.rows safety 0) (parent safety).source [4] (parent safety).normalized
    (parent safety).address (parent safety).native (fun _ => True) .root
    (Normalization.Tests.external_admitted _) AssemblyItem.Initializers.Tests.debug_valid
  apply family.constant 1 () (before safety permitted) (admitted_frame safety permitted)
  change ordinary (child safety (before safety permitted)).1 = true
  cases permitted
  · rw [refused]; rfl
  · rw [successful]; rfl

/-- The extra real stack allocation changes the child's fresh identity but
does not prevent native frame preservation. No common replay model is used. -/
theorem shifted_parent_retained (safety shifted : Bool) :
    frame safety (child safety (NativeAllocationIdentityTests.native safety shifted)).2 := by
  have family := Enclosing.unfold_frames ops ReachablePrefixTests.allocate safety 6 64
    (ReachablePrefixTests.base safety) (some CallerGrowingChainTests.growth) Insertion.Tests.model debug
    1 (ConstantPublicationTests.rows safety 0) (parent safety).source [4] (parent safety).normalized
    (parent safety).address (parent safety).native (fun _ => True) .root
    (Normalization.Tests.external_admitted _) AssemblyItem.Initializers.Tests.debug_valid
  apply family.constant 1 () (NativeAllocationIdentityTests.native safety shifted)
    (NativeAllocationIdentityTests.before_frame safety shifted)
  change ordinary (child safety (NativeAllocationIdentityTests.native safety shifted)).1 = true
  rw [NativeAllocationIdentityTests.native_result]; rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeFrameInductionTests
