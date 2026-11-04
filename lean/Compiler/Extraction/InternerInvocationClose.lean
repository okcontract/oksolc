/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInvocationTrace
import Compiler.Extraction.InternerCallerCloseVerified

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Close
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Interner.InvocationTrace

/-- Handoff leaves only a detached lookup for outer cleanup. Its actual close
records no resource event, preserves the reached memory, and checks at the end
of the preceding tagged stream without consuming any suffix event. -/
theorem transferred_stream (external : External σ) (allocator : Nat)
    (lookup : NormalizationOwnership.State) (handle : Handle) (slice : ArgumentSlice) (world : World σ)
    (leading trailing : List (Event Failure ι))
    (detached : handle.owned = none) (unowned : lookup.owned = false) (owner : lookup.owner = .caller) :
    let before : OwnedCall.State σ := ⟨world, ⟨some handle, some slice, true⟩⟩
    let execution := capture external allocator lookup .transfer handle before
    let logical : Interner.Scoped.Session := ⟨⟨some lookup, handle.values, .transfer⟩,
      { world.graph with allocationCursor := leading.length }⟩
    execution.2.events = [] ∧ execution.2.effects.session = world.memory ∧
    cleanup external allocator before = (.ok (), ⟨world, ⟨none, some slice, true⟩⟩) ∧
    checked execution (normalizations leading) (normalizations trailing) lookup .transfer handle.values logical.heap =
      .ok (Interner.Scoped.close (resources (leading ++ trailing) (.preparation .incomplete)) logical) ∧
    Interner.Scoped.close (resources (leading ++ trailing) (.preparation .incomplete)) logical =
      ⟨⟨some { lookup with dead := true }, handle.values, .transfer⟩, logical.heap⟩ := by
  intro before execution logical
  have captured : capture external allocator lookup .transfer handle before = ({ lookup with dead := true },
      ⟨⟨world.memory, handle, some slice, none⟩, []⟩) := by
    simp [capture, before, NormalizationOwnership.Code.closeWith,
      NormalizationOwnership.Code.deinitWith, normalizationOwnershipCode, unowned]
  have closed : cleanup external allocator before = (.ok (), ⟨world, ⟨none, some slice, true⟩⟩) := by
    simpa only [cleanup, before, ↓reduceIte] using
      deinit_detached external allocator before handle rfl detached
  have linked := checked_of_cleanup external allocator lookup .transfer handle before
    ⟨world, ⟨none, some slice, true⟩⟩ (normalizations leading) (normalizations trailing) handle.values
    logical.heap (by simp only [logical, normalizations_length])
    (taken_spec external allocator lookup handle slice true world detached unowned owner) closed
  have checkedClose := linked.2.1
  have shape := linked.2.2
  simp only [captured, List.nil_append, normalizations_length] at checkedClose shape
  exact ⟨by simp only [execution, captured], by simp only [execution, captured], closed,
    by simpa only [execution, captured, resources, normalizations_append] using checkedClose,
    by simpa only [resources, normalizations_append, logical] using shape⟩

/-- Ordinary exits close the detached lookup. Semantic rejections retain the
actual handed-off locals and effects without claiming accepted cleanup. -/
structure HandoffCompletion (external : External σ) (allocator : Nat)
    (lookup : NormalizationOwnership.State) (handle : Handle) (slice : ArgumentSlice)
    (leading trailing : List (Event Failure ι))
    (actual : Except OwnedCall.Fault α × World σ)
    (logical : Except Interner.Error α × Interner.Scoped.Session)
    (finished : Except OwnedCall.Fault α × OwnedCall.State σ) : Prop where
  native : finished = if ordinary actual.1 then (actual.1, ⟨actual.2, ⟨none, some slice, true⟩⟩)
    else (actual.1, ⟨actual.2, ⟨some handle, some slice, true⟩⟩)
  result : actual.1 = logical.1.mapError OwnedCall.Fault.language
  reached : logical.2 = ⟨⟨some lookup, handle.values, .transfer⟩,
    { actual.2.graph with allocationCursor := leading.length }⟩
  closed : ordinary actual.1 = true →
    let execution := capture external allocator lookup .transfer handle ⟨actual.2, ⟨some handle, some slice, true⟩⟩
    let r := resources (leading ++ trailing) (.preparation .incomplete)
    checked execution (normalizations leading) (normalizations trailing) lookup .transfer handle.values logical.2.heap =
      .ok (Interner.Scoped.close r logical.2) ∧
    Interner.Scoped.close r logical.2 =
      ⟨⟨some { lookup with dead := true }, handle.values, .transfer⟩,
        { actual.2.graph with allocationCursor := leading.length }⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Close
