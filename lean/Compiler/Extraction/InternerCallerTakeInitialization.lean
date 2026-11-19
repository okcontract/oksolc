/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerTakeVerified

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Take
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open ResourceAdapter NormalizationOwnership.Trace

/-- Initialization supplies readiness; permitted take responses and the actual
recorder derive acceptance. Only the segment cursor must be connected. -/
theorem after_initialization_verified (external : External σ) (allocator : Nat) (source : View) (request : Interner.Request)
    (before : World σ) (cursor : Nat) (reached : Session σ)
    (initialized : Except Fault (List NodeId) × OwnedCall.State σ)
    (initialScope : Except Interner.Error (List NodeId) × Interner.Scoped.Session)
    (other : Meaning) (read : Read) (sequence : BitVec 32) (values : List NodeId)
    (known : Initialization.Coupled allocator source request before cursor reached initialized initialScope other read sequence)
    (returned : initialized.1 = .ok values) (admitted : Admitted external)
    (leading suffix : List (Event Failure)) (start : initialScope.2.heap.allocationCursor = leading.length) :
    ∃ handle lookup scope, initialized.2.scope.lookup = some handle ∧ initialScope.2.scope.lookup = some lookup ∧
      lookup = token lookup.origin handle ∧ handle.values = values ∧
      request.item.eval (Folding.wordMeaning other) read values sequence =
        request.item.eval (Folding.wordMeaning other) read request.arguments sequence ∧
      let execution := capture external allocator lookup.origin handle initialized.2.world.memory
      checked execution leading suffix lookup values initialScope.2.heap = .ok scope ∧
      scope = Interner.Scoped.take
        (Scope.resources (leading ++ (execution.2.events ++ suffix)) (.preparation .incomplete)) initialScope.2 ∧
      Coupled allocator source request.arguments handle initialized.2.world
        (leading.length + execution.2.events.length) execution.2.effects.session execution.1
        (OwnedCall.take external allocator initialized.2) scope := by
  obtain ⟨handle, lookup, present, scopedLookup, tokenEq, ready, contents, word, localShape, scopeShape⟩ :=
    known.2.2.2.2.2 values returned
  have graph : { initialized.2.world.graph with allocationCursor := leading.length } = initialScope.2.heap := by
    rw [known.2.1, known.2.2.2.1]
    have position : cursor = leading.length := by simpa only [known.2.2.2.1] using start
    rw [position]
  have scopeInput : (⟨⟨some (token lookup.origin handle), handle.values, .lookup⟩,
      { initialized.2.world.graph with allocationCursor := leading.length }⟩ : Interner.Scoped.Session) = initialScope.2 := by
    rw [graph, ← tokenEq, contents, ← scopeShape]
  have derived := verified external allocator lookup.origin source request.arguments handle initialized.2.world
    leading suffix ready admitted
  dsimp only at derived
  rw [scopeInput] at derived
  have nativeState : (⟨initialized.2.world, { lookup := some handle }⟩ : OwnedCall.State σ) = initialized.2 := by
    rw [← localShape]
  rw [nativeState] at derived
  refine ⟨handle, lookup, _, present, scopedLookup, tokenEq, contents, ?_, ?_, rfl, derived.2⟩
  · simpa only [contents] using word
  · simpa only [graph, ← tokenEq, contents] using derived.1

/-- Compatibility for clients naming a particular accepted scope. The general
producer above now supplies the take proof; this premise only identifies that
computed scope with the client's expected result. -/
theorem after_initialization (external : External σ) (allocator : Nat) (source : View) (request : Interner.Request)
    (before : World σ) (cursor : Nat) (reached : Session σ)
    (initialized : Except Fault (List NodeId) × OwnedCall.State σ)
    (initialScope : Except Interner.Error (List NodeId) × Interner.Scoped.Session)
    (other : Meaning) (read : Read) (sequence : BitVec 32) (values : List NodeId)
    (known : Initialization.Coupled allocator source request before cursor reached initialized initialScope other read sequence)
    (returned : initialized.1 = .ok values) (admitted : Admitted external)
    (leading suffix : List (Event Failure)) (scope : Except Interner.Error Unit × Interner.Scoped.Session)
    (start : initialScope.2.heap.allocationCursor = leading.length)
    (accepted : ∀ handle lookup, initialized.2.scope.lookup = some handle → initialScope.2.scope.lookup = some lookup →
      lookup = token lookup.origin handle →
      checked (capture external allocator lookup.origin handle initialized.2.world.memory) leading suffix lookup
        values initialScope.2.heap = .ok scope) :
    ∃ handle lookup, initialized.2.scope.lookup = some handle ∧ initialScope.2.scope.lookup = some lookup ∧
      handle.values = values ∧
      request.item.eval (Folding.wordMeaning other) read values sequence =
        request.item.eval (Folding.wordMeaning other) read request.arguments sequence ∧
      let execution := capture external allocator lookup.origin handle initialized.2.world.memory
      scope = Interner.Scoped.take
        (Scope.resources (leading ++ (execution.2.events ++ suffix)) (.preparation .incomplete)) initialScope.2 ∧
      Coupled allocator source request.arguments handle initialized.2.world
        (leading.length + execution.2.events.length) execution.2.effects.session execution.1
        (OwnedCall.take external allocator initialized.2) scope := by
  obtain ⟨handle, lookup, computed, present, scopedLookup, tokenEq, contents, word, checkedResult, projected, derived⟩ :=
    after_initialization_verified external allocator source request before cursor reached initialized initialScope
      other read sequence values known returned admitted leading suffix start
  have expected := accepted handle lookup present scopedLookup tokenEq
  have same := Except.ok.inj (checkedResult.symm.trans expected)
  subst scope
  exact ⟨handle, lookup, present, scopedLookup, contents, word, projected, derived⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Take
