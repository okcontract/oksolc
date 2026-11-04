/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationTraceMemory

namespace Compiler.Extraction.Memory.Arguments.Normalization.ResourceAdapter.TraceBridge
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open NormalizationOwnership.Trace

theorem observe_ordinary (protocol : NormalizationOwnership.Outcome × NormalizationOwnership.State)
    (after : ResourceAdapter.State σ) (result : Except Failure Outcome) (clean : after.rejected = none)
    (observed : ResourceAdapter.observe (.ok protocol) after = some result) :
    result = .error .outOfMemory ∨ ∃ outcome, result = .ok outcome := by
  rcases protocol with ⟨outcome, lookup⟩
  cases outcome with
  | allocationFailure => simp [ResourceAdapter.observe, clean] at observed; exact Or.inl observed.symm
  | lookup => simp [ResourceAdapter.observe, clean] at observed; exact Or.inr ⟨.lookup, observed.symm⟩
  | cleaned => simp [ResourceAdapter.observe, clean] at observed; exact Or.inr ⟨.cleaned, observed.symm⟩
  | transferred =>
    cases output : outputSlice after with
    | none => simp [ResourceAdapter.observe, clean, output] at observed
    | some slice =>
      simp [ResourceAdapter.observe, clean, output] at observed
      exact Or.inr ⟨.transferred slice, observed.symm⟩

theorem observe_transfer (protocol : NormalizationOwnership.Outcome × NormalizationOwnership.State)
    (after : ResourceAdapter.State σ) (slice : ArgumentSlice) (clean : after.rejected = none)
    (observed : ResourceAdapter.observe (.ok protocol) after = some (.ok (.transferred slice))) :
    protocol.1 = .transferred := by
  rcases protocol with ⟨outcome, lookup⟩
  cases outcome <;> simp [ResourceAdapter.observe, clean] at observed ⊢

/-- One accepted resource-scope execution, bound to its physical producer and
actual caller buffer. It has the same cursor/ownership result, reached memory,
complete production postcondition, exact transferred contents, original-storage
frame and word meaning.
Ordinary OOM is covered; semantic faults reject before scope projection.
This local lifecycle theorem does not discharge intervening graph operations. -/
theorem production_verified (external : External σ) (budget allocator : Nat) (commutative : Bool) (source : View)
    (request : Interner.Request) (exit : NormalizationOwnership.Exit) (before : Session σ)
    (memory : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (graph : Interner.Heap) (leading suffix : List (Event Failure))
    (scope : Except Interner.Error NormalizationOwnership.Outcome × Interner.Scoped.Session)
    (other : Meaning) (read : Read) (sequence : BitVec 32)
    (valid : Valid before) (represented : Represents before.memory source request.arguments)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory (.array 2 word) = .ok (pointer, memory))
    (decoded : Interner.Scoped.commutative request.item = .ok commutative) (admitted : Admitted external)
    (start : graph.allocationCursor = leading.length)
    (accepted : checked (captured external budget allocator commutative source ⟨before.memory.nextId, 0, 2⟩ request.arguments exit
      { before with memory := memory }) leading suffix request exit graph = .ok scope) :
    let buffer : View := ⟨before.memory.nextId, 0, 2⟩
    let input : Session σ := { before with memory := memory }
    let execution := captured external budget allocator commutative source buffer request.arguments exit input
    let native := Normalization.run normalizationOwnershipCode external budget allocator commutative source buffer request.arguments exit input
    ∃ protocol, execution.1 = .ok protocol ∧ Scope.observe scope = (some protocol, leading.length + execution.2.events.length) ∧
      native.2 = execution.2.effects.session ∧
      (native.1 = .error .outOfMemory ∨ ∃ outcome, native.1 = .ok outcome) ∧
      Post external budget allocator commutative source buffer request.arguments exit input native.1 native.2 ∧
      ((∀ id cell, before.memory.heap.lookup id = some cell → native.2.memory.heap.lookup id = some cell) ∧
       (∀ id block, before.heap id = some block → native.2.heap id = some block)) ∧
      (∀ slice, native.1 = .ok (.transferred slice) →
        scope.2.scope.items = slice.items ∧
        request.item.eval (Folding.wordMeaning other) read slice.items sequence =
        request.item.eval (Folding.wordMeaning other) read request.arguments sequence) := by
  let buffer : View := ⟨before.memory.nextId, 0, 2⟩
  let input : Session σ := { before with memory := memory }
  let execution := captured external budget allocator commutative source buffer request.arguments exit input
  let native := Normalization.run normalizationOwnershipCode external budget allocator commutative source buffer request.arguments exit input
  obtain ⟨protocol, result, clean, projected, scopeRan⟩ := checked_scope external budget allocator commutative source buffer request exit input graph
    leading suffix scope represented.1 rfl decoded start accepted
  change scope = Scope.run (Scope.resources (leading ++ (execution.2.events ++ suffix)) (.preparation .incomplete)) request exit graph at scopeRan
  have same := capture_native external budget allocator commutative source buffer request.arguments exit input
  have observation : ResourceAdapter.observe (.ok protocol) execution.2.effects = some native.1 := by
    have equality := congrArg Prod.fst same
    simpa only [result] using equality
  have state : native.2 = execution.2.effects.session := (congrArg Prod.snd same).symm
  have ordinary := observe_ordinary protocol execution.2.effects native.1 clean observation
  obtain ⟨post, frame, wordPreserved⟩ := Normalization.production_verified external budget allocator commutative source request.arguments exit
    before native.2 memory pointer native.1 request.item other read sequence valid represented allocated decoded admitted rfl
  refine ⟨protocol, result, projected, state, ordinary, post, ?_, ?_⟩
  · rcases frame with incomplete | exhausted | frame
    · rcases ordinary with failed | ⟨outcome, done⟩
      · rw [failed] at incomplete; simp at incomplete
      · rw [done] at incomplete; simp at incomplete
    · rcases ordinary with failed | ⟨outcome, done⟩
      · rw [failed] at exhausted; simp at exhausted
      · rw [done] at exhausted; simp at exhausted
    · exact frame
  · intro slice transferred
    change native.1 = .ok (.transferred slice) at transferred
    refine ⟨?_, wordPreserved slice transferred⟩
    have owned := observe_transfer protocol execution.2.effects slice clean (by simpa only [transferred] using observation)
    have scopeSuccess := Scope.observe_transferred scope protocol.2 (leading.length + execution.2.events.length)
      (by simpa only [← owned] using projected)
    have scopedItems := Scope.run_contents (Scope.resources (leading ++ (execution.2.events ++ suffix)) (.preparation .incomplete))
      request exit graph .transferred (by simpa only [← scopeRan] using scopeSuccess)
    rw [← scopeRan] at scopedItems
    have same := Option.some.inj (scopedItems.symm.trans (normalized_projection request.item commutative source request.arguments represented.1 decoded))
    rw [transferred] at post
    exact same.trans post.verified.2.2.2.1.symm

end Compiler.Extraction.Memory.Arguments.Normalization.ResourceAdapter.TraceBridge
