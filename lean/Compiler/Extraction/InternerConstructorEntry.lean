/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerArgumentPreparationFailure

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray

/-- Every ordinary literal operation reaches its actual prepared source and
returns through the original argument mark. Rejected preparation remains
nonordinary; this derives entry rather than assuming a successful initializer. -/
theorem Arguments.operation_entry (external : External σ) (budget allocator : Nat)
    (p : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives σ)
    (q : Caller.Queries) (opcode : Opcode) (values : List NodeId) (debug : AssemblyItem.Fields.Values)
    (before : World σ) (valid : Valid before.memory) :
    let actual := operation external budget allocator p q opcode values debug before
    ordinary actual.1 = true → ∃ source prepared,
      prepare values before = (.ok source, prepared) ∧ Prepared values before source prepared ∧
      actual = returned values before.memory.memory.nextId
        (ConstructorItem.operation external budget allocator (p source) q source opcode values debug prepared) := by
  dsimp only
  intro completed
  cases prepared : prepare values before with
  | mk result after =>
    cases result with
    | error fault =>
      rw [operation_rejected _ _ _ _ _ _ _ _ _ _ _ prepared] at completed
      have rejected := error_nonordinary values valid after fault prepared
      simp only [rejected, Bool.false_eq_true] at completed
    | ok source =>
      exact ⟨source, after, rfl, prepare_success values before after source valid prepared,
        operation_prepared _ _ _ _ _ _ _ _ _ _ _ prepared⟩

/-- Ordinary named-local execution derives binary shape, actual copy/overwrite
preparation and the original return mark. The unused overwrite index remains
unrestricted when the source skips the overwrite. -/
theorem ViewInput.local_entry (context : PairInput.Context σ) (opcode : Opcode) (slice : ArgumentSlice)
    (selected : Nat) (repeated : NodeId) (first : Bool) (debug : AssemblyItem.Fields.Values)
    (before : World σ) (good : Good (view slice) slice.items before)
    (inside : first = true → selected < slice.items.length) :
    let actual := (constructors context).localOperation opcode slice selected repeated first debug before
    ordinary actual.1 = true → ∃ source prepared,
      LocalArguments.zigLocal (view slice) selected repeated first before = (.ok source, prepared) ∧
      Arguments.Prepared (if first then slice.items.set selected repeated else slice.items) before source prepared ∧
      actual = TemporaryArguments.unwind before.memory.memory.nextId
        (ConstructorItem.operation context.external context.budget context.allocator (context.primitives source)
          context.queries source opcode (if first then slice.items.set selected repeated else slice.items) debug prepared) := by
  dsimp only
  intro completed
  rcases items : slice.items with _ | ⟨left, _ | ⟨right, _ | ⟨extra, tail⟩⟩⟩
  · simp only [constructors, items] at completed
    cases completed
  · simp only [constructors, items] at completed
    cases completed
  · rw [local_forwarded _ slice left right items] at completed ⊢
    have input : Good (view slice) [left, right] before := by simpa only [items] using good
    have bound : first = true → selected < 2 := by simpa only [items] using inside
    cases prepared : LocalArguments.zigLocal (view slice) selected repeated first before with
    | mk result after =>
      cases result with
      | error fault =>
        rw [local_rejected _ _ _ _ _ _ _ _ _ _ _ _ prepared] at completed
        have rejected := LocalArguments.error_nonordinary left right repeated selected first input bound after fault prepared
        simp only [rejected, Bool.false_eq_true] at completed
      | ok source =>
        refine ⟨source, after, rfl, ?_, ?_⟩
        · simpa only [items] using local_input_optional (view slice) source left right repeated selected first before after input bound prepared
        · simpa only [items] using local_prepared context opcode (view slice) source left right repeated selected first debug before after prepared
  · simp only [constructors, items] at completed
    cases completed

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem
