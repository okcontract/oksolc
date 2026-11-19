/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationResourcesInit
import Compiler.Extraction.NormalizationMemoryCaller

namespace Compiler.Extraction.Memory.Arguments.Normalization.ResourceAdapter
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- Exact interpretation of the source-bound ownership resource protocol by
the physical normalization execution, including ordinary OOM, semantic faults
and every finite preparation budget. No completed-execution premise or memory
postcondition is assumed, and a protocol rejection cannot silently disappear. -/
theorem run_eq (external : External σ) (budget allocator : Nat) (commutative : Bool) (source buffer : View)
    (values : List NodeId) (exit : NormalizationOwnership.Exit) (before : Session σ) :
    run external budget allocator commutative source buffer values exit before =
      let (result, after) := Normalization.run normalizationOwnershipCode external budget allocator commutative source buffer values exit before
      (some result, after) := by
  have spec := init_spec external budget allocator commutative source buffer values before
  cases executed : initialized external budget allocator commutative source buffer values before with
  | mk result after =>
    rw [executed] at spec
    dsimp only [initialized] at executed
    rcases spec with ⟨same, aligned⟩
    dsimp only at same aligned
    cases native : Normalization.init normalizationOwnershipCode external budget allocator commutative source buffer values before with
    | mk outcome reached =>
      rw [native] at same
      cases result with
      | error failure =>
        rcases failure with ⟨failure, lookup⟩
        cases rejected : after.rejected <;> simp only [observeInit, rejected, Prod.mk.injEq, Option.some.injEq] at same
        · rcases same with ⟨rfl, rfl⟩
          simp [run, NormalizationOwnership.Code.runPrepared, executed, observe, rejected, Normalization.run, native]
        · rename_i rejection
          cases rejection <;> simp at same
          rcases same with ⟨rfl, rfl⟩
          simp [run, NormalizationOwnership.Code.runPrepared, executed, observe, rejected, Normalization.run, native]
      | ok lookup =>
        cases lookup with
        | none =>
          cases rejected : after.rejected <;> simp only [observeInit, rejected, Prod.mk.injEq, Option.some.injEq] at same
          · rcases same with ⟨rfl, rfl⟩
            simp [run, NormalizationOwnership.Code.runPrepared, executed, observe, rejected, Normalization.run, native]
          · rename_i rejection
            cases rejection <;> simp at same
            rcases same with ⟨rfl, rfl⟩
            simp [run, NormalizationOwnership.Code.runPrepared, executed, observe, rejected, Normalization.run, native]
        | some lookup =>
          obtain ⟨clean, transferred, tokenEq⟩ := aligned lookup rfl
          simp only [observeInit, clean, Prod.mk.injEq, Option.some.injEq] at same
          rcases same with ⟨rfl, rfl⟩
          have continuedRun := continued_eq external budget allocator source buffer values lookup.origin exit after.handle after.session
          unfold continued at continuedRun
          rw [← tokenEq] at continuedRun
          cases after with
          | mk session handle transfer rejection =>
            cases clean; cases transferred
            simpa only [run, NormalizationOwnership.Code.runPrepared, executed,
              Normalization.run, native] using continuedRun

/-- The protocol accepts exactly the result and reached state of the memory
execution. In particular, its missing-descriptor rejection is unreachable. -/
theorem run_checked (external : External σ) (budget allocator : Nat) (commutative : Bool) (source buffer : View)
    (values : List NodeId) (exit : NormalizationOwnership.Exit) (before after : Session σ) (result : Except Failure Outcome) :
    run external budget allocator commutative source buffer values exit before = (some result, after) ↔
      Normalization.run normalizationOwnershipCode external budget allocator commutative source buffer values exit before = (result, after) := by
  rw [run_eq]
  cases Normalization.run normalizationOwnershipCode external budget allocator commutative source buffer values exit before
  simp only [Prod.mk.injEq, Option.some.injEq]

/-- Composition into the complete production-operation theorem, now for the
ownership protocol's actual physical resource adapter. Native contracts are
unchanged; no abstract sort or lifecycle postcondition is an assumption. -/
theorem production_verified (external : External σ) (budget allocator : Nat) (commutative : Bool) (source : View)
    (values : List NodeId) (exit : NormalizationOwnership.Exit) (before after : Session σ)
    (memory : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value) (result : Except Failure Outcome)
    (item : Item) (other : Meaning) (read : Read) (sequence : BitVec 32)
    (valid : Valid before) (represented : Represents before.memory source values)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory (.array 2 word) = .ok (pointer, memory))
    (decoded : Interner.Scoped.commutative item = .ok commutative) (admitted : Admitted external)
    (executed : run external budget allocator commutative source ⟨before.memory.nextId, 0, 2⟩ values exit
      { before with memory := memory } = (some result, after)) :
    Post external budget allocator commutative source ⟨before.memory.nextId, 0, 2⟩ values exit
      { before with memory := memory } result after ∧
    (result = .error (.preparation .incomplete) ∨ result = .error (.preparation (.memory .outOfMemory)) ∨
      ((∀ id cell, before.memory.heap.lookup id = some cell → after.memory.heap.lookup id = some cell) ∧
       (∀ id block, before.heap id = some block → after.heap id = some block))) ∧
    (∀ slice, result = .ok (.transferred slice) →
      item.eval (Folding.wordMeaning other) read slice.items sequence = item.eval (Folding.wordMeaning other) read values sequence) := by
  exact Normalization.production_verified external budget allocator commutative source values exit before after memory pointer result
    item other read sequence valid represented allocated decoded admitted
    ((run_checked external budget allocator commutative source _ values exit _ after result).mp executed)

end Compiler.Extraction.Memory.Arguments.Normalization.ResourceAdapter
