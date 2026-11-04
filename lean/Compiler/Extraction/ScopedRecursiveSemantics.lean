/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.InternerScopePreservation
import Compiler.Extraction.ScopedRecursiveFrames

namespace Compiler.Extraction.ScopedRecursive
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul

theorem step_safe (env : AddressMask.Environment) (other : Meaning) (pushes : Pushes other)
    (r : Scoped.Resources) (permutation : ∀ ids, (r.sort ids).Perm ids)
    (p : Primitives) (primitive : Scoped.GraphContracts (Dispatch.wordDispatchMeaning env other) p)
    (reads : Heap → Reads)
    (coherent : ∀ before, Invariant (Dispatch.wordDispatchMeaning env other) before →
      Sound (Dispatch.wordDispatchMeaning env other) before.read (reads before))
    (usizeBits : Nat) (find : Recursive.Find)
    (recursive : Recursive.FindSound (Dispatch.wordDispatchMeaning env other) find) :
    Recursive.FindSound (Dispatch.wordDispatchMeaning env other) (step r p reads usizeBits find) := by
  have words := Recursive.constructors_sound (Dispatch.wordBaseMeaning env other) pushes find recursive (Debug := Unit)
  have addresses := Recursive.constructors_address env (ArithmeticShift.shiftMeaning other) find
    (by simpa only [Dispatch.word_dispatch_address_model] using recursive) (Debug := Unit)
  have shifts := Recursive.constructors_sar (AddressMask.addressMeaning env other) find recursive (Debug := Unit)
  have contracts : Scoped.Contracts (Dispatch.wordDispatchMeaning env other) (callbacks p reads usizeBits find) := {
    toGraphContracts := ⟨primitive.insert, primitive.publish⟩
    simplify := by
      intro key operation before value valid evaluated
      exact Dispatch.default_key_simplify_safe env other (reads before) (Recursive.constructors find)
        words addresses shifts before valid (coherent before valid) key operation value () usizeBits evaluated
  }
  intro request before value valid evaluated
  exact Scoped.find_safe (Dispatch.wordBaseMeaning env other) r permutation _ contracts request before value valid evaluated

/-- No fixed recursion bound and no recursive-correctness assumption. Every
finite unfolding preserves word semantics with its actual cleanup effects.
The only graph primitive premises are insertion and publication preservation. -/
theorem unfold_safe (env : AddressMask.Environment) (other : Meaning) (pushes : Pushes other)
    (r : Scoped.Resources) (permutation : ∀ ids, (r.sort ids).Perm ids)
    (p : Primitives) (primitive : Scoped.GraphContracts (Dispatch.wordDispatchMeaning env other) p)
    (reads : Heap → Reads)
    (coherent : ∀ before, Invariant (Dispatch.wordDispatchMeaning env other) before →
      Sound (Dispatch.wordDispatchMeaning env other) before.read (reads before))
    (usizeBits depth : Nat) :
    Recursive.FindSound (Dispatch.wordDispatchMeaning env other) (unfold r p reads usizeBits depth) := by
  induction depth with
  | zero =>
    intro request before value valid _
    exact Safe.fail _ before .unsupported _ valid
  | succ depth ih => exact step_safe env other pushes r permutation p primitive reads coherent usizeBits _ ih

/-- The attached representative graph discharges the read-oracle premise.
Physical addresses and native completed-execution refinement remain separate. -/
theorem unfold_representatives_safe (env : AddressMask.Environment) (other : Meaning) (pushes : Pushes other)
    (r : Scoped.Resources) (permutation : ∀ ids, (r.sort ids).Perm ids)
    (p : Primitives) (primitive : Scoped.GraphContracts (Dispatch.wordDispatchMeaning env other) p)
    (usizeBits depth : Nat) :
    Recursive.FindSound (Dispatch.wordDispatchMeaning env other) (unfold r p representativeReads usizeBits depth) :=
  unfold_safe env other pushes r permutation p primitive representativeReads
    (fun before valid => representative_reads_sound _ before valid) usizeBits depth

theorem detailed_safe (env : AddressMask.Environment) (other : Meaning) (pushes : Pushes other)
    (r : Scoped.Resources) (permutation : ∀ ids, (r.sort ids).Perm ids)
    (p : Primitives) (primitive : Scoped.GraphContracts (Dispatch.wordDispatchMeaning env other) p)
    (reads : Heap → Reads)
    (coherent : ∀ before, Invariant (Dispatch.wordDispatchMeaning env other) before →
      Sound (Dispatch.wordDispatchMeaning env other) before.read (reads before))
    (usizeBits depth : Nat) (request : Request) (before : Heap) (value : Word)
    (valid : Invariant (Dispatch.wordDispatchMeaning env other) before)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.read
      request.arguments request.sequence = some value) :
    let (result, after) := detailed r p reads usizeBits depth request before
    Invariant (Dispatch.wordDispatchMeaning env other) after.heap ∧ Stable before after.heap ∧
      match result with | .error _ => True | .ok id => after.heap.read id = some value := by
  have checked := unfold_safe env other pushes r permutation p primitive reads coherent usizeBits depth
    request before value valid evaluated
  cases ran : detailed r p reads usizeBits depth request before with
  | mk result after =>
    have final := checked result after.heap (by rw [detailed_projection, ran])
    cases result <;> exact final

/-- Word semantics, structural preservation and closed local ownership hold
for the very same scoped execution, including allocation errors and cutoffs. -/
theorem detailed_verified (env : AddressMask.Environment) (other : Meaning) (pushes : Pushes other)
    (r : Scoped.Resources) (permutation : ∀ ids, (r.sort ids).Perm ids)
    (p : Primitives) (primitive : Scoped.GraphContracts (Dispatch.wordDispatchMeaning env other) p)
    (frames : Recursive.PrimitiveFrames p) (usizeBits depth : Nat) (request : Request) (before : Heap) (value : Word)
    (valid : Invariant (Dispatch.wordDispatchMeaning env other) before)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.read
      request.arguments request.sequence = some value) :
    let (result, after) := detailed r p representativeReads usizeBits depth request before
    Invariant (Dispatch.wordDispatchMeaning env other) after.heap ∧ Stable before after.heap ∧
      Extends before after.heap ∧ Scoped.Closed after.scope ∧
      match result with | .error _ => True | .ok id => after.heap.read id = some value := by
  have semantic := detailed_safe env other pushes r permutation p primitive representativeReads
    (fun before valid => representative_reads_sound _ before valid) usizeBits depth request before value valid evaluated
  have structural := detailed_preserves r p frames representativeReads usizeBits depth request before
  cases ran : detailed r p representativeReads usizeBits depth request before with
  | mk result after =>
    rw [ran] at semantic structural
    cases result <;> exact ⟨semantic.1, semantic.2.1, structural.1, structural.2, semantic.2.2⟩

/-- Completed observations of this model, not a claim about native execution.
An exhausted unfolding or unsupported primitive remains explicitly incomplete. -/
def Executes (r : Scoped.Resources) (p : Primitives) (reads : Heap → Reads) (usizeBits : Nat)
    (request : Request) (before : Heap) (result : Except Error NodeId) (after : Heap) : Prop :=
  ∃ depth, unfold r p reads usizeBits depth request before = (result, after) ∧ result ≠ .error .unsupported

theorem executes_safe (env : AddressMask.Environment) (other : Meaning) (pushes : Pushes other)
    (r : Scoped.Resources) (permutation : ∀ ids, (r.sort ids).Perm ids)
    (p : Primitives) (primitive : Scoped.GraphContracts (Dispatch.wordDispatchMeaning env other) p)
    (reads : Heap → Reads)
    (coherent : ∀ before, Invariant (Dispatch.wordDispatchMeaning env other) before →
      Sound (Dispatch.wordDispatchMeaning env other) before.read (reads before))
    (usizeBits : Nat) (request : Request) (before after : Heap) (result : Except Error NodeId)
    (value : Word) (valid : Invariant (Dispatch.wordDispatchMeaning env other) before)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.read
      request.arguments request.sequence = some value)
    (execution : Executes r p reads usizeBits request before result after) :
    Invariant (Dispatch.wordDispatchMeaning env other) after ∧ Stable before after ∧
      (match (generalizing := false) result with | .error _ => True | .ok id => after.read id = some value) := by
  obtain ⟨depth, ran, _⟩ := execution
  have checked := unfold_safe env other pushes r permutation p primitive reads coherent usizeBits depth
    request before value valid evaluated result after ran
  cases result <;> exact checked

theorem unsupported_not_execution (r : Scoped.Resources) (p : Primitives) (reads : Heap → Reads)
    (usizeBits : Nat) (request : Request) (before after : Heap) :
    ¬Executes r p reads usizeBits request before (.error .unsupported) after := by
  rintro ⟨_, _, complete⟩
  exact complete rfl

end Compiler.Extraction.ScopedRecursive
