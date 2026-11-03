/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeStep
import Compiler.Extraction.InternerCallerInsertionSpareSuccessTests
import Compiler.Extraction.InternerCallerInsertionGrowingChainTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.NativeSpareTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open AssemblyItem.Creation.NativeFields.Tests (input)
open CallerInputTests (values request key)
open CallerSpareSuccessTests
open ConstructorItem.NativeRecursion

/-- Reuse the first actual insertion and existing spare-call preparation. The
fixture allocator denies backing requests, so success cannot come from growth. -/
theorem initial_facts (safety empty : Bool) :
    NativeGraph.Facts safety 7 6 ⟨lifetime empty, 0⟩ 5 (before safety empty) [old safety empty] := by
  have represented := initial_representation safety empty
  have geometry := initial_geometry safety empty
  have keys := Publication.GraphTests.initial_facts safety empty
  have graph := CallerFirstSuccessTests.graph_and_key_projection safety empty
  refine ⟨(CallerFirstSuccessTests.native_borrow_good safety empty).2.1, graph.1, graph.2,
    ⟨owner safety empty, geometry.1, geometry.2.1, geometry.2.2.1⟩, ?_, by simp,
    (fun _ => ⟨represented.2.1, represented.1, represented.2.2.1⟩), keys.1, represented.2.2.2.2,
    keys.2.1, keys.2.2.1, keys.2.2.2, ?_⟩
  · simp only [readHeader, readItems] at geometry ⊢
    rw [geometry.2.2.2.1, geometry.2.2.2.2]
    rfl
  · intro row member
    have same := List.mem_singleton.mp member
    subst row
    exact Constant.Data.nonpush _ _ (by change (1#32) ≠ 2#32; decide)

theorem reached_frame (safety empty : Bool) :
    CallFrame safety 7 6 [old safety empty] (argumentView empty) (request empty).arguments
      (CallerSpareSuccessTests.normalized empty) itemSource input (fun _ => True) (taken safety empty).2.world := by
  have entry := derived_input safety empty
  have facts := initial_facts safety empty
  have array : ArraySource (argumentView empty) (before safety empty).memory.memory :=
    ArraySource.registered facts.valid (facts.resident (old safety empty) (by simp)).2
  exact CallFrame.caller entry facts (CallerFirstSuccessTests.borrowed_source_apart safety empty) array (fun _ => True) trivial

theorem published_observed (safety empty : Bool) :
    SparePublished ops CallerSpareSuccessTests.allocate safety 7 6 Insertion.Tests.model input (key empty) (CallerSpareSuccessTests.normalized empty) (taken safety empty).2.world := by
  have entry := derived_input safety empty
  have observed := preparation_results safety empty
  have fields := initial_geometry safety empty
  have nativeFrame := entry.native_frame 6 (owner safety empty) fields.1
  refine ⟨by decide, 5, ?_, ?_, operands empty, handle empty, (duplicated safety empty).2, object empty,
    (made safety empty).2, copied empty, (cloned safety empty).2, (ready safety empty).effects.allocator * 10 + 8,
    observed.1, observed.2.1, observed.2.2.1, ?_⟩
  · exact (readField_eq_of_lookup _ _ (Owner.headerAddress ⟨6, 0⟩) capacityOffset nativeFrame).trans fields.2.2.2.2
  · rw [entry.origin.graph, (initial_facts safety empty).projected]
    simp
  · intro installed assigned
    have same : ready safety empty = installed := Except.ok.inj (observed.2.2.2.symm.trans assigned)
    have rows : ((taken safety empty).2.world.graph.representatives.getD []) = [old safety empty] := by
      rw [entry.origin.graph, (initial_facts safety empty).projected]
      rfl
    rw [← same, rows]
    exact probe_result safety empty

def actual (safety empty : Bool) (growth : Option (Growth.Registered.Callbacks Nat)) :=
  Insertion.Native.insert ops CallerSpareSuccessTests.allocate safety 7 6 (argumentView empty) itemSource Insertion.Tests.model input
    (key empty) (CallerSpareSuccessTests.normalized empty) true growth (taken safety empty).2.world

/-- The same regression is an instance of the general proper-child completion,
for arbitrary optional growth callbacks: spare storage does not invoke them. -/
theorem completed (safety empty : Bool) (growth : Option (Growth.Registered.Callbacks Nat)) :
    (actual safety empty growth).1 = .ok 1 ∧
      ∃ added data capacity, NativeGraph.Facts safety 7 6 data capacity (actual safety empty growth).2 ([old safety empty] ++ added) := by
  have entry := derived_input safety empty
  have checked := (reached_frame safety empty).published ops CallerSpareSuccessTests.allocate growth Insertion.Tests.model (key empty)
    (Normalization.Tests.external_admitted _) entry.publication.aligned
    (by rw [entry.origin.graph, (initial_facts safety empty).projected]; simp) (Or.inr (Or.inl (published_observed safety empty)))
  simpa only [entry.origin.graph, (initial_facts safety empty).projected, Option.getD_some, Storage.idFor,
    List.length_singleton] using checked

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.NativeSpareTests
