/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerNativeRouting
import Compiler.Extraction.InternerCallerCustodyTests
import Compiler.Extraction.InternerPhysicalDispatch

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.RoutingTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open AssemblyItem.Creation.NativeFields.Tests (input source)
open CallerInputTests (values)

/-- The existing initialized rows use sequence 77. This request uses the
production default sequence, so its cache decision is an actual miss. -/
def request (empty : Bool) : Interner.Request := { CallerInputTests.request empty with sequence := 0 }
def key (empty : Bool) : Key := { CallerInputTests.key empty with sequence := 0 }

def seed (empty : Bool) (find : Recursive.Find (Publication.Effects Nat)) : Primitives (Publication.Effects Nat) :=
  Recursive.callbacks
    { simplify := fun _ _ before => (.error (.language .unsupported), before)
      publish := Publication.publish ops.probe ops.arguments 7 (parent empty)
      insert := fun _ _ _ before => (.error (.language .unsupported), before) }
    Interner.representativeReads 64 find

def full (safety empty : Bool) (find : Recursive.Find (Publication.Effects Nat)) :=
  ConstructorFrame.find (Publication.external ops.arguments) 160 7
    (callerPrimitives ops allocate safety 7 6 (parent empty) source Insertion.Tests.model input (seed empty find) (some growth))
    Interner.Queries.queries (parent empty) (request empty) (before safety empty 4)

theorem made (empty : Bool) : Interner.makeKey (request empty) (values empty) = .ok (key empty) := by
  cases empty <;> rfl

theorem missed (safety empty : Bool) : (before safety empty 4).graph.table (key empty) = none := by
  cases safety <;> cases empty <;> insertion_kernel_rfl

/-- The exact previous normalization/take observations also execute this
request: sequence affects its key, not normalization or argument ownership. -/
theorem entry (safety empty : Bool) :
    CallerInput 7 (parent empty) source (request empty) (values empty) input (key empty)
      (before safety empty 4) (taken safety empty 4).2 (normalized safety empty 4) (lookup empty) := by
  have prior := initialized_prefix safety empty 4 (by decide)
  have calls := prefix_results safety empty 4 (by decide)
  obtain ⟨slice, remaining, origin⟩ := Native.caller_input ops.arguments 160 7 (parent empty) source (request empty) input
    (before safety empty 4) (stack safety empty 4) _ (values empty) (prepared safety empty 4).2 (taken safety empty 4).2 (key empty)
    prior.parent_good (Normalization.Tests.external_admitted _) prior.facts.nativeInput.choose_spec.2.2 rfl
    calls.1 (Prod.ext calls.2.1 rfl) (Prod.ext calls.2.2.1 rfl) (made empty) prior.facts.live prior.facts.unique (by
      intro old found _ _
      have absent := missed safety empty
      rw [prior.facts.linked, OwnedKeys.view, found] at absent
      cases absent)
  have same := Local.mk.inj (origin.origin.scope.symm.trans calls.2.2.2)
  cases Option.some.inj same.1
  cases Option.some.inj same.2.1
  exact origin

theorem room (safety empty : Bool) : Interner.Queries.queries.atCapacity (before safety empty 4).graph = false := by
  have prior := initialized_prefix safety empty 4 (by decide)
  rw [Interner.Queries.capacity_exact _ _ prior.facts.projected, prior.count]
  decide

theorem classified (empty : Bool) : Interner.Queries.queries.deterministic (request empty).item = .ok true := rfl

theorem first_nonconstant (safety empty : Bool) :
    (Interner.representativeReads (taken safety empty 4).2.world.graph).constant 0 = .ok none := by
  have prior := initialized_prefix safety empty 4 (by decide)
  rw [(entry safety empty).origin.graph]
  simp only [Interner.representativeReads, prior.facts.projected, Nested.storageReads]
  have selected : Storage.representativeProgram.run (cells safety empty 4) 0 = .ok (CallerFirstSuccessTests.row safety empty) := by
    have head := prior.first
    cases rows : cells safety empty 4 with
    | nil => simp only [rows, List.head?_nil] at head; contradiction
    | cons first rest =>
      simp only [rows, List.head?_cons, Option.some.injEq] at head
      rw [head]
      simp [Storage.Lookup.run, Storage.representativeProgram, Storage.Bound.reject, Storage.Index.eval]
  simp only [Storage.ConstantRead.run, Storage.constantProgram, selected]
  rfl

/-- Use the actual ordered dispatcher. No recursive callback is replaced with
a success oracle: the equation holds for every recursive constructor callback. -/
theorem simplified (safety empty : Bool) (find : Recursive.Find (Publication.Effects Nat)) :
    (seed empty find).simplify (key empty) (normalized safety empty 4) (taken safety empty 4).2.world =
      (.ok none, (taken safety empty 4).2.world) := by
  have constant := first_nonconstant safety empty
  change Dispatch.simplify (Interner.representativeReads (taken safety empty 4).2.world.graph)
    (Recursive.constructors find) 64 254 (values empty) () (taken safety empty 4).2.world = _
  generalize (taken safety empty 4).2.world = world at constant ⊢
  generalize Interner.representativeReads world.graph = reads at constant ⊢
  cases empty with
  | true => rfl
  | false =>
    have collected : Dispatch.collectConstants reads [0] = .ok none := by
      unfold Dispatch.collectConstants
      rw [constant]
      rfl
    change Dispatch.simplify reads (Recursive.constructors find) 64 254 [0] () world = _
    simp only [Dispatch.simplify, Dispatch.simplifyWithInputs, Dispatch.simplifyOptionsWithInputs, Dispatch.constantStage,
      List.length_cons, List.length_nil, List.isEmpty_cons, Nat.reduceAdd, Bool.false_eq_true,
      collected, Nested.readAction, Dispatch.orNext]
    rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.RoutingTests
