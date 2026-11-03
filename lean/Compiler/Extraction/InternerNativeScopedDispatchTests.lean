/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeScopedTake
import Compiler.Extraction.InternerCallerScopeProjectionTests
import Compiler.Extraction.InternerNativeSpareInsertionTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ScopeTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray Recursive
open Insertion.Native
open NormalizationOwnership.Trace

/-- Inhabited child relations for every snapshot frame; these callbacks are
control fixtures, not native constructor implementation certificates. -/
def resultChildren (action : m NodeId) : Associative.Constructors AssemblyItem.Fields.Values m where
  operation := fun _ _ _ => action
  constant := fun _ _ => action
  materialize := fun _ _ _ => action
  borrowedOperation := fun _ _ _ _ => action
  localOperation := fun _ _ _ _ _ _ => action

theorem outcome_children (cursor : World σ → Nat) (predicate : World σ → Prop) (result : Except Interner.Error NodeId) :
    (projectionAt (cursorGraph cursor) predicate).Constructors
      (resultChildren (fun before => (result.mapError Fault.language, before)))
      (resultChildren (fun before => (result, before))) := by
  have projected : ProjectsAt (cursorGraph cursor) predicate
      (fun before => (result.mapError Fault.language, before)) (fun before => (result, before)) :=
    fun _ held _ => ⟨held, rfl, rfl⟩
  exact ⟨fun _ _ _ => projected, fun _ _ => projected, fun _ _ _ => projected,
    fun _ _ _ _ => projected, fun _ _ _ _ _ _ => projected⟩

theorem seed_graph_operations (seed : Interner.Primitives) (children : Associative.Constructors AssemblyItem.Fields.Values)
    (usizeBits : Nat) (debug : AssemblyItem.Fields.Values) :
    (dispatchModel seed children usizeBits debug).publish = seed.publish ∧
      (dispatchModel seed children usizeBits debug).insert = seed.insert := ⟨rfl, rfl⟩

/-- Reuse actual spare-call preparation in both layouts and for empty/nonempty
inputs. The child relation is explicitly the induction obligation; all native
input, graph, custody and snapshot premises come from the existing fixture. -/
theorem spare_from_children (safety empty : Bool) (base : PairInput.Context (Publication.Effects Nat))
    (allocator : base.allocator = 7) (usizeBits : Nat) (debug : AssemblyItem.Fields.Values)
    (cursor : World (Publication.Effects Nat) → Nat) (children : Constructors (Publication.Effects Nat))
    (model : Associative.Constructors AssemblyItem.Fields.Values) (seed : Interner.Primitives)
    (resources : Interner.Scoped.Resources) (lookup : NormalizationOwnership.State)
    (coupled : ∀ rows, (projectionAt (cursorGraph cursor) (fun world => True ∧
      InputFrame safety base.allocator 6 rows (CallerSpareSuccessTests.argumentView empty)
        (CallerInputTests.request empty).arguments (CallerSpareSuccessTests.normalized empty) world)).SourceConstructorsAt (Nested.storageReads rows) debug children model)
    (publishes : ∀ id, ProjectsAt (cursorGraph cursor) (fun _ => True)
      ((base.primitives (CallerSpareSuccessTests.argumentView empty) CallerSpareSuccessTests.itemSource
        AssemblyItem.Creation.NativeFields.Tests.input).publish (CallerInputTests.key empty) (CallerSpareSuccessTests.normalized empty) id)
      (seed.publish (CallerInputTests.key empty) id))
    (inserts : ProjectsAt (cursorGraph cursor) (fun _ => True)
      ((base.primitives (CallerSpareSuccessTests.argumentView empty) CallerSpareSuccessTests.itemSource
        AssemblyItem.Creation.NativeFields.Tests.input).insert (CallerInputTests.key empty) (CallerSpareSuccessTests.normalized empty) true)
      (seed.insert (CallerInputTests.key empty) true)) :
    let before := (CallerSpareSuccessTests.taken safety empty).2
    let physical := (context base 6 usizeBits children debug).primitives (CallerSpareSuccessTests.argumentView empty)
      CallerSpareSuccessTests.itemSource AssemblyItem.Creation.NativeFields.Tests.input
    let executed := Interner.findCode.controlMiss (OwnedCall.execution base.external base.allocator physical)
      (CallerInputTests.request empty) (CallerInputTests.key empty) true before
    let logical := Interner.findCode.controlMiss (Interner.Scoped.execution resources (dispatchModel seed model usizeBits debug))
      (CallerInputTests.request empty) (CallerInputTests.key empty) true
      (Caller.ScopeProjection.scopeAt (cursorGraph cursor) lookup (CallerInputTests.values empty) before)
    ordinary executed.1 = true → executed.1 = logical.1.mapError Fault.language ∧
      Caller.ScopeProjection.scopeAt (cursorGraph cursor) lookup (CallerInputTests.values empty) executed.2 = logical.2 := by
  have entry := CallerSpareSuccessTests.derived_input safety empty
  have input : InputFrame safety base.allocator 6 [CallerSpareSuccessTests.old safety empty]
      (CallerSpareSuccessTests.argumentView empty) (CallerInputTests.request empty).arguments
      (CallerSpareSuccessTests.normalized empty) (CallerSpareSuccessTests.taken safety empty).2.world := by
    simpa only [allocator] using (NativeSpareTests.reached_frame safety empty).1
  have projected := scoped_miss_from_frame cursor safety 6 base usizeBits children model seed debug
    (CallerSpareSuccessTests.argumentView empty) (CallerInputTests.request empty).arguments CallerSpareSuccessTests.itemSource
    AssemblyItem.Creation.NativeFields.Tests.input (CallerInputTests.key empty) (CallerSpareSuccessTests.normalized empty)
    [CallerSpareSuccessTests.old safety empty] (CallerSpareSuccessTests.taken safety empty).2 (fun _ => True) trivial resources lookup
    (CallerInputTests.values empty) (CallerSpareSuccessTests.lookup empty) (CallerInputTests.request empty) true
    ⟨congrArg Local.lookup entry.origin.scope, congrArg Local.slice entry.origin.scope⟩ input entry.publication.aligned coupled publishes inserts
  exact fun completed => (projected completed).2

/-- The retained spare-call initializer supplies readiness and the exact
successful native take, in both layouts and for empty/nonempty arguments. -/
theorem spare_take_entry (safety empty : Bool) :
    Ready 7 (CallerSpareSuccessTests.argumentView empty) (CallerInputTests.request empty).arguments
      (CallerSpareSuccessTests.lookup empty) (CallerSpareSuccessTests.prepared safety empty).2.world.memory ∧
    OwnedCall.take (Publication.external Publication.GraphTests.host) 7
      ⟨(CallerSpareSuccessTests.prepared safety empty).2.world, { lookup := some (CallerSpareSuccessTests.lookup empty) }⟩ =
      (.ok (), (CallerSpareSuccessTests.taken safety empty).2) := by
  have calls := Publication.GraphTests.prefix_results safety empty
  have initialization := Caller.initialize_origin (Publication.external Publication.GraphTests.host) 160 7
    (CallerSpareSuccessTests.argumentView empty) (CallerInputTests.request empty) (CallerSpareSuccessTests.before safety empty)
    (Publication.GraphTests.stack safety empty) _ (CallerInputTests.values empty) (CallerSpareSuccessTests.prepared safety empty).2
    (CallerFirstSuccessTests.native_borrow_good safety empty).2
    (Publication.external_admitted _ (Normalization.Tests.external_admitted _)) calls.1 (Prod.ext calls.2.1 rfl)
  obtain ⟨handle, locals, ready, _, _⟩ := initialization.1
  have preparedScope : (CallerSpareSuccessTests.prepared safety empty).2.scope =
      { lookup := some (CallerSpareSuccessTests.lookup empty) } := by
    cases safety <;> cases empty <;> insertion_kernel_rfl
  have same := Option.some.inj (congrArg Local.lookup (locals.symm.trans preparedScope))
  subst handle
  have state : (⟨(CallerSpareSuccessTests.prepared safety empty).2.world,
      { lookup := some (CallerSpareSuccessTests.lookup empty) }⟩ : State (Publication.Effects Nat)) =
      (CallerSpareSuccessTests.prepared safety empty).2 := by rw [← preparedScope]
  exact ⟨ready, by rw [state]; exact Prod.ext calls.2.2.1 rfl⟩

/-- The same prepared native frame now reaches ordinary cleanup and the checked
close of its actual scoped result. Graph callbacks remain local obligations;
no complete native dispatcher or miss preservation contract is supplied. -/
theorem spare_closed_from_children (safety empty : Bool) (base : PairInput.Context (Publication.Effects Nat))
    (allocator : base.allocator = 7) (host : base.external = Publication.external Publication.GraphTests.host) (usizeBits : Nat) (debug : AssemblyItem.Fields.Values)
    (cursor : World (Publication.Effects Nat) → Nat) (children : Constructors (Publication.Effects Nat))
    (model : Associative.Constructors AssemblyItem.Fields.Values) (seed : Interner.Primitives)
    (coupled : ∀ rows, (projectionAt (cursorGraph cursor) (fun world => True ∧
      InputFrame safety base.allocator 6 rows (CallerSpareSuccessTests.argumentView empty)
        (CallerInputTests.request empty).arguments (CallerSpareSuccessTests.normalized empty) world)).SourceConstructorsAt (Nested.storageReads rows) debug children model)
    (publishes : ∀ id, ProjectsAt (cursorGraph cursor) (fun _ => True)
      ((base.primitives (CallerSpareSuccessTests.argumentView empty) CallerSpareSuccessTests.itemSource
        AssemblyItem.Creation.NativeFields.Tests.input).publish (CallerInputTests.key empty) (CallerSpareSuccessTests.normalized empty) id)
      (seed.publish (CallerInputTests.key empty) id))
    (inserts : ProjectsAt (cursorGraph cursor) (fun _ => True)
      ((base.primitives (CallerSpareSuccessTests.argumentView empty) CallerSpareSuccessTests.itemSource
        AssemblyItem.Creation.NativeFields.Tests.input).insert (CallerInputTests.key empty) (CallerSpareSuccessTests.normalized empty) true)
      (seed.insert (CallerInputTests.key empty) true))
    (memory : GraphContracts base.allocator (CallerSpareSuccessTests.argumentView empty)
      (CallerInputTests.request empty).arguments (base.primitives (CallerSpareSuccessTests.argumentView empty)
        CallerSpareSuccessTests.itemSource AssemblyItem.Creation.NativeFields.Tests.input))
    (leading suffix : List (NormalizationOwnership.Trace.Event Failure)) :
    let lookup := (Caller.Take.capture base.external base.allocator .input (CallerSpareSuccessTests.lookup empty)
      (CallerSpareSuccessTests.prepared safety empty).2.world.memory).1.2
    let before := (CallerSpareSuccessTests.taken safety empty).2
    let physical := (context base 6 usizeBits children debug).primitives (CallerSpareSuccessTests.argumentView empty)
      CallerSpareSuccessTests.itemSource AssemblyItem.Creation.NativeFields.Tests.input
    let body := Interner.findCode.controlMiss (OwnedCall.execution base.external base.allocator physical)
      (CallerInputTests.request empty) (CallerInputTests.key empty) true before
    ordinary body.1 = true → cursor body.2.world = leading.length →
    ∃ after, OwnedCall.finish base.external base.allocator body.1 body.2 = (body.1, after) ∧
      CleanupPost base.external base.allocator (CallerSpareSuccessTests.argumentView empty)
        (CallerInputTests.request empty).arguments (CallerSpareSuccessTests.normalized empty) body.2 after ∧
      let phase : NormalizationOwnership.Exit := if body.2.scope.handedOff then .transfer else .cleanup
      let execution := Caller.Close.capture base.external base.allocator lookup phase (CallerSpareSuccessTests.lookup empty) body.2
      let resources := Scope.resources (leading ++ (execution.2.events ++ suffix)) (.preparation .incomplete)
      let logical := Interner.findCode.controlMiss (Interner.Scoped.execution resources (dispatchModel seed model usizeBits debug))
        (CallerInputTests.request empty) (CallerInputTests.key empty) true
        (Caller.ScopeProjection.scopeAt (cursorGraph cursor) lookup (CallerSpareSuccessTests.lookup empty).values before)
      body.1 = logical.1.mapError Fault.language ∧
      logical.2 = Caller.ScopeProjection.scopeAt (cursorGraph cursor) lookup (CallerSpareSuccessTests.lookup empty).values body.2 ∧
      after.world.memory = execution.2.effects.session ∧
      Caller.Close.checked execution leading suffix lookup logical.2.scope.phase logical.2.scope.items logical.2.heap =
        .ok (Interner.Scoped.close resources logical.2) := by
  intro lookup before physical body completed start
  have entry := CallerSpareSuccessTests.derived_input safety empty
  have input : InputFrame safety base.allocator 6 [CallerSpareSuccessTests.old safety empty]
      (CallerSpareSuccessTests.argumentView empty) (CallerInputTests.request empty).arguments
      (CallerSpareSuccessTests.normalized empty) (CallerSpareSuccessTests.taken safety empty).2.world := by
    simpa only [allocator] using (NativeSpareTests.reached_frame safety empty).1
  have takeEntry := spare_take_entry safety empty
  have ready : Ready base.allocator (CallerSpareSuccessTests.argumentView empty) (CallerInputTests.request empty).arguments
      (CallerSpareSuccessTests.lookup empty) (CallerSpareSuccessTests.prepared safety empty).2.world.memory := by
    simpa only [allocator] using takeEntry.1
  have takeCall : OwnedCall.take base.external base.allocator
      ⟨(CallerSpareSuccessTests.prepared safety empty).2.world, { lookup := some (CallerSpareSuccessTests.lookup empty) }⟩ =
      (.ok (), before) := by simpa only [allocator, host] using takeEntry.2
  have admitted : Admitted base.external := by
    rw [host]
    exact Publication.external_admitted _ (Normalization.Tests.external_admitted _)
  have complete := closed_miss_after_take cursor safety 6 base usizeBits children model seed debug
    (CallerSpareSuccessTests.argumentView empty) (CallerInputTests.request empty).arguments CallerSpareSuccessTests.itemSource
    AssemblyItem.Creation.NativeFields.Tests.input (CallerInputTests.key empty) (CallerSpareSuccessTests.normalized empty)
    [CallerSpareSuccessTests.old safety empty] (CallerSpareSuccessTests.prepared safety empty).2.world
    (CallerSpareSuccessTests.lookup empty) (CallerSpareSuccessTests.lookup empty) before .input ready admitted takeCall
    (fun _ => True) trivial (CallerInputTests.request empty) true entry.origin.scope input entry.publication.aligned
    coupled publishes inserts
    (fun id world _ held => memory.publish _ _ id world entry.publication.aligned held)
    (fun world _ held => memory.insert _ _ true world entry.publication.aligned held) leading suffix
  obtain ⟨after, finished, clean, _, projected⟩ := complete.2 completed start
  exact ⟨after, finished, clean, projected⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ScopeTests
