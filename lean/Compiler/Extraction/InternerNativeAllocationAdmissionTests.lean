/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstantFoldDispatchTests
import Compiler.Extraction.InternerNativeParentEntry
import Compiler.Extraction.InternerNativeFrameEffects
import Compiler.Extraction.InternerUniformModelTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeAllocationAdmissionTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open NativeRecursion Insertion.Native
open RecursiveTests (debug)

abbrev parent (safety : Bool) := ConstantFoldTests.parent safety 0

/-- Reuse an actual normalized/taken caller, including its live native item.
Only allocator-private state changes between the two child inputs. -/
def before (safety : Bool) (permitted : Bool) : World (Publication.Effects Nat) :=
  (parent safety).taken.2.world.mapEffects
    (Publication.Effects.mapAllocator (fun _ => if permitted then 1 else 0))

def frame (safety : Bool) : World (Publication.Effects Nat) → Prop :=
  CallFrame safety 7 6 (ConstantPublicationTests.rows safety 0) (parent safety).source [4]
    (parent safety).normalized (parent safety).address (parent safety).native (fun _ => True)

attribute [local irreducible] ConstantPublicationTests.ready ConstantFoldTests.rootArguments
  RecursiveTests.Call.constructed RecursiveTests.Call.stack

theorem initial_frame (safety : Bool) : frame safety (parent safety).taken.2.world := by
  have literal := ConstantFoldTests.literal safety 0
  have prior := ConstantPublicationTests.contract safety 0 RecursiveNonemptyTests.failing (some CallerGrowingChainTests.growth)
  have entry := ConstantFoldTests.established safety 0
  have privateSource : Caller.SourcePrivate (parent safety).source (parent safety).constructed.memory.effects.keys := by
    rw [congrArg Publication.Effects.keys entry.item.effects, congrArg Publication.Effects.keys literal.2.1.effects]
    exact fun key => literal.2.1.key_apart [4] _ _ _ prior.2.1.valid 7 key prior.2.1.live
  exact CallFrame.caller entry.entry
    (entry.constructed.native (by rw [ConstantPublicationTests.rows_count]; decide)) privateSource
    (literal.2.1.arraySource.frame (fun _ cell found => entry.item.memory _ cell found)) (fun _ => True) trivial

theorem admitted_frame (safety permitted : Bool) : frame safety (before safety permitted) :=
  (CallFrame.mapAllocator_iff _).mpr (initial_frame safety)

/-- One fixed allocator callback permits or refuses item creation according to
its private state. The successful address comes from the existing fresh-region
allocator fixture. No compiler outcome is replaced by a logical callback. -/
def ops : Insertion.Operations Nat := { CallerGrowingChainTests.ops with
  create := fun wanted reached =>
    if reached.effects = 0 then (none, reached.effects)
    else CallerGrowingChainTests.ops.create wanted reached }

def base (safety : Bool) : PairInput.Context (Publication.Effects Nat) :=
  { ReachablePrefixTests.base safety with
    primitives := fun source address native =>
      callerPrimitives ops ReachablePrefixTests.allocate safety 7 6 source address
        Insertion.Tests.model native (ReachablePrefixTests.seed source) (some CallerGrowingChainTests.growth) }

def children (safety : Bool) := NativeRecursion.unfold (base safety) 6 64 1

def child (safety : Bool) : GraphAction (Publication.Effects Nat) NodeId :=
  (children safety).constant 1 debug

attribute [local irreducible] children

theorem parent_selected (safety : Bool) :
    Interner.Queries.queries.deterministic (parent safety).request.item = .ok true ∧
    (parent safety).request.item.kind = 1 := ⟨rfl, rfl⟩

theorem native_operand (safety permitted : Bool) :
    (NativeReads.reads 6 (before safety permitted).memory.memory).constant 4 = .ok (some 0) := by
  have current := (ConstantFoldTests.established safety 0).taken
  change (NativeReads.reads 6 (parent safety).taken.2.world.memory.memory).constant 4 = _
  rw [(current.native (by rw [ConstantPublicationTests.rows_count]; decide)).reads]
  exact (ConstantPublicationTests.value_read safety 0 _ current).1

/-- The existing ISZERO dispatch really requests this constant child on both
inputs. The counterexample is not an unrelated call under an inactive guard. -/
theorem dispatch_calls_child (safety permitted : Bool) :
    ((NativeRecursion.context (base safety) 6 64 (children safety) debug).primitives
      (parent safety).source (parent safety).address (parent safety).native).simplify
      (parent safety).key (parent safety).normalized (before safety permitted) =
        ((child safety (before safety permitted)).1.map some, (child safety (before safety permitted)).2) := by
  rw [NativeRecursion.dispatcher_snapshot]
  exact ConstantFoldTests.iszero_result _ (children safety) 0 debug _ _ _ (native_operand safety permitted) rfl
    (input := NativeRecursion.operand) (address := (parent safety).normalized.address)

theorem successful (safety : Bool) : (child safety (before safety true)).1 = .ok 5 := by
  cases safety <;> insertion_kernel_rfl

theorem refused (safety : Bool) :
    (child safety (before safety false)).1 = .error (.language .outOfMemory) := by
  cases safety <;> insertion_kernel_rfl

theorem same_graph (safety : Bool) : (before safety true).graph = (before safety false).graph := rfl

/-- This is a counterexample to a uniform projection from the structural frame,
not a compiler miscompilation. Both ordinary results come from the same complete
native constructor, initialized caller, and fixed host callbacks. -/
theorem no_model (safety : Bool) (observe : World (Publication.Effects Nat) → Interner.Heap)
    (same : observe (before safety true) = observe (before safety false)) :
    ¬ ∃ model : Interner.Action NodeId, Recursive.ProjectsAt observe (frame safety) (child safety) model := by
  rintro ⟨model, coupled⟩
  have conflict := Recursive.Uniform.agrees_of_projects observe (frame safety) (child safety) model coupled
    (before safety true) (before safety false) (admitted_frame safety true) (admitted_frame safety false)
    (by rw [successful]; rfl) (by rw [refused]; rfl) same
  have results := conflict.1
  rw [successful, refused] at results
  cases results

theorem no_cursor_model (safety : Bool) (position : Nat) :
    ¬ ∃ model : Interner.Action NodeId,
      Recursive.ProjectsAt (Recursive.cursorGraph (fun _ => position)) (frame safety) (child safety) model :=
  no_model safety _ rfl

/-- Narrowing the chosen model's domain cannot repair this while admission must
still follow from every structurally valid caller. This directly rejects the
unrestricted premise pair of the current uniform one-step theorem. -/
theorem no_source_admission (safety : Bool) (observe : World (Publication.Effects Nat) → Interner.Heap)
    (same : observe (before safety true) = observe (before safety false)) (reads : Nested.Reads) :
    ¬ ∃ domains : Recursive.Uniform.Domains (Publication.Effects Nat) AssemblyItem.Fields.Values,
      Recursive.Uniform.SourceAdmission domains debug reads (frame safety) ∧
      Recursive.Uniform.Agreement observe domains (children safety) := by
  rintro ⟨domains, admitted, agreement⟩
  have conflict := agreement.constant 1 debug (before safety true) (before safety false)
    (admitted.constant 1 _ (admitted_frame safety true)) (admitted.constant 1 _ (admitted_frame safety false))
    (by change ordinary (child safety (before safety true)).1 = true; rw [successful]; rfl)
    (by change ordinary (child safety (before safety false)).1 = true; rw [refused]; rfl) same
  have results := conflict.1
  change (child safety (before safety true)).1 = (child safety (before safety false)).1 at results
  rw [successful, refused] at results
  cases results

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeAllocationAdmissionTests
