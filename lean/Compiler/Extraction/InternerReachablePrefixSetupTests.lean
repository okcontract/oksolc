/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursivePublicationTests
import Compiler.Extraction.InternerNativeRecursion

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ReachablePrefixTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops GraphFacts)
open RecursiveTests (Call debug)

/-- Share the first backing response; each recursive fixture selects whether
its later nonempty allocation succeeds. -/
def allocator (grow : Bool) : Backing.Registry.Allocate Nat := fun allocator bytes alignment effects =>
  if allocator == 7 && bytes == 160 && alignment == 8 then (some 4096, effects * 10 + 7)
  else if grow then CallerGrowingChainTests.allocate allocator bytes alignment effects
  else (none, effects * 10 + 7)

def allocate := allocator true
def firstOnly := allocator false

def seed (source : View) : Primitives (Publication.Effects Nat) where
  simplify := fun _ _ before => (.error (.language .unsupported), before)
  publish := Publication.publish ops.probe ops.arguments 7 source
  insert := fun _ _ _ before => (.error (.language .unsupported), before)

def base (safety : Bool) : PairInput.Context (Publication.Effects Nat) :=
  ⟨Publication.external ops.arguments, 160, 7,
    fun source address native => callerPrimitives ops allocate safety 7 6 source address Insertion.Tests.model native (seed source),
    Interner.Queries.queries⟩

/-- ADDRESS, ORIGIN, CALLER and CALLVALUE have distinct deterministic keys and
no operands. Each enters the existing complete native recursive constructor. -/
def opcode : Nat → Opcode | 0 => 48 | 1 => 50 | 2 => 51 | _ => 52
def primitives (safety : Bool) :=
  (NativeRecursion.context (base safety) 6 64 NativeRecursion.exhausted debug).primitives ⟨0, 0, 0⟩
def invoke (safety : Bool) (n : Nat) :=
  (NativeRecursion.step (base safety) 6 64 NativeRecursion.exhausted).operation (opcode n) [] debug

/-- Sequence the same full constructor entries under the selected recursion context. -/
def sequence (constructors : NativeRecursion.Constructors (Publication.Effects Nat)) :
    Nat → GraphAction (Publication.Effects Nat) NodeId
  | 0 => constructors.operation (opcode 0) [] debug
  | n + 1 => do let _ ← sequence constructors n; constructors.operation (opcode (n + 1)) [] debug
def run (safety : Bool) (n : Nat) :=
  sequence (NativeRecursion.step (base safety) 6 64 NativeRecursion.exhausted) n (CallerInputTests.world safety)
def before (safety : Bool) (n : Nat) := (run safety n).2
def prior (safety : Bool) : Nat → World (Publication.Effects Nat)
  | 0 => CallerInputTests.world safety
  | n + 1 => before safety n
def call (safety : Bool) (n : Nat) : Call :=
  ⟨Interner.constructorCode.operationRequest (opcode n) [], ⟨0, 0, 0⟩, prior safety n⟩
def object : Nat → Nat | 0 => 10 | n + 1 => 14 + 3 * n
def operands (n : Nat) : ArgumentSlice := ⟨object n, []⟩
def row (safety : Bool) (n : Nat) := (call safety n).publicationRow (object n) (operands n) (call safety n).taken.2.world
def cells (safety : Bool) : Nat → List Storage.Cell
  | 0 => [row safety 0]
  | n + 1 => cells safety n ++ [row safety (n + 1)]
def backing : Nat := 11

attribute [local irreducible] invoke run before

theorem initial (safety : Bool) :
    NativeGraph.Facts safety 7 6 CallerInputTests.sentinel 0 (CallerInputTests.world safety) [] := by
  obtain ⟨after, ran, facts, _⟩ := NativeGraph.initialized safety 7 6 (CallerInputTests.raw safety)
    (AssemblyClone.NativeFields.QueryTests.ownerCell safety true) CallerInputTests.sentinel Insertion.Tests.model
    (AssemblyClone.NativeFields.QueryTests.initial_valid safety true) (by cases safety <;> rfl) rfl rfl rfl
  have same := (Prod.mk.inj (Except.ok.inj (ran.symm.trans (CallerInputTests.initializer safety)))).2
  rw [same] at facts
  exact facts

def Observed (safety : Bool) (n : Nat) : Prop :=
    (call safety n).observations = (call safety n).expected ∧
    (call safety n).duplicate.1 = .ok (operands n, ⟨view (call safety n).normalized, [], none⟩) ∧
    (call safety n).create.1 = .ok (object n) ∧ (call safety n).clone.1 = .ok (call safety n).native

/-- Keep each closed execution in one kernel check, then project its observed
components. Separate auxiliary lemmas repeat the complete recursive prefix. -/
private def Paired (safety : Bool) (n : Nat) : Prop :=
    ((call safety n).observations, (call safety n).duplicate.1, (call safety n).create.1, (call safety n).clone.1) =
    ((call safety n).expected, .ok (operands n, ⟨view (call safety n).normalized, [], none⟩),
      .ok (object n), .ok (call safety n).native)

private theorem of_paired (safety : Bool) (n : Nat) (checked : Paired safety n) : Observed safety n := by
  have first := Prod.mk.inj checked
  have second := Prod.mk.inj first.2
  have third := Prod.mk.inj second.2
  exact ⟨first.1, second.1, third.1, third.2⟩

private theorem observed_0 (safety : Bool) : Observed safety 0 := by
  apply of_paired; cases safety <;> unfold Paired <;> insertion_kernel_rfl

private theorem observed_1 (safety : Bool) : Observed safety 1 := by
  apply of_paired; cases safety <;> unfold Paired <;> insertion_kernel_rfl

private theorem observed_2 (safety : Bool) : Observed safety 2 := by
  apply of_paired; cases safety <;> unfold Paired <;> insertion_kernel_rfl

private theorem observed_3 (safety : Bool) : Observed safety 3 := by
  apply of_paired; cases safety <;> unfold Paired <;> insertion_kernel_rfl

theorem observed (safety : Bool) (n : Nat) (bounded : n < 4) : Observed safety n := by
  have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact observed_0 safety
  · exact observed_1 safety
  · exact observed_2 safety
  · exact observed_3 safety

theorem classified (n : Nat) :
    Interner.Queries.queries.deterministic (Interner.constructorCode.operationRequest (opcode n) []).item = .ok true := by
  cases n with
  | zero => rfl
  | succ n => cases n with
    | zero => rfl
    | succ n => cases n <;> rfl

theorem count (safety : Bool) (n : Nat) : (cells safety n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [cells, List.length_append, List.length_singleton, ih]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ReachablePrefixTests
