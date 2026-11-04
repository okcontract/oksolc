/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorItemSetupTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.Tests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (parent cells startId lifetime ops growth grownLifetime)
open CallerInputTests (values)

abbrev reserve := CallerGrowingChainTests.allocate

def operands (empty : Bool) : ArgumentSlice := ⟨startId empty 4 + (if empty then 2 else 3), values empty⟩
def handle (empty : Bool) : Handle := ⟨view (normalized empty), values empty, none⟩
def object (empty : Bool) := startId empty 4 + (if empty then 2 else 4)
def duplicated (safety empty : Bool) := takeOwned normalizationOwnershipCode (Publication.external ops.arguments) 7
  ⟨view (normalized empty), (normalized empty).items, none⟩ (taken safety empty).2.world.memory
def created (safety empty : Bool) := AssemblyItem.Creation.create (observe ops.create) 7 (native empty).item (duplicated safety empty).2
def cloned (safety empty : Bool) := AssemblyClone.Physical.run (observe ops.copy) 7 (native empty) (created safety empty).2
def ready (safety empty : Bool) :=
  ((AssemblyClone.NativeFields.install (native empty) (object empty) (cloned safety empty).2).toOption).getD (cloned safety empty).2
def value (safety empty : Bool) := ((key empty).eval Insertion.Tests.model (taken safety empty).2.world.graph.read).getD 0
def row (safety empty : Bool) : Storage.Cell :=
  ⟨(native empty).item, value safety empty, object empty, values empty, 0, (operands empty).address⟩
def execute (safety empty : Bool) := Native.execution ops reserve safety 7 6 (parent empty) (itemSource empty) Insertion.Tests.model
  (native empty) (key empty) (normalized empty) true (cells safety empty 4) (taken safety empty).2.world (some growth)
def projected (safety empty : Bool) (after : Native.Frame Nat) := Insertion.projected (cells safety empty 4)
  (taken safety empty).2.world (key empty) (row safety empty) Storage.publishedOwnership after

def preparationObservations (safety empty : Bool) :=
  ((duplicated safety empty).1, (created safety empty).1, (cloned safety empty).1,
    (cloned safety empty).2.memory.nextId, decide ((ready safety empty).memory.nextAddress ≤ 8192))
def preparationExpected (empty : Bool) :=
  ((Except.ok (operands empty, handle empty) : Except Failure (ArgumentSlice × Handle)),
    (Except.ok (object empty) : Except AssemblyItem.Creation.Fault Nat),
    (Except.ok (native empty) : Except AssemblyClone.Physical.Fault AssemblyClone.NativeFields.ItemValue), grownLifetime empty, true)

theorem preparation_observed (safety empty : Bool) : preparationObservations safety empty = preparationExpected empty := by
  cases safety <;> cases empty <;> insertion_kernel_rfl

theorem preparation_results (safety empty : Bool) :
    duplicated safety empty = (.ok (operands empty, handle empty), (duplicated safety empty).2) ∧
    created safety empty = (.ok (object empty), (created safety empty).2) ∧
    cloned safety empty = (.ok (native empty), (cloned safety empty).2) ∧
    (cloned safety empty).2.memory.nextId = grownLifetime empty ∧
    (ready safety empty).memory.nextAddress ≤ 8192 := by
  have calls := preparation_observed safety empty
  simp only [preparationObservations, preparationExpected, Prod.mk.injEq, decide_eq_true_eq] at calls
  exact ⟨Prod.ext calls.1 rfl, Prod.ext calls.2.1 rfl, Prod.ext calls.2.2.1 rfl, calls.2.2.2⟩

theorem ready_valid (safety empty : Bool) : Valid (ready safety empty) := by
  have incoming := entry safety empty
  have calls := preparation_results safety empty
  let graph : Storage.State → Native.Frame Nat → Interner.Heap := fun owner state => Interner.InsertionExecution.project
    (cells safety empty 4) (taken safety empty).2.world.graph.table
    (cell (native empty) (key empty) (normalized empty) (value safety empty) owner state) (key empty) owner
  obtain ⟨installed, _, _, _, established, assigned, _⟩ := incoming.prepare ops reserve safety 7 6 (object empty)
    (parent empty) (itemSource empty) (request empty) (values empty) (native empty) (native empty) (key empty) (normalized empty)
    (operands empty) (lookup empty) (handle empty) (constructed safety empty) (taken safety empty).2
    (cells safety empty 4) (value safety empty) graph (duplicated safety empty).2 (created safety empty).2 (cloned safety empty).2
    (Normalization.Tests.external_admitted _) calls.1 calls.2.1 calls.2.2.1
  have same : ready safety empty = installed := by simp only [ready, assigned, Except.toOption, Option.getD_some]
  rw [same]
  exact established.valid

theorem backing_fits (safety empty : Bool) : Compiler.ZigAir.Memory.RegionAllocation.Fits (ready safety empty).memory ⟨416, 8⟩ 8192 := by
  have valid := (ready_valid safety empty).memory
  have bound := (preparation_results safety empty).2.2.2.2
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro entry present layout shaped
  simp only [Compiler.ZigAir.Memory.State.valid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at valid
  have checked := valid.1.2 entry present
  simp only [shaped, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact Or.inr (by omega)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.Tests
