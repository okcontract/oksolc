/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursivePublicationTests
import Compiler.Extraction.InternerConstructorArguments
import Compiler.Extraction.InternerReachablePrefixTests
import Compiler.Extraction.InternerConstantPublicationTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveNonemptyTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops cells lifetime GraphFacts)
open RecursiveTests (Call debug)

attribute [local irreducible] invoke

abbrev initial (safety : Bool) := ReachablePrefixTests.before safety 3
def zero (safety : Bool) : Call := ConstantInputTests.call safety 0
def zeroObject (safety : Bool) := (zero safety).before.memory.memory.nextId + 2
def zeroHandle (safety : Bool) : Handle := ⟨view (zero safety).normalized, [], none⟩
def duplicated (safety : Bool) := takeOwned normalizationOwnershipCode (Publication.external ops.arguments) 7
  (zeroHandle safety) (zero safety).taken.2.world.memory
def created (safety : Bool) := AssemblyItem.Creation.create (observe ops.create) 7 (zero safety).native.item (duplicated safety).2
def cloned (safety : Bool) := AssemblyClone.Physical.run (observe ops.copy) 7 (zero safety).native (created safety).2
def installed (safety : Bool) :=
  ((AssemblyClone.NativeFields.install (zero safety).native (zeroObject safety) (cloned safety).2).toOption).getD (cloned safety).2
def zeroValue (safety : Bool) := ((zero safety).key.eval Insertion.Tests.model (zero safety).taken.2.world.graph.read).getD 0
def zeroRow (safety : Bool) : Storage.Cell :=
  ⟨(zero safety).native.item, zeroValue safety, zeroObject safety, [], 0, (zero safety).normalized.address⟩
def rows (safety : Bool) := ReachablePrefixTests.cells safety 3 ++ [zeroRow safety]
def zeroProjected (safety : Bool) (after : Native.Frame Nat) := Insertion.projected (ReachablePrefixTests.cells safety 3)
  (zero safety).taken.2.world (zero safety).key (zeroRow safety) Storage.publishedOwnership after
def zeroPrimitives (safety : Bool) (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue) :=
  callerPrimitives ops ReachablePrefixTests.allocate safety 7 6 ⟨0, 0, 0⟩ address Insertion.Tests.model native RecursiveTests.childSeed
def zeroFull (safety : Bool) := constant (Publication.external ops.arguments) 160 7 (zeroPrimitives safety)
  Interner.Queries.queries 0 debug (initial safety)
def ready (safety : Bool) := (zeroFull safety).2.world

theorem zero_observed (safety : Bool) :
    (zero safety).observations = (zero safety).expected ∧
    (duplicated safety).1 = .ok ((zero safety).normalized, zeroHandle safety) ∧
    (created safety).1 = .ok (zeroObject safety) ∧ (cloned safety).1 = .ok (zero safety).native ∧
    (zero safety).before.memory.memory.nextId = 21 := by
  refine ⟨ConstantInputTests.observed safety 0, ?_⟩
  cases safety <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl,
    by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem zero_established (safety : Bool) : (zero safety).Established safety ReachablePrefixTests.backing 5 (ReachablePrefixTests.cells safety 3) :=
  ConstantInputTests.established safety 0

/-- A full constant constructor appends the actual Push-zero item and publishes
its key before returning through both local frames. This row will select the
nonempty recursive child; its native data is derived from the same clone. -/
theorem zero_contract (safety : Bool) :
    (zeroFull safety).1 = .ok 4 ∧ GraphFacts safety ReachablePrefixTests.backing 5 (ready safety) (rows safety) ∧
    AssemblyClone.NativeFields.Represents (ready safety).memory.memory ⟨zeroObject safety, 0⟩ (zero safety).native ∧
    (ready safety).graph.read = Storage.readValue (rows safety) ∧
    (∀ id native, (initial safety).memory.memory.heap.lookup id = some native → id ≠ 6 →
      id ≠ ReachablePrefixTests.backing → (ready safety).memory.memory.heap.lookup id = some native) := by
  have complete := ConstantPublicationTests.contract safety 0
  exact ⟨complete.1, complete.2.1, complete.2.2.1, complete.2.2.2.1, complete.2.2.2.2.1⟩

/-- The caller array present at initialization survives the complete prefix,
constant publication and both returns. Indexed reads and later constructor
frames consume this fact without observing the final heap independently. -/
theorem caller_source (safety : Bool) :
    Good (CallerInputTests.argumentView false) [0] (ready safety) := by
  have original : Good (CallerInputTests.argumentView false) [0] (CallerInputTests.world safety) :=
    ⟨(ReachablePrefixTests.initial safety).valid, (CallerInputTests.source_inputs safety false).1⟩
  obtain ⟨native, found⟩ := original.backed (by decide)
  have prefixFrame := (ReachablePrefixTests.initialized_prefix safety 3 (by decide)).frame _ native found (by decide) (by decide)
  have kept := (zero_contract safety).2.2.2.2 _ native prefixFrame (by decide) (by decide)
  exact ⟨(zero_contract safety).2.1.valid, represented_frame _ _ original.2 (kept.trans found.symm)⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveNonemptyTests
