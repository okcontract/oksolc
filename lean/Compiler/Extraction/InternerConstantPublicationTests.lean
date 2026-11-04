/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstantInputTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ConstantPublicationTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops GraphFacts)
open ConstantInputTests

attribute [local irreducible] ReachablePrefixTests.before RecursiveTests.Call.constructed RecursiveTests.Call.stack

theorem duplicate_result (safety : Bool) (value : Word) :
    (call safety value).duplicate =
      (.ok ((call safety value).normalized, ⟨view (call safety value).normalized, [], none⟩),
        (call safety value).taken.2.world.memory) :=
  (call safety value).duplicate_empty rfl rfl rfl (prepared safety value).2 (stack safety value).1

theorem creation_fits (safety : Bool) (value : Word) :
    Compiler.ZigAir.Memory.RegionAllocation.Fits (call safety value).duplicate.2.memory
      AssemblyItem.Creation.layout
      (((call safety value).duplicate.2.memory.nextAddress / AssemblyItem.Creation.layout.alignment + 1) *
        AssemblyItem.Creation.layout.alignment) := by
  have counter : (call safety value).duplicate.2.memory.nextAddress = (scratchReference safety).nextAddress := by
    rw [duplicate_result, (ConstantInputTests.normalized safety value).2.2.2]; exact (stack safety value).2
  have geometry :
      0 < ((scratchReference safety).nextAddress / AssemblyItem.Creation.layout.alignment + 1) * AssemblyItem.Creation.layout.alignment ∧
      (((scratchReference safety).nextAddress / AssemblyItem.Creation.layout.alignment + 1) * AssemblyItem.Creation.layout.alignment) % AssemblyItem.Creation.layout.alignment = 0 ∧
      ((scratchReference safety).nextAddress / AssemblyItem.Creation.layout.alignment + 1) * AssemblyItem.Creation.layout.alignment + AssemblyItem.Creation.layout.bytes ≤ Compiler.ZigAir.Memory.addressLimit ∧
      (scratchReference safety).nextAddress ≤ ((scratchReference safety).nextAddress / AssemblyItem.Creation.layout.alignment + 1) * AssemblyItem.Creation.layout.alignment := by
    cases safety <;> apply of_decide_eq_true <;> insertion_kernel_rfl
  have valid : (call safety value).duplicate.2.memory.valid = true := by
    rw [duplicate_result]; exact (established safety value).taken.valid.memory
  apply Compiler.ZigAir.Memory.RegionAllocation.fits_above _ _ _ valid
  · rw [counter]; exact geometry.1
  · rw [counter]; exact geometry.2.1
  · rw [counter]; exact geometry.2.2.1
  · rw [counter]; exact geometry.2.2.2

def object (safety : Bool) (value : Word) := (call safety value).before.memory.memory.nextId + 2

/-- The reached high-water mark derived from the actual creation response. -/
def publishedAddress (safety : Bool) := max (scratchReference safety).nextAddress
  (((scratchReference safety).nextAddress / AssemblyItem.Creation.layout.alignment + 1) *
    AssemblyItem.Creation.layout.alignment + AssemblyItem.Creation.layout.bytes)

theorem created (safety : Bool) (value : Word) :
    (call safety value).create.1 = .ok (object safety value) ∧
    (call safety value).create.2.memory.nextId = (initial safety).memory.memory.nextId + 3 ∧
    (call safety value).create.2.memory.nextAddress = publishedAddress safety := by
  have valid : Valid (call safety value).duplicate.2 := by
    rw [duplicate_result]; exact (established safety value).taken.valid
  have complete := AssemblyItem.Creation.create_from_response (observe ops.create) 7
    (((call safety value).duplicate.2.memory.nextAddress / AssemblyItem.Creation.layout.alignment + 1) *
      AssemblyItem.Creation.layout.alignment) (call safety value).native.item (call safety value).duplicate.2
    { (call safety value).duplicate.2.effects with allocator := (call safety value).duplicate.2.effects.allocator * 10 + 5 }
    valid rfl (creation_fits safety value)
  have counter := (Compiler.ZigAir.Memory.allocate_pointer _ _ _ _ (stack safety value).1).2
  rw [(prepared safety value).2.nextId] at counter
  have count : (call safety value).duplicate.2.memory.nextId = object safety value := by
    rw [duplicate_result, (ConstantInputTests.normalized safety value).2.2.2]; exact counter
  have reached := congrArg Prod.snd complete.1
  have address : (call safety value).duplicate.2.memory.nextAddress = (scratchReference safety).nextAddress := by
    rw [duplicate_result, (ConstantInputTests.normalized safety value).2.2.2]; exact (stack safety value).2
  refine ⟨(congrArg Prod.fst complete.1).trans (congrArg Except.ok count), ?_, ?_⟩
  · change (call safety value).create.2.memory.nextId = _
    rw [show (call safety value).create.2 = _ from reached]
    change (call safety value).duplicate.2.memory.nextId + 1 = _
    rw [count]; rfl
  · rw [show (call safety value).create.2 = _ from reached]
    change max (call safety value).duplicate.2.memory.nextAddress
      (((call safety value).duplicate.2.memory.nextAddress / AssemblyItem.Creation.layout.alignment + 1) *
        AssemblyItem.Creation.layout.alignment + AssemblyItem.Creation.layout.bytes) = _
    rw [address]; rfl

theorem cloned (safety : Bool) (value : Word) :
    (call safety value).clone = (.ok (call safety value).native, (call safety value).create.2) := rfl

def row (safety : Bool) (value : Word) := (call safety value).publicationRow (object safety value)
  (call safety value).normalized (call safety value).taken.2.world
def rows (safety : Bool) (value : Word) := ReachablePrefixTests.cells safety 3 ++ [row safety value]
theorem rows_count (safety : Bool) (value : Word) : (rows safety value).length = 5 := by
  simp only [rows, List.length_append, List.length_singleton,
    (ReachablePrefixTests.initialized_prefix safety 3 (by decide)).count]

/-- The native query reads the arbitrary data installed by publication. The
same statement applies after any established graph-preserving caller frame. -/
theorem value_read (safety : Bool) (value : Word) (world : World (Publication.Effects Nat))
    (facts : GraphFacts safety ReachablePrefixTests.backing 5 world (rows safety value)) :
    (Interner.representativeReads world.graph).constant 4 = .ok (some value) ∧
    Constant.value world.memory.memory (Owner.headerAddress ⟨6, 0⟩) 4 = .ok (.ok (some value)) := by
  have prior := ReachablePrefixTests.initialized_prefix safety 3 (by decide)
  have inside : (4 : NodeId).toNat < (rows safety value).length := by rw [rows_count]; decide
  have last : (rows safety value)[(4 : NodeId).toNat] = row safety value := by
    change (ReachablePrefixTests.cells safety 3 ++ [row safety value])[4] = _
    exact List.getElem_concat_length (by rw [prior.count]; rfl) inside
  have logical : Storage.representativeProgram.run (rows safety value) 4 = .ok (row safety value) := by
    rw [Storage.representative_correct, List.getElem?_eq_getElem inside, last]
  have constant : Storage.constantProgram.run (rows safety value) 4 = .ok (some value) := by
    simp only [Storage.constantProgram, Storage.ConstantRead.run, logical]
    rfl
  refine ⟨?_, ?_⟩
  · simp only [Interner.representativeReads, facts.projected, Nested.storageReads, constant]
  · exact ((facts.native (by rw [rows_count]; decide)).constants 4).trans (congrArg Except.ok constant)

def primitives (allocate : Backing.Registry.Allocate Nat) (growth : Option (Growth.Registered.Callbacks Nat)) (safety : Bool) (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue) :=
  callerPrimitives ops allocate safety 7 6 ⟨0, 0, 0⟩ address Insertion.Tests.model native RecursiveTests.childSeed growth

def full (safety : Bool) (value : Word) (allocate : Backing.Registry.Allocate Nat := ReachablePrefixTests.allocate)
    (growth : Option (Growth.Registered.Callbacks Nat) := none) := constant (Publication.external ops.arguments) 160 7 (primitives allocate growth safety)
  Interner.Queries.queries value RecursiveTests.debug (initial safety)
def ready (safety : Bool) (value : Word) (allocate : Backing.Registry.Allocate Nat := ReachablePrefixTests.allocate)
    (growth : Option (Growth.Registered.Callbacks Nat) := none) := (full safety value allocate growth).2.world

theorem contract (safety : Bool) (value : Word) (allocate : Backing.Registry.Allocate Nat := ReachablePrefixTests.allocate)
    (growth : Option (Growth.Registered.Callbacks Nat) := none) :
    (full safety value allocate growth).1 = .ok 4 ∧ GraphFacts safety ReachablePrefixTests.backing 5 (ready safety value allocate growth) (rows safety value) ∧
    AssemblyClone.NativeFields.Represents (ready safety value allocate growth).memory.memory ⟨object safety value, 0⟩ (call safety value).native ∧
    (ready safety value allocate growth).graph.read = Storage.readValue (rows safety value) ∧
    (∀ id native, (initial safety).memory.memory.heap.lookup id = some native → id ≠ 6 →
      id ≠ ReachablePrefixTests.backing → (ready safety value allocate growth).memory.memory.heap.lookup id = some native) ∧
    (ready safety value allocate growth).memory.memory.nextId = (initial safety).memory.memory.nextId + 3 ∧
    (ready safety value allocate growth).memory.memory.nextAddress = publishedAddress safety ∧
    (ready safety value allocate growth).graph.table (call safety value).key = some 4 ∧
    (ready safety value allocate growth).graph.table =
      Cache.put equalityFields (initial safety).graph.table (call safety value).key 4 ∧
    Owner.NativeLock.checkHeader (ready safety value allocate growth).memory.memory (Owner.headerAddress ⟨6, 0⟩) = .ok () := by
  have prior := ReachablePrefixTests.initialized_prefix safety 3 (by decide)
  have current := established safety value
  have room : Interner.Queries.queries.atCapacity (call safety value).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ current.constructed.projected, prior.count]; decide
  have routed := (call safety value).route (primitives allocate growth safety) (observed safety value) current.item.graph room rfl
  change (call safety value).invoked (primitives allocate growth safety) =
    (let done := finishInsertion ops allocate safety 7 6 (call safety value).source (call safety value).address
      Insertion.Tests.model (call safety value).native (call safety value).key true (call safety value).taken.2 growth
     if ordinary done.1 then (done.1, (call safety value).returned done.2) else done) at routed
  have duplicated := congrArg Prod.fst (duplicate_result safety value)
  have copied := congrArg Prod.fst (cloned safety value)
  have complete := (call safety value).spare_publication allocate growth safety ReachablePrefixTests.backing 5 (object safety value)
    (ReachablePrefixTests.cells safety 3) (call safety value).normalized (call safety value).duplicate.2 (call safety value).create.2 (call safety value).clone.2
    (primitives allocate growth safety) prior.facts (RecursiveTests.empty_good _ prior.facts.valid)
    (by change (2 : Int) ∈ AssemblyItem.itemTagValues; decide) (observed safety value)
    (by rw [prior.count]; decide) (by rw [prior.count]; decide)
    (Prod.ext duplicated rfl)
    (Prod.ext (created safety value).1 rfl) (Prod.ext copied rfl) routed
  have called : (call safety value).invoked (primitives allocate growth safety) = full safety value allocate growth := rfl
  rw [called, Storage.idFor, prior.count] at complete
  have initialLock : Owner.NativeLock.checkHeader (initial safety).memory.memory (Owner.headerAddress ⟨6, 0⟩) = .ok () := by
    cases safety <;> insertion_kernel_rfl
  refine ⟨complete.1, complete.2.1, complete.2.2.1, complete.2.2.2.1,
    fun id native found ownerApart backingApart => complete.2.2.2.2.1 id native found ownerApart backingApart
      (by intro old selected nonempty; exact False.elim (nonempty rfl)), ?_, ?_, complete.2.2.2.2.2.2.2.1, complete.2.2.2.2.2.2.2.2.1,
    complete.2.2.2.2.2.2.2.2.2.trans initialLock⟩
  · exact complete.2.2.2.2.2.1.trans ((congrArg (fun result => result.2.memory.nextId) (cloned safety value)).trans (created safety value).2.1)
  · exact complete.2.2.2.2.2.2.1.trans ((congrArg (fun result => result.2.memory.nextAddress) (cloned safety value)).trans (created safety value).2.2)

theorem other_missed (safety : Bool) (value other : Word) (apart : other ≠ value)
    (allocate : Backing.Registry.Allocate Nat) (growth : Option (Growth.Registered.Callbacks Nat)) :
    (ready safety value allocate growth).graph.table (ConstantInputTests.call safety other).key = none := by
  have table := (contract safety value allocate growth).2.2.2.2.2.2.2.2.1
  rw [table]
  have different : Cache.equal equalityFields (ConstantInputTests.call safety other).key
      (ConstantInputTests.call safety value).key = false := by
    apply Bool.eq_false_iff.mpr
    intro same
    exact apart (congrArg Key.data ((Cache.equality_iff _ _).mp same))
  simp only [Cache.put, different, Bool.false_eq_true, ↓reduceIte]
  exact ConstantInputTests.missed safety other

theorem first_read (safety : Bool) (value : Word) (world : World (Publication.Effects Nat))
    (facts : GraphFacts safety ReachablePrefixTests.backing 5 world (rows safety value)) :
    (Interner.representativeReads world.graph).constant 0 = .ok none ∧
    Constant.value world.memory.memory (Owner.headerAddress ⟨6, 0⟩) 0 = .ok (.ok none) := by
  have inside : (0 : NodeId).toNat < (rows safety value).length := by rw [rows_count]; decide
  have first : Storage.representativeProgram.run (rows safety value) 0 = .ok (ReachablePrefixTests.row safety 0) := by
    rw [Storage.representative_correct, List.getElem?_eq_getElem inside]; rfl
  have constant : Storage.constantProgram.run (rows safety value) 0 = .ok none := by
    simp only [Storage.constantProgram, Storage.ConstantRead.run, first]; rfl
  refine ⟨?_, ((facts.native (by rw [rows_count]; decide)).constants 0).trans (congrArg Except.ok constant)⟩
  simp only [Interner.representativeReads, facts.projected, Nested.storageReads, constant]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ConstantPublicationTests
