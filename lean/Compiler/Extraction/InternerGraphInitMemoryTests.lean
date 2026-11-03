/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerGraphInitTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.GraphInit.OwnerMemory.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray

def original : Session Nat := Normalization.Tests.original
def ownerCell (runtimeSafety writable : Bool) : Compiler.ZigAir.Memory.Allocation :=
  ⟨56, Compiler.Extraction.RepresentativeArray.Owner.viewType runtimeSafety, [], writable, true⟩
def before (runtimeSafety writable : Bool) : Session Nat :=
  { original with memory := ⟨(3, ownerCell runtimeSafety writable) :: original.memory.heap,
    4, 56 + (Compiler.Extraction.RepresentativeArray.Owner.layout runtimeSafety).bytes⟩ }
-- An unallocated empty sentinel with a nonzero offset is never dereferenced.
def sentinel : Address := ⟨99, 8⟩
def items : Value := .slice Compiler.Extraction.RepresentativeArray.itemsType sentinel 0
def capacity : Value := .scalar (.int false 64 0)
def completedCells : Cells := Cells.set (items.leaves 16).reverse 32 capacity
def withItems (runtimeSafety : Bool) : Compiler.ZigAir.Memory.State :=
  { (before runtimeSafety true).memory with
    heap := (before runtimeSafety true).memory.heap.replace 3 { ownerCell runtimeSafety true with cells := (items.leaves 16).reverse } }
def headerReady (runtimeSafety : Bool) : Session Nat :=
  { before runtimeSafety true with memory := { (before runtimeSafety true).memory with
    heap := (before runtimeSafety true).memory.heap.replace 3 { ownerCell runtimeSafety true with cells := completedCells } } }
def countOnly (runtimeSafety : Bool) : Session Nat :=
  { headerReady runtimeSafety with memory := { (headerReady runtimeSafety).memory with
    heap := (headerReady runtimeSafety).memory.heap.replace 3
      { ownerCell runtimeSafety true with cells := completedCells.set (if runtimeSafety then 64 else 48) (.scalar (.int false 32 0)) } } }
def mapCells (runtimeSafety : Bool) : Cells :=
  let metadata := completedCells.set (if runtimeSafety then 48 else 40) Compiler.Extraction.ExpressionMap.Initialization.Slot.metadata.value
  let counted := metadata.set (if runtimeSafety then 64 else 48) (.scalar (.int false 32 0))
  let available := counted.set (if runtimeSafety then 68 else 52) (.scalar (.int false 32 0))
  if runtimeSafety then available.set 56 (.scalar (.int false 64 0)) else available
def mapped (runtimeSafety : Bool) : Session Nat :=
  { headerReady runtimeSafety with memory := { (headerReady runtimeSafety).memory with
    heap := (headerReady runtimeSafety).memory.heap.replace 3
      { ownerCell runtimeSafety true with cells := mapCells runtimeSafety } } }
def after (runtimeSafety : Bool) : Session Nat :=
  { mapped runtimeSafety with memory := { (mapped runtimeSafety).memory with
    heap := (mapped runtimeSafety).memory.heap.replace 3
      { ownerCell runtimeSafety true with cells := (if runtimeSafety then (mapCells runtimeSafety).set 40 (.scalar (.int false 64 0)) else mapCells runtimeSafety) } } }
def initialized (runtimeSafety : Bool) : World Nat := ⟨emptyGraph, after runtimeSafety⟩

theorem initial_valid (runtimeSafety writable : Bool) : Valid (before runtimeSafety writable) := by
  have originalValid := Normalization.Tests.original_valid
  have framed : ∀ id, id ≠ 3 → (before runtimeSafety writable).memory.heap.lookup id = original.memory.heap.lookup id := by
    intro id apart
    simp only [before, Compiler.ZigAir.Memory.Heap.lookup_cons, if_neg (Ne.symm apart)]
  have shape : original.memory.heap.RetainsShape (before runtimeSafety writable).memory.heap := by
    intro id cell found
    have older := (valid_lookup original.memory id cell originalValid.memory found).1
    have apart : id ≠ 3 := by change id < 3 at older; omega
    exact ⟨cell, (framed id apart).trans found, Compiler.ZigAir.Memory.Allocation.SameShape.refl cell⟩
  exact Valid.private_memory_frame original (before runtimeSafety writable).memory 3 originalValid
    (originalValid.injected.fresh originalValid.memory) (by cases runtimeSafety <;> cases writable <;> decide) shape framed

theorem stack_owner_is_unregistered (runtimeSafety writable : Bool) : (before runtimeSafety writable).heap 3 = none :=
  Injected.stack_unregistered _ _ 3 (ownerCell runtimeSafety writable) (initial_valid runtimeSafety writable).injected rfl rfl

private theorem selected (runtimeSafety writable : Bool) :
    fieldPointer (before runtimeSafety writable).memory
      (.pointer (.pointer true false (Compiler.Extraction.RepresentativeArray.Owner.viewType runtimeSafety)) ⟨3, 0⟩)
      Compiler.Extraction.RepresentativeArray.Owner.representativesOffset =
      .ok (.pointer (.pointer true false Compiler.Extraction.RepresentativeArray.allocationType) ⟨3, 16⟩) :=
  Compiler.Extraction.RepresentativeArray.Owner.root_header_pointer runtimeSafety (before runtimeSafety writable).memory
    3 (ownerCell runtimeSafety writable) true (initial_valid runtimeSafety writable).memory rfl rfl

theorem actual_header_stores (runtimeSafety : Bool) :
    store (before runtimeSafety true).memory
      (.pointer (.pointer true false Compiler.Extraction.RepresentativeArray.itemsType) ⟨3, 16⟩) items = .ok (withItems runtimeSafety) ∧
    store (withItems runtimeSafety) (.pointer (.pointer true false usize) ⟨3, 32⟩)
      capacity = .ok (headerReady runtimeSafety).memory := by
  cases runtimeSafety <;> constructor <;> rfl

theorem header_valid (runtimeSafety : Bool) : (headerReady runtimeSafety).memory.valid = true :=
  store_preserves_valid _ _ _ _
    (store_preserves_valid _ _ _ _ (initial_valid runtimeSafety true).memory (actual_header_stores runtimeSafety).1)
    (actual_header_stores runtimeSafety).2

theorem native_count_write (runtimeSafety : Bool) :
    store (headerReady runtimeSafety).memory (.pointer (.pointer true false Compiler.Extraction.ExpressionMap.countType) ⟨3, if runtimeSafety then 64 else 48⟩)
      (.scalar (.int false 32 0)) = .ok (countOnly runtimeSafety).memory := by
  cases runtimeSafety <;> rfl

theorem actual_count_store (runtimeSafety : Bool) :
    Compiler.Extraction.ExpressionMap.initializeSize runtimeSafety (headerReady runtimeSafety).memory ⟨3, 0⟩ =
      .ok (countOnly runtimeSafety).memory := by
  have pointer := Compiler.Extraction.ExpressionMap.root_size_pointer runtimeSafety (headerReady runtimeSafety).memory 3
    { ownerCell runtimeSafety true with cells := completedCells } true (header_valid runtimeSafety) rfl rfl
  cases runtimeSafety <;> simpa only [Compiler.Extraction.ExpressionMap.initializeSize, pointer, bind, Except.bind] using native_count_write _

def withCells (runtimeSafety : Bool) (cells : Cells) : Compiler.ZigAir.Memory.State :=
  { (headerReady runtimeSafety).memory with
    heap := (headerReady runtimeSafety).memory.heap.replace 3 { ownerCell runtimeSafety true with cells := cells } }

theorem write_fixture (runtimeSafety : Bool) (cells : Cells)
    (slot : Compiler.Extraction.ExpressionMap.Initialization.Slot)
    (active : slot.Active runtimeSafety) (valid : (withCells runtimeSafety cells).valid = true) :
    Compiler.Extraction.ExpressionMap.Initialization.write runtimeSafety (withCells runtimeSafety cells) ⟨3, 0⟩ slot =
      .ok (withCells runtimeSafety (cells.set ((if runtimeSafety then 48 else 40) + slot.offset runtimeSafety) slot.value)) := by
  have pointer := Compiler.Extraction.ExpressionMap.Initialization.root_pointer runtimeSafety
    (withCells runtimeSafety cells) 3 { ownerCell runtimeSafety true with cells } true slot active valid rfl rfl
  simp only [Compiler.Extraction.ExpressionMap.Initialization.write, pointer, bind, Except.bind]
  obtain ⟨next, stored⟩ := Compiler.Extraction.ExpressionMap.Initialization.store_total runtimeSafety
    (withCells runtimeSafety cells) 3 { ownerCell runtimeSafety true with cells } slot active valid rfl rfl rfl
  obtain ⟨many, child, address, layout, cell, contents, pointerEq, _, _, accessed, written, update⟩ :=
    store_success _ _ _ _ stored
  cases pointerEq
  have found := (access_success_region _ _ _ _ _ accessed).1
  have equal : cell = { ownerCell runtimeSafety true with cells } := Option.some.inj found.symm
  subst cell
  have exactContents := (Cells.write_success _ _ _ _ _ written).2.2.2
  have single : slot.value.leaves ((if runtimeSafety then 48 else 40) + slot.offset runtimeSafety) = [((if runtimeSafety then 48 else 40) + slot.offset runtimeSafety, slot.value)] := by cases slot <;> rfl
  change contents = (slot.value.leaves ((if runtimeSafety then 48 else 40) + slot.offset runtimeSafety)).foldl (fun result entry => result.set entry.1 entry.2) cells at exactContents
  rw [single] at exactContents
  subst contents
  rw [update] at stored
  exact stored

theorem actual_map_stores (runtimeSafety : Bool) :
    Compiler.Extraction.ExpressionMap.Initialization.run runtimeSafety (headerReady runtimeSafety).memory ⟨3, 0⟩ =
      .ok (mapped runtimeSafety).memory := by
  let metadata := completedCells.set (if runtimeSafety then 48 else 40) Compiler.Extraction.ExpressionMap.Initialization.Slot.metadata.value
  let counted := metadata.set (if runtimeSafety then 64 else 48) (.scalar (.int false 32 0))
  let available := counted.set (if runtimeSafety then 68 else 52) (.scalar (.int false 32 0))
  have first := write_fixture runtimeSafety completedCells .metadata (by simp [Compiler.Extraction.ExpressionMap.Initialization.Slot.Active])
    (header_valid runtimeSafety)
  have second := write_fixture runtimeSafety metadata .size (by simp [Compiler.Extraction.ExpressionMap.Initialization.Slot.Active])
    (by cases runtimeSafety <;> decide +kernel)
  rw [Compiler.Extraction.ExpressionMap.Initialization.size_write] at second
  have third := write_fixture runtimeSafety counted .available (by simp [Compiler.Extraction.ExpressionMap.Initialization.Slot.Active])
    (by cases runtimeSafety <;> decide +kernel)
  change Compiler.Extraction.ExpressionMap.Initialization.write runtimeSafety (withCells runtimeSafety completedCells) ⟨3, 0⟩ .metadata = .ok (withCells runtimeSafety metadata) at first
  have secondExact : Compiler.Extraction.ExpressionMap.initializeSize runtimeSafety (withCells runtimeSafety metadata) ⟨3, 0⟩ = .ok (withCells runtimeSafety counted) := by
    cases runtimeSafety <;> exact second
  have thirdExact : Compiler.Extraction.ExpressionMap.Initialization.write runtimeSafety (withCells runtimeSafety counted) ⟨3, 0⟩ .available = .ok (withCells runtimeSafety available) := by
    cases runtimeSafety <;> exact third
  change Compiler.Extraction.ExpressionMap.Initialization.run runtimeSafety (withCells runtimeSafety completedCells) ⟨3, 0⟩ = _
  apply Compiler.Extraction.ExpressionMap.Initialization.run_of_writes runtimeSafety _ _ _ _ _ _ first secondExact thirdExact
  cases runtimeSafety
  · rfl
  · have fourth := write_fixture true available .lock (by simp [Compiler.Extraction.ExpressionMap.Initialization.Slot.Active]) (by decide +kernel)
    simpa only [↓reduceIte] using fourth

theorem actual_lock_store (runtimeSafety : Bool) :
    Compiler.Extraction.RepresentativeArray.Owner.NativeLock.initializeLock runtimeSafety
      (mapped runtimeSafety).memory ⟨3, 0⟩ = .ok (after runtimeSafety).memory := by
  cases runtimeSafety <;> decide +kernel

theorem actual_source_initializer (runtimeSafety : Bool) :
    zigInitInOwner runtimeSafety 7 (before runtimeSafety true) ⟨3, 0⟩ sentinel = .ok (7, initialized runtimeSafety) := by
  have pointer := selected runtimeSafety true
  have written := actual_header_stores runtimeSafety
  have header : Compiler.Extraction.RepresentativeArray.Owner.initializeHeader runtimeSafety
      (before runtimeSafety true).memory ⟨3, 0⟩ sentinel 0 0 = .ok (headerReady runtimeSafety).memory := by
    simp only [Compiler.Extraction.RepresentativeArray.Owner.initializeHeader, pointer, bind, Except.bind]
    change (do let middle ← store (before runtimeSafety true).memory
                   (.pointer (.pointer true false Compiler.Extraction.RepresentativeArray.itemsType) ⟨3, 16⟩) items
               store middle (.pointer (.pointer true false usize) ⟨3, 32⟩) capacity) = _
    simpa only [written.1, bind, Except.bind] using written.2
  simp only [zigInitInOwner, GraphInit.OwnerMemory.run, header, actual_map_stores, actual_lock_store, bind, Except.bind]
  rfl

theorem source_initializer (runtimeSafety : Bool) (meaning : Meaning) :
    ∃ finalWorld, zigInitInOwner runtimeSafety 7 (before runtimeSafety true) ⟨3, 0⟩ sentinel = .ok (7, finalWorld) ∧
      Valid finalWorld.memory ∧ Interner.Invariant meaning finalWorld.graph ∧
      Memory.GraphResident 7 finalWorld.memory.heap [] ∧ finalWorld.graph.representatives = some [] ∧
      Compiler.Extraction.RepresentativeArray.readHeader finalWorld.memory.memory ⟨3, 16⟩ = .ok (items, capacity) ∧
      finalWorld.memory.heap = (before runtimeSafety true).heap ∧ finalWorld.memory.effects = (before runtimeSafety true).effects ∧
      finalWorld.memory.memory.nextId = (before runtimeSafety true).memory.nextId ∧
      finalWorld.memory.memory.nextAddress = (before runtimeSafety true).memory.nextAddress ∧
      (∀ other, other ≠ 3 → finalWorld.memory.memory.heap.lookup other = (before runtimeSafety true).memory.heap.lookup other) ∧
      Compiler.Extraction.ExpressionMap.readSize runtimeSafety finalWorld.memory.memory ⟨3, 0⟩ = .ok (.scalar (.int false 32 0)) ∧
      (∀ key, zigEmptyCacheGet runtimeSafety finalWorld.memory.memory ⟨3, 0⟩ key = .ok (finalWorld.graph.table key)) ∧
      Compiler.Extraction.ExpressionMap.Initialization.observeEmpty runtimeSafety finalWorld.memory.memory ⟨3, 0⟩ = .ok () ∧
      (before runtimeSafety true).memory.heap.RetainsShape finalWorld.memory.memory.heap ∧
      Compiler.Extraction.RepresentativeArray.Owner.NativeLock.checkUnlocked runtimeSafety finalWorld.memory.memory ⟨3, 0⟩ = .ok () :=
  initialize_verified runtimeSafety 7 (before runtimeSafety true) 3 (ownerCell runtimeSafety true) sentinel meaning
    (initial_valid runtimeSafety true) rfl rfl rfl rfl

theorem initialized_validity_and_header (runtimeSafety : Bool) (meaning : Meaning) :
    Valid (initialized runtimeSafety).memory ∧ Interner.Invariant meaning (initialized runtimeSafety).graph ∧
      Compiler.Extraction.RepresentativeArray.readHeader (initialized runtimeSafety).memory.memory ⟨3, 16⟩ = .ok (items, capacity) := by
  obtain ⟨finalWorld, executed, valid, invariant, _, _, header, _⟩ := source_initializer runtimeSafety meaning
  have equal : finalWorld = initialized runtimeSafety := (Prod.mk.inj (Except.ok.inj (executed.symm.trans (actual_source_initializer runtimeSafety)))).2
  exact equal ▸ ⟨valid, invariant, header⟩

theorem all_native_ids_reject_without_sentinel (runtimeSafety : Bool) (id : NodeId) (meaning : Meaning) :
    (initialized runtimeSafety).memory.memory.heap.lookup sentinel.allocation = none ∧
      Compiler.Extraction.RepresentativeArray.representative (initialized runtimeSafety).memory.memory ⟨3, 16⟩ id = .ok (.error .invalidId) := by
  refine ⟨by cases runtimeSafety <;> rfl, ?_⟩
  exact empty_representative _ _ sentinel id (initialized_validity_and_header runtimeSafety meaning).2.2

theorem parent_offset_borrow_survives (runtimeSafety : Bool) (meaning : Meaning) :
    Represents (initialized runtimeSafety).memory.memory ⟨0, 1, 2⟩ [1, 2] := by
  obtain ⟨finalWorld, executed, _, _, _, _, _, _, _, _, _, frame, _, _⟩ := source_initializer runtimeSafety meaning
  have equal : finalWorld = initialized runtimeSafety := (Prod.mk.inj (Except.ok.inj (executed.symm.trans (actual_source_initializer runtimeSafety)))).2
  apply represented_frame ⟨0, 1, 2⟩ [1, 2] (before := (before runtimeSafety true).memory)
  · refine ⟨rfl, ?_⟩
    intro index inside
    have positions : index = 0 ∨ index = 1 := by simp only [List.length_cons, List.length_nil] at inside; omega
    rcases positions with rfl | rfl
    · exact (load_eq_of_lookup WordCopy.Tests.caller (before runtimeSafety true).memory
        true false word ⟨0, 4⟩ rfl).trans (WordCopy.Tests.represented_source.2 1 (by decide))
    · exact (load_eq_of_lookup WordCopy.Tests.caller (before runtimeSafety true).memory
        true false word ⟨0, 8⟩ rfl).trans (WordCopy.Tests.represented_source.2 2 (by decide))
  · exact equal ▸ frame 0 (by decide)

theorem registry_effects_and_lifetime_history_retained (runtimeSafety : Bool) (meaning : Meaning) :
    (initialized runtimeSafety).memory.heap 2 = original.heap 2 ∧
      load (initialized runtimeSafety).memory.memory ((⟨2, 0, 1⟩ : View).pointer 0) = .ok (number 99) ∧
      (initialized runtimeSafety).memory.effects = 5 ∧ (initialized runtimeSafety).memory.memory.nextId = 4 ∧
      (initialized runtimeSafety).memory.memory.nextAddress = 56 + (Compiler.Extraction.RepresentativeArray.Owner.layout runtimeSafety).bytes := by
  have registered := (initialized_validity_and_header runtimeSafety meaning).1.related 11 2 [99] (by decide) rfl
  exact ⟨rfl, registered.2.2 0 (by decide), rfl, rfl, rfl⟩

theorem readonly_owner_rejects (runtimeSafety : Bool) :
    zigInitInOwner runtimeSafety 7 (before runtimeSafety false) ⟨3, 0⟩ sentinel = .error .readOnly := by
  simp only [zigInitInOwner, GraphInit.OwnerMemory.run, Compiler.Extraction.RepresentativeArray.Owner.initializeHeader,
    selected runtimeSafety false, bind, Except.bind]
  cases runtimeSafety <;> rfl

theorem stale_owner_rejects (runtimeSafety : Bool) :
    zigInitInOwner runtimeSafety 7 (before runtimeSafety true) ⟨4, 0⟩ sentinel = .error .unallocated := by
  cases runtimeSafety <;> rfl

theorem nominal_owner_does_not_initialize (runtimeSafety : Bool) :
    let nominal := { before runtimeSafety true with memory := { (before runtimeSafety true).memory with
      heap := (before runtimeSafety true).memory.heap.replace 3
        { ownerCell runtimeSafety true with type := Compiler.Extraction.RepresentativeArray.Owner.allocationType runtimeSafety } } }
    zigInitInOwner runtimeSafety 7 nominal ⟨3, 0⟩ sentinel = .error .unsupported := by
  cases runtimeSafety <;> rfl

theorem registered_stack_owner_is_invalid (runtimeSafety : Bool) :
    ¬Valid ({ before runtimeSafety true with heap := Memory.write (before runtimeSafety true).heap 3 (some ⟨7, .arguments []⟩) } : Session Nat) := by
  intro invalid
  have impossible := Injected.stack_unregistered _ _ 3 (ownerCell runtimeSafety true) invalid.injected rfl rfl
  simp only [Memory.write, ↓reduceIte, Option.some_ne_none] at impossible

/-- The cache query is connected to this same initializer, for every semantic
key. The theorem assumes neither a loaded count nor a final correspondence. -/
theorem cache_queries_correspond (runtimeSafety : Bool) (meaning : Meaning) (key : Cache.Key) :
    zigEmptyCacheGet runtimeSafety (initialized runtimeSafety).memory.memory ⟨3, 0⟩ key =
      .ok ((initialized runtimeSafety).graph.table key) := by
  obtain ⟨finalWorld, executed, _, _, _, _, _, _, _, _, _, _, _, queries, _⟩ := source_initializer runtimeSafety meaning
  have same : finalWorld = initialized runtimeSafety :=
    (Prod.mk.inj (Except.ok.inj (executed.symm.trans (actual_source_initializer runtimeSafety)))).2
  exact same ▸ queries key

theorem header_count_uninitialized (runtimeSafety : Bool) :
    Compiler.Extraction.ExpressionMap.readSize runtimeSafety (headerReady runtimeSafety).memory ⟨3, 0⟩ = .error .uninitialized := by
  have pointer := Compiler.Extraction.ExpressionMap.root_size_pointer runtimeSafety (headerReady runtimeSafety).memory 3
    { ownerCell runtimeSafety true with cells := completedCells } false (header_valid runtimeSafety) rfl rfl
  simp only [Compiler.Extraction.ExpressionMap.readSize, pointer, bind, Except.bind]
  cases runtimeSafety <;> rfl

theorem header_without_count_rejects (runtimeSafety : Bool) (key : Cache.Key) :
    zigEmptyCacheGet runtimeSafety (headerReady runtimeSafety).memory ⟨3, 0⟩ key = .error .uninitialized := by
  simp only [zigEmptyCacheGet, Compiler.Extraction.ExpressionMap.getEmpty, Compiler.Extraction.ExpressionMap.getEmptyFrom, header_count_uninitialized, bind, Except.bind]

def nonemptyMemory (runtimeSafety : Bool) : Compiler.ZigAir.Memory.State :=
  let nextCell := { ownerCell runtimeSafety true with cells := completedCells.set (if runtimeSafety then 64 else 48) (.scalar (.int false 32 1)) }
  { (after runtimeSafety).memory with heap := (after runtimeSafety).memory.heap.replace 3 nextCell }

theorem nonempty_count_readback (runtimeSafety : Bool) :
    Compiler.Extraction.ExpressionMap.readSize runtimeSafety (nonemptyMemory runtimeSafety) ⟨3, 0⟩ =
      .ok (.scalar (.int false 32 1)) := by
  have valid : (nonemptyMemory runtimeSafety).valid = true := by cases runtimeSafety <;> decide +kernel
  have pointer := Compiler.Extraction.ExpressionMap.root_size_pointer runtimeSafety (nonemptyMemory runtimeSafety) 3
    { ownerCell runtimeSafety true with cells := completedCells.set (if runtimeSafety then 64 else 48) (.scalar (.int false 32 1)) } false valid rfl rfl
  simp only [Compiler.Extraction.ExpressionMap.readSize, pointer, bind, Except.bind]
  cases runtimeSafety <;> rfl

theorem nonempty_count_is_unsupported (runtimeSafety : Bool) (key : Cache.Key) :
    zigEmptyCacheGet runtimeSafety (nonemptyMemory runtimeSafety) ⟨3, 0⟩ key = .error .unsupported := by
  simp only [zigEmptyCacheGet, Compiler.Extraction.ExpressionMap.getEmpty, Compiler.Extraction.ExpressionMap.getEmptyFrom, nonempty_count_readback, bind, Except.bind]
  rfl

theorem map_selection_needs_complete_owner (runtimeSafety : Bool) (key : Cache.Key) :
    zigEmptyCacheGet runtimeSafety (after runtimeSafety).memory ⟨3, 8⟩ key = .error .memoryValidity ∧
      zigEmptyCacheGet runtimeSafety (after runtimeSafety).memory ⟨4, 0⟩ key = .error .unallocated ∧
      zigEmptyCacheGet (!runtimeSafety) (after runtimeSafety).memory ⟨3, 0⟩ key =
        .error (if runtimeSafety then .unsupported else .memoryValidity) := by
  simp only [zigEmptyCacheGet, Compiler.Extraction.ExpressionMap.getEmpty, Compiler.Extraction.ExpressionMap.getEmptyFrom]
  cases runtimeSafety <;> decide +kernel

theorem empty_lookup_leaves_opaque_fields_uninitialized (runtimeSafety : Bool) :
    ((countOnly runtimeSafety).memory.heap.lookup 3).map (fun cell => cell.cells.lookup 40) = some none ∧
      ((countOnly runtimeSafety).memory.heap.lookup 3).map (fun cell => cell.cells.lookup 52) = some none := by
  cases runtimeSafety <;> constructor <;> rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.GraphInit.OwnerMemory.Tests
