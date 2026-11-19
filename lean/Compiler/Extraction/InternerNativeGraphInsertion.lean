/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeGraphFrame
import Compiler.Extraction.InternerInsertionNativeBody

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Native types separate old item data from owner/backing writes and from a
replaced key. Both spare append and relocation supply this same allocation
frame; no final constant-query result is assumed. -/
theorem data_frame (safety : Bool) (allocator owner backing capacity : Nat)
    (before : World (Publication.Effects σ)) (rows : List Storage.Cell) (key : Key)
    (after : Compiler.ZigAir.Memory.State) (valid : Valid before.memory)
    (ownerLive : ∃ native, before.memory.memory.heap.lookup owner = some native ∧
      native.type = Owner.viewType safety ∧ native.writable = true)
    (owned : Backing.Release.Owned allocator ⟨backing, 0⟩ capacity before.memory)
    (items : ∀ row ∈ rows, ∃ native, before.memory.memory.heap.lookup row.itemAddress = some native ∧
      native.type = AssemblyItem.viewType ∧ Operation.Item before.memory.memory row)
    (live : OwnedKeys.Live allocator ⟨before.memory.effects.keys, before.memory.heap⟩)
    (data : ∀ row ∈ rows, Constant.Data before.memory.memory row)
    (frame : ∀ id native, before.memory.memory.heap.lookup id = some native → id ≠ owner → id ≠ backing →
      (∀ old, before.memory.effects.keys key = some old → key.arguments ≠ [] → id ≠ old.address) →
      after.heap.lookup id = some native) :
    ∀ row ∈ rows, Constant.Data after row := by
  intro row member
  obtain ⟨native, found, typed, _⟩ := items row member
  obtain ⟨ownerCell, ownerFound, ownerTyped, _⟩ := ownerLive
  obtain ⟨_, _, array, arrayFound, arrayTyped, _⟩ := owned
  have ownerApart := before.memory.memory.heap.lookup_ne_of_type_ne _ _ native ownerCell found ownerFound
    (by simp [typed, ownerTyped, AssemblyItem.viewType, Owner.viewType])
  have backingApart := before.memory.memory.heap.lookup_ne_of_type_ne _ _ native array found arrayFound
    (by simp [typed, arrayTyped, AssemblyItem.viewType, Backing.type])
  have kept := frame row.itemAddress native found ownerApart backingApart (by
    intro old stored nonempty
    have owned := (live key old stored).resolve_left nonempty
    obtain ⟨⟨cell, keyFound, keyTyped, _⟩, _⟩ := valid.related allocator old.address key.arguments nonempty owned
    exact before.memory.memory.heap.lookup_ne_of_type_ne _ _ native cell found keyFound
      (by simp [typed, keyTyped, AssemblyItem.viewType]))
  exact (data row member).frame (kept.trans found.symm)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- The source branch determines whether success publishes the key or only
transfers the argument owner into the appended row. -/
def successOwnership (deterministic : Bool) : Storage.State :=
  if deterministic then Storage.publishedOwnership else Storage.transferredOwnership

/-- The key registry follows that same source branch. -/
def successKeys (deterministic : Bool) (keys : OwnedKeys.Table) (key : Key)
    (normalized : ArgumentSlice) (rows : List Storage.Cell) : OwnedKeys.Table :=
  if deterministic then OwnedKeys.store keys key ⟨normalized.address, Storage.idFor rows⟩ else keys

theorem insert_success_at (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety deterministic : Bool) (allocator container : Nat) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (meaning : Meaning) (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (before : World (Publication.Effects σ)) (rows : List Storage.Cell)
    (growth : Option (Growth.Registered.Callbacks σ)) (backing : Compiler.ZigAir.Memory.Address)
    (header : readItems before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType backing rows.length))
    (projected : before.graph.representatives = some rows) (after : Frame σ) (row : Storage.Cell)
    (ran : execution ops allocate safety allocator container source address meaning input key normalized deterministic rows before growth =
      ((.ok (some .success), (successOwnership deterministic)), after))
    (candidate : cell input key normalized ((key.eval meaning before.graph.read).getD 0) (successOwnership deterministic) after = row) :
    insert ops allocate safety allocator container source address meaning input key normalized deterministic growth before =
      (.ok (Storage.idFor rows), Insertion.projected rows before key row (successOwnership deterministic) after) := by
  have checked := checkedExecution_read ops allocate safety allocator container source address meaning input key normalized
    deterministic rows before growth backing header
  rw [ran] at checked
  cases deterministic <;> simp only [insert, projected, body, checked, Interner.insertionOutcome, Except.mapError] <;> rw [candidate]

/-- Original publication interface of the shared success adapter. -/
theorem insert_published (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (allocator container : Nat) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (meaning : Meaning) (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (before : World (Publication.Effects σ)) (rows : List Storage.Cell)
    (growth : Option (Growth.Registered.Callbacks σ)) (backing : Compiler.ZigAir.Memory.Address)
    (header : readItems before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType backing rows.length))
    (projected : before.graph.representatives = some rows) (after : Frame σ) (row : Storage.Cell)
    (ran : execution ops allocate safety allocator container source address meaning input key normalized true rows before growth =
      ((.ok (some .success), Storage.publishedOwnership), after))
    (candidate : cell input key normalized ((key.eval meaning before.graph.read).getD 0) Storage.publishedOwnership after = row) :
    insert ops allocate safety allocator container source address meaning input key normalized true growth before =
      (.ok (Storage.idFor rows), Insertion.projected rows before key row Storage.publishedOwnership after) := by
  exact insert_success_at ops allocate safety true allocator container source address meaning input key normalized
    before rows growth backing header projected after row ran candidate

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Lift derived physical publication postconditions through the actual native
insertion adapter. First, spare and relocated backing share this graph reconstruction;
old item data follows the original allocation frame, and the new row needs its
actual installed data read. These are local source postconditions, not an assumed
final native graph or constructor correspondence. -/
theorem Facts.insert_success_at {safety : Bool} {allocator owner oldCapacity : Nat}
    {oldData : Compiler.ZigAir.Memory.Address}
    {world : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner oldData oldCapacity world rows)
    (deterministic : Bool) (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (meaning : Meaning) (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (after : Insertion.Native.Frame σ) (row : Storage.Cell) (lifetime capacity : Nat)
    (executed : Insertion.Native.execution ops allocate safety allocator owner source address meaning input key normalized
      deterministic rows world growth = ((.ok (some .success), (Insertion.Native.successOwnership deterministic)), after))
    (candidate : Insertion.cell input key normalized ((key.eval meaning world.graph.read).getD 0)
      (Insertion.Native.successOwnership deterministic) after = row)
    (valid : Valid (Insertion.memory after))
    (ownerLive : ∃ native, (Insertion.memory after).memory.heap.lookup owner = some native ∧
      native.type = Owner.viewType safety ∧ native.writable = true)
    (header : readHeader (Insertion.memory after).memory (Owner.headerAddress ⟨owner, 0⟩) =
      .ok (.slice itemsType ⟨lifetime, 0⟩ (rows.length + 1), .scalar (.int false 64 capacity)))
    (bounded : rows.length + 1 ≤ capacity)
    (owned : Backing.Release.Owned allocator ⟨lifetime, 0⟩ capacity (Insertion.memory after))
    (vector : Memory.Vector allocator (Insertion.memory after).heap lifetime (rows ++ [row]))
    (descriptors : DescriptorRelation.Prefix (Insertion.memory after).memory lifetime (rows ++ [row]))
    (resident : Memory.GraphResident allocator (Insertion.memory after).heap (rows ++ [row]))
    (items : ∀ logical ∈ rows ++ [row], ∃ native,
      (Insertion.memory after).memory.heap.lookup logical.itemAddress = some native ∧
        native.type = AssemblyItem.viewType ∧ Operation.Item (Insertion.memory after).memory logical)
    (live : OwnedKeys.Live allocator ⟨(Insertion.memory after).effects.keys, (Insertion.memory after).heap⟩)
    (unique : OwnedKeys.Unique (Insertion.memory after).effects.keys)
    (apart : OwnedKeys.Apart (Insertion.memory after).effects.keys
      (fun address => ∃ logical ∈ rows ++ [row], logical.arguments ≠ [] ∧ address = logical.argumentsAddress))
    (keys : (Insertion.memory after).effects.keys =
      Insertion.Native.successKeys deterministic world.memory.effects.keys key normalized rows)
    (data : Constant.Data (Insertion.memory after).memory row)
    (frame : ∀ id native, world.memory.memory.heap.lookup id = some native → id ≠ owner → id ≠ oldData.allocation →
      (∀ old, world.memory.effects.keys key = some old → key.arguments ≠ [] → id ≠ old.address) →
      (Insertion.memory after).memory.heap.lookup id = some native) :
    let actual := Insertion.Native.insert ops allocate safety allocator owner source address meaning input key normalized deterministic growth world
    actual = (.ok (Storage.idFor rows), Insertion.projected rows world key row (Insertion.Native.successOwnership deterministic) after) ∧
      Facts safety allocator owner ⟨lifetime, 0⟩ capacity actual.2 (rows ++ [row]) := by
  have inserted := Insertion.Native.insert_success_at ops allocate safety deterministic allocator owner source address meaning input key normalized
    world rows growth oldData (readHeader_items _ _ _ _ facts.header) facts.projected after row executed candidate
  dsimp only
  refine ⟨inserted, ?_⟩
  rw [inserted]
  refine ⟨valid, (by cases deterministic <;> rfl), ?_, ownerLive,
    (by simpa only [List.length_append, List.length_singleton] using header),
    (by simpa only [List.length_append, List.length_singleton] using bounded),
    (fun _ => ⟨owned, vector, descriptors⟩), resident, items, live, unique, apart, ?_⟩
  · cases deterministic with
    | true =>
      change Cache.put equalityFields world.graph.table key (Storage.idFor rows) =
        OwnedKeys.view (Insertion.memory after).effects.keys
      rw [keys, Insertion.Native.successKeys, if_pos rfl, OwnedKeys.view_store, facts.linked]
    | false =>
      change world.graph.table = OwnedKeys.view (Insertion.memory after).effects.keys
      rw [keys]
      exact facts.linked
  · intro logical member
    rcases List.mem_append.mp member with old | new
    · by_cases positive : oldCapacity = 0
      · have empty : rows = [] := List.eq_nil_of_length_eq_zero (by have bound := facts.bounded; omega)
        simp only [empty, List.not_mem_nil] at old
      · have owned := (facts.storage positive).1
        have root : oldData = ⟨oldData.allocation, 0⟩ := by
          have offset := owned.1
          cases oldData
          simp_all only
        exact data_frame safety allocator owner oldData.allocation oldCapacity world rows key (Insertion.memory after).memory
          facts.valid facts.ownerLive (root ▸ owned) facts.items facts.live facts.data frame logical old
    · have same := List.mem_singleton.mp new
      subst logical
      exact data

/-- Publication specializes the same native graph reconstruction as transfer. -/
theorem Facts.insert_published {safety : Bool} {allocator owner oldCapacity : Nat}
    {oldData : Compiler.ZigAir.Memory.Address}
    {world : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner oldData oldCapacity world rows)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (meaning : Meaning) (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (after : Insertion.Native.Frame σ) (row : Storage.Cell) (lifetime capacity : Nat)
    (executed : Insertion.Native.execution ops allocate safety allocator owner source address meaning input key normalized
      true rows world growth = ((.ok (some .success), Storage.publishedOwnership), after))
    (candidate : Insertion.cell input key normalized ((key.eval meaning world.graph.read).getD 0)
      Storage.publishedOwnership after = row)
    (valid : Valid (Insertion.memory after))
    (ownerLive : ∃ native, (Insertion.memory after).memory.heap.lookup owner = some native ∧
      native.type = Owner.viewType safety ∧ native.writable = true)
    (header : readHeader (Insertion.memory after).memory (Owner.headerAddress ⟨owner, 0⟩) =
      .ok (.slice itemsType ⟨lifetime, 0⟩ (rows.length + 1), .scalar (.int false 64 capacity)))
    (bounded : rows.length + 1 ≤ capacity)
    (owned : Backing.Release.Owned allocator ⟨lifetime, 0⟩ capacity (Insertion.memory after))
    (vector : Memory.Vector allocator (Insertion.memory after).heap lifetime (rows ++ [row]))
    (descriptors : DescriptorRelation.Prefix (Insertion.memory after).memory lifetime (rows ++ [row]))
    (resident : Memory.GraphResident allocator (Insertion.memory after).heap (rows ++ [row]))
    (items : ∀ logical ∈ rows ++ [row], ∃ native,
      (Insertion.memory after).memory.heap.lookup logical.itemAddress = some native ∧
        native.type = AssemblyItem.viewType ∧ Operation.Item (Insertion.memory after).memory logical)
    (live : OwnedKeys.Live allocator ⟨(Insertion.memory after).effects.keys, (Insertion.memory after).heap⟩)
    (unique : OwnedKeys.Unique (Insertion.memory after).effects.keys)
    (apart : OwnedKeys.Apart (Insertion.memory after).effects.keys
      (fun address => ∃ logical ∈ rows ++ [row], logical.arguments ≠ [] ∧ address = logical.argumentsAddress))
    (keys : (Insertion.memory after).effects.keys =
      OwnedKeys.store world.memory.effects.keys key ⟨normalized.address, Storage.idFor rows⟩)
    (data : Constant.Data (Insertion.memory after).memory row)
    (frame : ∀ id native, world.memory.memory.heap.lookup id = some native → id ≠ owner → id ≠ oldData.allocation →
      (∀ old, world.memory.effects.keys key = some old → key.arguments ≠ [] → id ≠ old.address) →
      (Insertion.memory after).memory.heap.lookup id = some native) :
    let actual := Insertion.Native.insert ops allocate safety allocator owner source address meaning input key normalized true growth world
    actual = (.ok (Storage.idFor rows), Insertion.projected rows world key row Storage.publishedOwnership after) ∧
      Facts safety allocator owner ⟨lifetime, 0⟩ capacity actual.2 (rows ++ [row]) := by
  exact facts.insert_success_at true ops allocate growth source address meaning input key normalized after row lifetime capacity
    executed candidate valid ownerLive header bounded owned vector descriptors resident items live unique apart keys data frame

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
