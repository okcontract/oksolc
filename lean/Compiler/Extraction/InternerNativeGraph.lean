/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerGraphInitOwnership
import Compiler.Extraction.InternerViewInput
import Compiler.Extraction.AssemblyItemGraphFrame
import Compiler.Extraction.RepresentativeBackingRelease
import Compiler.Extraction.RepresentativeConstant

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Persistent native graph facts over the existing world, independent of any
constructor's temporary input. Empty storage may use an unallocated, offset
sentinel; positive capacity requires the actual owned backing and descriptors.
Operation and constant-query agreement are derived below. Payloads, native nonempty
map buckets and allocator-vtable correspondence remain additional obligations. -/
structure Facts (safety : Bool) (allocator owner : Nat) (data : Compiler.ZigAir.Memory.Address)
    (capacity : Nat) (world : World (Publication.Effects σ)) (rows : List Storage.Cell) : Prop where
  valid : Valid world.memory
  projected : world.graph.representatives = some rows
  linked : world.graph.table = OwnedKeys.view world.memory.effects.keys
  ownerLive : ∃ native, world.memory.memory.heap.lookup owner = some native ∧
    native.type = Owner.viewType safety ∧ native.writable = true
  header : readHeader world.memory.memory (Owner.headerAddress ⟨owner, 0⟩) =
    .ok (.slice itemsType data rows.length, .scalar (.int false 64 capacity))
  bounded : rows.length ≤ capacity
  storage : capacity ≠ 0 → Backing.Release.Owned allocator data capacity world.memory ∧
    Memory.Vector allocator world.memory.heap data.allocation rows ∧
    DescriptorRelation.Prefix world.memory.memory data.allocation rows
  resident : Memory.GraphResident allocator world.memory.heap rows
  items : ∀ logical ∈ rows, ∃ native, world.memory.memory.heap.lookup logical.itemAddress = some native ∧
    native.type = AssemblyItem.viewType ∧ Operation.Item world.memory.memory logical
  live : OwnedKeys.Live allocator ⟨world.memory.effects.keys, world.memory.heap⟩
  unique : OwnedKeys.Unique world.memory.effects.keys
  apart : OwnedKeys.Apart world.memory.effects.keys
    (fun address => ∃ logical ∈ rows, logical.arguments ≠ [] ∧ address = logical.argumentsAddress)
  data : ∀ logical ∈ rows, Constant.Data world.memory.memory logical

/-- Every native operation query follows from the header, backing and actual
item fields. The empty case rejects the ID before touching its sentinel. -/
theorem Facts.operations {safety : Bool} {allocator owner capacity : Nat} {data : Compiler.ZigAir.Memory.Address}
    {world : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity world rows) (id : NodeId) (opcode : Opcode) :
    Operation.run world.memory.memory (Owner.headerAddress ⟨owner, 0⟩) id opcode =
      .ok ((Storage.operationProgram.run rows id opcode).map (Option.map Operation.returned)) := by
  by_cases empty : capacity = 0
  · have noRows : rows = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero (empty ▸ facts.bounded))
    have loaded := readHeader_items _ _ _ _ facts.header
    rw [noRows] at loaded ⊢
    rw [Operation.invalid_id _ _ data 0 id opcode loaded (Nat.zero_le _), Storage.operation_correct]
    rfl
  · obtain ⟨⟨offset, _, backing, found, typed, writable, _⟩, _, descriptors⟩ := facts.storage empty
    have loaded := readHeader_items _ _ _ _ facts.header
    have base : data = ⟨data.allocation, 0⟩ := by cases data; simp_all
    rw [base] at loaded
    exact Operation.query _ _ _ _ backing rows id opcode facts.valid.memory loaded found typed writable
      facts.bounded descriptors (fun row member => (facts.items row member).choose_spec.2.2)

theorem Facts.accepted {safety : Bool} {allocator owner capacity : Nat} {data : Compiler.ZigAir.Memory.Address}
    {world : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity world rows) :
    BorrowedQuery.Native.AcceptedQueries allocator (Owner.headerAddress ⟨owner, 0⟩) rows world.memory :=
  BorrowedQuery.Native.of_resident allocator _ rows world.memory facts.valid facts.resident facts.operations

/-- The non-Push guard reads only the represented kind. Its logical and native
misses follow together; no data-field or successful-query premise is needed. -/
theorem Facts.nonpush {safety : Bool} {allocator owner capacity : Nat} {data : Compiler.ZigAir.Memory.Address}
    {world : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity world rows) (id : NodeId) (inside : id.toNat < rows.length)
    (kind : rows[id.toNat].item.kind ≠ 2#32) :
    (Interner.representativeReads world.graph).constant id = .ok none ∧
    Constant.value world.memory.memory (Owner.headerAddress ⟨owner, 0⟩) id = .ok (.ok none) := by
  have nonempty : capacity ≠ 0 := by have bounded := facts.bounded; omega
  obtain ⟨⟨offset, _, backing, found, typed, writable, _⟩, _, descriptors⟩ := facts.storage nonempty
  have loaded := readHeader_items _ _ _ _ facts.header
  have base : data = ⟨data.allocation, 0⟩ := by cases data; simp_all
  rw [base] at loaded
  have notPush : (rows[id.toNat].item.kind.toNat : Int) ≠ 2 := by
    intro tag; apply kind; apply BitVec.eq_of_toNat_eq
    change rows[id.toNat].item.kind.toNat = 2
    omega
  have native := Constant.nonpush world.memory.memory _ data.allocation capacity backing rows id facts.valid.memory
    loaded found typed writable facts.bounded descriptors inside (facts.items _ (List.getElem_mem inside)).choose_spec.2.2 notPush
  have logical : Storage.representativeProgram.run rows id = .ok rows[id.toNat] := by
    rw [Storage.representative_correct, List.getElem?_eq_getElem inside]
  have missing : rows[id.toNat].isPush = false := beq_eq_false_iff_ne.mpr kind
  refine ⟨?_, native.2⟩
  simp only [Interner.representativeReads, facts.projected, Nested.storageReads, Storage.constantProgram,
    Storage.ConstantRead.run, logical, missing]
  rfl

/-- Every constant guard is determined by the same native graph, including
Push data, non-Push misses and invalid IDs. No query result is assumed. -/
theorem Facts.constants {safety : Bool} {allocator owner capacity : Nat} {data : Compiler.ZigAir.Memory.Address}
    {world : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity world rows) (id : NodeId) :
    Constant.value world.memory.memory (Owner.headerAddress ⟨owner, 0⟩) id =
      .ok (Storage.constantProgram.run rows id) := by
  by_cases inside : id.toNat < rows.length
  · by_cases push : rows[id.toNat].item.kind = 2#32
    · have positive : capacity ≠ 0 := by have bounded := facts.bounded; omega
      obtain ⟨⟨offset, _, backing, found, typed, writable, _⟩, _, descriptors⟩ := facts.storage positive
      have loaded := readHeader_items _ _ _ _ facts.header
      have base : data = ⟨data.allocation, 0⟩ := by cases data; simp_all
      rw [base] at loaded
      obtain ⟨item, itemFound, itemTyped, itemReads⟩ := facts.items _ (List.getElem_mem inside)
      have native := Constant.push world.memory.memory _ data.allocation capacity backing rows id
        facts.valid.memory loaded found typed writable facts.bounded descriptors inside item itemFound itemTyped
        (by simpa only [push] using itemReads.1) (facts.data _ (List.getElem_mem inside) push)
      rw [native.2, Storage.constant_correct, List.getElem?_eq_getElem inside]
      simp only [Option.bind_some, Storage.Cell.isPush, Storage.Cell.dataValue, push, BitVec.reduceBEq, ↓reduceIte]
    · have missed := (facts.nonpush id inside push).1
      simp only [Interner.representativeReads, facts.projected, Nested.storageReads] at missed
      rw [missed]
      exact (facts.nonpush id inside push).2
  · have missed := Constant.value_of_miss world.memory.memory _ id
      (Constant.invalid_id _ _ data rows.length id (readHeader_items _ _ _ _ facts.header) (by omega))
    rw [missed, Storage.constant_correct, List.getElem?_eq_none (by omega)]
    rfl

/-- The same invariant discharges the native agreement, residency and key
separation premises of the complete borrowed constructor's input connection. -/
theorem Facts.queried_input {safety : Bool} {allocator owner capacity : Nat} {data : Compiler.ZigAir.Memory.Address}
    {world : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity world rows) (id : NodeId) (opcode : Opcode)
    (value : Compiler.ZigAir.Memory.Value)
    (native : Operation.run world.memory.memory (Owner.headerAddress ⟨owner, 0⟩) id opcode = .ok (.ok (some value))) :
    ∃ slice, value = Operation.returned slice ∧
      BorrowedQuery.observe allocator id opcode world = .ok (some slice) ∧ Good (view slice) slice.items world ∧
      ∀ key old, world.memory.effects.keys key = some old → key.arguments ≠ [] →
        (view slice).length ≠ 0 → (view slice).allocation ≠ old.address :=
  ConstructorItem.ViewInput.queried_input allocator _ id opcode world rows value facts.projected facts.valid
    facts.resident facts.apart (facts.operations id opcode) native

/-- Native initialization supplies the empty instance, including retained owner
storage. No graph snapshot or initial native-query agreement is supplied. -/
theorem initialized (safety : Bool) (allocator owner : Nat) (before : Session σ)
    (cell : Compiler.ZigAir.Memory.Allocation) (sentinel : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (valid : Valid before) (found : before.memory.heap.lookup owner = some cell)
    (typed : cell.type = Owner.viewType safety) (writable : cell.writable = true) (stack : cell.stack = true) :
    ∃ after, GraphInit.Ownership.run safety allocator before ⟨owner, 0⟩ sentinel = .ok (allocator, after) ∧
      Facts safety allocator owner sentinel 0 after [] ∧
      GraphInit.Ownership.Established safety allocator before after owner sentinel meaning := by
  obtain ⟨after, ran, established⟩ :=
    GraphInit.Ownership.initialize_verified safety allocator before owner cell sentinel meaning valid found typed writable stack
  obtain ⟨ownerCell, ownerFound, shape⟩ := established.shape owner cell found
  refine ⟨after, ran, ⟨established.valid, established.representatives, established.projection.symm,
    ⟨ownerCell, ownerFound, shape.2.1.trans typed, shape.2.2.1.trans writable⟩,
    established.header, Nat.le_refl 0, ?_, established.resident, ?_, established.live, established.unique, ?_, ?_⟩, established⟩
  · intro impossible; exact False.elim (impossible rfl)
  · intro row member; cases member
  · intro key old present nonempty owned
    obtain ⟨row, member, _⟩ := owned
    cases member
  · intro row member; cases member

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
