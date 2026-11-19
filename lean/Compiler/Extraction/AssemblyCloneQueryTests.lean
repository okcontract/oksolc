/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyCloneQuery
import Compiler.Extraction.AssemblyItemCreationFieldTests

namespace Compiler.Extraction.AssemblyClone.NativeFields.QueryTests
open Compiler.ZigAir.Memory Compiler.Algebraic
open Compiler.Extraction.Memory.Arguments.Normalization
open RepresentativeArray
open AssemblyItem.Creation.NativeFields.Tests (input source sourceCell expectedCells copy returned_pair)

def incoming := AssemblyItem.Creation.Insertion.Tests.incoming
def old : Storage.Cell := ⟨input.item, 0, 5, incoming.items, 23, incoming.address⟩
def logical : Storage.Cell := { old with itemAddress := 8, sequence := 31 }
def ownerCell (runtimeSafety first : Bool) : Allocation :=
  ⟨768, Owner.viewType runtimeSafety,
    [(16, .pointer Publication.pointerType (if first then ⟨999, 19⟩ else ⟨7, 0⟩)),
     (24, .scalar (.int false 64 (if first then 0 else 1))),
     (32, .scalar (.int false 64 (if first then 0 else 2)))] ++
      (if runtimeSafety then [(40, .scalar (.int false 64 0))] else []), true, true⟩
def backing : Allocation := ⟨1024, .array 2 Expression.allocationType,
  [(0, .pointer (.pointer true false AssemblyItem.allocationType) ⟨5, 0⟩),
   (8, .pointer (.pointer true true WordArray.word) ⟨incoming.address, 0⟩),
   (16, .scalar (.int false 64 incoming.items.length)),
   (24, .scalar (.int false 32 0)), (28, .scalar (.int false 32 23))], true, false⟩
def initial (runtimeSafety first : Bool) : Session Nat :=
  { AssemblyItem.Creation.NativeFields.Tests.initial with
    heap := Memory.write (Memory.write AssemblyItem.Creation.NativeFields.Tests.initial.heap 5
      (some ⟨7, .item input.item⟩)) 7 (some ⟨7, .representatives [old]⟩)
    memory :=
    ⟨(7, backing) :: (6, ownerCell runtimeSafety first) :: AssemblyItem.Creation.NativeFields.Tests.initial.memory.heap, 8, 1088⟩ }

theorem initial_frame (runtimeSafety first : Bool) (id : Nat) (older : id < 6) :
    (initial runtimeSafety first).memory.heap.lookup id = AssemblyItem.Creation.NativeFields.Tests.initial.memory.heap.lookup id := by
  simp only [initial, Heap.lookup_cons, show 7 ≠ id by omega, show 6 ≠ id by omega, ↓reduceIte]

theorem initial_valid (runtimeSafety first : Bool) : Valid (initial runtimeSafety first) := by
  have prior := AssemblyItem.Creation.NativeFields.Tests.initial_valid
  refine ⟨by cases runtimeSafety <;> cases first <;> decide +kernel, ?_, ?_⟩
  · intro allocator id contents nonempty stored
    have apart : id ≠ 7 ∧ id ≠ 5 := by
      constructor <;> intro same <;> simp [initial, Memory.write, same] at stored
    have stored : AssemblyItem.Creation.NativeFields.Tests.initial.heap id = some ⟨allocator, .arguments contents⟩ := by
      simpa only [initial, Memory.write, if_neg apart.1, if_neg apart.2] using stored
    obtain ⟨⟨cell, found, typed, writable, stack⟩, represented⟩ := prior.related allocator id contents nonempty stored
    have older := (valid_lookup _ id cell prior.memory found).1
    have same := initial_frame runtimeSafety first id older
    exact ⟨⟨cell, same.trans found, typed, writable, stack⟩, represented_frame _ _ represented same⟩
  · intro id block stored
    by_cases seven : id = 7
    · subst id; exact ⟨backing, rfl, rfl⟩
    by_cases five : id = 5
    · subst id; exact ⟨sourceCell, by cases runtimeSafety <;> cases first <;> decide +kernel, rfl⟩
    have stored : AssemblyItem.Creation.NativeFields.Tests.initial.heap id = some block := by
      simpa only [initial, Memory.write, if_neg seven, if_neg five] using stored
    obtain ⟨cell, found, persistent⟩ := prior.injected id block stored
    have older := (valid_lookup _ id cell prior.memory found).1
    exact ⟨cell, (initial_frame runtimeSafety first id older).trans found, persistent⟩

def made (runtimeSafety first : Bool) := AssemblyItem.Creation.create AssemblyItem.Creation.Insertion.Tests.allocate 7 input.item (initial runtimeSafety first)
def cloned (runtimeSafety first : Bool) := Physical.run (copy) 7 input (made runtimeSafety first).2
def copied : ItemValue := { input with verbatim := some ⟨2, 3, ⟨9, [8, 9], 0⟩⟩ }
def ready (runtimeSafety first : Bool) : Session Nat :=
  { (cloned runtimeSafety first).2 with memory := { (cloned runtimeSafety first).2.memory with
    heap := (cloned runtimeSafety first).2.memory.heap.replace 8 { AssemblyItem.Creation.cell 80 with cells := expectedCells 9 0 } } }

theorem created_result (runtimeSafety first : Bool) : made runtimeSafety first = (.ok 8, (made runtimeSafety first).2) :=
  returned_pair _ _ (by cases runtimeSafety <;> cases first <;> decide +kernel)

theorem cloned_result (runtimeSafety first : Bool) : cloned runtimeSafety first = (.ok copied, (cloned runtimeSafety first).2) := by
  let duplicated := Physical.duplicate (copy) 7 ⟨3, [8, 9], 1⟩ (made runtimeSafety first).2
  have copiedBytes : duplicated = (.ok ⟨9, [8, 9], 0⟩, duplicated.2) :=
    returned_pair _ _ (by cases runtimeSafety <;> cases first <;> decide +kernel)
  have ran := Physical.run_duplicate (copy) 7 input ⟨2, 3, ⟨3, [8, 9], 1⟩⟩ ⟨9, [8, 9], 0⟩
    (made runtimeSafety first).2 duplicated.2 rfl copiedBytes
  exact returned_pair _ _ (congrArg Prod.fst ran)

theorem installed (runtimeSafety first : Bool) : Installed 7 8 copied (cloned runtimeSafety first).2 (ready runtimeSafety first) := by
  have post := AssemblyItem.Creation.create_verified AssemblyItem.Creation.Insertion.Tests.allocate 7 8 input.item
    (initial runtimeSafety first) (made runtimeSafety first).2 (initial_valid runtimeSafety first) (created_result runtimeSafety first)
  have represented : Represents (initial runtimeSafety first).memory source input :=
    AssemblyItem.Creation.NativeFields.Tests.source_represented.frame (initial_frame runtimeSafety first 5 (by decide))
  have live := AssemblyItem.Creation.NativeFields.represented_after_create _ _ 7 8 source input
    (initial_valid runtimeSafety first) represented post
  obtain ⟨after, assigned, result⟩ := clone_install (copy) 7 8 source input copied
    (made runtimeSafety first).2 (cloned runtimeSafety first).2 post.valid live post.owned (cloned_result runtimeSafety first)
  have written : AssemblyItem.Fields.assign (values copied) 8 (cloned runtimeSafety first).2.memory =
      .ok (ready runtimeSafety first).memory := by
    cases runtimeSafety <;> cases first <;> decide +kernel
  have stored : install copied 8 (cloned runtimeSafety first).2 = .ok (ready runtimeSafety first) :=
    install_assigned copied 8 (cloned runtimeSafety first).2 (ready runtimeSafety first).memory written
  cases Except.ok.inj (assigned.symm.trans stored)
  exact result

theorem installed_query (runtimeSafety first : Bool) : Operation.Item (ready runtimeSafety first).memory logical :=
  (installed runtimeSafety first).query logical rfl rfl (by decide)

theorem old_rows (runtimeSafety : Bool) : DescriptorRelation.Prefix (ready runtimeSafety false).memory 7 [old] := by
  intro index cell found
  cases index with
  | zero => cases Option.some.inj found; unfold DescriptorRelation.Row; cases runtimeSafety <;> decide +kernel
  | succ index => simp at found

theorem old_items (runtimeSafety : Bool) : ∀ cell ∈ [old], ∃ allocation, (ready runtimeSafety false).memory.heap.lookup cell.itemAddress = some allocation ∧
    allocation.type = AssemblyItem.viewType ∧ Operation.Item (ready runtimeSafety false).memory cell := by
  intro cell member
  cases List.mem_singleton.mp member
  refine ⟨sourceCell, ?_, rfl, ?_, fun _ => ?_⟩ <;> cases runtimeSafety <;> decide +kernel

theorem first_fits (runtimeSafety : Bool) : RegionAllocation.Fits (ready runtimeSafety true).memory ⟨160, 8⟩ 2048 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro entry present layout shaped
  have valid := (installed runtimeSafety true).valid.memory
  simp only [Compiler.ZigAir.Memory.State.valid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at valid
  have checked := valid.1.2 entry present
  simp only [shaped, Bool.and_eq_true, decide_eq_true_eq] at checked
  have bound : (ready runtimeSafety true).memory.nextAddress ≤ 2048 := by cases runtimeSafety <;> decide +kernel
  right; omega

def request (response : Option Nat := some 2048) : RegionAllocation.Allocator Nat := fun _ _ effects => (response, effects + 1)
def append (runtimeSafety first : Bool) (argumentsLength : Nat := incoming.items.length) (id : Int := if first then 0 else 1)
    (sequence : Int := 31) (response : Option Nat := some 2048) :=
  Append.Execution.ownerRun runtimeSafety (ready runtimeSafety first).memory ⟨6, 0⟩ ⟨8, 0⟩ ⟨incoming.address, 0⟩
    argumentsLength id sequence (request response) (ready runtimeSafety first).effects

theorem first_queries (runtimeSafety : Bool) (id : NodeId) (opcode : BitVec 8) :
    Operation.run (append runtimeSafety true).1.2 (Owner.headerAddress ⟨6, 0⟩) id opcode =
      .ok ((Storage.operationProgram.run [logical] id opcode).map (Option.map Operation.returned)) := by
  obtain ⟨after, executed, _, _, queries⟩ := (installed runtimeSafety true).first_query runtimeSafety 6 (ownerCell runtimeSafety true)
    ⟨999, 19⟩ logical 2048 (request) ((ready runtimeSafety true).effects + 1)
    rfl rfl (by decide) (by cases runtimeSafety <;> decide +kernel) rfl rfl
    (by cases runtimeSafety <;> decide +kernel) (by cases runtimeSafety <;> decide +kernel) (by decide) rfl
    (first_fits runtimeSafety)
    (Owner.NativeLock.checkHeader_of_cell runtimeSafety _ 6 (ownerCell runtimeSafety true)
      (installed runtimeSafety true).valid.memory (by cases runtimeSafety <;> decide +kernel) rfl
      (by intro active; subst runtimeSafety; rfl))
  have same : (append runtimeSafety true).1.2 = after := congrArg (fun result => result.1.2) executed
  rw [same]
  exact queries id opcode

theorem spare_queries (runtimeSafety : Bool) (id : NodeId) (opcode : BitVec 8) :
    Operation.run (append runtimeSafety false).1.2 (Owner.headerAddress ⟨6, 0⟩) id opcode =
      .ok ((Storage.operationProgram.run [old, logical] id opcode).map (Option.map Operation.returned)) := by
  obtain ⟨after, executed, _, _, queries⟩ := (installed runtimeSafety false).spare_query runtimeSafety 6 7 2 (ownerCell runtimeSafety false)
    backing [old] logical (request) rfl rfl (by decide)
    (by cases runtimeSafety <;> decide +kernel) rfl rfl (by cases runtimeSafety <;> decide +kernel) rfl rfl
    (by cases runtimeSafety <;> decide +kernel) (by cases runtimeSafety <;> decide +kernel) (old_rows runtimeSafety) (old_items runtimeSafety) (by decide) (by decide) (by decide)
  have same : (append runtimeSafety false).1.2 = after := congrArg (fun result => result.1.2) executed
  rw [same]
  exact queries id opcode

theorem all_append_outcomes (runtimeSafety first : Bool) (argumentsLength : Nat) (id sequence : Int) (response : Option Nat) :
    (append runtimeSafety first argumentsLength id sequence response).1.2.heap.lookup 8 =
      some { AssemblyItem.Creation.cell 80 with cells := expectedCells 9 0 } ∧
    Operation.Item (append runtimeSafety first argumentsLength id sequence response).1.2 logical :=
  AssemblyItem.Query.append_frame runtimeSafety (ready runtimeSafety first).memory 6 (ownerCell runtimeSafety first)
    ⟨8, 0⟩ ⟨incoming.address, 0⟩ argumentsLength id sequence (request response) (ready runtimeSafety first).effects
    logical _ (installed runtimeSafety first).valid.memory (by cases runtimeSafety <;> cases first <;> decide +kernel)
    rfl (by cases runtimeSafety <;> cases first <;> decide +kernel) rfl (installed_query runtimeSafety first)

theorem publication_outcomes (runtimeSafety first : Bool) (data : Address) (capacity : Nat) :
    let after := (Publication.Registered.run (Owner.headerAddress ⟨6, 0⟩) data capacity (ready runtimeSafety first)).2
    after.memory.heap.lookup 8 = some { AssemblyItem.Creation.cell 80 with cells := expectedCells 9 0 } ∧
      Operation.Item after.memory logical :=
  AssemblyItem.Query.publication_frame runtimeSafety 6 (ownerCell runtimeSafety first) data capacity (ready runtimeSafety first) logical _
    (installed runtimeSafety first).valid (by cases runtimeSafety <;> cases first <;> decide +kernel) rfl
    (by cases runtimeSafety <;> cases first <;> decide +kernel) rfl (installed_query runtimeSafety first)

theorem first_oom_keeps_item (runtimeSafety : Bool) :
    (append runtimeSafety true incoming.items.length 0 31 none).1 = (.ok none, (ready runtimeSafety true).memory) ∧
    (append runtimeSafety true incoming.items.length 0 31 none).2 = (ready runtimeSafety true).effects + 1 := by
  cases runtimeSafety <;> decide +kernel

theorem partial_descriptor_keeps_item (runtimeSafety : Bool) :
    (append runtimeSafety false addressLimit).1.1 = .error .malformed ∧
    readField (append runtimeSafety false addressLimit).1.2 (Owner.headerAddress ⟨6, 0⟩) (itemsOffset + 8) =
      .ok (.scalar (.int false 64 2)) ∧
    (append runtimeSafety false addressLimit).1.2.heap.lookup 8 =
      some { AssemblyItem.Creation.cell 80 with cells := expectedCells 9 0 } := by
  cases runtimeSafety <;> decide +kernel

theorem concrete_queries (runtimeSafety : Bool) :
    Operation.run (append runtimeSafety true).1.2 (Owner.headerAddress ⟨6, 0⟩) 0 254 =
      .ok (.ok (some (Operation.borrowed ⟨incoming.address, 0⟩ incoming.items.length))) ∧
    Operation.run (append runtimeSafety true).1.2 (Owner.headerAddress ⟨6, 0⟩) 0 253 = .ok (.ok none) ∧
    Operation.run (append runtimeSafety true).1.2 (Owner.headerAddress ⟨6, 0⟩) 1 254 = .ok (.ok none) := by
  rw [first_queries, first_queries, first_queries]
  decide +kernel

/-- Root type inequality alone would admit a descriptor nested in another
aggregate. The common frame requires absence at every declared offset. -/
theorem nested_descriptor_requires_exclusion :
    let wrapper := Ty.aggregate "nested" ⟨40, 8⟩ [(8, .object Expression.allocationType)]
    wrapper ≠ Expression.allocationType ∧ acceptsView wrapper 8 Expression.allocationType = true := by decide

end Compiler.Extraction.AssemblyClone.NativeFields.QueryTests
