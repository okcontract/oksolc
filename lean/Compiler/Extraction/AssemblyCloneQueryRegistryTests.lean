/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyCloneQueryRegistry
import Compiler.Extraction.AssemblyCloneQueryTests
import Compiler.Extraction.RepresentativeBorrowedQueryTests

namespace Compiler.Extraction.AssemblyClone.NativeFields.RegistryTests
open Compiler.ZigAir.Memory Compiler.Algebraic
open Compiler.Extraction.Memory.Arguments.Normalization
open RepresentativeArray QueryTests
open AssemblyItem.Creation.NativeFields.Tests (input copy)

theorem created_row (safety first : Bool) : Memory.Resident 7 (ready safety first).heap logical := by
  exact created_resident AssemblyItem.Creation.Insertion.Tests.allocate (copy) 7 8 input copied
    (initial safety first) (made safety first).2 (cloned safety first).2 (ready safety first) logical
    (initial_valid safety first) (Or.inr (by rfl')) rfl rfl (created_result safety first)
    (cloned_result safety first) (installed safety first)

theorem ready_registered (safety first : Bool) (id : Nat) (allocation : Memory.Allocation)
    (stored : (initial safety first).heap id = some allocation) :
    (ready safety first).heap id = some allocation := by
  have created := AssemblyItem.Creation.create_verified AssemblyItem.Creation.Insertion.Tests.allocate 7 8 input.item
    (initial safety first) (made safety first).2 (initial_valid safety first) (created_result safety first)
  have clone := Physical.run_valid (copy) 7 input copied (made safety first).2 (cloned safety first).2
    created.valid (cloned_result safety first)
  rw [(installed safety first).heap]
  exact clone.registered created.valid id _ (created.registered (initial_valid safety first) id _ stored)

def cells (first : Bool) := if first then [logical] else [old, logical]
def lifetime (first : Bool) := if first then 10 else 7
def reached (safety first : Bool) : Session Nat :=
  { ready safety first with
    memory := (append safety first).1.2
    effects := (append safety first).2
    heap := Memory.write (ready safety first).heap (lifetime first) (some ⟨7, .representatives (cells first)⟩) }
def world (safety first : Bool) : OwnedCall.World Nat :=
  ⟨Interner.observedHeap (cells first) (fun _ => none), reached safety first⟩

theorem reached_eq (safety first : Bool) (after : Session Nat)
    (executed : append safety first = ((.ok (some ()), after.memory), after.effects))
    (heap : after.heap = Memory.write (ready safety first).heap (lifetime first) (some ⟨7, .representatives (cells first)⟩)) :
    reached safety first = after := by
  have memory := congrArg (fun result => result.1.2) executed
  have effects := congrArg Prod.snd executed
  cases after
  simp only [reached, memory, effects, ← heap]

theorem registered_execution (safety first : Bool) :
    (append safety first).1.1 = .ok (some ()) ∧ Valid (reached safety first) ∧
    Memory.Vector 7 (reached safety first).heap (lifetime first) (cells first) ∧
    Memory.GraphResident 7 (reached safety first).heap (cells first) ∧
    OwnedCall.BorrowedQuery.Native.AcceptedQueries 7 (Owner.headerAddress ⟨6, 0⟩) (cells first) (reached safety first) := by
  cases first with
  | true =>
    obtain ⟨after, executed, heap, _, valid, vector, _, _, resident, queries⟩ :=
      (installed safety true).first_registered_query safety 6 (ownerCell safety true) ⟨999, 19⟩ logical 2048
        (fun _ => request) ((ready safety true).effects + 1) rfl rfl (by decide)
        (by cases safety <;> decide +kernel) rfl rfl (by cases safety <;> decide +kernel)
        (by cases safety <;> decide +kernel) (created_row safety true) (by decide) rfl (first_fits safety)
      (Owner.NativeLock.checkHeader_of_cell safety _ 6 (ownerCell safety true)
        (installed safety true).valid.memory (by cases safety <;> decide +kernel) rfl
        (by intro active; subst safety; rfl))
    have next : (ready safety true).memory.nextId = lifetime true := by cases safety <;> decide +kernel
    rw [next] at heap vector
    rw [reached_eq safety true after executed heap]
    exact ⟨congrArg (fun result => result.1.1) executed, valid, vector, resident, queries⟩
  | false =>
    have oldResident : Memory.GraphResident 7 (ready safety false).heap [old] := by
      intro cell member; cases List.mem_singleton.mp member
      exact ⟨ready_registered safety false 5 _ (by rfl'), Or.inr (ready_registered safety false 0 _ (by rfl'))⟩
    obtain ⟨after, executed, heap, _, valid, vector, _, _, resident, queries⟩ :=
      (installed safety false).spare_registered_query safety 6 7 2 (ownerCell safety false) backing [old] logical
        (request) rfl rfl (by decide) (by cases safety <;> decide +kernel) rfl rfl
        (by cases safety <;> decide +kernel) rfl rfl (by cases safety <;> decide +kernel)
        (by cases safety <;> decide +kernel) (ready_registered safety false 7 _ (by rfl'))
        (old_rows safety) (old_items safety) oldResident (created_row safety false) (by decide) (by decide) (by decide)
    rw [reached_eq safety false after executed heap]
    exact ⟨congrArg (fun result => result.1.1) executed, valid, vector, resident, queries⟩

theorem accepted_borrow (safety first : Bool) :
    OwnedCall.BorrowedQuery.observe 7 (if first then 0 else 1) 254 (world safety first) = .ok (some incoming) ∧
    OwnedCall.Good (Memory.Arguments.view incoming) incoming.items (world safety first) := by
  have result := (registered_execution safety first).2.2.2.2
  have hit : Operation.run (reached safety first).memory (Owner.headerAddress ⟨6, 0⟩) (if first then 0 else 1) 254 =
      .ok (.ok (some (Operation.returned incoming))) := by
    rw [result.1]; cases first <;> decide +kernel
  obtain ⟨slice, same, checked, good⟩ := (result.2 (world safety first).graph rfl).2 _ _ _ hit
  have observed := (result.2 (world safety first).graph rfl).1 (if first then 0 else 1) 254
  have expected : (Storage.operationProgram.run (cells first) (if first then 0 else 1) 254).mapError
      OwnedCall.BorrowedQuery.Rejection.query = .ok (some incoming) := by cases first <;> decide +kernel
  have equal : slice = incoming := Option.some.inj (Except.ok.inj (checked.symm.trans (observed.trans expected)))
  exact ⟨observed.trans expected, equal ▸ good⟩

theorem misses (safety first : Bool) :
    OwnedCall.BorrowedQuery.observe 7 99 254 (world safety first) = .ok none ∧
    OwnedCall.BorrowedQuery.observe 7 0 253 (world safety first) = .ok none := by
  have queries : ∀ id opcode, OwnedCall.BorrowedQuery.observe 7 id opcode (world safety first) =
      (Storage.operationProgram.run (cells first) id opcode).mapError OwnedCall.BorrowedQuery.Rejection.query :=
    ((registered_execution safety first).2.2.2.2.2 (world safety first).graph rfl).1
  rw [queries, queries]; cases first <;> decide +kernel

theorem exact_key (safety first : Bool) :
    (reached safety first).heap 8 = some ⟨7, .item input.item⟩ ∧
    (reached safety first).heap incoming.address = some ⟨7, .arguments incoming.items⟩ := by
  have resident := (registered_execution safety first).2.2.2.1 logical (by cases first <;> simp [cells])
  refine ⟨resident.1, ?_⟩
  rcases resident.2 with impossible | stored
  · cases impossible
  · exact stored

end Compiler.Extraction.AssemblyClone.NativeFields.RegistryTests
