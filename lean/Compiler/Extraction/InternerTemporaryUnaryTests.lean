/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerTemporaryUnaryProofs
import Compiler.Extraction.InternerConstructorFrameTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryUnary.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open Normalization.Tests

def source : View := ⟨3, 0, 1⟩
def unaryMemory : Compiler.ZigAir.Memory.State :=
  ⟨(3, { scratchCell with type := .array 1 word }) :: original.memory.heap, 4, 56⟩
def prepared := (prepare 99 Semantic.Tests.caller).2

theorem actual_allocation : Compiler.ZigAir.Memory.allocate original.memory (.array 1 word) =
    .ok (.pointer (.pointer true false (.array 1 word)) ⟨3, 0⟩, unaryMemory) := by rfl'

theorem initialized_word : (prepare 99 Semantic.Tests.caller).1 = .ok source ∧
    Compiler.ZigAir.Memory.load prepared.memory.memory (source.pointer 0) = .ok (number 99) ∧
    prepared.memory.memory.nextId = 4 ∧ prepared.memory.effects = 5 := ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem good_is_derived : Good source [99] prepared := by
  obtain ⟨after, ran, good, _⟩ := prepare_verified 99 Semantic.Tests.caller _ unaryMemory original_valid actual_allocation
  have same : prepared = after := congrArg Prod.snd ran
  exact same.symm ▸ good

theorem previous_storage_preserved : prepared.graph = Semantic.Tests.caller.graph ∧
    prepared.memory.heap = original.heap ∧ prepared.memory.memory.heap.lookup 0 = original.memory.heap.lookup 0 ∧
    prepared.memory.memory.heap.lookup 2 = original.memory.heap.lookup 2 := ⟨rfl, rfl, by rfl', by rfl'⟩

theorem no_default_second_word :
    Compiler.ZigAir.Memory.load prepared.memory.memory ((⟨3, 0, 2⟩ : View).pointer 1) = .error .memoryValidity := by rfl'

def uninitialized : World Nat := { Semantic.Tests.caller with memory := { original with memory := unaryMemory } }
def outOfBounds := writeOne ⟨3, 1, 1⟩ 99 uninitialized

theorem rejected_store_retains_uninitialized_state : outOfBounds =
    (.error (.memory (.preparation (.memory .memoryValidity))), uninitialized) := by rfl'

theorem rejected_store_does_not_initialize :
    Compiler.ZigAir.Memory.load outOfBounds.2.memory.memory (source.pointer 0) = .error .uninitialized := by rfl'

/-- These callbacks observe sequencing and reached effects; they are not native
graph correspondence. A separate nonvacuous contract fixture appears below. -/
def grown (before : World Nat) : World Nat := { before with
  graph := { before.graph with read := fun id => if id = 99 then some 0 else if id = 98 then some 1 else before.graph.read id },
  memory := { before.memory with effects := before.memory.effects + 13 } }
def callbacks (firstFault secondFault : Option Fault := none) : Primitives Nat :=
  { Semantic.Tests.callbacks Semantic.Tests.meaning 99 with
    simplify := fun _ slice before =>
      let (result, after) := nested success 7 slice before
      match result with
      | .error fault => (.error fault, after)
      | .ok () => if slice.items == [1] then
          (match firstFault with | none => .ok (some 99) | some fault => .error fault, grown after)
        else (match secondFault with | none => .ok (some 98) | some fault => .error fault, after) }
def run (replacement : Replacement := .bool_left) (firstFault secondFault : Option Fault := none)
    (budget : Nat := 160) (external : External Nat := success) (before : World Nat := Semantic.Tests.caller) :=
  zigUnary replacement external budget 7 (callbacks firstFault secondFault) Caller.Tests.queries 1 3 before
def first (fault : Option Fault := none) := invoke success 160 7 (callbacks fault none) Caller.Tests.queries
  (Interner.buildOpcode .ISZERO) 1 Semantic.Tests.caller

theorem first_ordinary_error_skips_second : run .bool_left (some (.language .outOfMemory)) =
    first (some (.language .outOfMemory)) := by
  apply first_error_result _ _ _ _ _ _ _ _ _ _ (Or.inl rfl)
  rfl'

theorem first_rejection_skips_second : run .bool_left (some (.memory (.preparation .incomplete))) =
    first (some (.memory (.preparation .incomplete))) := by
  apply first_error_result _ _ _ _ _ _ _ _ _ _ (Or.inl rfl)
  rfl'

theorem first_error_retains_growth : (run .bool_left (some (.language .outOfMemory))).1 =
    .error (.language .outOfMemory) ∧ (run .bool_left (some (.language .outOfMemory))).2.graph.read 99 = some 0 ∧
    (run .bool_left (some (.language .outOfMemory))).2.memory.memory.heap = original.memory.heap :=
  ⟨by rfl', by rfl', by rfl'⟩

theorem first_rejection_retains_frame :
    (run .bool_left (some (.memory (.preparation .incomplete)))).1 = .error (.memory (.preparation .incomplete)) ∧
    ordinary (run .bool_left (some (.memory (.preparation .incomplete)))).1 = false ∧
    Compiler.ZigAir.Memory.load (run .bool_left (some (.memory (.preparation .incomplete)))).2.memory.memory
      (source.pointer 0) = .ok (number 1) ∧
    (run .bool_left (some (.memory (.preparation .incomplete)))).2.graph.read 99 = some 0 :=
  ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem second_uses_returned_id_and_world : run =
    invoke success 160 7 (callbacks none none) Caller.Tests.queries (Interner.buildOpcode .ISZERO) 99 first.2 := by
  apply after_first _ _ _ _ _ _ _ _ _ _ _ (Or.inl rfl)
  rfl'

theorem both_calls_unwind : run.1 = .ok 98 ∧ run.2.graph.read 99 = some 0 ∧ run.2.graph.read 98 = some 1 ∧
    run.2.memory.memory.heap = original.memory.heap ∧ run.2.memory.effects > 18 :=
  ⟨by rfl', by rfl', by rfl', by rfl', by decide +kernel⟩

theorem lifetime_identity_advances : 4 < first.2.memory.memory.nextId ∧
    first.2.memory.memory.nextId < run.2.memory.memory.nextId ∧
    run.2.memory.memory.heap.lookup 3 = none := ⟨by decide +kernel, by decide +kernel, by rfl'⟩

theorem second_error_retains_first_growth : (run .bool_left none (some (.language .outOfMemory))).1 =
    .error (.language .outOfMemory) ∧ (run .bool_left none (some (.language .outOfMemory))).2.graph.read 99 = some 0 ∧
    (run .bool_left none (some (.language .outOfMemory))).2.memory.memory.heap = original.memory.heap :=
  ⟨by rfl', by rfl', by rfl'⟩

theorem second_rejection_retains_second_input :
    let rejected := run .bool_left none (some (.memory (.preparation .incomplete)))
    rejected.1 = .error (.memory (.preparation .incomplete)) ∧ ordinary rejected.1 = false ∧
      Compiler.ZigAir.Memory.load rejected.2.memory.memory ((⟨first.2.memory.memory.nextId, 0, 1⟩ : View).pointer 0) =
        .ok (number 99) ∧ rejected.2.memory.memory.heap.lookup 3 = none :=
  ⟨by rfl', by rfl', by rfl', by rfl'⟩

def parentStack := (TemporaryArguments.prepare 3 1 Semantic.Tests.caller).2
def nestedCall := run .bool_left none none 160 success parentStack
theorem older_parent_borrow_survives : nestedCall.1 = .ok 98 ∧
    Compiler.ZigAir.Memory.load nestedCall.2.memory.memory ((⟨3, 0, 2⟩ : View).pointer 0) = .ok (number 3) ∧
    Compiler.ZigAir.Memory.load nestedCall.2.memory.memory ((⟨3, 0, 2⟩ : View).pointer 1) = .ok (number 1) ∧
    nestedCall.2.memory.memory.heap.lookup 3 = parentStack.memory.memory.heap.lookup 3 :=
  ⟨by rfl', by rfl', by rfl', by rfl'⟩

def exhausted : World Nat := { Semantic.Tests.caller with memory := { original with memory :=
  { original.memory with nextAddress := Compiler.ZigAir.Memory.addressLimit } } }
theorem stack_limit_is_rejection : run .bool_left none none 160 success exhausted =
    (.error (.memory (.preparation (.memory .outOfMemory))), exhausted) ∧
    ordinary (run .bool_left none none 160 success exhausted).1 = false := ⟨by rfl', by rfl'⟩

theorem constructor_oom_unwinds : (run .bool_left none none 160 (external (fun _ => true))).1 =
    .error (.language .outOfMemory) ∧ (run .bool_left none none 160 (external (fun _ => true))).2.memory.memory.heap =
      original.memory.heap ∧ (run .bool_left none none 160 (external (fun _ => true))).2.graph = Semantic.Tests.caller.graph :=
  ⟨by rfl', by rfl', by rfl'⟩

def secondOOMExternal : External Nat := { success with allocate := fun site state bytes effects =>
  if 200 ≤ effects then (none, effects + bytes) else success.allocate site state bytes effects }
def secondOOM := run .bool_left none none 160 secondOOMExternal
theorem second_allocator_oom_keeps_first_growth : secondOOM.1 = .error (.language .outOfMemory) ∧
    secondOOM.2.graph.read 99 = some 0 ∧ secondOOM.2.memory.memory.heap = original.memory.heap ∧
    secondOOM.2.memory.effects > first.2.memory.effects := ⟨by rfl', by rfl', by rfl', by decide +kernel⟩

def secondFull := zigUnary .bool_left success 160 7 (callbacks none none)
  { Caller.Tests.queries with atCapacity := fun graph => graph.read 99 == some 0 } 1 3 Semantic.Tests.caller
theorem second_capacity_keeps_first_growth : secondFull.1 = .error (.language .capacity) ∧
    secondFull.2.graph.read 99 = some 0 ∧ secondFull.2.memory.memory.heap = original.memory.heap :=
  ⟨by rfl', by rfl', by rfl'⟩

theorem outside_family_is_rejected : run .neg_left = (.error .outsideOwnedContinuation, Semantic.Tests.caller) := rfl

def semanticCaller : World Nat := { Semantic.Tests.caller with graph := { Semantic.Tests.wordGraph with
  read := fun id => if id = 99 then some 0 else Semantic.Tests.wordGraph.read id } }
def semanticRun := invoke success 160 7 (Semantic.Tests.callbacks Semantic.Tests.meaning 99) Caller.Tests.queries
  (Interner.buildOpcode .ISZERO) 1 semanticCaller
theorem nonvacuous_constructor_contract : semanticRun.1 = .ok 99 ∧
    Valid semanticRun.2.memory ∧ Semantic.Ensures Semantic.Tests.meaning semanticCaller.graph semanticRun.1
      semanticRun.2.graph (fun id graph => graph.read id = some 0) := by
  have checked := invoke_verified success 160 7 (Semantic.Tests.callbacks Semantic.Tests.meaning 99)
    Caller.Tests.queries (Interner.buildOpcode .ISZERO) 1 semanticCaller _ unaryMemory
    Compiler.Extraction.Recursive.Tests.base 0 original_valid actual_allocation (external_admitted _)
    (Semantic.Tests.ownership _ _) (Semantic.Tests.semantics _ _)
    ⟨(by intro _ _ impossible; cases impossible), trivial⟩ (by rfl')
  exact ⟨by rfl', checked (by rfl')⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryUnary.Tests
