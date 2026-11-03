/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRuleMaxExponentProofs
import Compiler.Extraction.InternerTemporaryUnaryTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryArguments.MaxExponent.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open Compiler.Extraction.Dispatch (opAND opISZERO opSUB)
open Normalization.Tests

def source : View := ⟨0, 0, 2⟩
def caller : World Nat := { Semantic.Tests.caller with graph := { Semantic.Tests.wordGraph with
  read := fun id => if id = 99 ∨ id = 98 ∨ id = 97 ∨ id = 96 then none else Semantic.Tests.wordGraph.read id } }
def grown (before : World Nat) : World Nat := { before with
  graph := { before.graph with read := fun id => if id = 99 then some 1 else before.graph.read id },
  memory := { before.memory with effects := before.memory.effects + 13 } }
def published (known : NodeId) (value : Word) (before : World Nat) : World Nat :=
  { grown before with graph := { before.graph with read := fun id => if id = known then some value else (grown before).graph.read id } }
def constant (fault : Option Fault := none) : Word → GraphAction Nat NodeId := fun value before =>
  if value == 1 then
    (match fault with | none => .ok 99 | some error => .error error, grown before)
  else (.error .outsideOwnedContinuation, before)

/-- Controlled callbacks observe physical IDs as well as the returned words.
They do not establish native graph/container correspondence. -/
def callbacks (failed : Option Opcode := none) : Primitives Nat := { Semantic.Tests.callbacks Semantic.Tests.meaning 99 with
  simplify := fun key slice before =>
    let expected := if key.instruction == opAND then [1, 99] else if key.instruction == opISZERO then [98] else [97, 98]
    let known := if key.instruction == opAND then 98 else if key.instruction == opISZERO then 97 else 96
    let value := if key.instruction == opAND then 0 else 1
    if key.arguments != expected then (.error .missingHandle, before)
    else if failed == some key.instruction then (.error (.language .outOfMemory), published known value before)
    else (Semantic.Tests.callbacks Semantic.Tests.meaning known).simplify key slice (published known value before) }

def run (failed : Option Opcode := none) (constantFault : Option Fault := none)
    (external : External Nat := Normalization.Tests.success) (input : View := source) (before : World Nat := caller) :=
  zigChain (constant constantFault) external 160 7 (callbacks failed) Caller.Tests.queries input before

theorem full_chain_result : (run).1 = .ok (some 96) := by rfl'
theorem full_chain_unwinds : (run).2.memory.memory.heap = original.memory.heap ∧
    (run).2.memory.memory.nextId > 7 := ⟨by rfl', by decide +kernel⟩
theorem original_borrow_survives : (run).2.memory.memory.heap.lookup 0 = original.memory.heap.lookup 0 := by rfl'
theorem reached_graph_growth : caller.graph.read 99 = none ∧ caller.graph.read 98 = none ∧
    (run).2.graph.read 99 = some 1 ∧ (run).2.graph.read 98 = some 0 ∧
    (run).2.graph.read 97 = some 1 ∧ (run).2.graph.read 96 = some 1 :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩
theorem constant_oom_skips_all_arrays : run none (some (.language .outOfMemory)) =
    (.error (.language .outOfMemory), grown caller) := by rfl'
theorem constant_rejection_keeps_world : run none (some .missingHandle) = (.error .missingHandle, grown caller) := by rfl'
theorem bounds_reject_after_constant : run none none Normalization.Tests.success ⟨0, 0, 1⟩ =
    (.error (.memory (.preparation (.memory .sourceBounds))), grown caller) := by rfl'
theorem missing_borrow_rejects_after_constant : run none none Normalization.Tests.success ⟨99, 0, 2⟩ =
    (.error (.memory (.preparation (.memory .unallocated))), grown caller) := by rfl'
theorem wrong_offset_is_observed : (run none none Normalization.Tests.success ⟨0, 1, 2⟩).1 = .error .missingHandle := by rfl'
theorem parity_oom_skips_later_arrays : (run (some opAND)).1 = .error (.language .outOfMemory) ∧
    (run (some opAND)).2.memory.memory.heap = original.memory.heap := ⟨by rfl', by rfl'⟩
theorem even_oom_keeps_parity_effects : (run (some opISZERO)).1 = .error (.language .outOfMemory) ∧
    (run (some opAND)).2.memory.effects < (run (some opISZERO)).2.memory.effects := ⟨by rfl', by decide +kernel⟩
theorem final_oom_keeps_even_effects : (run (some opSUB)).1 = .error (.language .outOfMemory) ∧
    (run (some opISZERO)).2.memory.effects < (run (some opSUB)).2.memory.effects ∧
    (run (some opSUB)).2.memory.memory.heap = original.memory.heap := ⟨by rfl', by decide +kernel, by rfl'⟩
theorem first_allocator_oom_keeps_constant : (run none none (external (fun _ => true))).1 = .error (.language .outOfMemory) ∧
    (run none none (external (fun _ => true))).2.memory.effects > (grown caller).memory.effects ∧
    (run none none (external (fun _ => true))).2.graph.read 99 = some 1 := ⟨by rfl', by decide +kernel, by rfl'⟩
def limited := zigChain (fun _ before => (.ok 0, grown before)) Normalization.Tests.success 0 7
  (callbacks) Caller.Tests.queries source caller
theorem observation_rejection_keeps_storage : limited.1 = .error (.memory (.preparation .incomplete)) ∧
    (limited.2.memory.memory.heap.lookup 3).isSome = true :=
  ⟨by rfl', by rfl'⟩

def parent := (prepare 3 1 caller).2
theorem older_parent_array_survives : (run none none Normalization.Tests.success source parent).1 = .ok (some 96) ∧
    Compiler.ZigAir.Memory.load (run none none Normalization.Tests.success source parent).2.memory.memory
      ((⟨3, 0, 2⟩ : View).pointer 0) = .ok (number 3) ∧
    Compiler.ZigAir.Memory.load (run none none Normalization.Tests.success source parent).2.memory.memory
      ((⟨3, 0, 2⟩ : View).pointer 1) = .ok (number 1) := ⟨by rfl', by rfl', by rfl'⟩

/-- The borrowed read uses the post-child memory, including an explicitly
changed input fixture. Such mutation is not a production borrow-frame contract. -/
def mutableCaller : World Nat := { caller with memory := { caller.memory with memory := { caller.memory.memory with
  heap := caller.memory.memory.heap.map (fun (id, cell) => (id, if id = 0 then { cell with writable := true } else cell)) } } }
def changingConstant : Word → GraphAction Nat NodeId := fun _ before =>
  match Compiler.ZigAir.Memory.store before.memory.memory (source.pointer 1) (number 2) with
  | .error fault => (.error (.memory (.preparation (.memory fault))), before)
  | .ok memory => (.ok 99, { grown before with memory := { (grown before).memory with memory } })
def changed := (changingConstant 1 mutableCaller).2
theorem changed_returned : changingConstant 1 mutableCaller = (.ok 99, changed) := by rfl'
theorem post_constant_load_is_observed : zigChain changingConstant Normalization.Tests.success 160 7
    (callbacks) Caller.Tests.queries source mutableCaller =
    (do let odd ← parity Normalization.Tests.success 160 7 (callbacks) Caller.Tests.queries source 99
        let even ← TemporaryUnary.invoke Normalization.Tests.success 160 7 (callbacks) Caller.Tests.queries opISZERO odd
        return some (← invoke Normalization.Tests.success 160 7 (callbacks) Caller.Tests.queries opSUB even odd)) changed :=
  after_constant _ _ _ _ _ _ _ _ _ _ changed_returned
theorem changed_operand_is_not_snapshot : (zigChain changingConstant Normalization.Tests.success 160 7
    (callbacks) Caller.Tests.queries source mutableCaller).1 = .error .missingHandle := by rfl'

def pairCaller : World Nat := { caller with graph := { caller.graph with
  read := fun id => if id = 99 then some 1 else if id = 98 then some 0 else caller.graph.read id } }
def pairRun := invoke Normalization.Tests.success 160 7 (Semantic.Tests.callbacks Semantic.Tests.meaning 98)
  Caller.Tests.queries opAND 1 99 pairCaller
theorem nonvacuous_pair_contract : pairRun.1 = .ok 98 ∧ Valid pairRun.2.memory ∧
    Semantic.Ensures Semantic.Tests.meaning pairCaller.graph pairRun.1 pairRun.2.graph (fun id graph => graph.read id = some 0) := by
  have checked := invoke_verified Normalization.Tests.success 160 7 (Semantic.Tests.callbacks Semantic.Tests.meaning 98)
    Caller.Tests.queries opAND 1 99 pairCaller _ before.memory Compiler.Extraction.Recursive.Tests.base 0
    original_valid actual_caller_allocation (external_admitted _) (Semantic.Tests.ownership _ _)
    (Semantic.Tests.semantics _ _) ⟨(by intro _ _ impossible; cases impossible), trivial⟩ (by rfl')
  exact ⟨by rfl', checked (by rfl')⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryArguments.MaxExponent.Tests
