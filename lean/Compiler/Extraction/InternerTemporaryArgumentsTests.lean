/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.TemporaryArgumentsProgram
import Compiler.Extraction.InternerConstructorFrameTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryArguments.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open Normalization.Tests

def source : View := ⟨3, 0, 2⟩
def prepared := (prepare 99 1 Semantic.Tests.caller).2

theorem ordered_arguments :
    (prepare 99 1 Semantic.Tests.caller).1 = .ok source ∧
    Compiler.ZigAir.Memory.load prepared.memory.memory (source.pointer 0) = .ok (number 99) ∧
    Compiler.ZigAir.Memory.load prepared.memory.memory (source.pointer 1) = .ok (number 1) ∧
    prepared.memory.memory.nextId = 4 ∧ prepared.memory.effects = 5 :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩

theorem good_is_derived : Good source [99, 1] prepared := by
  obtain ⟨after, ran, good, _⟩ := prepare_verified 99 1 Semantic.Tests.caller _ before.memory
    original_valid actual_caller_allocation
  have same : prepared = after := congrArg Prod.snd ran
  exact same.symm ▸ good

theorem previous_storage_preserved :
    prepared.graph = Semantic.Tests.caller.graph ∧ prepared.memory.heap = original.heap ∧
    prepared.memory.memory.heap.lookup 0 = original.memory.heap.lookup 0 ∧
    prepared.memory.memory.heap.lookup 2 = original.memory.heap.lookup 2 :=
  ⟨rfl, rfl, by rfl', by rfl'⟩

/-- An invalid extent is a boundary negative, not a native initializer path.
The rejected second store retains the first initialized word. -/
def short : World Nat := { Semantic.Tests.caller with memory := { original with memory :=
  { before.memory with heap := (3, { scratchCell with type := .array 1 word }) :: original.memory.heap } } }
def rejectedWrites := writePair source 99 1 short

theorem rejected_store_retains_prefix :
    rejectedWrites.1 = .error (.memory (.preparation (.memory .memoryValidity))) ∧
    Compiler.ZigAir.Memory.load rejectedWrites.2.memory.memory (source.pointer 0) = .ok (number 99) ∧
    rejectedWrites.2.memory.memory.nextId = 4 ∧ rejectedWrites.2.graph = short.graph ∧
    rejectedWrites.2.memory.effects = short.memory.effects := ⟨by rfl', by rfl', by rfl', rfl, rfl⟩

def negativeTen : Word := BitVec.ofInt 256 (-10)
def caller : World Nat := { Semantic.Tests.caller with graph := { Semantic.Tests.wordGraph with
  read := fun id => if id = 42 then some negativeTen else Semantic.Tests.wordGraph.read id } }
def grown (before : World Nat) : World Nat := { before with
  graph := { before.graph with read := fun id => if id = 99 then some 0 else before.graph.read id },
  memory := { before.memory with effects := before.memory.effects + 13 } }
def child (result : Except Fault NodeId) : Word → GraphAction Nat NodeId :=
  fun _ before => (result, grown before)
def run (result : Except Fault NodeId := .ok 99) (budget : Nat := 160) (external : External Nat := success) :=
  zigNegation .neg_left (child result) external budget 7 (Semantic.Tests.callbacks Semantic.Tests.meaning 42)
    Caller.Tests.queries 1 3 caller

theorem first_error_skips_temporary_and_outer_call :
    run (.error (.language .outOfMemory)) = (.error (.language .outOfMemory), grown caller) := by rfl'

theorem first_rejection_keeps_reached_state :
    run (.error .missingHandle) = (.error .missingHandle, grown caller) := by rfl'

theorem success_unwinds_temporary :
    (run).1 = .ok 42 ∧ (run).2.graph.read 99 = some 0 ∧ (run).2.graph.read 42 = some negativeTen ∧
    (run).2.memory.memory.heap = original.memory.heap ∧ (run).2.memory.memory.nextId = 7 ∧
    (run).2.memory.effects = 238 := ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩

def parentStack := (prepare 3 1 caller).2
def nested := zigNegation .neg_left (child (.ok 99)) success 160 7
  (Semantic.Tests.callbacks Semantic.Tests.meaning 42) Caller.Tests.queries 1 3 parentStack

/-- A regression with an initialized older stack borrow. Universal parent-frame
preservation across production graph mutations remains an RC-05 obligation. -/
theorem nested_parent_borrow_survives :
    nested.1 = .ok 42 ∧
    Compiler.ZigAir.Memory.load nested.2.memory.memory (source.pointer 0) = .ok (number 3) ∧
    Compiler.ZigAir.Memory.load nested.2.memory.memory (source.pointer 1) = .ok (number 1) ∧
    nested.2.memory.memory.heap.lookup 3 = parentStack.memory.memory.heap.lookup 3 ∧
    nested.2.memory.memory.nextId = 8 := ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩

def full := zigNegation .neg_left (child (.ok 99)) success 160 7
  (Semantic.Tests.callbacks Semantic.Tests.meaning 42) { Caller.Tests.queries with atCapacity := fun _ => true }
  1 3 caller

theorem outer_capacity_unwinds_after_child :
    full.1 = .error (.language .capacity) ∧ full.2.graph.read 99 = some 0 ∧
    full.2.memory.memory.heap = original.memory.heap ∧ full.2.memory.memory.nextId = 4 ∧
    full.2.memory.effects = 18 := ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩

theorem outer_oom_retains_child_growth :
    (run (.ok 99) 160 (external (fun _ => true))).1 = .error (.language .outOfMemory) ∧
    (run (.ok 99) 160 (external (fun _ => true))).2.graph.read 99 = some 0 ∧
    (run (.ok 99) 160 (external (fun _ => true))).2.memory.memory.heap = original.memory.heap ∧
    (run (.ok 99) 160 (external (fun _ => true))).2.memory.effects > 18 :=
  ⟨by rfl', by rfl', by rfl', by decide +kernel⟩

def rejectingCallbacks : Primitives Nat := { Semantic.Tests.callbacks Semantic.Tests.meaning 42 with
  simplify := fun _ _ before => (.error (.memory (.preparation .incomplete)), before) }
def suspended := zigNegation .neg_left (child (.ok 99)) success 160 7 rejectingCallbacks
  Caller.Tests.queries 1 3 caller

theorem rejected_outer_observation_retains_initialized_temporary :
    suspended.1 = .error (.memory (.preparation .incomplete)) ∧
    ordinary suspended.1 = false ∧
    Compiler.ZigAir.Memory.load suspended.2.memory.memory (source.pointer 0) = .ok (number 99) ∧
    Compiler.ZigAir.Memory.load suspended.2.memory.memory (source.pointer 1) = .ok (number 1) ∧
    (suspended.2.memory.memory.heap.lookup 4).isSome = true :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩

def exhausted : World Nat := { caller with memory := { caller.memory with
  memory := { caller.memory.memory with nextAddress := Compiler.ZigAir.Memory.addressLimit - 4 } } }
def noStack := zigNegation .neg_right (child (.ok 99)) success 160 7
  (Semantic.Tests.callbacks Semantic.Tests.meaning 42) Caller.Tests.queries 1 3 exhausted

theorem stack_limit_keeps_child_and_rejects :
    noStack.1 = .error (.memory (.preparation (.memory .outOfMemory))) ∧ ordinary noStack.1 = false ∧
    noStack.2 = grown exhausted := ⟨by rfl', by rfl', by rfl'⟩

theorem outside_family_is_rejected :
    zigNegation .not_right (child (.ok 99)) success 160 7 (Semantic.Tests.callbacks Semantic.Tests.meaning 42)
      Caller.Tests.queries 1 3 caller = (.error .outsideOwnedContinuation, caller) := rfl

theorem prepared_constructor_contract :
    ∃ after, prepare 99 1 (grown caller) = (.ok source, after) ∧
      let ran := ConstructorFrame.operation success 160 7 (Semantic.Tests.callbacks Semantic.Tests.meaning 42)
        Caller.Tests.queries source (Interner.buildOpcode .SUB) [99, 1] after
      ordinary ran.1 = true →
        Valid (unwind 3 ran).2.memory ∧ Closed ran.2.scope ∧
        Semantic.Ensures Semantic.Tests.meaning (grown caller).graph ran.1 (unwind 3 ran).2.graph
          (fun id graph => graph.read id = some negativeTen) := by
  apply prepared_operation_verified success 160 7 (Semantic.Tests.callbacks Semantic.Tests.meaning 42)
    Caller.Tests.queries 99 1 (grown caller) _ before.memory Compiler.Extraction.Recursive.Tests.base negativeTen
    ⟨original_valid.memory, original_valid.related, original_valid.injected⟩ actual_caller_allocation (external_admitted _)
    (Semantic.Tests.ownership _ _) (Semantic.Tests.semantics _ _)
  · exact ⟨(by intro _ _ impossible; cases impossible), trivial⟩
  · -- This caller already contains the child's newly returned constant ID.
    -- Preparation does not establish graph denotation or recursive preservation.
    change _ = some negativeTen
    rfl'

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryArguments.Tests
