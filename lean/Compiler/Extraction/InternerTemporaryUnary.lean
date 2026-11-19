/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerTemporaryArguments

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryUnary
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open TemporaryArguments (unwind unwind_verified)

/-- The single reached store of a unary source initializer. A rejected store
retains its allocated storage without manufacturing initialized contents. -/
def writeOne (source : View) (value : NodeId) : GraphAction σ View := fun before =>
  TemporaryArguments.orderedStores
    (Compiler.ZigAir.Memory.store before.memory.memory (source.pointer 0) (number value))
    (fun written => .ok written) source before

theorem writeOne_success (source target : View) (value : NodeId) (before after : World σ)
    (ran : writeOne source value before = (.ok target, after)) :
    target = source ∧ before.memory.memory.heap.RetainsShape after.memory.memory.heap :=
  TemporaryArguments.orderedStores_success _ _ source target before after
    (fun memory stored => Compiler.ZigAir.Memory.store_retains_shape _ _ _ memory stored)
    (fun written memory same => by cases Except.ok.inj same; exact Compiler.ZigAir.Memory.Heap.RetainsShape.refl _) ran

def prepare (value : NodeId) : GraphAction σ View := fun before =>
  let source : View := ⟨before.memory.memory.nextId, 0, 1⟩
  match Compiler.ZigAir.Memory.allocate before.memory.memory (.array 1 word) with
  | .error fault => (.error (.memory (.preparation (.memory fault))), before)
  | .ok (_, allocated) =>
    writeOne source value { before with memory := { before.memory with memory := allocated } }

theorem writeOne_of_store (source : View) (value : NodeId) (before : World σ)
    (memory : Compiler.ZigAir.Memory.State)
    (stored : Compiler.ZigAir.Memory.store before.memory.memory (source.pointer 0) (number value) = .ok memory) :
    writeOne source value before = (.ok source, { before with memory := { before.memory with memory } }) := by
  exact TemporaryArguments.orderedStores_of_success _ _ source before memory memory stored rfl

theorem prepare_of_store (value : NodeId) (before : World σ) (pointer : Compiler.ZigAir.Memory.Value)
    (allocated memory : Compiler.ZigAir.Memory.State)
    (allocation : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 1 word) = .ok (pointer, allocated))
    (stored : Compiler.ZigAir.Memory.store allocated
      ((⟨before.memory.memory.nextId, 0, 1⟩ : View).pointer 0) (number value) = .ok memory) :
    prepare value before = (.ok ⟨before.memory.memory.nextId, 0, 1⟩,
      { before with memory := { before.memory with memory } }) := by
  simp only [prepare, allocation]
  exact writeOne_of_store _ value _ memory stored

/-- Initialization and Good follow the actual allocation/store. All older
physical storage, graph state, registry and effects remain exactly framed. -/
theorem prepare_verified (value : NodeId) (before : World σ) (pointer : Compiler.ZigAir.Memory.Value)
    (allocated : Compiler.ZigAir.Memory.State) (initial : Valid before.memory)
    (allocation : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 1 word) = .ok (pointer, allocated)) :
    ∃ after, prepare value before = (.ok ⟨before.memory.memory.nextId, 0, 1⟩, after) ∧
      Good ⟨before.memory.memory.nextId, 0, 1⟩ [value] after ∧ after.graph = before.graph ∧
      after.memory.heap = before.memory.heap ∧ after.memory.effects = before.memory.effects ∧
      after.memory.memory.nextId = before.memory.memory.nextId + 1 ∧
      (∀ id cell, before.memory.memory.heap.lookup id = some cell → after.memory.memory.heap.lookup id = some cell) := by
  let source : View := ⟨before.memory.memory.nextId, 0, 1⟩
  have empty : Represents before.memory.memory ⟨0, 0, 0⟩ [] := ⟨rfl, by intro index inside; simp at inside⟩
  obtain ⟨allocatedValid, _, _, kept⟩ := caller_array_buffer 1 before.memory allocated pointer ⟨0, 0, 0⟩ [] initial empty allocation
  have cap := writable_fresh before.memory.memory allocated 1 pointer allocation
  obtain ⟨memory, stored⟩ := write_total allocated source 0 value allocatedValid.memory cap (by simp [source])
  have unregistered : before.memory.heap source.allocation = none := initial.injected.fresh initial.memory
  have finalValid := TemporaryMemory.stored_valid { before.memory with memory := allocated } memory source 0 value
    allocatedValid unregistered (by simp [source]) stored
  have contents : Represents memory source [value] := by
    refine ⟨rfl, ?_⟩
    intro index inside
    have zero : index = 0 := by simpa using inside
    subst index
    exact Compiler.ZigAir.Memory.load_after_store _ _ _ _ stored
  let after : World σ := { before with memory := { before.memory with memory } }
  refine ⟨after, prepare_of_store value before pointer allocated memory allocation stored,
    ⟨finalValid, contents⟩, rfl, rfl, rfl, ?_, ?_⟩
  · exact (Compiler.ZigAir.Memory.store_keeps_counters _ _ _ _ stored).1.trans
      (Compiler.ZigAir.Memory.allocate_pointer _ _ _ _ allocation).2
  · intro id cell found
    have older := (Compiler.ZigAir.Memory.valid_lookup _ _ _ initial.memory found).1
    have frame := (write_allocation_frame _ _ source 0 value stored).2.2 id (by dsimp [source]; omega)
    exact frame.trans (kept id cell found)

/-- The successful initializer retains the allocation high-water mark through its actual store. -/
theorem prepare_address (value : NodeId) (before after : World σ) (source : View)
    (pointer : Compiler.ZigAir.Memory.Value) (allocated : Compiler.ZigAir.Memory.State)
    (valid : Valid before.memory)
    (allocation : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 1 word) = .ok (pointer, allocated))
    (ran : prepare value before = (.ok source, after)) :
    after.memory.memory.nextAddress = allocated.nextAddress := by
  let sourceView : View := ⟨before.memory.memory.nextId, 0, 1⟩
  have empty : Represents before.memory.memory ⟨0, 0, 0⟩ [] := ⟨rfl, by intro index inside; simp at inside⟩
  obtain ⟨allocatedValid, _, _, _⟩ := caller_array_buffer 1 before.memory allocated pointer ⟨0, 0, 0⟩ [] valid empty allocation
  have cap := writable_fresh before.memory.memory allocated 1 pointer allocation
  obtain ⟨memory, stored⟩ := write_total allocated sourceView 0 value allocatedValid.memory cap (by simp [sourceView])
  have same := congrArg (fun result => result.2.memory.memory.nextAddress)
    ((prepare_of_store value before pointer allocated memory allocation stored).symm.trans ran)
  exact same.symm.trans (Compiler.ZigAir.Memory.store_keeps_counters _ _ _ _ stored).2

/-- Enter the existing constructor frame only after the unary initializer's
store. Ordinary outcomes unwind this caller array; rejected observations retain
the reached frame. Array cleanup never erases reached graph/callback effects. -/
def invoke (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries)
    (opcode : Opcode) (operand : NodeId) : GraphAction σ NodeId := fun before =>
  let mark := before.memory.memory.nextId
  match prepare operand before with
  | (.error fault, reached) => (.error fault, reached)
  | (.ok source, prepared) => unwind mark
    (ConstructorFrame.operation external budget allocator p q source opcode [operand] prepared)

theorem invoke_of_preparation (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Caller.Queries) (opcode : Opcode) (operand : NodeId) (before prepared : World σ) (source : View)
    (initialized : prepare operand before = (.ok source, prepared)) :
    invoke external budget allocator p q opcode operand before = unwind before.memory.memory.nextId
      (ConstructorFrame.operation external budget allocator p q source opcode [operand] prepared) := by
  simp only [invoke, initialized]

theorem invoke_preparation_error (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Caller.Queries) (opcode : Opcode) (operand : NodeId) (before reached : World σ) (fault : Fault)
    (failed : prepare operand before = (.error fault, reached)) :
    invoke external budget allocator p q opcode operand before = (.error fault, reached) := by
  simp only [invoke, failed]

theorem invoke_verified (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries)
    (opcode : Opcode) (operand : NodeId) (before : World σ) (pointer : Compiler.ZigAir.Memory.Value)
    (allocated : Compiler.ZigAir.Memory.State) (other : Meaning) (value : Word) (initial : Valid before.memory)
    (allocation : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 1 word) = .ok (pointer, allocated))
    (admitted : Admitted external) (ownership : ∀ source values, OwnedCall.Contracts allocator source values p)
    (contracts : ∀ source values, Semantic.Contracts allocator source values (Folding.wordMeaning other) p)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (evaluated : (Interner.constructorCode.operationRequest opcode [operand]).item.eval
      (Folding.wordMeaning other) before.graph.read [operand] Interner.constructorCode.sequence = some value) :
    ordinary (invoke external budget allocator p q opcode operand before).1 = true →
      Valid (invoke external budget allocator p q opcode operand before).2.memory ∧
      Semantic.Ensures (Folding.wordMeaning other) before.graph
        (invoke external budget allocator p q opcode operand before).1
        (invoke external budget allocator p q opcode operand before).2.graph
        (fun id graph => graph.read id = some value) := by
  obtain ⟨prepared, initialized, good, graph, _⟩ := prepare_verified operand before pointer allocated initial allocation
  have checked := ConstructorFrame.operation_verified external budget allocator p q
    ⟨before.memory.memory.nextId, 0, 1⟩ opcode [operand] prepared other value good admitted
    (ownership _ _) (contracts _ _) (graph.symm ▸ valid) (graph.symm ▸ evaluated)
  rw [invoke_of_preparation _ _ _ _ _ _ _ _ _ _ initialized]
  intro completed
  have post := unwind_verified before.memory.memory.nextId (Folding.wordMeaning other)
    ⟨before.memory.memory.nextId, 0, 1⟩ [operand] prepared _ value checked completed
  exact ⟨post.1, graph ▸ post.2.2⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryUnary
