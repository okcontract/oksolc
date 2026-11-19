/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerTemporaryMemory

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryArguments
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray

/-- Retain the reached prefix of two initializer phases. A unary initializer
uses an identity second phase, so both families share the same state handoff. -/
def orderedStores (first : Except Compiler.ZigAir.Memory.Fault Compiler.ZigAir.Memory.State)
    (second : Compiler.ZigAir.Memory.State → Except Compiler.ZigAir.Memory.Fault Compiler.ZigAir.Memory.State)
    (source : View) (before : World σ) : Except Fault View × World σ :=
  match first with
  | .error fault => (.error (.memory (.preparation (.memory fault))), before)
  | .ok written =>
    let middle := { before with memory := { before.memory with memory := written } }
    match second written with
    | .error fault => (.error (.memory (.preparation (.memory fault))), middle)
    | .ok memory => (.ok source, { before with memory := { before.memory with memory } })

def writePair (source : View) (first second : NodeId) : GraphAction σ View := fun before =>
  orderedStores (Compiler.ZigAir.Memory.store before.memory.memory (source.pointer 0) (number first))
    (fun written => Compiler.ZigAir.Memory.store written (source.pointer 1) (number second)) source before

/-- Successful ordered initialization retains native metadata and returns the
same view. Each phase must establish its own memory frame. -/
theorem orderedStores_success
    (first : Except Compiler.ZigAir.Memory.Fault Compiler.ZigAir.Memory.State)
    (second : Compiler.ZigAir.Memory.State → Except Compiler.ZigAir.Memory.Fault Compiler.ZigAir.Memory.State)
    (source target : View) (before after : World σ)
    (firstFrame : ∀ memory, first = .ok memory → before.memory.memory.heap.RetainsShape memory.heap)
    (secondFrame : ∀ written memory, second written = .ok memory → written.heap.RetainsShape memory.heap)
    (ran : orderedStores first second source before = (.ok target, after)) :
    target = source ∧ before.memory.memory.heap.RetainsShape after.memory.memory.heap := by
  cases firstCall : first with
  | error fault => simp only [orderedStores, firstCall, Prod.mk.injEq] at ran; cases ran.1
  | ok written =>
    cases secondCall : second written with
    | error fault => simp only [orderedStores, firstCall, secondCall, Prod.mk.injEq] at ran; cases ran.1
    | ok memory =>
      have same := Prod.mk.inj ran
      simp only [firstCall, secondCall] at same
      cases Except.ok.inj same.1
      cases same.2
      exact ⟨rfl, (firstFrame written firstCall).trans (secondFrame written memory secondCall)⟩

theorem writePair_success (source target : View) (first second : NodeId) (before after : World σ)
    (ran : writePair source first second before = (.ok target, after)) :
    target = source ∧ before.memory.memory.heap.RetainsShape after.memory.memory.heap :=
  orderedStores_success _ _ source target before after
    (fun memory stored => Compiler.ZigAir.Memory.store_retains_shape _ _ _ memory stored)
    (fun written memory stored => Compiler.ZigAir.Memory.store_retains_shape written _ _ memory stored) ran

/-- Two source-literal stores, after evaluating both operands. The negation
call site evaluates its first child before this phase. Storage is allocated here;
the argument view is not reconstructed at an arbitrary constructor boundary. -/
def prepare (first second : NodeId) : GraphAction σ View := fun before =>
  let source : View := ⟨before.memory.memory.nextId, 0, 2⟩
  match Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) with
  | .error fault => (.error (.memory (.preparation (.memory fault))), before)
  | .ok (_, allocated) =>
    writePair source first second { before with memory := { before.memory with memory := allocated } }

private theorem stored_valid (before : Session σ) (memory : Compiler.ZigAir.Memory.State)
    (target : View) (index : Nat) (value : NodeId) (valid : Valid before)
    (unregistered : before.heap target.allocation = none) (inside : index < target.length)
    (stored : Compiler.ZigAir.Memory.store before.memory (target.pointer index) (number value) = .ok memory) :
    Valid ({ before with memory } : Session σ) :=
  TemporaryMemory.stored_valid before memory target index value valid unregistered inside stored

theorem pair_contents (allocated written memory : Compiler.ZigAir.Memory.State) (source : View)
    (first second : NodeId) (length : source.length = 2)
    (firstStore : Compiler.ZigAir.Memory.store allocated (source.pointer 0) (number first) = .ok written)
    (secondStore : Compiler.ZigAir.Memory.store written (source.pointer 1) (number second) = .ok memory) :
    Represents memory source [first, second] := by
  refine ⟨by simp [length], ?_⟩
  intro index inside
  have bound : index < 2 := by simpa using inside
  have alternatives : index = 0 ∨ index = 1 := by omega
  rcases alternatives with zero | one
  · subst index
    exact (write_frame written memory source 1 0 second secondStore (by omega)).trans
      (Compiler.ZigAir.Memory.load_after_store allocated _ _ written firstStore)
  · subst index
    exact Compiler.ZigAir.Memory.load_after_store written _ _ memory secondStore

theorem orderedStores_of_success
    (first : Except Compiler.ZigAir.Memory.Fault Compiler.ZigAir.Memory.State)
    (second : Compiler.ZigAir.Memory.State → Except Compiler.ZigAir.Memory.Fault Compiler.ZigAir.Memory.State)
    (source : View) (before : World σ) (written memory : Compiler.ZigAir.Memory.State)
    (firstStore : first = .ok written) (secondStore : second written = .ok memory) :
    orderedStores first second source before =
      (.ok source, { before with memory := { before.memory with memory } }) := by
  simp only [orderedStores, firstStore, secondStore]

theorem writePair_of_stores (source : View) (first second : NodeId) (before : World σ)
    (written memory : Compiler.ZigAir.Memory.State)
    (firstStore : Compiler.ZigAir.Memory.store before.memory.memory (source.pointer 0) (number first) = .ok written)
    (secondStore : Compiler.ZigAir.Memory.store written (source.pointer 1) (number second) = .ok memory) :
    writePair source first second before =
      (.ok source, { before with memory := { before.memory with memory } }) :=
  orderedStores_of_success _ _ source before written memory firstStore secondStore

theorem prepare_of_stores (first second : NodeId) (before : World σ)
    (pointer : Compiler.ZigAir.Memory.Value) (allocated written memory : Compiler.ZigAir.Memory.State)
    (allocation : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, allocated))
    (firstStore : Compiler.ZigAir.Memory.store allocated
      ((⟨before.memory.memory.nextId, 0, 2⟩ : View).pointer 0) (number first) = .ok written)
    (secondStore : Compiler.ZigAir.Memory.store written
      ((⟨before.memory.memory.nextId, 0, 2⟩ : View).pointer 1) (number second) = .ok memory) :
    prepare first second before = (.ok ⟨before.memory.memory.nextId, 0, 2⟩,
      { before with memory := { before.memory with memory } }) := by
  simp only [prepare, allocation]
  exact writePair_of_stores _ first second _ written memory firstStore secondStore

/-- Derive the complete Good input of ConstructorFrame.operation from the
actual allocation and ordered initialized prefix. No target-content or final
validity premise is supplied. Previous allocations, registry and graph remain
exact; the stack view is independent of every allocator-owned registry entry. -/
theorem prepare_with_writable (first second : NodeId) (before : World σ)
    (pointer : Compiler.ZigAir.Memory.Value) (allocated : Compiler.ZigAir.Memory.State)
    (valid : Valid before.memory)
    (allocation : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, allocated)) :
    ∃ after, prepare first second before = (.ok ⟨before.memory.memory.nextId, 0, 2⟩, after) ∧
      Good ⟨before.memory.memory.nextId, 0, 2⟩ [first, second] after ∧
      after.graph = before.graph ∧ after.memory.heap = before.memory.heap ∧ after.memory.effects = before.memory.effects ∧
      after.memory.memory.nextId = before.memory.memory.nextId + 1 ∧
      (∀ id cell, before.memory.memory.heap.lookup id = some cell → after.memory.memory.heap.lookup id = some cell) ∧
      Writable after.memory.memory ⟨before.memory.memory.nextId, 0, 2⟩ ∧
      after.memory.heap before.memory.memory.nextId = none := by
  let source : View := ⟨before.memory.memory.nextId, 0, 2⟩
  have empty : Represents before.memory.memory ⟨0, 0, 0⟩ [] := ⟨rfl, by intro index inside; simp at inside⟩
  obtain ⟨allocatedValid, _, _, kept⟩ := caller_buffer before.memory allocated pointer ⟨0, 0, 0⟩ [] valid empty allocation
  have cap := writable_fresh before.memory.memory allocated 2 pointer allocation
  obtain ⟨written, firstStore⟩ := write_total allocated source 0 first allocatedValid.memory cap (by simp [source])
  have unregistered : before.memory.heap source.allocation = none := valid.injected.fresh valid.memory
  have writtenValid := stored_valid { before.memory with memory := allocated } written source 0 first
    allocatedValid unregistered (by simp [source]) firstStore
  have writtenCap := writable_store allocated written source _ _ firstStore cap
  obtain ⟨memory, secondStore⟩ := write_total written source 1 second writtenValid.memory writtenCap (by simp [source])
  have finalValid := stored_valid { before.memory with memory := written } memory source 1 second
    writtenValid unregistered (by simp [source]) secondStore
  have contents := pair_contents allocated written memory source first second rfl firstStore secondStore
  let after : World σ := { before with memory := { before.memory with memory } }
  refine ⟨after, prepare_of_stores first second before pointer allocated written memory allocation firstStore secondStore,
    ⟨finalValid, contents⟩, rfl, rfl, rfl, ?_, ?_,
    writable_store written memory source _ _ secondStore writtenCap, unregistered⟩
  · exact (Compiler.ZigAir.Memory.store_keeps_counters _ _ _ _ secondStore).1.trans
      ((Compiler.ZigAir.Memory.store_keeps_counters _ _ _ _ firstStore).1.trans (Compiler.ZigAir.Memory.allocate_pointer _ _ _ _ allocation).2)
  · intro id cell found
    have older := (Compiler.ZigAir.Memory.valid_lookup _ _ _ valid.memory found).1
    have firstFrame := (write_allocation_frame _ _ source 0 first firstStore).2.2 id (by dsimp [source]; omega)
    have secondFrame := (write_allocation_frame _ _ source 1 second secondStore).2.2 id (by dsimp [source]; omega)
    exact secondFrame.trans (firstFrame.trans (kept id cell found))

/-- Retain the original preparation interface. The stronger result additionally
derives permission for a reached local-array overwrite, without a final writable
or initialized-buffer premise. -/
theorem prepare_verified (first second : NodeId) (before : World σ)
    (pointer : Compiler.ZigAir.Memory.Value) (allocated : Compiler.ZigAir.Memory.State)
    (valid : Valid before.memory)
    (allocation : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, allocated)) :
    ∃ after, prepare first second before = (.ok ⟨before.memory.memory.nextId, 0, 2⟩, after) ∧
      Good ⟨before.memory.memory.nextId, 0, 2⟩ [first, second] after ∧
      after.graph = before.graph ∧ after.memory.heap = before.memory.heap ∧ after.memory.effects = before.memory.effects ∧
      after.memory.memory.nextId = before.memory.memory.nextId + 1 ∧
      (∀ id cell, before.memory.memory.heap.lookup id = some cell → after.memory.memory.heap.lookup id = some cell) := by
  obtain ⟨after, ran, good, graph, heap, effects, counter, frame, _⟩ :=
    prepare_with_writable first second before pointer allocated valid allocation
  exact ⟨after, ran, good, graph, heap, effects, counter, frame⟩

/-- The existing ordered initializer keeps each reached store's address counter. -/
theorem orderedStores_address
    (first : Except Compiler.ZigAir.Memory.Fault Compiler.ZigAir.Memory.State)
    (second : Compiler.ZigAir.Memory.State → Except Compiler.ZigAir.Memory.Fault Compiler.ZigAir.Memory.State)
    (source target : View) (before after : World σ)
    (firstFrame : ∀ memory, first = .ok memory → memory.nextAddress = before.memory.memory.nextAddress)
    (secondFrame : ∀ written memory, second written = .ok memory → memory.nextAddress = written.nextAddress)
    (ran : orderedStores first second source before = (.ok target, after)) :
    after.memory.memory.nextAddress = before.memory.memory.nextAddress := by
  cases firstCall : first with
  | error fault => simp only [orderedStores, firstCall, Prod.mk.injEq] at ran; cases ran.1
  | ok written =>
    cases secondCall : second written with
    | error fault => simp only [orderedStores, firstCall, secondCall, Prod.mk.injEq] at ran; cases ran.1
    | ok memory =>
      have same := Prod.mk.inj ran
      simp only [firstCall, secondCall] at same
      cases Except.ok.inj same.1
      cases same.2
      exact (secondFrame written memory secondCall).trans (firstFrame written firstCall)

/-- Both reached initializer stores preserve the actual allocation counter. -/
theorem prepare_address (first second : NodeId) (before after : World σ) (source : View)
    (pointer : Compiler.ZigAir.Memory.Value) (allocated : Compiler.ZigAir.Memory.State)
    (allocation : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, allocated))
    (ran : prepare first second before = (.ok source, after)) :
    after.memory.memory.nextAddress = allocated.nextAddress := by
  let target : View := ⟨before.memory.memory.nextId, 0, 2⟩
  let initial : World σ := { before with memory := { before.memory with memory := allocated } }
  have firstFrame : ∀ memory, Compiler.ZigAir.Memory.store allocated (target.pointer 0) (number first) = .ok memory →
      memory.nextAddress = allocated.nextAddress := fun memory stored =>
    (Compiler.ZigAir.Memory.store_keeps_counters allocated (target.pointer 0) (number first) memory stored).2
  have secondFrame : ∀ written memory, Compiler.ZigAir.Memory.store written (target.pointer 1) (number second) = .ok memory →
      memory.nextAddress = written.nextAddress := fun written memory stored =>
    (Compiler.ZigAir.Memory.store_keeps_counters written (target.pointer 1) (number second) memory stored).2
  simp only [prepare, allocation, writePair] at ran
  exact orderedStores_address (Compiler.ZigAir.Memory.store allocated (target.pointer 0) (number first))
    (fun written => Compiler.ZigAir.Memory.store written (target.pointer 1) (number second))
    target source initial after firstFrame secondFrame ran

def unwind (mark : Nat) (ran : Except Fault NodeId × State σ) : Except Fault NodeId × World σ :=
  (ran.1, if ordinary ran.1 then
    { ran.2.world with memory := { ran.2.world.memory with
      memory := Compiler.ZigAir.Memory.cleanup mark ran.2.world.memory.memory } } else ran.2.world)

theorem unwind_keeps_reached (mark : Nat) (ran : Except Fault NodeId × State σ) :
    (unwind mark ran).1 = ran.1 ∧ (unwind mark ran).2.graph = ran.2.world.graph ∧
    (unwind mark ran).2.memory.effects = ran.2.world.memory.effects ∧
    (unwind mark ran).2.memory.memory.nextId = ran.2.world.memory.memory.nextId ∧
    (unwind mark ran).2.memory.memory.nextAddress = ran.2.world.memory.memory.nextAddress := by
  unfold unwind
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem unwind_verified (mark : Nat) (meaning : Meaning) (source : View) (values : List NodeId)
    (before : World σ) (ran : Except Fault NodeId × State σ) (value : Word)
    (checked : ConstructorFrame.Post meaning source values before ran value) :
    ordinary (unwind mark ran).1 = true →
      Valid (unwind mark ran).2.memory ∧ Closed ran.2.scope ∧
      Semantic.Ensures meaning before.graph (unwind mark ran).1 (unwind mark ran).2.graph
        (fun id after => after.read id = some value) := by
  intro completed
  change ordinary ran.1 = true at completed
  have facts := checked completed
  simp only [unwind, completed, ↓reduceIte]
  exact ⟨Valid.cleanup _ facts.1.1 _, facts.2.1, facts.2.2⟩

/-- Supply the constructor's Good premise from this site's stores, then unwind
the temporary on ordinary return. The remaining graph and recursive callback
contracts are stated explicitly; this is not the recursive induction endpoint. -/
theorem prepared_opcode_verified (external : External σ) (budget allocator : Nat)
    (p : Primitives σ) (q : Caller.Queries) (opcode : Opcode) (first second : NodeId) (before : World σ)
    (pointer : Compiler.ZigAir.Memory.Value) (allocated : Compiler.ZigAir.Memory.State)
    (other : Meaning) (value : Word) (initial : Valid before.memory)
    (allocation : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, allocated))
    (admitted : Admitted external)
    (ownership : ∀ source values, OwnedCall.Contracts allocator source values p)
    (contracts : ∀ source values, Semantic.Contracts allocator source values (Folding.wordMeaning other) p)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (evaluated : (Interner.constructorCode.operationRequest opcode [first, second]).item.eval
      (Folding.wordMeaning other) before.graph.read [first, second] Interner.constructorCode.sequence = some value) :
    ∃ prepared, prepare first second before = (.ok ⟨before.memory.memory.nextId, 0, 2⟩, prepared) ∧
      let ran := ConstructorFrame.operation external budget allocator p q
        ⟨before.memory.memory.nextId, 0, 2⟩ opcode [first, second] prepared
      ordinary ran.1 = true →
        Valid (unwind before.memory.memory.nextId ran).2.memory ∧ Closed ran.2.scope ∧
        Semantic.Ensures (Folding.wordMeaning other) before.graph ran.1
          (unwind before.memory.memory.nextId ran).2.graph (fun id after => after.read id = some value) := by
  obtain ⟨prepared, ran, good, graph, _⟩ := prepare_verified first second before pointer allocated initial allocation
  have checked := ConstructorFrame.operation_verified external budget allocator p q
    ⟨before.memory.memory.nextId, 0, 2⟩ opcode [first, second] prepared other value
    good admitted (ownership _ _) (contracts _ _) (graph.symm ▸ valid) (graph.symm ▸ evaluated)
  refine ⟨prepared, ran, ?_⟩
  dsimp only
  intro completed
  have post := unwind_verified before.memory.memory.nextId (Folding.wordMeaning other)
    ⟨before.memory.memory.nextId, 0, 2⟩ [first, second] prepared _ value checked completed
  exact ⟨post.1, post.2.1, graph ▸ post.2.2⟩

/-- Preserve the source-bound negation interface as the SUB instance. -/
theorem prepared_operation_verified (external : External σ) (budget allocator : Nat)
    (p : Primitives σ) (q : Caller.Queries) (first second : NodeId) (before : World σ)
    (pointer : Compiler.ZigAir.Memory.Value) (allocated : Compiler.ZigAir.Memory.State)
    (other : Meaning) (value : Word) (initial : Valid before.memory)
    (allocation : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, allocated))
    (admitted : Admitted external)
    (ownership : ∀ source values, OwnedCall.Contracts allocator source values p)
    (contracts : ∀ source values, Semantic.Contracts allocator source values (Folding.wordMeaning other) p)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (evaluated : (Interner.constructorCode.operationRequest (Interner.buildOpcode .SUB) [first, second]).item.eval
      (Folding.wordMeaning other) before.graph.read [first, second] Interner.constructorCode.sequence = some value) :
    ∃ prepared, prepare first second before = (.ok ⟨before.memory.memory.nextId, 0, 2⟩, prepared) ∧
      let ran := ConstructorFrame.operation external budget allocator p q
        ⟨before.memory.memory.nextId, 0, 2⟩ (Interner.buildOpcode .SUB) [first, second] prepared
      ordinary ran.1 = true →
        Valid (unwind before.memory.memory.nextId ran).2.memory ∧ Closed ran.2.scope ∧
        Semantic.Ensures (Folding.wordMeaning other) before.graph ran.1
          (unwind before.memory.memory.nextId ran).2.graph (fun id after => after.read id = some value) :=
  prepared_opcode_verified external budget allocator p q (Interner.buildOpcode .SUB) first second before
    pointer allocated other value initial allocation admitted ownership contracts valid evaluated

/-- Enter the existing constructor with the actual prepared pair. Rejected
observations retain storage; ordinary outcomes unwind only this caller frame. -/
def invoke (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries)
    (opcode : Opcode) (first second : NodeId) : GraphAction σ NodeId := fun before =>
  match prepare first second before with
  | (.error fault, reached) => (.error fault, reached)
  | (.ok source, prepared) => unwind before.memory.memory.nextId
    (ConstructorFrame.operation external budget allocator p q source opcode [first, second] prepared)

theorem invoke_of_preparation (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Caller.Queries) (opcode : Opcode) (first second : NodeId) (before prepared : World σ) (source : View)
    (initialized : prepare first second before = (.ok source, prepared)) :
    invoke external budget allocator p q opcode first second before = unwind before.memory.memory.nextId
      (ConstructorFrame.operation external budget allocator p q source opcode [first, second] prepared) := by
  simp only [invoke, initialized]

theorem invoke_preparation_error (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Caller.Queries) (opcode : Opcode) (first second : NodeId) (before reached : World σ) (fault : Fault)
    (failed : prepare first second before = (.error fault, reached)) :
    invoke external budget allocator p q opcode first second before = (.error fault, reached) := by
  simp only [invoke, failed]

theorem invoke_verified (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries)
    (opcode : Opcode) (first second : NodeId) (before : World σ) (pointer : Compiler.ZigAir.Memory.Value)
    (allocated : Compiler.ZigAir.Memory.State) (other : Meaning) (value : Word) (initial : Valid before.memory)
    (allocation : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, allocated))
    (admitted : Admitted external) (ownership : ∀ source values, OwnedCall.Contracts allocator source values p)
    (contracts : ∀ source values, Semantic.Contracts allocator source values (Folding.wordMeaning other) p)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (evaluated : (Interner.constructorCode.operationRequest opcode [first, second]).item.eval
      (Folding.wordMeaning other) before.graph.read [first, second] Interner.constructorCode.sequence = some value) :
    ordinary (invoke external budget allocator p q opcode first second before).1 = true →
      Valid (invoke external budget allocator p q opcode first second before).2.memory ∧
      Semantic.Ensures (Folding.wordMeaning other) before.graph
        (invoke external budget allocator p q opcode first second before).1
        (invoke external budget allocator p q opcode first second before).2.graph
        (fun id graph => graph.read id = some value) := by
  obtain ⟨prepared, initialized, checked⟩ := prepared_opcode_verified external budget allocator p q opcode
    first second before pointer allocated other value initial allocation admitted ownership contracts valid evaluated
  rw [invoke_of_preparation _ _ _ _ _ _ _ _ _ _ _ initialized]
  intro completed
  exact ⟨(checked completed).1, (checked completed).2.2⟩

/-- Evaluate the first operand's borrowed load at this reached world before
preparing either store. The second operand is the earlier child's returned ID. -/
def borrowedFirst (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries)
    (opcode : Opcode) (source : View) (index : Nat) (second : NodeId) : GraphAction σ NodeId := fun before =>
  if index < source.length then
    match TemporaryMemory.readId before.memory.memory source index with
    | .error fault => (.error (.memory (.preparation (.memory fault))), before)
    | .ok first => invoke external budget allocator p q opcode first second before
  else (.error (.memory (.preparation (.memory .sourceBounds))), before)

theorem borrowedFirst_of_load (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Caller.Queries) (opcode : Opcode) (source : View) (index : Nat) (first second : NodeId) (before : World σ)
    (inside : index < source.length)
    (loaded : Compiler.ZigAir.Memory.load before.memory.memory (source.pointer index) = .ok (number first)) :
    borrowedFirst external budget allocator p q opcode source index second before =
      invoke external budget allocator p q opcode first second before := by
  simp only [borrowedFirst, inside, ↓reduceIte, TemporaryMemory.readId_of_load _ _ _ _ loaded]

theorem borrowedFirst_read_error (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Caller.Queries) (opcode : Opcode) (source : View) (index : Nat) (second : NodeId)
    (before : World σ) (fault : Compiler.ZigAir.Memory.Fault) (inside : index < source.length)
    (failed : TemporaryMemory.readId before.memory.memory source index = .error fault) :
    borrowedFirst external budget allocator p q opcode source index second before =
      (.error (.memory (.preparation (.memory fault))), before) := by
  simp only [borrowedFirst, inside, ↓reduceIte, failed]

theorem borrowedFirst_verified (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Caller.Queries) (opcode : Opcode) (source : View) (values : List NodeId) (index : Nat)
    (inside : index < values.length) (second : NodeId) (before : World σ)
    (pointer : Compiler.ZigAir.Memory.Value) (allocated : Compiler.ZigAir.Memory.State)
    (other : Meaning) (value : Word) (initial : Valid before.memory)
    (represented : Represents before.memory.memory source values)
    (allocation : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, allocated))
    (admitted : Admitted external) (ownership : ∀ source values, OwnedCall.Contracts allocator source values p)
    (contracts : ∀ source values, Semantic.Contracts allocator source values (Folding.wordMeaning other) p)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (evaluated : (Interner.constructorCode.operationRequest opcode [values[index], second]).item.eval
      (Folding.wordMeaning other) before.graph.read [values[index], second] Interner.constructorCode.sequence = some value) :
    ordinary (borrowedFirst external budget allocator p q opcode source index second before).1 = true →
      Valid (borrowedFirst external budget allocator p q opcode source index second before).2.memory ∧
      Semantic.Ensures (Folding.wordMeaning other) before.graph
        (borrowedFirst external budget allocator p q opcode source index second before).1
        (borrowedFirst external budget allocator p q opcode source index second before).2.graph
        (fun id graph => graph.read id = some value) := by
  rw [borrowedFirst_of_load external budget allocator p q opcode source index values[index] second before
    (represented.1 ▸ inside) (represented.2 index inside)]
  exact invoke_verified external budget allocator p q opcode values[index] second before pointer allocated
    other value initial allocation admitted ownership contracts valid evaluated

/-- The source-bound child occurs before temporary allocation. Ordinary return
unwinds this site's storage after the complete constructor has cleaned its own
locals; rejected observations retain the reached storage, graph and effects. -/
def negate (constant : Word → GraphAction σ NodeId) (external : External σ) (budget allocator : Nat)
    (p : Primitives σ) (q : Caller.Queries) (select : Unit → NodeId) : GraphAction σ NodeId := fun before =>
  match constant 0 before with
  | (.error fault, reached) => (.error fault, reached)
  | (.ok first, middle) =>
    let second := select ()
    invoke external budget allocator p q (Interner.buildOpcode .SUB) first second middle

theorem first_error (constant : Word → GraphAction σ NodeId) (external : External σ) (budget allocator : Nat)
    (p : Primitives σ) (q : Caller.Queries) (select : Unit → NodeId) (before reached : World σ) (fault : Fault)
    (failed : constant 0 before = (.error fault, reached)) :
    negate constant external budget allocator p q select before = (.error fault, reached) := by
  simp only [negate, failed]

theorem after_first (constant : Word → GraphAction σ NodeId) (external : External σ) (budget allocator : Nat)
    (p : Primitives σ) (q : Caller.Queries) (select : Unit → NodeId) (first : NodeId)
    (before middle prepared : World σ) (source : View)
    (child : constant 0 before = (.ok first, middle))
    (arguments : prepare first (select ()) middle = (.ok source, prepared)) :
    negate constant external budget allocator p q select before =
      unwind middle.memory.memory.nextId
        (ConstructorFrame.operation external budget allocator p q source (Interner.buildOpcode .SUB) [first, select ()] prepared) := by
  simp only [negate, child, invoke, arguments]


end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryArguments
