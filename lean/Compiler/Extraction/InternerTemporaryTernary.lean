/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerTemporaryUnary

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryTernary
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open TemporaryArguments (unwind unwind_verified)

def tailView (source : View) : View := ⟨source.allocation, source.first + 2, 1⟩

/-- Reuse the pair's ordered stores and the unary leaf store at the third
offset. Each failure retains exactly the reached initialized prefix. -/
def writeTriple (source : View) (first second third : NodeId) : GraphAction σ View :=
  Effect.bind (TemporaryArguments.writePair source first second)
    (fun _ => Effect.bind (TemporaryUnary.writeOne (tailView source) third) (fun _ => Effect.pure source))

theorem writeTriple_success (source target : View) (first second third : NodeId) (before after : World σ)
    (ran : writeTriple source first second third before = (.ok target, after)) :
    target = source ∧ before.memory.memory.heap.RetainsShape after.memory.memory.heap := by
  obtain ⟨view, middle, pair, continued⟩ := Effect.bind_success_phases _ _ before after target ran
  obtain ⟨tail, reached, last, returned⟩ := Effect.bind_success_phases _ _ middle after target continued
  have same := Prod.mk.inj returned
  have preserved := (TemporaryArguments.writePair_success source view first second before middle pair).2.trans
    (TemporaryUnary.writeOne_success (tailView source) tail third middle reached last).2
  exact ⟨(Except.ok.inj same.1).symm, same.2 ▸ preserved⟩

def prepare (first second third : NodeId) : GraphAction σ View := fun before =>
  let source : View := ⟨before.memory.memory.nextId, 0, 3⟩
  match Compiler.ZigAir.Memory.allocate before.memory.memory (.array 3 word) with
  | .error fault => (.error (.memory (.preparation (.memory fault))), before)
  | .ok (_, allocated) =>
    writeTriple source first second third { before with memory := { before.memory with memory := allocated } }

theorem writeTriple_of_phases (source : View) (first second third : NodeId) (before middle after : World σ)
    (pair : TemporaryArguments.writePair source first second before = (.ok source, middle))
    (last : TemporaryUnary.writeOne (tailView source) third middle = (.ok (tailView source), after)) :
    writeTriple source first second third before = (.ok source, after) := by
  have step := Effect.bind_success (TemporaryArguments.writePair source first second)
    (fun _ => Effect.bind (TemporaryUnary.writeOne (tailView source) third) (fun _ => Effect.pure source))
    before middle source pair
  have final := Effect.bind_success (TemporaryUnary.writeOne (tailView source) third)
    (fun _ => Effect.pure source) middle after (tailView source) last
  exact step.trans final

theorem writeTriple_pair_error (source : View) (first second third : NodeId) (before reached : World σ) (fault : Fault)
    (failed : TemporaryArguments.writePair source first second before = (.error fault, reached)) :
    writeTriple source first second third before = (.error fault, reached) :=
  Effect.bind_failure _ _ _ _ _ failed

theorem writeTriple_third_error (source : View) (first second third : NodeId) (before middle reached : World σ)
    (fault : Fault) (pair : TemporaryArguments.writePair source first second before = (.ok source, middle))
    (failed : TemporaryUnary.writeOne (tailView source) third middle = (.error fault, reached)) :
    writeTriple source first second third before = (.error fault, reached) := by
  have step := Effect.bind_success (TemporaryArguments.writePair source first second)
    (fun _ => Effect.bind (TemporaryUnary.writeOne (tailView source) third) (fun _ => Effect.pure source))
    before middle source pair
  have last := Effect.bind_failure (TemporaryUnary.writeOne (tailView source) third)
    (fun _ => Effect.pure source) middle reached fault failed
  exact step.trans last

theorem writeTriple_of_stores (source : View) (first second third : NodeId) (before : World σ)
    (written middle memory : Compiler.ZigAir.Memory.State)
    (firstStore : Compiler.ZigAir.Memory.store before.memory.memory (source.pointer 0) (number first) = .ok written)
    (secondStore : Compiler.ZigAir.Memory.store written (source.pointer 1) (number second) = .ok middle)
    (thirdStore : Compiler.ZigAir.Memory.store middle (source.pointer 2) (number third) = .ok memory) :
    writeTriple source first second third before =
      (.ok source, { before with memory := { before.memory with memory } }) := by
  have pair := TemporaryArguments.writePair_of_stores source first second before written middle firstStore secondStore
  have last := TemporaryUnary.writeOne_of_store (tailView source) third
    ({ before with memory := { before.memory with memory := middle } } : World σ) memory thirdStore
  exact writeTriple_of_phases source first second third before _ _ pair last

theorem triple_contents (allocated written middle memory : Compiler.ZigAir.Memory.State) (source : View)
    (first second third : NodeId) (length : source.length = 3)
    (firstStore : Compiler.ZigAir.Memory.store allocated (source.pointer 0) (number first) = .ok written)
    (secondStore : Compiler.ZigAir.Memory.store written (source.pointer 1) (number second) = .ok middle)
    (thirdStore : Compiler.ZigAir.Memory.store middle (source.pointer 2) (number third) = .ok memory) :
    Represents memory source [first, second, third] := by
  have pair := TemporaryArguments.pair_contents allocated written middle
    (⟨source.allocation, source.first, 2⟩ : View) first second rfl firstStore secondStore
  refine ⟨by simp [length], ?_⟩
  intro index inside
  have alternatives : index = 0 ∨ index = 1 ∨ index = 2 := by change index < 3 at inside; omega
  rcases alternatives with zero | one | two
  · subst index
    exact (write_frame middle memory source 2 0 third thirdStore (by omega)).trans (pair.2 0 (by simp))
  · subst index
    exact (write_frame middle memory source 2 1 third thirdStore (by omega)).trans (pair.2 1 (by simp))
  · subst index
    exact Compiler.ZigAir.Memory.load_after_store middle _ _ memory thirdStore

/-- Derive initialized contents, validity, fresh ownership and the older-memory
frame from the actual allocation and existing store transformers. -/
theorem prepare_verified (first second third : NodeId) (before : World σ)
    (pointer : Compiler.ZigAir.Memory.Value) (allocated : Compiler.ZigAir.Memory.State)
    (initial : Valid before.memory)
    (allocation : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 3 word) = .ok (pointer, allocated)) :
    ∃ after, prepare first second third before = (.ok ⟨before.memory.memory.nextId, 0, 3⟩, after) ∧
      Good ⟨before.memory.memory.nextId, 0, 3⟩ [first, second, third] after ∧
      after.graph = before.graph ∧ after.memory.heap = before.memory.heap ∧ after.memory.effects = before.memory.effects ∧
      after.memory.memory.nextId = before.memory.memory.nextId + 1 ∧
      (∀ id cell, before.memory.memory.heap.lookup id = some cell → after.memory.memory.heap.lookup id = some cell) := by
  let source : View := ⟨before.memory.memory.nextId, 0, 3⟩
  have empty : Represents before.memory.memory ⟨0, 0, 0⟩ [] := ⟨rfl, by intro index inside; simp at inside⟩
  obtain ⟨allocatedValid, _, _, kept⟩ := caller_array_buffer 3 before.memory allocated pointer ⟨0, 0, 0⟩ [] initial empty allocation
  have cap := writable_fresh before.memory.memory allocated 3 pointer allocation
  have unregistered : before.memory.heap source.allocation = none := initial.injected.fresh initial.memory
  obtain ⟨written, firstStore⟩ := write_total allocated source 0 first allocatedValid.memory cap (by simp [source])
  have writtenValid := TemporaryMemory.stored_valid { before.memory with memory := allocated } written source 0 first
    allocatedValid unregistered (by simp [source]) firstStore
  have writtenCap := writable_store allocated written source _ _ firstStore cap
  obtain ⟨middle, secondStore⟩ := write_total written source 1 second writtenValid.memory writtenCap (by simp [source])
  have middleValid := TemporaryMemory.stored_valid { before.memory with memory := written } middle source 1 second
    writtenValid unregistered (by simp [source]) secondStore
  have middleCap := writable_store written middle source _ _ secondStore writtenCap
  obtain ⟨memory, thirdStore⟩ := write_total middle source 2 third middleValid.memory middleCap (by simp [source])
  have finalValid := TemporaryMemory.stored_valid { before.memory with memory := middle } memory source 2 third
    middleValid unregistered (by simp [source]) thirdStore
  have contents := triple_contents allocated written middle memory source first second third rfl firstStore secondStore thirdStore
  let after : World σ := { before with memory := { before.memory with memory } }
  have ran : prepare first second third before = (.ok source, after) := by
    simp only [prepare, allocation]
    exact writeTriple_of_stores source first second third _ written middle memory firstStore secondStore thirdStore
  refine ⟨after, ran, ⟨finalValid, contents⟩, rfl, rfl, rfl, ?_, ?_⟩
  · exact (Compiler.ZigAir.Memory.store_keeps_counters _ _ _ _ thirdStore).1.trans
      ((Compiler.ZigAir.Memory.store_keeps_counters _ _ _ _ secondStore).1.trans
        ((Compiler.ZigAir.Memory.store_keeps_counters _ _ _ _ firstStore).1.trans
          (Compiler.ZigAir.Memory.allocate_pointer _ _ _ _ allocation).2))
  · intro id cell found
    have older := (Compiler.ZigAir.Memory.valid_lookup _ _ _ initial.memory found).1
    have firstFrame := (write_allocation_frame _ _ source 0 first firstStore).2.2 id (by dsimp [source]; omega)
    have secondFrame := (write_allocation_frame _ _ source 1 second secondStore).2.2 id (by dsimp [source]; omega)
    have thirdFrame := (write_allocation_frame _ _ source 2 third thirdStore).2.2 id (by dsimp [source]; omega)
    exact thirdFrame.trans (secondFrame.trans (firstFrame.trans (kept id cell found)))

def invoke (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries)
    (opcode : Opcode) (first second third : NodeId) : GraphAction σ NodeId := fun before =>
  let mark := before.memory.memory.nextId
  match prepare first second third before with
  | (.error fault, reached) => (.error fault, reached)
  | (.ok source, prepared) => unwind mark
    (ConstructorFrame.operation external budget allocator p q source opcode [first, second, third] prepared)

theorem invoke_verified (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries)
    (opcode : Opcode) (first second third : NodeId) (before : World σ) (pointer : Compiler.ZigAir.Memory.Value)
    (allocated : Compiler.ZigAir.Memory.State) (other : Meaning) (value : Word) (initial : Valid before.memory)
    (allocation : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 3 word) = .ok (pointer, allocated))
    (admitted : Admitted external) (ownership : ∀ source values, OwnedCall.Contracts allocator source values p)
    (contracts : ∀ source values, Semantic.Contracts allocator source values (Folding.wordMeaning other) p)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (evaluated : (Interner.constructorCode.operationRequest opcode [first, second, third]).item.eval
      (Folding.wordMeaning other) before.graph.read [first, second, third] Interner.constructorCode.sequence = some value) :
    ordinary (invoke external budget allocator p q opcode first second third before).1 = true →
      Valid (invoke external budget allocator p q opcode first second third before).2.memory ∧
      Semantic.Ensures (Folding.wordMeaning other) before.graph
        (invoke external budget allocator p q opcode first second third before).1
        (invoke external budget allocator p q opcode first second third before).2.graph
        (fun id graph => graph.read id = some value) := by
  obtain ⟨prepared, initialized, good, graph, _⟩ := prepare_verified first second third before pointer allocated initial allocation
  have checked := ConstructorFrame.operation_verified external budget allocator p q
    ⟨before.memory.memory.nextId, 0, 3⟩ opcode [first, second, third] prepared other value good admitted
    (ownership _ _) (contracts _ _) (graph.symm ▸ valid) (graph.symm ▸ evaluated)
  simp only [invoke, initialized]
  intro completed
  have post := unwind_verified before.memory.memory.nextId (Folding.wordMeaning other)
    ⟨before.memory.memory.nextId, 0, 3⟩ [first, second, third] prepared _ value checked completed
  exact ⟨post.1, graph ▸ post.2.2⟩

/-- This literal's readonly loads precede temporary allocation. The retained
native query prefix must supply the represented two-element view. -/
def borrowed (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries)
    (opcode : Opcode) (source : View) (third : NodeId) : GraphAction σ NodeId := fun before =>
  if source.length = 2 then
    match TemporaryMemory.readId before.memory.memory source 0 with
    | .error fault => (.error (.memory (.preparation (.memory fault))), before)
    | .ok first => match TemporaryMemory.readId before.memory.memory source 1 with
      | .error fault => (.error (.memory (.preparation (.memory fault))), before)
      | .ok second => invoke external budget allocator p q opcode first second third before
  else (.error (.memory (.preparation (.memory .sourceBounds))), before)

theorem borrowed_bad_length (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries)
    (opcode : Opcode) (source : View) (third : NodeId) (before : World σ) (length : source.length ≠ 2) :
    borrowed external budget allocator p q opcode source third before =
      (.error (.memory (.preparation (.memory .sourceBounds))), before) := by
  simp only [borrowed, length, ↓reduceIte]

theorem borrowed_first_error (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries)
    (opcode : Opcode) (source : View) (third : NodeId) (before : World σ) (fault : Compiler.ZigAir.Memory.Fault)
    (length : source.length = 2) (failed : TemporaryMemory.readId before.memory.memory source 0 = .error fault) :
    borrowed external budget allocator p q opcode source third before =
      (.error (.memory (.preparation (.memory fault))), before) := by
  simp only [borrowed, length, ↓reduceIte, failed]

theorem borrowed_second_error (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries)
    (opcode : Opcode) (source : View) (first third : NodeId) (before : World σ) (fault : Compiler.ZigAir.Memory.Fault)
    (length : source.length = 2)
    (loaded : Compiler.ZigAir.Memory.load before.memory.memory (source.pointer 0) = .ok (number first))
    (failed : TemporaryMemory.readId before.memory.memory source 1 = .error fault) :
    borrowed external budget allocator p q opcode source third before =
      (.error (.memory (.preparation (.memory fault))), before) := by
  simp only [borrowed, length, ↓reduceIte, TemporaryMemory.readId_of_load _ _ _ _ loaded, failed]

theorem borrowed_of_loads (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries)
    (opcode : Opcode) (source : View) (first second third : NodeId) (before : World σ)
    (length : source.length = 2)
    (firstLoad : Compiler.ZigAir.Memory.load before.memory.memory (source.pointer 0) = .ok (number first))
    (secondLoad : Compiler.ZigAir.Memory.load before.memory.memory (source.pointer 1) = .ok (number second)) :
    borrowed external budget allocator p q opcode source third before =
      invoke external budget allocator p q opcode first second third before := by
  simp only [borrowed, length, ↓reduceIte, TemporaryMemory.readId_of_load _ _ _ _ firstLoad,
    TemporaryMemory.readId_of_load _ _ _ _ secondLoad]

theorem borrowed_verified (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries)
    (opcode : Opcode) (source : View) (first second third : NodeId) (before : World σ)
    (pointer : Compiler.ZigAir.Memory.Value) (allocated : Compiler.ZigAir.Memory.State) (other : Meaning) (value : Word)
    (initial : Valid before.memory) (represented : Represents before.memory.memory source [first, second])
    (allocation : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 3 word) = .ok (pointer, allocated))
    (admitted : Admitted external) (ownership : ∀ source values, OwnedCall.Contracts allocator source values p)
    (contracts : ∀ source values, Semantic.Contracts allocator source values (Folding.wordMeaning other) p)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (evaluated : (Interner.constructorCode.operationRequest opcode [first, second, third]).item.eval
      (Folding.wordMeaning other) before.graph.read [first, second, third] Interner.constructorCode.sequence = some value) :
    ordinary (borrowed external budget allocator p q opcode source third before).1 = true →
      Valid (borrowed external budget allocator p q opcode source third before).2.memory ∧
      Semantic.Ensures (Folding.wordMeaning other) before.graph
        (borrowed external budget allocator p q opcode source third before).1
        (borrowed external budget allocator p q opcode source third before).2.graph
        (fun id graph => graph.read id = some value) := by
  rw [borrowed_of_loads external budget allocator p q opcode source first second third before
    represented.1.symm (represented.2 0 (by simp)) (represented.2 1 (by simp))]
  exact invoke_verified external budget allocator p q opcode first second third before pointer allocated other value
    initial allocation admitted ownership contracts valid evaluated

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryTernary
