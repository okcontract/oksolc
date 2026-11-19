/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPairInput
import Compiler.Extraction.InternerLocalArgumentsProofs
import Compiler.Extraction.RepresentativeBorrowedQuery

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ViewInput
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray

/-- A caller-owned view enters the complete local-item constructor directly.
Its allocation, offset and length survive the boundary. Only the callee's item
and scratch frames unwind here; this does not allocate or retire an input array. -/
def operation (context : PairInput.Context σ) (source : View) (opcode : Opcode)
    (values : List NodeId) (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := fun before =>
  let ran := ConstructorItem.operation context.external context.budget context.allocator
    (context.primitives source) context.queries source opcode values debug before
  (ran.1, ran.2.world)

/-- The admitted named array performs its original allocation, aggregate copy
and optional overwrite before entering the full constructor on that same view.
The source-local IDs annotate the native reads; local_input derives agreement. -/
def localOperation (context : PairInput.Context σ) (opcode : Opcode) (source : View)
    (left right repeated : NodeId) (selected : Nat) (repeatedIsFirst : Bool)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := fun before =>
  match LocalArguments.zigLocal source selected repeated repeatedIsFirst before with
  | (.error fault, reached) => (.error fault, reached)
  | (.ok target, prepared) => TemporaryArguments.unwind before.memory.memory.nextId
      (ConstructorItem.operation context.external context.budget context.allocator (context.primitives target)
        context.queries target opcode (if repeatedIsFirst then [left, right].set selected repeated else [left, right]) debug prepared)

/-- Borrowed calls retain their operand allocation. The named-local callback
executes the original copy and overwrite before entering the same constructor.
The helper's two-element guard excludes the rejected shapes. -/
def constructors (context : PairInput.Context σ) : Associative.Constructors AssemblyItem.Fields.Values (GraphAction σ) :=
  { PairInput.constructors context with
    borrowedOperation := fun address opcode values debug => operation context ⟨address, 0, values.length⟩ opcode values debug
    localOperation := fun opcode source selected repeated first debug =>
      match source.items with
      | [left, right] => localOperation context opcode (view source) left right repeated selected first debug
      | _ => fun before => (.error .outsideOwnedContinuation, before) }

attribute [local irreducible] ConstructorItem.operation TemporaryArguments.unwind

theorem forwards (context : PairInput.Context σ) (source : View) (opcode : Opcode)
    (values : List NodeId) (debug : AssemblyItem.Fields.Values) (before : World σ) :
    operation context source opcode values debug before =
      (let ran := ConstructorItem.operation context.external context.budget context.allocator
        (context.primitives source) context.queries source opcode values debug before
       (ran.1, ran.2.world)) := by unfold operation; with_reducible rfl

theorem borrowed_forwards (context : PairInput.Context σ) (slice : ArgumentSlice) (opcode : Opcode)
    (debug : AssemblyItem.Fields.Values) :
    (constructors context).borrowedOperation slice.address opcode slice.items debug =
      operation context (view slice) opcode slice.items debug := by unfold constructors view; with_reducible rfl

theorem local_forwarded (context : PairInput.Context σ) (source : ArgumentSlice) (left right : NodeId)
    (items : source.items = [left, right]) (opcode : Opcode) (selected : Nat) (repeated : NodeId)
    (first : Bool) (debug : AssemblyItem.Fields.Values) :
    (constructors context).localOperation opcode source selected repeated first debug =
      localOperation context opcode (view source) left right repeated selected first debug := by
  simp only [constructors, items]

/-- The actual native query and graph correspondence determine the contents
and key separation needed by the complete constructor. Neither a descriptor
alone nor an arbitrary list of IDs establishes this input contract. -/
theorem queried_input (allocator : Nat) (header : Compiler.ZigAir.Memory.Address)
    (id : NodeId) (opcode : Opcode) (before : World (Publication.Effects σ))
    (cells : List Storage.Cell) (value : Compiler.ZigAir.Memory.Value)
    (present : before.graph.representatives = some cells) (valid : Valid before.memory)
    (resident : Memory.GraphResident allocator before.memory.heap cells)
    (apart : OwnedKeys.Apart before.memory.effects.keys
      (fun address => ∃ cell ∈ cells, cell.arguments ≠ [] ∧ address = cell.argumentsAddress))
    (agreement : RepresentativeArray.Operation.run before.memory.memory header id opcode =
      .ok ((operationProgram.run cells id opcode).map (Option.map RepresentativeArray.Operation.returned)))
    (native : RepresentativeArray.Operation.run before.memory.memory header id opcode = .ok (.ok (some value))) :
    ∃ slice, value = RepresentativeArray.Operation.returned slice ∧
      BorrowedQuery.observe allocator id opcode before = .ok (some slice) ∧ Good (view slice) slice.items before ∧
      ∀ key old, before.memory.effects.keys key = some old → key.arguments ≠ [] →
        (view slice).length ≠ 0 → (view slice).allocation ≠ old.address := by
  obtain ⟨slice, descriptor, observed, good⟩ := BorrowedQuery.Native.accepted allocator header id opcode before cells value
    present valid resident agreement native
  have read := (BorrowedQuery.accepted allocator id opcode before slice observed).1
  have logical : operationProgram.run cells id opcode = .ok (some slice) := by
    simpa only [Interner.representativeReads, present, Nested.storageReads] using read
  obtain ⟨cell, entry, _, _, same⟩ := Storage.operation_found cells id opcode slice logical
  refine ⟨slice, descriptor, observed, good, ?_⟩
  intro key old found nonempty length alias
  apply apart key old found nonempty
  refine ⟨cell, List.mem_of_getElem? entry, ?_, ?_⟩
  · intro empty
    apply length
    rw [← same]
    change cell.arguments.length = 0
    rw [empty]; rfl
  · rw [← same] at alias
    exact alias.symm

/-- Derive the same prepared-input contract used by literal callers from the
actual named copy and overwrite. This also enables Prepared.key_apart and
Prepared.caller_input without assuming final contents or writable storage. -/
theorem local_input (source target : View) (left right repeated : NodeId) (selected : Nat)
    (repeatedIsFirst : Bool) (before after : World σ) (good : Good source [left, right] before)
    (inside : selected < 2)
    (ran : LocalArguments.zigLocal source selected repeated repeatedIsFirst before = (.ok target, after)) :
    Arguments.Prepared (if repeatedIsFirst then [left, right].set selected repeated else [left, right]) before target after := by
  have storage := LocalArguments.prepare_storage source target selected repeated repeatedIsFirst before after ran
  have length : source.length = 2 := good.2.1.symm
  cases allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) with
  | error fault =>
    simp only [LocalArguments.zigLocal, LocalArguments.copy, length, bne_self_eq_false,
      Bool.false_eq_true, ↓reduceIte, allocated, Prod.mk.injEq] at ran
    cases ran.1
  | ok pair =>
    obtain ⟨reached, called, contents, graph, heap, effects, counter, frame⟩ :=
      LocalArguments.prepare_verified source left right repeated selected repeatedIsFirst before pair.1 pair.2
        good.1 good.2 inside allocated
    have same := Prod.mk.inj (called.symm.trans ran)
    cases Except.ok.inj same.1
    cases same.2
    have size : (if repeatedIsFirst then [left, right].set selected repeated else [left, right]).length = 2 := by
      split <;> simp
    have nonempty : (if repeatedIsFirst then [left, right].set selected repeated else [left, right]).isEmpty = false := by
      apply List.isEmpty_eq_false_iff.mpr
      intro empty
      rw [empty] at size
      contradiction
    exact ⟨by simp only [nonempty, Bool.false_eq_true, ↓reduceIte, size], contents, graph, heap, effects,
      by simpa only [nonempty, Bool.false_eq_true, ↓reduceIte] using counter, frame,
      fun _ => by simpa only [size] using storage⟩

/-- The selected slot is a precondition only when the source executes the
optional overwrite. An unchanged local copy permits any unused slot value. -/
theorem local_input_optional (source target : View) (left right repeated : NodeId) (selected : Nat)
    (repeatedIsFirst : Bool) (before after : World σ) (good : Good source [left, right] before)
    (inside : repeatedIsFirst = true → selected < 2)
    (ran : LocalArguments.zigLocal source selected repeated repeatedIsFirst before = (.ok target, after)) :
    Arguments.Prepared (if repeatedIsFirst then [left, right].set selected repeated else [left, right]) before target after := by
  cases repeatedIsFirst with
  | true => exact local_input source target left right repeated selected true before after good (inside rfl) ran
  | false =>
    apply local_input source target left right repeated 0 false before after good (by decide)
    simpa only [LocalArguments.zigLocal, Bool.false_eq_true, ↓reduceIte] using ran

theorem local_prepared (context : PairInput.Context σ) (opcode : Opcode) (source target : View)
    (left right repeated : NodeId) (selected : Nat) (repeatedIsFirst : Bool) (debug : AssemblyItem.Fields.Values)
    (before after : World σ)
    (ran : LocalArguments.zigLocal source selected repeated repeatedIsFirst before = (.ok target, after)) :
    localOperation context opcode source left right repeated selected repeatedIsFirst debug before =
      TemporaryArguments.unwind before.memory.memory.nextId
        (ConstructorItem.operation context.external context.budget context.allocator (context.primitives target)
          context.queries target opcode (if repeatedIsFirst then [left, right].set selected repeated else [left, right]) debug after) := by
  simp only [localOperation, ran]

theorem local_rejected (context : PairInput.Context σ) (opcode : Opcode) (source : View)
    (left right repeated : NodeId) (selected : Nat) (repeatedIsFirst : Bool) (debug : AssemblyItem.Fields.Values)
    (before after : World σ) (fault : Fault)
    (ran : LocalArguments.zigLocal source selected repeated repeatedIsFirst before = (.error fault, after)) :
    localOperation context opcode source left right repeated selected repeatedIsFirst debug before = (.error fault, after) := by
  simp only [localOperation, ran]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ViewInput
