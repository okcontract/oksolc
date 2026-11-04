/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerBorrowedConstructor
import Compiler.Extraction.InternerQueries
import Compiler.Extraction.InternerInsertionValidity

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.BorrowedQuery
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray

/-- Validate the exact query observation in the existing registry and typed
heap. This is a proof-side validator, not an extra branch in native Zig. Empty
slices require no live sentinel. Nonempty graph operands must be persistent,
writable full allocations containing every returned ID in its original order. -/
def typed (slice : ArgumentSlice) (state : Compiler.ZigAir.Memory.State) : Bool :=
  if slice.items.isEmpty then true else
  match state.heap.lookup slice.address with
  | none => false
  | some cell => decide (cell.type = .array slice.items.length word) && cell.writable && !cell.stack

def contents (slice : ArgumentSlice) (state : Compiler.ZigAir.Memory.State) : Bool :=
  (List.range slice.items.length).all fun index =>
    match slice.items[index]? with
    | none => false
    | some id => match Compiler.ZigAir.Memory.load state ((view slice).pointer index) with
      | .error _ => false
      | .ok value => decide (value = number id)

def checkSlice (allocator : Nat) (slice : ArgumentSlice) (state : Session σ) : Bool :=
  Insertion.ownsArguments allocator slice state.heap && typed slice state.memory && contents slice state.memory

theorem typed_sound (slice : ArgumentSlice) (state : Compiler.ZigAir.Memory.State)
    (checked : typed slice state = true) (nonempty : slice.items ≠ []) :
    Owned state slice.address slice.items.length := by
  simp only [typed, List.isEmpty_eq_false_iff.mpr nonempty, Bool.false_eq_true, ↓reduceIte] at checked
  cases found : state.heap.lookup slice.address with
  | none => simp [found] at checked
  | some cell =>
    simp only [found, Bool.and_eq_true, decide_eq_true_eq] at checked
    exact ⟨cell, found, checked.1.1, checked.1.2, by cases stack : cell.stack <;> simp_all⟩

theorem contents_sound (slice : ArgumentSlice) (state : Compiler.ZigAir.Memory.State)
    (checked : contents slice state = true) : Represents state (view slice) slice.items := by
  refine ⟨rfl, ?_⟩
  intro index inside
  have atIndex := List.all_eq_true.mp checked index (List.mem_range.mpr inside)
  simp only [List.getElem?_eq_getElem inside] at atIndex
  cases loaded : Compiler.ZigAir.Memory.load state ((view slice).pointer index) with
  | error fault => simp [loaded] at atIndex
  | ok value =>
    simp only [loaded, decide_eq_true_eq] at atIndex
    exact congrArg Except.ok atIndex

theorem slice_sound (allocator : Nat) (slice : ArgumentSlice) (state : Session σ)
    (checked : checkSlice allocator slice state = true) :
    SliceValid allocator state.heap slice ∧ Represents state.memory (view slice) slice.items ∧
      (slice.items ≠ [] → Owned state.memory slice.address slice.items.length) := by
  simp only [checkSlice, Bool.and_eq_true] at checked
  exact ⟨Insertion.ownsArguments_sound allocator slice state.heap checked.1.1,
    contents_sound slice state.memory checked.2, typed_sound slice state.memory checked.1.2⟩

/-- Every live graph slice in a valid related world passes the checker. This
uses existing ownership and memory invariants; it does not establish them for
the native storage implementation or future graph mutations. -/
theorem slice_complete (allocator : Nat) (slice : ArgumentSlice) (state : Session σ)
    (valid : Valid state) (live : SliceValid allocator state.heap slice) :
    checkSlice allocator slice state = true := by
  by_cases empty : slice.items = []
  · simp [checkSlice, Insertion.ownsArguments, typed, contents, empty]
  · have stored := live.resolve_left empty
    obtain ⟨⟨cell, found, shaped, writable, persistent⟩, represented⟩ :=
      valid.related allocator slice.address slice.items empty stored
    simp only [checkSlice, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp [Insertion.ownsArguments, List.isEmpty_eq_false_iff.mpr empty, stored]
    · simp [typed, List.isEmpty_eq_false_iff.mpr empty, found, shaped, writable, persistent]
    · apply List.all_eq_true.mpr
      intro index inside
      have bound := List.mem_range.mp inside
      simp only [List.getElem?_eq_getElem bound, represented.2 index bound, decide_true]

inductive Rejection where
  | query (fault : ReadError)
  | unbacked
  deriving DecidableEq, Repr

/-- Observe the source-bound operationArguments reader, then validate precisely
its returned allocation and values. Query faults remain distinct from misses
and memory rejection. No successful query is rewritten to another descriptor. -/
def observe (allocator : Nat) (id : NodeId) (opcode : Opcode) (before : World σ) :
    Except Rejection (Option ArgumentSlice) := do
  let found ← ((Interner.representativeReads before.graph).operation id opcode).mapError Rejection.query
  match found with
  | none => .ok none
  | some slice => if checkSlice allocator slice before.memory then .ok (some slice) else .error .unbacked

theorem accepted (allocator : Nat) (id : NodeId) (opcode : Opcode) (before : World σ) (slice : ArgumentSlice)
    (checked : observe allocator id opcode before = .ok (some slice)) :
    (Interner.representativeReads before.graph).operation id opcode = .ok (some slice) ∧
      checkSlice allocator slice before.memory = true := by
  cases found : (Interner.representativeReads before.graph).operation id opcode with
  | error fault => simp [observe, found, Except.mapError, bind, Except.bind] at checked
  | ok returned =>
    cases returned with
    | none => simp [observe, found, Except.mapError, bind, Except.bind] at checked
    | some actual =>
      simp only [observe, found, Except.mapError, bind, Except.bind] at checked
      split at checked
      · rename_i live
        cases checked
        exact ⟨rfl, live⟩
      · contradiction

theorem accepted_good (allocator : Nat) (id : NodeId) (opcode : Opcode) (before : World σ) (slice : ArgumentSlice)
    (valid : Valid before.memory) (checked : observe allocator id opcode before = .ok (some slice)) :
    Good (view slice) slice.items before :=
  ⟨valid, (slice_sound allocator slice before.memory (accepted allocator id opcode before slice checked).2).2.1⟩

theorem resident_accepted (allocator : Nat) (id : NodeId) (opcode : Opcode) (before : World σ)
    (cells : List Storage.Cell) (slice : ArgumentSlice) (present : before.graph.representatives = some cells)
    (valid : Valid before.memory) (resident : Memory.GraphResident allocator before.memory.heap cells)
    (found : (Interner.representativeReads before.graph).operation id opcode = .ok (some slice)) :
    observe allocator id opcode before = .ok (some slice) := by
  have native : operationProgram.run cells id opcode = .ok (some slice) := by
    simpa only [Interner.representativeReads, present, Nested.storageReads] using found
  obtain ⟨cell, entry, _, _, returned⟩ := operation_found cells id opcode slice native
  have live := (resident cell (List.mem_of_getElem? entry)).2
  rw [returned] at live
  have checked := slice_complete allocator slice before.memory valid live
  simp [observe, found, Except.mapError, bind, Except.bind, checked]

/-- Compose an accepted native query observation with the actual borrowed
constructor and complete normalization caller. The source's initial Good is
derived by the proved checker, rather than supplied for an arbitrary list.
The caller uses the source-bound capacity/determinism/validation queries. Graph
callbacks, the global valid world and recursive simulation remain compiler
obligations. Acceptance concerns this reached world, not all future calls. -/
theorem operation_verified (find : Recursive.Find σ) (external : External σ) (budget allocator : Nat)
    (p : Primitives σ) (id : NodeId) (queryOpcode opcode : Opcode) (slice : ArgumentSlice) (debug : Debug)
    (before : World σ) (other : Meaning) (value : Word)
    (validMemory : Valid before.memory) (checked : observe allocator id queryOpcode before = .ok (some slice))
    (admitted : Admitted external) (ownership : OwnedCall.Contracts allocator (view slice) slice.items p)
    (contracts : Semantic.Contracts allocator (view slice) slice.items (Folding.wordMeaning other) p)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (evaluated : (Interner.constructorCode.operationRequest opcode slice.items).item.eval (Folding.wordMeaning other)
      before.graph.read slice.items Interner.constructorCode.sequence = some value) :
    let ran := (Recursive.constructors find (Recursive.BorrowedConstructor.caller external budget allocator p Interner.Queries.queries)).borrowedOperation
      slice.address opcode slice.items debug before
    ordinary ran.1 = true →
      Good (view slice) slice.items ran.2 ∧
      Closed (ConstructorFrame.operation external budget allocator p Interner.Queries.queries (view slice) opcode slice.items before).2.scope ∧
      Semantic.Ensures (Folding.wordMeaning other) before.graph ran.1 ran.2.graph (fun result after => after.read result = some value) :=
  Recursive.BorrowedConstructor.operation_verified find external budget allocator p Interner.Queries.queries
    slice.address opcode slice.items debug before other value
    (accepted_good allocator id queryOpcode before slice validMemory checked) admitted ownership contracts valid evaluated

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.BorrowedQuery
