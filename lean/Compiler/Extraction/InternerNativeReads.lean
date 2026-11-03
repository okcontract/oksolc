/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeGraph
import Compiler.Extraction.InternerTemporaryMemory

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeReads
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Reify the contents of the native borrowed descriptor for the existing list
projection. This allocates no native buffer and does not change its address.
The admitted graph operands are full allocations; offset descriptors and native
read failures remain explicit rejected observations. -/
def arguments (memory : Compiler.ZigAir.Memory.State) (value : Compiler.ZigAir.Memory.Value) :
    Except Compiler.ZigAir.Memory.Fault ArgumentSlice := do
  let .slice type address length := value | .error .malformed
  if type ≠ .slice false Expression.idType then .error .malformed else do
  if address.offset ≠ 0 then .error .unsupported else do
  let items ← (List.finRange length).mapM fun index =>
    TemporaryMemory.readId memory ⟨address.allocation, 0, length⟩ index.val
  return ⟨address.allocation, items⟩

/-- The logical query interface has a distinct nonordinary safety rejection.
No native fault becomes an absent constant/operation or an allocation error. -/
def checked (result : Except Compiler.ZigAir.Memory.Fault (Except Storage.ReadError α)) :
    Except Storage.ReadError α :=
  match result with
  | .ok value => value
  | .error _ => .error .safetyFault

theorem checked_fault (fault : Compiler.ZigAir.Memory.Fault) :
    checked (.error fault : Except Compiler.ZigAir.Memory.Fault (Except Storage.ReadError α)) =
      .error .safetyFault := rfl

theorem arguments_offset (memory : Compiler.ZigAir.Memory.State)
    (address : Compiler.ZigAir.Memory.Address) (length : Nat) (offset : address.offset ≠ 0) :
    arguments memory (Operation.borrowed address length) = .error .unsupported := by
  simp only [arguments, Operation.borrowed, ne_self_iff_false, ↓reduceIte]
  exact if_pos offset

def operation (memory : Compiler.ZigAir.Memory.State) (owner : Nat) (id : NodeId) (opcode : Opcode) :
    Except Storage.ReadError (Option ArgumentSlice) := checked do
  let result ← Operation.run memory (Owner.headerAddress ⟨owner, 0⟩) id opcode
  match result with
  | .error fault => return .error fault
  | .ok none => return .ok none
  | .ok (some descriptor) => return .ok (some (← arguments memory descriptor))

/-- Every guard observes the actual owner, backing and item fields. The
operand contents are read from the returned allocation, never from graph
annotations. This is the entry snapshot used by the existing dispatcher. -/
def reads (owner : Nat) (memory : Compiler.ZigAir.Memory.State) : Nested.Reads where
  constant := fun id => checked (Constant.value memory (Owner.headerAddress ⟨owner, 0⟩) id)
  operation := operation memory owner

/-- Evaluate each source query against the world reached at that call site. -/
def query (owner : Nat) : Nested.QueryRead (GraphAction σ) := fun action before =>
  (Nested.readAction (m := GraphAction σ) (action (reads owner before.memory.memory))) before

theorem query_at (owner : Nat) (action : Nested.Reads → Except ReadError α) (before : World σ) :
    query owner action before =
      (Nested.readAction (action (reads owner before.memory.memory)) : GraphAction σ α) before := rfl

theorem arguments_represented (memory : Compiler.ZigAir.Memory.State) (slice : ArgumentSlice)
    (represented : Represents memory (view slice) slice.items) :
    arguments memory (Operation.returned slice) = .ok slice := by
  have loaded (index : Fin slice.items.length) :
      TemporaryMemory.readId memory (view slice) index.val = .ok slice.items[index.val] :=
    TemporaryMemory.readId_of_load _ _ _ _ (represented.2 index.val index.isLt)
  have equal : (fun index : Fin slice.items.length => TemporaryMemory.readId memory (view slice) index.val) =
      (fun index : Fin slice.items.length => (pure slice.items[index.val] : Except Compiler.ZigAir.Memory.Fault NodeId)) :=
    funext loaded
  have reduced : arguments memory (Operation.returned slice) = (do
    let items ← (List.finRange slice.items.length).mapM fun index : Fin slice.items.length =>
      TemporaryMemory.readId memory (view slice) index.val
    pure (ArgumentSlice.mk slice.address items)) := by rfl
  rw [reduced, equal, List.mapM_pure]
  simp only [List.finRange, List.map_ofFn, Function.comp_def, List.ofFn_getElem]
  rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeReads

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Native query guards and scalar contents agree for every ID and opcode.
The result follows from the reached owner/field/operand correspondence, not a
query-result premise or a logical-query fallback in the native reader. -/
theorem Facts.reads {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {world : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity world rows) :
    NativeReads.reads owner world.memory.memory = Interner.representativeReads world.graph := by
  have constants : ∀ id, (NativeReads.reads owner world.memory.memory).constant id =
      (Interner.representativeReads world.graph).constant id := by
    intro id
    simp only [NativeReads.reads, NativeReads.checked, facts.constants id,
      Interner.representativeReads, facts.projected, Nested.storageReads]
  have operations : ∀ id opcode, (NativeReads.reads owner world.memory.memory).operation id opcode =
      (Interner.representativeReads world.graph).operation id opcode := by
    intro id opcode
    simp only [NativeReads.reads, NativeReads.operation, facts.operations id opcode,
      Interner.representativeReads, facts.projected, Nested.storageReads]
    cases query : Storage.operationProgram.run rows id opcode with
    | error fault => rfl
    | ok found =>
      cases found with
      | none => rfl
      | some slice =>
        have observed := BorrowedQuery.Native.observed allocator id opcode world rows facts.projected facts.valid facts.resident
        rw [query] at observed
        have good := BorrowedQuery.accepted_good allocator id opcode world slice facts.valid observed
        have contents := NativeReads.arguments_represented world.memory.memory slice good.2
        simp only [Except.map, Option.map, bind, Except.bind, contents, pure, Except.pure, NativeReads.checked]
  cases native : NativeReads.reads owner world.memory.memory
  cases logical : Interner.representativeReads world.graph
  simp only [native, logical] at constants operations
  have sameConstants := funext constants
  have sameOperations := funext (fun id => funext (operations id))
  subst_vars
  have equality : (Interner.representativeReads world.graph).overrideEquality = none := by
    simp only [Interner.representativeReads, facts.projected, Nested.storageReads]
  have nativeEquality : (NativeReads.reads owner world.memory.memory).overrideEquality = none := rfl
  simp only [native, logical] at equality nativeEquality
  simp_all

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
