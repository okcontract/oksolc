/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyCloneProgram
import Compiler.Extraction.ExpressionLifetime

namespace Compiler.Extraction.AssemblyClone.Physical
open Compiler.Extraction.Memory Compiler.Extraction.Storage
open Compiler.Extraction.Memory.Arguments.Normalization

def descriptor (bytes : Bytes) : AssemblyItemDeinit.Bytes := ⟨bytes.address, bytes.contents.length, bytes.offset⟩
def number (value : BitVec 8) : Compiler.ZigAir.Memory.Value := .scalar (.int false 8 value.toNat)
def pointer (bytes : Bytes) (index : Nat) : Compiler.ZigAir.Memory.Value :=
  .pointer (.pointer false false AssemblyItemDeinit.byte) ⟨bytes.address, bytes.offset + index⟩

/-- Check actual typed reads, including initialization and extent. The supplied
logical contents are not a replacement for reading the source allocation. -/
def readable (state : Compiler.ZigAir.Memory.State) (bytes : Bytes) : Bool :=
  bytes.contents.zipIdx.all fun (value, index) =>
    match Compiler.ZigAir.Memory.load state (pointer bytes index) with
    | .error _ => false
    | .ok found => decide (found = number value)

def Reads (state : Compiler.ZigAir.Memory.State) (bytes : Bytes) : Prop :=
  ∀ value index, (value, index) ∈ bytes.contents.zipIdx →
    Compiler.ZigAir.Memory.load state (pointer bytes index) = .ok (number value)

theorem readable_sound (state : Compiler.ZigAir.Memory.State) (bytes : Bytes)
    (checked : readable state bytes = true) : Reads state bytes := by
  simp only [readable, List.all_eq_true] at checked
  intro value index present
  have accepted := checked (value, index) present
  cases read : Compiler.ZigAir.Memory.load state (pointer bytes index) with
  | error fault => simp [read] at accepted
  | ok found => simpa [read] using accepted

theorem Reads.frame (before after : Compiler.ZigAir.Memory.State) (bytes : Bytes)
    (reads : Reads before bytes) (same : after.heap.lookup bytes.address = before.heap.lookup bytes.address) :
    Reads after bytes := by
  intro value index present
  exact (Compiler.ZigAir.Memory.load_eq_of_lookup before after false false AssemblyItemDeinit.byte _ same).trans
    (reads value index present)

abbrev Allocate (σ : Type) := Nat → Session σ → Option Nat × σ

inductive Fault where
  | outOfMemory
  | memory (reason : Compiler.ZigAir.Memory.Fault)
  | registryCollision | sourceMismatch | copyMismatch
  deriving DecidableEq, Repr

def cell (length base : Nat) (contents : Compiler.ZigAir.Memory.Cells) : Compiler.ZigAir.Memory.Allocation :=
  ⟨base, .array length AssemblyItemDeinit.byte, contents, true, false⟩

def extend (before : Session σ) (length base : Nat) (contents : Compiler.ZigAir.Memory.Cells) : Compiler.ZigAir.Memory.State :=
  ⟨(before.memory.nextId, cell length base contents) :: before.memory.heap,
    before.memory.nextId + 1, max before.memory.nextAddress (base + length)⟩

def copiedCells (source : Bytes) : Compiler.ZigAir.Memory.Cells :=
  source.contents.zipIdx.map fun (value, index) => (index, number value)

/-- Executable contract for the native byte dupe used by clone. Allocation
precedes source reads. The copy is one exact typed-copy operation under the
frozen host.copy contract, not a new byte-loop or a claim about memcpy AIR.
Invalid responses reject and retain the reached storage/effects; ordinary OOM
does not read the source. Both heaps use normalization's existing lifetime IDs. -/
def copyAt (allocator base : Nat) (source : Bytes) (before : Session σ) (effects : σ) :
    Except Fault Bytes × Session σ :=
  let allocated := extend before source.contents.length base []
  if !allocated.valid then (.error (.memory .memoryValidity), { before with effects }) else
  let reached : Session σ := { before with memory := allocated, effects }
  match before.heap before.memory.nextId with
  | some _ => (.error .registryCollision, reached)
  | none =>
    let heap := write before.heap before.memory.nextId (some ⟨allocator, .bytes source.contents.length⟩)
    let prepared : Session σ := { reached with heap }
    if !readable allocated source then (.error .sourceMismatch, prepared) else
    let destination : Bytes := ⟨before.memory.nextId, source.contents, 0⟩
    let copied : Session σ := ⟨heap, extend before source.contents.length base (copiedCells source), effects⟩
    if copied.memory.valid && readable copied.memory destination && readable copied.memory source then
      (.ok destination, copied)
    else (.error .copyMismatch, copied)

def duplicate (request : Allocate σ) (allocator : Nat) (source : Bytes) (before : Session σ) :
    Except Fault Bytes × Session σ :=
  if source.contents = [] then (.ok ⟨before.memory.nextId, [], 0⟩, before) else
  if !before.memory.valid then (.error (.memory .malformed), before) else
  if source.contents.length ≥ Compiler.ZigAir.Memory.addressLimit then (.error (.memory .sourceBounds), before) else
  let (response, effects) := request source.contents.length before
  match response with
  | none => (.error .outOfMemory, { before with effects })
  | some base => copyAt allocator base source before effects

structure Copied (allocator : Nat) (source : Bytes) (before : Session σ) (destination : Bytes) (after : Session σ) : Prop where
  contents : destination.contents = source.contents
  address : destination.address = before.memory.nextId
  valid : Valid after
  owned : AssemblyItemDeinit.Owned allocator (descriptor destination) after
  reads : Reads after.memory destination
  sourceReads : Reads after.memory source
  frame : ∀ id, id ≠ before.memory.nextId → after.heap id = before.heap id ∧
    after.memory.heap.lookup id = before.memory.heap.lookup id
  nextId : after.memory.nextId = before.memory.nextId + if source.contents = [] then 0 else 1
  nextAddress : before.memory.nextAddress ≤ after.memory.nextAddress
  offset : destination.offset = 0

theorem copyAt_shape (allocator base : Nat) (source destination : Bytes) (before after : Session σ) (effects : σ)
    (executed : copyAt allocator base source before effects = (.ok destination, after)) :
    destination = ⟨before.memory.nextId, source.contents, 0⟩ ∧
    after = ⟨write before.heap before.memory.nextId (some ⟨allocator, .bytes source.contents.length⟩),
      extend before source.contents.length base (copiedCells source), effects⟩ ∧
    after.memory.valid = true ∧ readable after.memory destination = true ∧ readable after.memory source = true := by
  dsimp only [copyAt] at executed
  split at executed
  · simp at executed
  · split at executed
    · simp at executed
    · split at executed
      · simp at executed
      · split at executed
        next accepted =>
          cases executed
          simp only [Bool.and_eq_true] at accepted
          exact ⟨rfl, rfl, accepted.1.1, accepted.1.2, accepted.2⟩
        · simp at executed

theorem extend_lookup (before : Session σ) (length base id : Nat) (contents : Compiler.ZigAir.Memory.Cells)
    (apart : id ≠ before.memory.nextId) :
    (extend before length base contents).heap.lookup id = before.memory.heap.lookup id := by
  simp [extend, Compiler.ZigAir.Memory.Heap.lookup_cons, Ne.symm apart]

theorem copyAt_valid (allocator base : Nat) (source destination : Bytes) (before after : Session σ) (effects : σ)
    (initial : Valid before) (nonempty : source.contents ≠ [])
    (executed : copyAt allocator base source before effects = (.ok destination, after)) :
    Copied allocator source before destination after := by
  obtain ⟨rfl, rfl, valid, reads, sourceReads⟩ := copyAt_shape allocator base source destination before after effects executed
  refine ⟨rfl, rfl, ⟨valid, ?_, ?_⟩, ?_, readable_sound _ _ reads, readable_sound _ _ sourceReads,
    ?_, ?_, Nat.le_max_left _ _, rfl⟩
  · intro owner id values present stored
    have apart : id ≠ before.memory.nextId := by
      intro same; simp [write, same] at stored
    obtain ⟨⟨old, found, typed, writable, stack⟩, represented⟩ := initial.related owner id values present
      (by simpa [write, apart] using stored)
    have framed := extend_lookup before source.contents.length base id (copiedCells source) apart
    exact ⟨⟨old, framed.trans found, typed, writable, stack⟩, represented_frame _ values represented framed⟩
  · intro id block stored
    by_cases same : id = before.memory.nextId
    · subst id; exact ⟨cell source.contents.length base (copiedCells source), by simp [extend, Compiler.ZigAir.Memory.Heap.lookup_cons], rfl⟩
    · obtain ⟨old, found, _persistent⟩ := initial.injected id block (by simpa [write, same] using stored)
      exact ⟨old, (extend_lookup before source.contents.length base id (copiedCells source) same).trans found, _persistent⟩
  · exact Or.inr ⟨by simp [descriptor, write], cell source.contents.length base (copiedCells source),
      by simp [descriptor, extend, Compiler.ZigAir.Memory.Heap.lookup_cons], rfl, rfl, rfl, rfl⟩
  · intro id apart
    exact ⟨by simp [write, apart], extend_lookup before source.contents.length base id (copiedCells source) apart⟩
  · simp only [if_neg nonempty, extend]

theorem duplicate_valid (request : Allocate σ) (allocator : Nat) (source destination : Bytes) (before after : Session σ)
    (initial : Valid before) (executed : duplicate request allocator source before = (.ok destination, after)) :
    Copied allocator source before destination after := by
  dsimp only [duplicate] at executed
  split at executed
  next empty =>
    cases executed
    refine ⟨empty.symm, rfl, initial, Or.inl rfl, ?_, ?_,
      fun _ _ => ⟨rfl, rfl⟩, by simp [empty], Nat.le_refl _, rfl⟩
    · intro value index present; cases present
    · intro value index present; simp [empty] at present
  next nonempty =>
    split at executed
    · simp at executed
    · split at executed
      · simp at executed
      · cases requested : request source.contents.length before with
        | mk response effects =>
          simp only [requested] at executed
          cases response with
          | none => simp at executed
          | some base => exact copyAt_valid allocator base source destination before after effects initial nonempty executed

theorem copyAt_not_oom (allocator base : Nat) (source : Bytes) (before after : Session σ) (effects : σ) :
    copyAt allocator base source before effects ≠ (.error .outOfMemory, after) := by
  intro executed
  dsimp only [copyAt] at executed
  split at executed
  · simp at executed
  · split at executed
    · simp at executed
    · split at executed
      · simp at executed
      · split at executed <;> simp at executed

theorem duplicate_oom (request : Allocate σ) (allocator : Nat) (source : Bytes) (before after : Session σ)
    (executed : duplicate request allocator source before = (.error .outOfMemory, after)) :
    ∃ effects, request source.contents.length before = (none, effects) ∧ after = { before with effects } := by
  dsimp only [duplicate] at executed
  split at executed
  · simp at executed
  · split at executed
    · simp at executed
    · split at executed
      · simp at executed
      · cases requested : request source.contents.length before with
        | mk response effects =>
          simp only [requested] at executed
          cases response with
          | none => cases executed; exact ⟨effects, rfl, rfl⟩
          | some base => exact False.elim (copyAt_not_oom allocator base source before after effects executed)

end Compiler.Extraction.AssemblyClone.Physical
