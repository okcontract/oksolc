/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.Memory

/-! Owned cache entries add allocation identities to the existing value key.
Hash-table bucket allocation and probing are a framed `getOrPut` primitive.
Only its completed logical entry is exposed: new entries already contain the
incoming key; existing entries retain the old key. The uninitialized value of
a new entry is never read. Allocator effects survive failure and cleanup.
Physical hash-table/pointer refinement remains separate. -/
namespace Compiler.Extraction.OwnedKeys
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage

structure Entry where
  address : Nat
  id : NodeId
  deriving DecidableEq, Repr

abbrev Table := Key → Option Entry

def slice (key : Key) (entry : Entry) : ArgumentSlice := ⟨entry.address, key.arguments⟩
def view (table : Table) : Cache.Table := fun key => (table key).map Entry.id

def store (table : Table) (key : Key) (entry : Entry) : Table :=
  fun query => if query = key then some entry else table query

structure State where
  table : Table
  memory : Memory.Heap

def Live (allocator : Nat) (s : State) : Prop :=
  ∀ key entry, s.table key = some entry → Memory.SliceValid allocator s.memory (slice key entry)

/-- Distinct nonempty keys exclusively own their argument allocations. Empty
slices may share sentinel addresses, even with live allocations. -/
def Unique (table : Table) : Prop :=
  ∀ a x b y, table a = some x → table b = some y → a ≠ b →
    a.arguments ≠ [] → b.arguments ≠ [] → x.address ≠ y.address

def Fresh (table : Table) (key : Key) (incoming : Entry) : Prop :=
  ∀ old entry, table old = some entry → key.arguments ≠ [] → old.arguments ≠ [] →
    incoming.address ≠ entry.address

def Apart (table : Table) (kept : Nat → Prop) : Prop :=
  ∀ key entry, table key = some entry → key.arguments ≠ [] → ¬ kept entry.address

def Frame (kept : Nat → Prop) (before after : Memory.Heap) : Prop :=
  ∀ address, kept address → after address = before address

structure Code where
  releaseExisting : Bool
  replaceKey : Bool
  value : Scalar NodeId

/-- Shared publication control, interpreted either by the logical ownership
model or by the typed-memory execution. The interpreter must retain the reached
state on failure; publication never rolls allocator effects back. -/
structure Operations (α ε : Type) where
  getOrPut : Key → α → Bool × α
  lookup : Key → α → Option Entry
  release : ArgumentSlice → α → Except ε Unit × α
  write : Key → Entry → α → α
  outOfMemory : ε

def Code.complete (code : Code) (ops : Operations α ε) (key : Key) (incoming : Entry)
    (before : α) : Except ε Unit × α :=
  let old := ops.lookup key before
  let (released, reached) := match old with
    | some entry => if code.releaseExisting then ops.release (slice key entry) before else (.ok (), before)
    | none => (.ok (), before)
  match released with
  | .error fault => (.error fault, reached)
  | .ok () =>
    let address := if code.replaceKey then incoming.address else (old.getD incoming).address
    (.ok (), ops.write key ⟨address, code.value.run incoming.id⟩ reached)

def Code.execute (code : Code) (ops : Operations α ε) (key : Key) (incoming : Entry)
    (before : α) : Except ε Unit × α :=
  let (ok, reached) := ops.getOrPut key before
  if ok then code.complete ops key incoming reached else (.error ops.outOfMemory, reached)

def logicalOperations (getOrPut : Key → σ → Bool × σ)
    (onFree : ArgumentSlice → σ → σ) (allocator : Nat) : Operations (State × σ) Memory.Fault where
  getOrPut key before := let (ok, effects) := getOrPut key before.2; (ok, before.1, effects)
  lookup key before := before.1.table key
  release owned before :=
    let effects := onFree owned before.2
    match Memory.releaseSlice before.1.memory allocator owned with
    | .error fault => (.error fault, before.1, effects)
    | .ok memory => (.ok (), { before.1 with memory }, effects)
  write key entry before := ({ before.1 with table := store before.1.table key entry }, before.2)
  outOfMemory := .outOfMemory

def unpack (result : Except ε Unit × (State × σ)) : (Except ε Unit × State) × σ :=
  ((result.1, result.2.1), result.2.2)

/-- The free callback tracks private allocator effects; the existing memory
model checks its logical allocation preconditions. A memory fault remains an
explicit invalid-execution outcome, not a recoverable native allocator error. -/
def Code.finish (code : Code) (onFree : ArgumentSlice → σ → σ) (allocator : Nat)
    (key : Key) (incoming : Entry) (before : State) (effects : σ) :
    (Except Memory.Fault Unit × State) × σ :=
  unpack (code.complete (logicalOperations (fun _ state => (true, state)) onFree allocator)
    key incoming (before, effects))

def Code.run (code : Code) (getOrPut : Key → σ → Bool × σ)
    (onFree : ArgumentSlice → σ → σ) (allocator : Nat) (key : Key) (incoming : Entry)
    (before : State) (effects : σ) : (Except Memory.Fault Unit × State) × σ :=
  unpack (code.execute (logicalOperations getOrPut onFree allocator) key incoming (before, effects))

/-- Compatibility with the established logical publication semantics. -/
theorem Code.finish_equation (code : Code) (onFree : ArgumentSlice → σ → σ) (allocator : Nat)
    (key : Key) (incoming : Entry) (before : State) (effects : σ) :
    code.finish onFree allocator key incoming before effects =
  let old := before.table key
  let (released, effects) : Except Memory.Fault Memory.Heap × σ := match old with
    | none => (.ok before.memory, effects)
    | some entry => if code.releaseExisting then
        (Memory.releaseSlice before.memory allocator (slice key entry), onFree (slice key entry) effects)
      else (.ok before.memory, effects)
  match released with
  | .error fault => ((.error fault, before), effects)
  | .ok memory =>
    let address := if code.replaceKey then incoming.address
      else (old.getD incoming).address
    ((.ok (), { table := store before.table key ⟨address, code.value.run incoming.id⟩, memory }), effects) := by
  cases found : before.table key with
  | none => simp [finish, complete, logicalOperations, unpack, found]
  | some old =>
    cases release : code.releaseExisting
    · simp [finish, complete, logicalOperations, unpack, found, release]
    · cases freed : Memory.releaseSlice before.memory allocator (slice key old) <;>
        simp [finish, complete, logicalOperations, unpack, found, release, freed]

theorem Code.run_equation (code : Code) (getOrPut : Key → σ → Bool × σ)
    (onFree : ArgumentSlice → σ → σ) (allocator : Nat) (key : Key) (incoming : Entry)
    (before : State) (effects : σ) : code.run getOrPut onFree allocator key incoming before effects =
  let (ok, effects) := getOrPut key effects
  if ok then code.finish onFree allocator key incoming before effects
  else ((.error .outOfMemory, before), effects) := by
  cases called : getOrPut key effects with
  | mk ok next =>
    cases ok <;> simp [run, execute, finish, complete, logicalOperations, unpack, called]

def retire (before : State) (key : Key) : Memory.Heap :=
  match before.table key with
  | none => before.memory
  | some old => if key.arguments = [] then before.memory
    else Memory.write before.memory old.address none

def after (before : State) (key : Key) (incoming : Entry) : State :=
  ⟨store before.table key incoming, retire before key⟩

def freeEffects (table : Table) (key : Key) (onFree : ArgumentSlice → σ → σ) (effects : σ) : σ :=
  match table key with
  | none => effects
  | some old => onFree (slice key old) effects

end Compiler.Extraction.OwnedKeys
