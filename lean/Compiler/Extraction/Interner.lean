/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.CacheProofs
import Compiler.Extraction.StorageOperations

/-! Semantic projection of the interner's control flow. The heap retains values,
the cache and optional representative structure. When present, that structure
must be coherent with the values. Local callbacks thread an allocation cursor;
their graph frame is enforced by the interface. Cleanup ownership and physical
allocation effects still need refinement. Recursive closure and physical memory refinement are
separate from this control-flow model and its primitive contracts. -/
namespace Compiler.Extraction.Interner
open Compiler.Algebraic Contract.Yul
open Compiler.Extraction.Cache

structure Heap where
  read : Read
  table : Table
  /-- Concrete representative observations are separate from their word values.
  `none` retains the explicitly abstract value-only interface. -/
  representatives : Option (List Storage.Cell) := none
  /-- Position in a caller-supplied allocation-outcome stream. This is logical
  effect state, not a physical allocator or an allocation lifetime identity. -/
  allocationCursor : Nat := 0

def Represented (meaning : Meaning) (heap : Heap) : Prop :=
  match heap.representatives with
  | none => True
  | some cells => heap.read = Storage.readValue cells ∧ Storage.Coherent meaning cells

structure Invariant (meaning : Meaning) (heap : Heap) : Prop where
  cache : Valid meaning heap.read heap.table
  representation : Represented meaning heap

theorem Invariant.with_cursor {meaning : Meaning} {heap : Heap}
    (valid : Invariant meaning heap) (cursor : Nat) :
    Invariant meaning { heap with allocationCursor := cursor } := ⟨valid.cache, valid.representation⟩

abbrev Stable (before after : Heap) := Preserves Heap.read before after

inductive Error where
  | outOfMemory | capacity | unsupported | invalidOptional | invalidId | safetyFault | assemblyException
  deriving DecidableEq, Repr

abbrev Action (α : Type) := Effect Heap Error α
abbrev Local (α : Type) := Effect Nat Error α

def Local.fromExcept (result : Except Error α) : Local α := fun cursor => (result, cursor)

/-- Local allocation callbacks can fail differently on repeated calls. Their
state cannot overwrite word values, cache entries or representative cells. -/
def liftLocal (action : Local α) : Action α := fun heap =>
  let (result, cursor) := action heap.allocationCursor
  (result, { heap with allocationCursor := cursor })

def fail (error : Error) : Action α := fun heap => (.error error, heap)
def lift (result : Except Error α) : Action α := fun heap => (result, heap)
def get : Action Heap := fun heap => (.ok heap, heap)

/-- All outcomes retain the invariant and old IDs, including errors after a
recursive simplification has added nodes. Success has an additional postcondition. -/
def Safe (meaning : Meaning) (action : Action α) (before : Heap) (post : α → Heap → Prop) : Prop :=
  ∀ result after, action before = (result, after) →
    Invariant meaning after ∧ Stable before after ∧
      (match result with | .error _ => True | .ok value => post value after)

theorem Safe.pure (meaning : Meaning) (before : Heap) (value : α) (post : α → Heap → Prop)
    (valid : Invariant meaning before) (result : post value before) :
    Safe meaning (pure value) before post := by
  intro outcome after run
  change (Except.ok value, before) = (outcome, after) at run
  cases run
  exact ⟨valid, fun _ _ h => h, result⟩

theorem Safe.fail (meaning : Meaning) (before : Heap) (error : Error) (post : α → Heap → Prop)
    (valid : Invariant meaning before) : Safe meaning (fail error) before post := by
  intro outcome after run
  cases run
  exact ⟨valid, fun _ _ h => h, trivial⟩

theorem Safe.bind (meaning : Meaning) (before : Heap) (first : Action α) (next : α → Action β)
    (middle : α → Heap → Prop) (post : β → Heap → Prop)
    (safeFirst : Safe meaning first before middle)
    (safeNext : ∀ value heap, Invariant meaning heap → Stable before heap → middle value heap →
      Safe meaning (next value) heap post) : Safe meaning (first >>= next) before post := by
  intro result after run
  change Effect.bind first next before = (result, after) at run
  unfold Effect.bind at run
  cases step : first before with
  | mk outcome heap =>
    obtain ⟨valid, stable, fact⟩ := safeFirst outcome heap step
    cases outcome with
    | error error =>
      simp only [step] at run
      cases run
      exact ⟨valid, stable, trivial⟩
    | ok value =>
      have final := safeNext value heap valid stable fact result after (by simpa only [step] using run)
      exact ⟨final.1, stable.trans final.2.1, final.2.2⟩

structure Request where
  item : Item
  arguments : List NodeId
  sequence : BitVec 32

/-- These primitives do not assume correctness of find or of a Builder. The
recursive optimizer is the sole graph-transforming search callback. Insertion
and publication can be supplied by the separately checked transaction models. -/
structure Primitives where
  atCapacity : Heap → Bool
  normalize : Request → Local (List NodeId)
  deterministic : Item → Except Error Bool
  takeOwned : List NodeId → Local Unit
  simplify : Key → Action (Option NodeId)
  insert : Key → Bool → Action NodeId
  publish : Key → NodeId → Action Unit

inductive ResultId where
  | captured | literal (id : NodeId)
  deriving DecidableEq, Repr

def ResultId.run (code : ResultId) (id : NodeId) : NodeId :=
  match code with
  | .captured => id
  | .literal value => value

structure FindCode where
  hit : ResultId
  simplified : ResultId
  published : ResultId

def makeKey (request : Request) (args : List NodeId) : Except Error Key :=
  match keyCode.run request.item args request.sequence with
  | none => .error .invalidOptional
  | some key => .ok key

def FindCode.miss (code : FindCode) (p : Primitives) (request : Request)
    (key : Key) (deterministic : Bool) : Action NodeId := do
  if deterministic && (request.item.kind == 1) then
    let simplified ← p.simplify key
    match simplified with
    | some id =>
      let _ ← p.publish key (code.published.run id)
      return code.simplified.run id
    | none => pure ()
  p.insert key deterministic

def FindCode.owned (code : FindCode) (p : Primitives) (request : Request)
    (args : List NodeId) (deterministic : Bool) : Action NodeId := do
  let _ ← liftLocal (p.takeOwned args)
  let key ← lift (makeKey request args)
  code.miss p request key deterministic

/-- The extractor admits the exact source control skeleton and emits its result
and publication expressions. Cleanup is a semantic frame contract: graph/cache
observations are unchanged by releasing only locally owned temporary buffers.
Key construction occurs at both actual source sites, retaining error order. -/
def FindCode.run (code : FindCode) (p : Primitives) (request : Request) : Action NodeId := do
  let before ← get
  if p.atCapacity before then fail .capacity else do
    let args ← liftLocal (p.normalize request)
    let deterministic ← lift (p.deterministic request.item)
    if deterministic then
      let key ← lift (makeKey request args)
      match before.table key with
      | some id => return code.hit.run id
      | none => pure ()
    code.owned p request args deterministic

structure ForceCode where
  published : ResultId

/-- Representative validation reads the heap, without modifying it. Both key
construction sites and the sequence-zero binding follow the native source. -/
def ForceCode.run (code : ForceCode) (p : Primitives)
    (validate : NodeId → Heap → Except Error Unit) (id : NodeId)
    (item : Item) (arguments : List NodeId) : Action Unit := do
  let before ← get
  let _ ← lift (validate id before)
  let request : Request := ⟨item, arguments, 0⟩
  let args ← liftLocal (p.normalize request)
  let key ← lift (makeKey request args)
  match before.table key with
  | some _ => return ()
  | none => pure ()
  let _ ← liftLocal (p.takeOwned args)
  let key ← lift (makeKey request args)
  p.publish key (code.published.run id)

def Normalizes (meaning : Meaning) (p : Primitives) : Prop :=
  ∀ request args read cursor after, p.normalize request cursor = (.ok args, after) →
    request.item.eval meaning read args request.sequence =
      request.item.eval meaning read request.arguments request.sequence

def Publishes (meaning : Meaning) (p : Primitives) : Prop :=
  ∀ key id before value, Invariant meaning before → key.eval meaning before.read = some value →
    before.read id = some value → Safe meaning (p.publish key id) before (fun _ _ => True)

/-- Callbacks preserve every earlier ID and the cache invariant on errors too.
The simplify contract includes the no-rewrite outcome and arbitrary graph growth.
It is a remaining obligation, not a claim that the full optimizer is verified. -/
structure Contracts (meaning : Meaning) (p : Primitives) : Prop where
  normalize : Normalizes meaning p
  simplify : ∀ key before value, Invariant meaning before → key.eval meaning before.read = some value →
    Safe meaning (p.simplify key) before (fun result after =>
      ∀ id, result = some id → after.read id = some value)
  insert : ∀ key deterministic before value, Invariant meaning before → key.eval meaning before.read = some value →
    Safe meaning (p.insert key deterministic) before (fun id after => after.read id = some value)
  publish : Publishes meaning p

/-- Atomic successful publication changes only the map; allocation failure leaves
both observations unchanged. The supplied Boolean is an arbitrary allocation outcome. -/
def publish (succeeds : Bool) (key : Key) (id : NodeId) : Action Unit := fun before =>
  if succeeds then (.ok (), { before with table := put equalityFields before.table key id })
  else (.error .outOfMemory, before)

theorem publish_safe (meaning : Meaning) (succeeds : Bool) (key : Key) (id : NodeId)
    (before : Heap) (value : Word) (valid : Invariant meaning before)
    (denotation : key.eval meaning before.read = some value) (actual : before.read id = some value) :
    Safe meaning (publish succeeds key id) before (fun _ _ => True) := by
  intro result after run
  cases succeeds <;> simp only [publish, Bool.false_eq_true, if_false, if_true] at run
  · cases run
    exact ⟨valid, fun _ _ h => h, trivial⟩
  · cases run
    exact ⟨⟨put_valid meaning before.read before.table valid.cache key id value denotation actual,
      valid.representation⟩, fun _ _ h => h, trivial⟩

end Compiler.Extraction.Interner
