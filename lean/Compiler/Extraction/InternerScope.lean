/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.InternerControl
import Compiler.Extraction.InternerProgram
import Compiler.Extraction.NormalizationEffects

/-! Invocation-local ownership for the source-bound interner. Recursive graph
actions cannot inspect or overwrite the caller's scope. `Exit.cleanup` is the
native normalized_owned flag; `Exit.transfer` records its handoff to insertion
or successful publication. A downstream owner may itself free the buffer.
Allocation identities and physical borrow refinement remain separate. -/
namespace Compiler.Extraction.Interner.Scoped
open Compiler.Algebraic Compiler.Extraction.Cache

structure Scope where
  lookup : Option NormalizationOwnership.State := none
  items : List NodeId := []
  phase : NormalizationOwnership.Exit := .lookup
  deriving DecidableEq, Repr

structure Session where
  scope : Scope
  heap : Heap

abbrev Action (α : Type) := Effect Session Error α

structure Resources where
  sort : List NodeId → List NodeId
  allocate : NormalizationOwnership.Allocation → List NodeId → Nat → Bool × Nat
  release : List NodeId → NormalizationOwnership.State → Nat → Nat
  /-- Effects of an admitted, successful preparation, after destination
  selection and before any lookup or duplicate. The memory refinement must
  reject concrete preparation faults; this total projection must not encode
  them as recoverable OOM or authorize deferred cleanup. -/
  prepare : List NodeId → NormalizationOwnership.State → Nat → Nat := fun _ _ cursor => cursor

def liftGraph (action : Interner.Action α) : Action α := fun before =>
  let (result, heap) := action before.heap
  (result, { before with heap })

def commutative (item : Item) : Except Error Bool :=
  if normalizeCode.guard.run item then
    match item.instruction with
    | none => .error .invalidOptional
    | some opcode => .ok (normalizeCode.commutative.contains opcode)
  else .ok false

def initScope (r : Resources) (request : Request) : Action (List NodeId) := fun before =>
  match commutative request.item with
  | .error error => (.error error, before)
  | .ok commutes =>
    let (lookup, cursor) := normalizationOwnershipCode.initWith commutes request.arguments.length 2
      (r.allocate .temporary request.arguments) before.heap.allocationCursor
    let heap := { before.heap with allocationCursor := cursor }
    match lookup with
    | none => (.error .outOfMemory, { before with heap })
    | some lookup =>
      let cursor := if lookup.origin = .input then cursor else r.prepare request.arguments lookup cursor
      let items := if commutes && decide (normalizeCode.threshold ≤ request.arguments.length)
        then r.sort request.arguments else request.arguments
      (.ok items, ⟨⟨some lookup, items, .lookup⟩, { heap with allocationCursor := cursor }⟩)

def take (r : Resources) : Action Unit := fun before =>
  match before.scope.lookup with
  | none => (.error .safetyFault, before)
  | some lookup =>
    let ((ok, lookup), cursor) := normalizationOwnershipCode.takeWith
      (r.allocate .duplicate before.scope.items) lookup before.heap.allocationCursor
    (if ok then .ok () else .error .outOfMemory,
      ⟨{ before.scope with lookup := some lookup, phase := if ok then .cleanup else before.scope.phase },
        { before.heap with allocationCursor := cursor }⟩)

def handoff : Action Unit := fun before =>
  (.ok (), { before with scope := { before.scope with phase := .transfer } })

/-- Caller cleanup precedes lookup deinit. The updated handle from takeOwned
is used, so transferred temporaries cannot be freed a second time. -/
def close (r : Resources) (before : Session) : Session :=
  match before.scope.lookup with
  | none => before
  | some lookup =>
    let (lookup, cursor) := if before.scope.phase = .cleanup then
      (lookup.move .caller .released, r.release before.scope.items lookup before.heap.allocationCursor)
      else (lookup, before.heap.allocationCursor)
    let (lookup, cursor) := normalizationOwnershipCode.deinitWith (r.release before.scope.items) lookup cursor
    ⟨{ before.scope with lookup := some lookup }, { before.heap with allocationCursor := cursor }⟩

def execution (r : Resources) (p : Primitives) : Execution Action where
  get := liftGraph Interner.get
  lift := fun result => liftGraph (Interner.lift result)
  atCapacity := p.atCapacity
  normalize := initScope r
  deterministic := p.deterministic
  takeOwned := fun _ => take r
  handoff := Scoped.handoff
  simplify := fun key => liftGraph (p.simplify key)
  insert := fun key deterministic => liftGraph (p.insert key deterministic)
  publish := fun key id => liftGraph (p.publish key id)

def finish (r : Resources) (action : Action α) (before : Heap) : Except Error α × Session :=
  let (result, after) := action ⟨{}, before⟩
  (result, close r after)

def findDetailed (r : Resources) (p : Primitives) (request : Request) (before : Heap) :=
  finish r (findCode.controlRun (execution r p) request) before

def find (r : Resources) (p : Primitives) (request : Request) : Interner.Action NodeId := fun before =>
  let (result, after) := findDetailed r p request before
  (result, after.heap)

def forceDetailed (r : Resources) (p : Primitives) (validate : NodeId → Heap → Except Error Unit)
    (id : NodeId) (item : Item) (arguments : List NodeId) (before : Heap) :=
  finish r (forceCode.controlRun (execution r p) validate id item arguments) before

def force (r : Resources) (p : Primitives) (validate : NodeId → Heap → Except Error Unit)
    (id : NodeId) (item : Item) (arguments : List NodeId) : Interner.Action Unit := fun before =>
  let (result, after) := forceDetailed r p validate id item arguments before
  (result, after.heap)

def Ready (scope : Scope) : Prop :=
  ∃ lookup, scope.lookup = some lookup ∧ scope.phase = .lookup ∧ NormalizationOwnership.Ready lookup

def Taken (scope : Scope) : Prop :=
  ∃ lookup, scope.lookup = some lookup ∧ scope.phase = .cleanup ∧ NormalizationOwnership.Taken lookup

def Transferred (scope : Scope) : Prop :=
  ∃ lookup, scope.lookup = some lookup ∧ scope.phase = .transfer ∧ NormalizationOwnership.Taken lookup

def Live (scope : Scope) : Prop :=
  (scope.lookup = none ∧ scope.phase = .lookup) ∨ Ready scope ∨ Taken scope ∨ Transferred scope

def Closed (scope : Scope) : Prop :=
  match scope.lookup with
  | none => scope.phase = .lookup
  | some lookup => NormalizationOwnership.Safe ((match scope.phase with
      | .lookup => .lookup | .cleanup => .cleaned | .transfer => .transferred), lookup)

end Compiler.Extraction.Interner.Scoped
