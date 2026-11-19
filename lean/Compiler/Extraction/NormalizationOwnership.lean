/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.CacheIR

/-! Ownership projection of NormalizedArguments. The single allocation token
is either the initializer's temporary or the duplicate made on transfer; those
allocations are mutually exclusive on admitted executions. Input and scratch
borrows never own that token. Allocator freshness/pairing, memcpy/sort framing,
physical slice validity and machine layout remain primitive obligations. -/
namespace Compiler.Extraction.Cache.NormalizationOwnership

inductive Comparison where
  | lt | le | gt | ge
  deriving DecidableEq, Repr

def Comparison.test (comparison : Comparison) (a b : Nat) : Bool := match comparison with
  | .lt => decide (a < b) | .le => decide (a ≤ b)
  | .gt => decide (b < a) | .ge => decide (b ≤ a)

inductive Origin where
  | input | scratch | allocation
  deriving DecidableEq, Repr
inductive Owner where
  | absent | lookup | caller | released
  deriving DecidableEq, Repr

structure State where
  origin : Origin := .input
  owner : Owner := .absent
  owned : Bool := false
  dead : Bool := false
  invalid : Bool := false
  deriving DecidableEq, Repr

/-- A failed move records a logical ownership violation; it is not a fabricated
native error return. The preservation theorem must exclude every such state. -/
def State.move (state : State) (expected next : Owner) : State :=
  if state.owner = expected then { state with owner := next }
  else { state with invalid := true }

structure Code where
  threshold : Nat
  useScratch : Comparison
  ownTemporary : Comparison
  clearOnTake : Bool
  freeOnDeinit : Bool
  deriving DecidableEq, Repr

inductive Allocation where
  | temporary | duplicate
  deriving DecidableEq, Repr

/-- Private allocator effects are separate from the logical ownership token.
A failed allocation retains its reached effects. Release is non-fallible, as in
native free; physical validity still needs a primitive memory contract. -/
structure Primitives (σ : Type) where
  allocate : Allocation → σ → Bool × σ
  release : State → σ → σ

/-- `none` is allocation failure before the lookup object is initialized.
Commutativity has already been obtained from the source-bound item test. -/
def Code.initWith (code : Code) (commutative : Bool) (length bufferLength : Nat)
    (allocate : σ → Bool × σ) (effects : σ) : Option State × σ :=
  if !commutative || decide (length < code.threshold) then (some {}, effects) else
  if code.useScratch.test length bufferLength then
    (some {
      origin := .scratch
      owned := code.ownTemporary.test length bufferLength
      invalid := decide (bufferLength < length) }, effects)
  else
    let (ok, effects) := allocate effects
    (if ok then some {
      origin := .allocation, owner := .lookup,
      owned := code.ownTemporary.test length bufferLength } else none, effects)

def Code.init (code : Code) (commutative : Bool) (length bufferLength : Nat)
    (allocationSucceeds : Bool) : Option State :=
  (code.initWith commutative length bufferLength (fun (_ : Unit) => (allocationSucceeds, ())) ()).1

/-- Transfer invokes duplication only when the lookup does not own a temporary.
A failed duplicate leaves ownership unchanged while retaining primitive effects. -/
def Code.takeWith (code : Code) (duplicate : σ → Bool × σ) (state : State) (effects : σ) :
    (Bool × State) × σ :=
  if state.owned then
    ((true, { state.move .lookup .caller with owned := if code.clearOnTake then false else state.owned }), effects)
  else
    let (ok, effects) := duplicate effects
    ((ok, if ok then state.move .absent .caller else state), effects)

def Code.take (code : Code) (duplicateSucceeds : Bool) (state : State) : Bool × State :=
  (code.takeWith (fun (_ : Unit) => (duplicateSucceeds, ())) state ()).1

/-- Release observes the live lookup before its ownership update and final
invalidation, matching the native free followed by `self.* = undefined`. -/
def Code.deinitWith (code : Code) (release : State → σ → σ) (state : State) (effects : σ) : State × σ :=
  let (after, effects) := if code.freeOnDeinit && state.owned then
    (state.move .lookup .released, release state effects) else (state, effects)
  ({ after with dead := true }, effects)

def Code.deinit (code : Code) (state : State) : State :=
  (code.deinitWith (fun _ (_ : Unit) => ()) state ()).1

/-- Find/forceEqual use a lookup at most once: end before transfer (cache hit or
an earlier error), transfer ownership downstream, or free a transferred buffer
on a later error. Caller cleanup precedes lookup deinit, matching defer order. -/
inductive Exit where
  | lookup | transfer | cleanup
  deriving DecidableEq, Repr
inductive Outcome where
  | allocationFailure | lookup | transferred | cleaned
  deriving DecidableEq, Repr

def Code.finishWith (code : Code) (p : Primitives σ) (outcome : Outcome) (state : State) (effects : σ) :
    (Outcome × State) × σ :=
  let (state, effects) := code.deinitWith p.release state effects
  ((outcome, state), effects)

/-- Continue with an already initialized lookup at the current effect state.
This boundary is shared by the ownership projection and preparation-aware
execution, so duplication and cleanup never consult an earlier effect state. -/
def Code.continueWith (code : Code) (p : Primitives σ) (exit : Exit) (state : State) (effects : σ) :
    (Outcome × State) × σ :=
  match exit with
  | .lookup => code.finishWith p .lookup state effects
  | .transfer | .cleanup =>
    let ((success, taken), effects) := code.takeWith (p.allocate .duplicate) state effects
    if !success then code.finishWith p .allocationFailure taken effects else
    match exit with
    | .transfer => code.finishWith p .transferred taken effects
    | _ => code.finishWith p .cleaned (taken.move .caller .released) (p.release taken effects)

/-- One interpreter serves both stateful allocation/deallocation and the earlier
Boolean interface. Caller cleanup precedes lookup deinit on the cleanup exit. -/
def Code.runWith (code : Code) (commutative : Bool) (length bufferLength : Nat)
    (p : Primitives σ) (exit : Exit) (effects : σ) : (Outcome × State) × σ :=
  let (lookup, effects) := code.initWith commutative length bufferLength (p.allocate .temporary) effects
  match lookup with
  | none => ((.allocationFailure, { dead := true }), effects)
  | some state => code.continueWith p exit state effects

def Code.run (code : Code) (commutative : Bool) (length bufferLength : Nat)
    (allocationSucceeds duplicateSucceeds : Bool) (exit : Exit) : Outcome × State :=
  (code.runWith commutative length bufferLength
    { allocate := fun site (_ : Unit) => (match site with
        | .temporary => allocationSucceeds | .duplicate => duplicateSucceeds, ()),
      release := fun _ _ => () } exit ()).1

/-- After local lifetime ends, every allocation is either released or belongs
to the caller. No input/scratch borrow is freed and no owned allocation leaks. -/
def Safe (result : Outcome × State) : Prop :=
  result.2.dead = true ∧ result.2.invalid = false ∧
    if result.1 = .transferred then result.2.owner = .caller
    else result.2.owner = .absent ∨ result.2.owner = .released

end Compiler.Extraction.Cache.NormalizationOwnership
