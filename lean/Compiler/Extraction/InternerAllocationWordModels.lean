/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerAllocationRecursiveModels
import Compiler.Extraction.InternerNativeSuffixWords
import Compiler.Extraction.InternerScopePreservation

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Recursive Caller.ProtocolTrace Interner.InvocationTrace

/-- A protocol checkpoint changes the cursor only, including when it rejects.
The continuation must be safe for every accepted identity and reached cursor. -/
private theorem checkpoint_bind_safe (meaning : Meaning) (action : Interner.Action α)
    (next : α → Interner.Action β) (before : Interner.Heap) (post : β → Interner.Heap → Prop)
    (valid : Interner.Invariant meaning before)
    (frame : (action before).2 = { before with allocationCursor := (action before).2.allocationCursor })
    (continuation : ∀ value cursor, Interner.Safe meaning (next value) { before with allocationCursor := cursor } post) :
    Interner.Safe meaning (action >>= next) before post := by
  apply Interner.Safe.bind meaning before action next
    (fun _ after => after = { before with allocationCursor := after.allocationCursor }) post
  · intro result after ran
    rw [ran] at frame
    dsimp only at frame
    refine ⟨?_, ?_, ?_⟩
    · rw [frame]; exact valid.with_cursor _
    · rw [frame]; exact fun _ _ found => found
    · cases result with
      | error error => trivial
      | ok value => exact frame
  · intro value after _ _ retained
    rw [retained]
    exact continuation value _

/-- Entry checkpoints require no stream-validity hypothesis for word safety.
A foreign or missing slot rejects without changing graph observations. -/
theorem enter_bind_safe (meaning : Meaning) (stream : List ProtocolEvent)
    (next : Nat × Nat → Interner.Action α) (before : Interner.Heap) (post : α → Interner.Heap → Prop)
    (valid : Interner.Invariant meaning before)
    (continuation : ∀ ids cursor, Interner.Safe meaning (next ids) { before with allocationCursor := cursor } post) :
    Interner.Safe meaning (enter stream >>= next) before post :=
  checkpoint_bind_safe meaning (enter stream) next before post valid
    (by unfold enter; split <;> rfl) continuation

/-- Fixed input insertion is safe for all protocol streams. A checkpoint or
callback rejection keeps the actual reached graph; it is never a rollback axiom. -/
theorem insertionReplay_safe (input : AssemblyClone.NativeFields.ItemValue) (normalized : ArgumentSlice)
    (meaning : Meaning) (key : Key) (deterministic : Bool) (stream : List ProtocolEvent)
    (mismatch : Insertion.Native.Fault) (sequence : BitVec 32) (before : Interner.Heap) (value : Word)
    (valid : Interner.Invariant meaning before)
    (pushes : input.item.kind = 2#32 → Insertion.Native.PushValues meaning)
    (bound : keyCode.run input.item normalized.items sequence = some key)
    (evaluated : key.eval meaning before.read = some value) :
    Interner.Safe meaning (insertionReplay input normalized meaning key deterministic stream mismatch)
      before (fun id after => after.read id = some value) := by
  apply checkpoint_bind_safe meaning (insertionRead stream) _ before _ valid
  · unfold insertionRead; split <;> rfl
  · intro ids cursor
    exact Insertion.Native.allocationReplay_safe input key normalized meaning deterministic ids.1
      (insertions stream) mismatch sequence _ value (valid.with_cursor cursor) pushes bound evaluated

/-- The publication trace selects only a resource outcome. The shared cache
proof still checks the supplied key and returned representative's equal value. -/
theorem publish_safe (meaning : Meaning) (stream : List ProtocolEvent) (key : Key) (id : NodeId)
    (before : Interner.Heap) (value : Word) (valid : Interner.Invariant meaning before)
    (evaluated : key.eval meaning before.read = some value) (found : before.read id = some value) :
    Interner.Safe meaning (Interner.InvocationTrace.publish stream key id) before (fun _ _ => True) := by
  intro result after ran
  unfold Interner.InvocationTrace.publish at ran
  split at ran
  · split at ran
    · cases called : Interner.publish _ key id before with
      | mk outcome reached =>
        rw [called] at ran
        cases ran
        have safe := Interner.publish_safe meaning _ key id before value valid evaluated found result reached called
        exact ⟨safe.1.with_cursor _, safe.2.1, by cases result <;> trivial⟩
    · cases ran
      exact ⟨valid.with_cursor _, fun _ _ actual => actual, trivial⟩
  · cases ran
    exact ⟨valid.with_cursor _, fun _ _ actual => actual, trivial⟩

/-- A request's key domain binds the original item, normalized operands and
sequence. It does not constrain stream outcomes or select a final state. -/
def RequestKey (request : Interner.Request) (key : Key) : Prop :=
  keyCode.run request.item key.arguments request.sequence = some key

theorem request_key (request : Interner.Request) (args : List NodeId) (key : Key)
    (made : Interner.makeKey request args = .ok key) : RequestKey request key := by
  unfold Interner.makeKey at made
  cases encoded : keyCode.run request.item args request.sequence with
  | none => simp [encoded] at made
  | some produced =>
    simp only [encoded, Except.ok.injEq] at made
    subst produced
    rw [RequestKey, (key_inputs request.item args request.sequence key encoded).1]
    exact encoded

/-- Native caller admission binds the represented item's semantics to the
request. The fixed insertion identity is supplied at the actual caller entry. -/
theorem nativeInputGraphReplay_contracts (meaning : Meaning) (seed : Interner.Primitives)
    (request : Interner.Request) (native : AssemblyClone.NativeFields.ItemValue) (incoming : Nat)
    (stream : List ProtocolEvent) (mismatch : Insertion.Native.Fault)
    (sameItem : native.item = request.item)
    (pushes : request.item.kind = 2#32 → Insertion.Native.PushValues meaning) :
    Interner.Scoped.GraphContractsFor meaning
      (inputGraphReplay seed native incoming meaning stream mismatch) (RequestKey request) where
  insert := by
    intro key bound deterministic before value valid evaluated
    exact insertionReplay_safe native ⟨incoming, key.arguments⟩ meaning key deterministic
      stream mismatch request.sequence before value valid (by simpa only [sameItem] using pushes)
      (by simpa only [sameItem] using bound) evaluated
  publish := publish_safe meaning stream

/-- Constructor preparation specializes the same native caller contracts. -/
theorem inputGraphReplay_contracts (meaning : Meaning) (seed : Interner.Primitives)
    (request : Interner.Request) (debug : AssemblyItem.Fields.Values) (incoming : Nat)
    (stream : List ProtocolEvent) (mismatch : Insertion.Native.Fault)
    (pushes : request.item.kind = 2#32 → Insertion.Native.PushValues meaning) :
    Interner.Scoped.GraphContractsFor meaning
      (inputGraphReplay seed (input request.item debug) incoming meaning stream mismatch) (RequestKey request) :=
  nativeInputGraphReplay_contracts meaning seed request (input request.item debug) incoming stream mismatch rfl pushes

/-- Word preservation for the caller's fixed native input model. The complete
caller and constructor models share this proof, with their own allocation cursor. -/
theorem callerModel_safe (env : AddressMask.Environment) (other : Meaning) (usizeBits : Nat)
    (seed : Interner.Primitives) (stream : List ProtocolEvent) (mismatch : Insertion.Native.Fault)
    (children : Associative.Constructors AssemblyItem.Fields.Values)
    (correct : Associative.ConstructorSound (Dispatch.wordBaseMeaning env other) children)
    (addresses : AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) children.operation)
    (shifts : ArithmeticShift.Constructs (AddressMask.addressMeaning env other) children.operation)
    (debug : AssemblyItem.Fields.Values) (native : AssemblyClone.NativeFields.ItemValue)
    (incoming : Nat) (request : Interner.Request) (sameItem : native.item = request.item)
    (before : Interner.Heap) (value : Word) (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before)
    (pushes : request.item.kind = 2#32 → Insertion.Native.PushValues other)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.read request.arguments request.sequence = some value) :
    Interner.Safe (Dispatch.wordDispatchMeaning env other)
      (Interner.Scoped.find (resources stream (.preparation .incomplete))
        (dispatchModel (inputGraphReplay seed native incoming (Dispatch.wordDispatchMeaning env other) stream mismatch)
          children usizeBits debug) request)
      before (fun id after => after.read id = some value) := by
  apply Interner.Scoped.find_safe_for (Dispatch.wordBaseMeaning env other) _
    (fun ids => InsertionSort.sortIds_perm ids) _ (RequestKey request) _ request (request_key request) before value valid evaluated
  have graph := nativeInputGraphReplay_contracts (Dispatch.wordDispatchMeaning env other) seed request native
    incoming stream mismatch sameItem (fun h => pushes h)
  refine ⟨⟨graph.insert, graph.publish⟩, ?_⟩
  intro key _ operation heap expected invariant denotation
  exact Dispatch.default_key_simplify_safe env other (Interner.representativeReads heap) children
    correct addresses shifts heap invariant (Interner.representative_reads_sound _ heap invariant)
    key operation expected debug usizeBits denotation

/-- One scoped constructor step, using the exact fixed replay model consumed by
native correspondence. Only proper-child word laws remain in this step theorem. -/
theorem requestModel_safe (env : AddressMask.Environment) (other : Meaning) (usizeBits : Nat)
    (seed : Interner.Primitives) (stream : List ProtocolEvent) (mismatch : Insertion.Native.Fault)
    (children : Associative.Constructors AssemblyItem.Fields.Values)
    (correct : Associative.ConstructorSound (Dispatch.wordBaseMeaning env other) children)
    (addresses : AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) children.operation)
    (shifts : ArithmeticShift.Constructs (AddressMask.addressMeaning env other) children.operation)
    (debug : AssemblyItem.Fields.Values) (initialId : Nat) (request : Interner.Request)
    (before : Interner.Heap) (value : Word) (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before)
    (pushes : request.item.kind = 2#32 → Insertion.Native.PushValues other)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.read request.arguments request.sequence = some value) :
    Interner.Safe (Dispatch.wordDispatchMeaning env other)
      (requestModel (Dispatch.wordDispatchMeaning env other) usizeBits seed stream mismatch children debug initialId request)
      before (fun id after => after.read id = some value) :=
  callerModel_safe env other usizeBits seed stream mismatch children correct addresses shifts debug
    (input request.item debug) (initialId + 2) request rfl before value valid pushes evaluated

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
