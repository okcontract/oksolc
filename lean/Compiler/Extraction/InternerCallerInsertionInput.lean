/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerPublicationInput
import Compiler.Extraction.InternerInsertionPreparation
import Compiler.Extraction.InternerGraphInitOwnership

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- Native insertion's entry facts, derived at the caller's actual take boundary.
The origin retains the detached outer lookup and all pre-normalization storage.
This does not assume preservation across intervening recursive child calls. -/
structure CallerInput (allocator : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (request : Interner.Request) (values : List NodeId) (input : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (before : World (Publication.Effects σ)) (taken : OwnedCall.State (Publication.Effects σ))
    (normalized : ArgumentSlice) (remaining : Handle) : Prop where
  origin : Caller.Origin allocator source request values before taken normalized remaining
  item : AssemblyClone.NativeFields.Represents taken.world.memory.memory itemSource input
  keyed : keyCode.run input.item normalized.items request.sequence = some key
  publication : Publication.Input allocator source key normalized taken.world
  keys : taken.world.memory.effects.keys = before.memory.effects.keys
  live : OwnedKeys.Live allocator ⟨taken.world.memory.effects.keys, taken.world.memory.heap⟩
  unique : OwnedKeys.Unique taken.world.memory.effects.keys
  fresh : ∀ query entry, taken.world.memory.effects.keys query = some entry → query.arguments ≠ [] →
    normalized.address ≠ entry.address

/-- The source-bound stack allocation, initializer, take and makeKey establish
the incoming argument owner and native item reads used by insertion. Initial
key invariants are transported, not assumed again at the reached entry. -/
theorem caller_input (host : External σ) (budget allocator : Nat) (source : View)
    (itemSource : Compiler.ZigAir.Memory.Address) (request : Interner.Request)
    (input : AssemblyClone.NativeFields.ItemValue) (before : World (Publication.Effects σ))
    (memory : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (values : List NodeId) (prepared taken : OwnedCall.State (Publication.Effects σ)) (key : Key)
    (good : Good source request.arguments before) (admitted : Admitted host)
    (represented : AssemblyClone.NativeFields.Represents before.memory.memory itemSource input)
    (sameItem : input.item = request.item)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (initialized : Caller.initLookup (Publication.external host) budget allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))
    (transferred : take (Publication.external host) allocator prepared = (.ok (), taken))
    (made : Interner.makeKey request values = .ok key)
    (live : OwnedKeys.Live allocator ⟨before.memory.effects.keys, before.memory.heap⟩)
    (unique : OwnedKeys.Unique before.memory.effects.keys)
    (sourceApart : ∀ old, before.memory.effects.keys key = some old → key.arguments ≠ [] →
      source.length ≠ 0 → source.allocation ≠ old.address) :
    ∃ normalized remaining, CallerInput allocator source itemSource request values input key before taken normalized remaining := by
  obtain ⟨normalized, remaining, origin, keys, publication⟩ :=
    Publication.caller_input host budget allocator source request before memory pointer values prepared taken key
      good admitted allocated initialized transferred made (live key) sourceApart
  obtain ⟨cell, found⟩ := represented.live
  refine ⟨normalized, remaining, origin, represented.frame ((origin.memory _ _ found).trans found.symm),
    ?_, publication, keys, ?_, ?_, ?_⟩
  · rw [sameItem, origin.aligned]
    unfold Interner.makeKey at made
    cases actual : keyCode.run request.item values request.sequence with
    | none => simp [actual] at made
    | some produced => simp [actual] at made; cases made; rfl
  · intro query entry stored
    rw [keys] at stored
    rcases live query entry stored with empty | owned
    · exact Or.inl empty
    · exact Or.inr (origin.registry _ _ owned)
  · rw [keys]; exact unique
  · intro query entry stored nonempty
    rw [keys] at stored
    exact origin.fresh _ _ ((live query entry stored).resolve_left nonempty)

/-- A successful native empty-map projection determines the whole key table;
it cannot validate a caller-supplied ownership table. -/
theorem initialized_keys (runtimeSafety : Bool) (memory : Compiler.ZigAir.Memory.State)
    (owner : Compiler.ZigAir.Memory.Address) (table : OwnedKeys.Table)
    (observed : GraphInit.Ownership.keys runtimeSafety memory owner = .ok table) :
    table = fun _ => none := by
  unfold GraphInit.Ownership.keys at observed
  cases actual : Compiler.Extraction.ExpressionMap.Initialization.observeEmpty runtimeSafety memory owner with
  | error fault => simp [actual, bind, Except.bind] at observed
  | ok result => simpa only [actual, bind, Except.bind, Except.ok.injEq] using observed.symm

/-- Establish insertion entry from the same native initializer and caller
prefix. The function arguments still require their native input representation;
initial key ownership, validity and source/key separation are derived here. -/
theorem initialized_caller_input (host : External σ) (budget allocator container : Nat) (runtimeSafety : Bool)
    (raw : Session σ) (ownerCell : Compiler.ZigAir.Memory.Allocation) (sentinel : Compiler.ZigAir.Memory.Address)
    (meaning : Meaning) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (request : Interner.Request) (input : AssemblyClone.NativeFields.ItemValue) (before : World (Publication.Effects σ))
    (memory : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (values : List NodeId) (prepared taken : OwnedCall.State (Publication.Effects σ)) (key : Key)
    (initial : Valid raw) (found : raw.memory.heap.lookup container = some ownerCell)
    (typed : ownerCell.type = RepresentativeArray.Owner.viewType runtimeSafety)
    (writable : ownerCell.writable = true) (stack : ownerCell.stack = true)
    (initializedOwner : GraphInit.Ownership.run runtimeSafety allocator raw ⟨container, 0⟩ sentinel = .ok (allocator, before))
    (arguments : Represents before.memory.memory source request.arguments) (admitted : Admitted host)
    (represented : AssemblyClone.NativeFields.Represents before.memory.memory itemSource input)
    (sameItem : input.item = request.item)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (initialized : Caller.initLookup (Publication.external host) budget allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))
    (transferred : take (Publication.external host) allocator prepared = (.ok (), taken))
    (made : Interner.makeKey request values = .ok key) :
    ∃ normalized remaining,
      GraphInit.Ownership.Established runtimeSafety allocator raw before container sentinel meaning ∧
      CallerInput allocator source itemSource request values input key before taken normalized remaining := by
  obtain ⟨world, executed, established⟩ := GraphInit.Ownership.initialize_verified runtimeSafety allocator raw container
    ownerCell sentinel meaning initial found typed writable stack
  have same := (Prod.mk.inj (Except.ok.inj (executed.symm.trans initializedOwner))).2
  subst world
  have empty := initialized_keys runtimeSafety before.memory.memory ⟨container, 0⟩ _ established.nativeKeys
  obtain ⟨normalized, remaining, entry⟩ := caller_input host budget allocator source itemSource request input before memory
    pointer values prepared taken key ⟨established.valid, arguments⟩ admitted represented sameItem allocated initialized
    transferred made established.live established.unique (by intro old impossible; rw [empty] at impossible; cases impossible)
  exact ⟨normalized, remaining, established, entry⟩

variable {σ : Type} {allocator : Nat} {source : View} {itemSource : Compiler.ZigAir.Memory.Address}
  {request : Interner.Request} {values : List NodeId} {nativeItem : AssemblyClone.NativeFields.ItemValue}
  {key : Key} {before : World (Publication.Effects σ)} {taken : OwnedCall.State (Publication.Effects σ)}
  {normalized : ArgumentSlice} {remaining : Handle}

/-- Every represented native allocation, including the graph owner and backing,
can be read at insertion entry with its original contents and permissions. -/
theorem CallerInput.native_frame
    (input : CallerInput allocator source itemSource request values nativeItem key before taken normalized remaining)
    (id : Nat) (cell : Compiler.ZigAir.Memory.Allocation)
    (found : before.memory.memory.heap.lookup id = some cell) :
    taken.world.memory.memory.heap.lookup id = before.memory.memory.heap.lookup id :=
  (input.origin.memory id cell found).trans found.symm

/-- Outer lookup cleanup remains a no-op after insertion has consumed the
normalized allocation. It must not require that allocation to remain live. -/
theorem CallerInput.outer_deinit
    (input : CallerInput allocator source itemSource request values nativeItem key before taken normalized remaining)
    (host : External σ) (reached : World (Publication.Effects σ)) (handedOff : Bool) :
    deinit (Publication.external host) allocator ⟨reached, { taken.scope with handedOff }⟩ =
      (.ok (), ⟨reached, { taken.scope with lookup := none, handedOff }⟩) :=
  input.origin.deinit (Publication.external host) allocator source request values before taken normalized remaining reached handedOff

/-- Once the production caller has handed the normalized slice to insertion,
its outer defers do not release it again. Ordinary outcomes close the detached
lookup; a semantic rejection retains the reached locals without invented unwind. -/
theorem CallerInput.finish_insert
    (input : CallerInput allocator source itemSource request values nativeItem key before taken normalized remaining)
    (host : External σ) (reached : World (Publication.Effects σ)) (result : Except OwnedCall.Fault α) :
    finish (Publication.external host) allocator result ⟨reached, { taken.scope with handedOff := true }⟩ =
      if ordinary result then (result, ⟨reached, { taken.scope with lookup := none, handedOff := true }⟩)
      else (result, ⟨reached, { taken.scope with handedOff := true }⟩) := by
  unfold finish
  split
  · simp only [cleanup, ↓reduceIte, input.outer_deinit host reached true]
  · rfl

/-- Execute the caller's handoff before invoking insertion with its actual
normalized slice. Cleanup uses that insertion's reached world and result,
including semantic rejections; no callback preservation contract is assumed. -/
theorem CallerInput.handoff_insert
    (input : CallerInput allocator source itemSource request values nativeItem key before taken normalized remaining)
    (host : External σ) (insert : ArgumentSlice → GraphAction (Publication.Effects σ) α) :
    (let (result, reached) := (do handoff; graph insert : Action (Publication.Effects σ) α) taken
     finish (Publication.external host) allocator result reached) =
      (let (result, reached) := insert normalized taken.world
       if ordinary result then (result, ⟨reached, { taken.scope with lookup := none, handedOff := true }⟩)
       else (result, ⟨reached, { taken.scope with handedOff := true }⟩)) := by
  cases taken with
  | mk world scope =>
    have aligned := input.origin.scope
    change scope = ⟨some remaining, some normalized, false⟩ at aligned
    subst scope
    exact finish_handoff (Publication.external host) allocator remaining normalized world insert input.origin.detached

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
