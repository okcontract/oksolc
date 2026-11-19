/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCheckpointRecursiveMiss

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Native.CheckpointEntry
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ConstructorItem ConstructorItem.NativeRecursion Recursive Interner.InvocationTrace

/-- A represented native item and the actual caller prefix supply the reached
miss frame. Complete child replay supplies its correspondence; no constructor
preparation, selected child result or final graph is assumed at this boundary. -/
theorem caller_induction_from_sources (depth : Nat)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits : Nat) (meaning : Meaning)
    (base : PairInput.Context (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (outerOps : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (outerAllocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (outerBase : PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (outerGrowth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent)))
    (allocators : outerBase.allocator = base.allocator)
    (debug : AssemblyItem.Fields.Values) (source : View) (request : Interner.Request)
    (before : ChildTrace.TracedWorld σ ProtocolEvent)
    (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue)
    (memory : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (data : Compiler.ZigAir.Memory.Address) (capacity : Nat) (rows : List Storage.Cell)
    (parent : World (Publication.Effects σ) → Prop)
    (models : List ProtocolEvent → AllocationTrace.Models) (seed : Interner.Primitives)
    (stream leading trailing : List ProtocolEvent) (mismatch : Insertion.Native.Fault)
    (stack : Enclosing safety base.allocator owner parent)
    (facts : NativeGraph.Facts safety outerBase.allocator owner data capacity before rows)
    (represented : Represents before.memory.memory source request.arguments)
    (privateSource : Caller.SourcePrivate source before.memory.effects.keys)
    (array : ArraySource source before.memory.memory)
    (retained : ∀ after : ChildTrace.TracedWorld σ ProtocolEvent, Valid after.memory → after.graph = before.graph →
      Retains before after → parent (ChildTrace.erase after))
    (item : AssemblyClone.NativeFields.Represents before.memory.memory address native)
    (sameItem : native.item = request.item)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (admitted : Admitted ops.arguments) (outerAdmitted : Admitted outerOps.arguments)
    (typed : AssemblyItem.Initializers.DebugTyped debug)
    (sources : AllocationTrace.RecursiveSources ops allocate safety owner usizeBits meaning base growth debug depth models) :
    let children := AllocationTrace.children ops allocate safety owner meaning base growth usizeBits depth
    let observations := ChildTrace.liftObservations
      (ProtocolTrace.observe (AllocationTrace.unfold ops allocate safety owner meaning base growth usizeBits depth))
    let p := physical outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits children debug source address native
    let ports := AllocationTrace.graphObservations outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
      children observations debug source address native
    let buffer : View := ⟨before.memory.memory.nextId, 0, 2⟩
    let entry := ConstructorItem.ProtocolTrace.start {before with memory := {before.memory with memory}} leading
    let body := findBody (Publication.external outerOps.arguments) outerBase.budget outerBase.allocator p outerBase.queries
      ports source buffer request entry
    let actual := find (Publication.external outerOps.arguments) outerBase.budget outerBase.allocator p outerBase.queries
      ports source buffer request entry
    ordinary body.1 = true → actual.2.events ++ trailing = stream →
    Induction outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits children observations debug
      source address native request (AllocationTrace.streamReplay stream (models stream)) seed
      (before.memory.memory.nextId + 1) stream mismatch buffer entry trailing := by
  intro children observations p ports buffer entry body actual completed joined
  intro values key deterministic normalized taken room initialized classified keyed absent transferred
  have nativeInitialized : Caller.initLookup (Publication.external outerOps.arguments) outerBase.budget outerBase.allocator source
      buffer request entry.native = (.ok values, normalized.2.native) := Prod.ext initialized rfl
  have nativeTaken : OwnedCall.take (Publication.external outerOps.arguments) outerBase.allocator normalized.2.native =
      (.ok (), taken.2.native) := Prod.ext transferred rfl
  obtain ⟨owned, remaining, input⟩ := Insertion.Native.caller_input outerOps.arguments outerBase.budget outerBase.allocator
    source address request native before memory pointer values normalized.2.native taken.2.native key
    ⟨facts.valid, represented⟩ outerAdmitted item sameItem allocated nativeInitialized nativeTaken keyed
    facts.live facts.unique (privateSource key)
  have parentTaken := retained taken.2.native.world input.origin.held.1.1 input.origin.graph
    ⟨input.keys, input.origin.memory, input.origin.registry⟩
  have frame : CallFrame safety base.allocator owner rows source request.arguments owned address native parent
      (ChildTrace.erase taken.2.native.world) := by
    have held := CallFrame.caller input facts privateSource array (fun world => parent (ChildTrace.erase world)) parentTaken
    rw [allocators] at held
    exact (CallFrame.mapAllocator_iff Prod.fst).mpr held
  obtain ⟨commutative, decoded⟩ : ∃ commutative, Interner.Scoped.commutative request.item = .ok commutative := by
    cases decoded : Interner.Scoped.commutative request.item with
    | error fault => simp only [Caller.initLookup, decoded] at nativeInitialized; cases nativeInitialized
    | ok commutative => exact ⟨commutative, rfl⟩
  obtain ⟨lookup, captured, recording⟩ := initialized_taken_recorded (Publication.external outerOps.arguments)
    outerBase.budget outerBase.allocator commutative source request before memory pointer values normalized.2.native taken.2.native leading
    meaning (fun _ => none) 0 facts.valid represented allocated decoded
    (Publication.external_admitted outerOps.arguments outerAdmitted) nativeInitialized nativeTaken
  dsimp only at recording
  obtain ⟨slice, handle, locals, lifetime, contents, unowned, caller, _, _, takeRecord, _⟩ := recording
  obtain ⟨token, tokenUnowned, tokenCaller, tokenShape⟩ : ∃ token : NormalizationOwnership.State,
      token.owned = false ∧ token.owner = .caller ∧
        taken.2.tokens = {lookup := some token, items := handle.values, phase := .cleanup} :=
    ⟨_, unowned, caller, congrArg (fun ran => ran.2.tokens) takeRecord⟩
  have sliceSame : owned = slice := Option.some.inj (congrArg Local.slice (input.origin.scope.symm.trans locals))
  rw [sliceSame] at frame
  have reduced := findBody_taken (Publication.external outerOps.arguments) outerBase.budget outerBase.allocator p outerBase.queries
    ports source buffer request key deterministic values entry normalized.2 taken.2 room (Prod.ext initialized rfl)
    classified keyed absent (Prod.ext transferred rfl)
  change body = _ at reduced
  have bodyCompleted := completed
  change ordinary body.1 = true at bodyCompleted
  rw [reduced] at bodyCompleted
  have bodyJoined : (finish (Publication.external outerOps.arguments) outerBase.allocator body.1 body.2).2.events ++ trailing = stream := joined
  rw [reduced] at bodyJoined
  have checked := miss_from_recursive_sources depth ops allocate safety owner usizeBits meaning base growth
    outerOps outerAllocate outerBase outerGrowth allocators debug source buffer address native request key slice deterministic
    taken.2.native.world handle token rows parent models seed (before.memory.memory.nextId + 1) stream taken.2.events trailing mismatch
    stack admitted typed frame (by simpa only [sliceSame] using input.publication.aligned)
    lifetime.detached tokenUnowned tokenCaller sources
  have shape : (⟨⟨taken.2.native.world, ⟨some handle, some slice, false⟩⟩,
      {lookup := some token, items := handle.values, phase := .cleanup}, taken.2.events⟩ : Recorded _) = taken.2 := by
    rw [← locals, ← tokenShape]
  rw [shape] at checked
  exact checked bodyCompleted bodyJoined

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Native.CheckpointEntry
