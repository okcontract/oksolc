/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeInsertionModel
import Compiler.Extraction.InternerNativeDispatchFrames
import Compiler.Extraction.InternerNativeParentPublication
import Compiler.Extraction.InternerNativeParentEntry
import Compiler.Extraction.InternerNativeMissFrame
import Compiler.Extraction.InternerNativeMissWords
import Compiler.Extraction.InternerTakenSite

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray Recursive

/-- Simplifier failure closes the actual reached normalized owner and detached
lookup. Native correspondence follows from graph custody and the shared cleanup
proof; only the separate enclosing frame needs its local release law. Semantic
rejections still retain their reached state and do not invent unwinding. -/
theorem CallFrame.failure {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {world : World (Publication.Effects σ)}
    (frame : CallFrame safety allocator owner rows source values normalized address native parent world)
    (host : External σ) (lookup : Handle) (detached : lookup.owned = none) (fault : Fault)
    (releaseParent : ∀ after, free (Publication.external host) allocator normalized world.memory = (.ok (), after) →
      parent { world with memory := after }) :
    Returns (GraphFrame safety allocator owner rows parent)
      (OwnedCall.finish (Publication.external host) allocator (.error fault : Except Fault NodeId)
        ⟨world, ⟨some lookup, some normalized, false⟩⟩) (.error fault) world.graph := by
  cases completed : ordinary (.error fault : Except Fault NodeId) with
  | false => simp only [Returns, OwnedCall.finish, completed, Bool.false_eq_true, ↓reduceIte, false_implies]
  | true =>
    obtain ⟨added, data, capacity, facts, custody, _⟩ := frame.1.1
    obtain ⟨after, finished, post⟩ := finish_taken (Publication.external host) allocator source values normalized lookup
      ⟨world, ⟨some lookup, some normalized, false⟩⟩ (.error fault : Except Fault NodeId) completed
      rfl detached rfl frame.1.2.1 (fun _ => frame.1.2.2.1) frame.1.2.2.2
    have preserved := facts.cleanup_post host normalized post (fun _ => frame.1.2.2.1)
      (fun _ => custody.apart) (fun _ => custody.operands)
    have parentKept := releaseParent after.world.memory (post.freed rfl).1
    have reached : after.world = { world with memory := after.world.memory } :=
      congrArg (fun graph => (⟨graph, after.world.memory⟩ : World (Publication.Effects σ))) post.graph
    rw [finished]
    exact fun _ => ⟨post.closed, ⟨⟨added, data, capacity, preserved.1⟩, reached ▸ parentKept⟩, rfl, post.graph⟩

/-- Complete a failed proper child under an actual live parent call. The
child's original take provenance and current private custody discharge the
parent's native release law. Only the next outer predicate needs a release
law; the source failure and closed-scope return use the shared completion. -/
theorem CallFrame.failure_parent {safety : Bool} {allocator owner : Nat}
    {rows parentRows : List Storage.Cell} {source parentSource : View}
    {request : Interner.Request} {values parentValues : List NodeId}
    {normalized parentNormalized : ArgumentSlice} {lookup : Handle}
    {address parentAddress : Compiler.ZigAir.Memory.Address}
    {native parentNative : AssemblyClone.NativeFields.ItemValue}
    {outer : World (Publication.Effects σ) → Prop} {before world : World (Publication.Effects σ)}
    {taken : State (Publication.Effects σ)}
    (origin : Caller.Origin allocator source request values before taken normalized lookup)
    (initial : CallFrame safety allocator owner parentRows parentSource parentValues parentNormalized
      parentAddress parentNative outer before)
    (frame : CallFrame safety allocator owner rows source request.arguments normalized address native
      (CallFrame safety allocator owner parentRows parentSource parentValues parentNormalized parentAddress parentNative outer) world)
    (host : External σ) (fault : Fault)
    (releaseOuter : ∀ after, free (Publication.external host) allocator normalized world.memory = (.ok (), after) →
      outer { world with memory := after }) :
    Returns (GraphFrame safety allocator owner rows
      (CallFrame safety allocator owner parentRows parentSource parentValues parentNormalized parentAddress parentNative outer))
      (OwnedCall.finish (Publication.external host) allocator (.error fault : Except Fault NodeId)
        ⟨world, ⟨some lookup, some normalized, false⟩⟩) (.error fault) world.graph := by
  obtain ⟨added, data, capacity, facts, custody, _⟩ := frame.1.1
  exact frame.failure host lookup origin.detached fault
    (CallFrame.release origin initial frame.parent host facts.projected custody releaseOuter)

/-- Publication completion follows the reached graph custody, actual probe
decision and shared publication/cleanup proofs. The logical callback must select
that same decision; the separate outer predicate needs only local frame laws. -/
theorem CallFrame.publication_action {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {world : World (Publication.Effects σ)}
    (frame : CallFrame safety allocator owner rows source values normalized address native parent world)
    (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ) (key : Key) (id : NodeId)
    (lookup : Handle) (detached : lookup.owned = none) (aligned : key.arguments = normalized.items)
    (publish : Key → NodeId → Interner.Action Unit)
    (matched : publish key id world.graph =
      Interner.publish (hostProbe key (Publication.forget world.memory)).1 key id world.graph)
    (publicationParent : parent (Publication.publish hostProbe host allocator source key normalized id world).2)
    (releaseParent : ∀ before after currentRows, parent before →
      before.graph.representatives = some currentRows →
      Caller.GraphCustody allocator normalized currentRows before.memory →
      free (Publication.external host) allocator normalized before.memory = (.ok (), after) →
        parent { before with memory := after }) :
    let ran := (do
      let _ ← graph (fun slice => Publication.publish hostProbe host allocator source key slice id)
      let _ ← handoff
      pure id : Action (Publication.Effects σ) NodeId) ⟨world, ⟨some lookup, some normalized, false⟩⟩
    let logical := (do let _ ← publish key id; pure id : Interner.Action NodeId) world.graph
    Returns (GraphFrame safety allocator owner rows parent)
      (OwnedCall.finish (Publication.external host) allocator ran.1 ran.2)
      (logical.1.mapError Fault.language) logical.2 := by
  obtain ⟨added, data, capacity, facts, custody, privateSource⟩ := frame.1.1
  cases response : hostProbe key (Publication.forget world.memory) with
  | mk accepted effects =>
    obtain ⟨published, after, called, _, finished, kept, post, _, _, privateOwned⟩ := facts.finish_publication
      (before := ⟨world, ⟨some lookup, some normalized, false⟩⟩)
      hostProbe host source values key normalized lookup id accepted effects rfl detached aligned
      frame.1.2 custody privateSource response
    have projected := Publication.publish_projection hostProbe host allocator source key normalized id world
      accepted effects facts.valid (custody.publication source key aligned privateSource facts.live) frame.1.2.2.1 response
    simp only [called] at projected publicationParent
    have parentKept : parent after.world := by
      cases outcome : accepted with
      | true => simpa only [post.handedOff (by simp only [outcome])] using publicationParent
      | false =>
        have freed := releaseParent published after.world.memory (rows ++ added) publicationParent
          (by rw [← post.graph]; exact kept.projected) (privateOwned outcome)
          (post.freed (by simp only [outcome])).1
        have reached : after.world = { published with memory := after.world.memory } :=
          congrArg (fun graph => (⟨graph, after.world.memory⟩ : World (Publication.Effects σ))) post.graph
        exact reached ▸ freed
    have graphEqual := congrArg Prod.snd projected
    cases accepted <;>
      simp only [bind, Effect.bind, graph, called, handoff, Pure.pure, Effect.pure, Bool.false_eq_true, ↓reduceIte,
        matched, response, Interner.publish, Except.mapError] at finished graphEqual ⊢ <;>
      rw [finished] <;>
      exact fun _ => ⟨post.closed, ⟨⟨added, data, capacity, kept⟩, parentKept⟩, rfl, post.graph.trans graphEqual⟩

/-- The logical-model client uses the same actual publication proof. -/
theorem CallFrame.publication {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {world : World (Publication.Effects σ)}
    (frame : CallFrame safety allocator owner rows source values normalized address native parent world)
    (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ) (key : Key) (id : NodeId)
    (lookup : Handle) (detached : lookup.owned = none) (aligned : key.arguments = normalized.items)
    (model : Interner.Primitives)
    (matched : model.publish key id world.graph =
      Interner.publish (hostProbe key (Publication.forget world.memory)).1 key id world.graph)
    (publicationParent : parent (Publication.publish hostProbe host allocator source key normalized id world).2)
    (releaseParent : ∀ before after currentRows, parent before →
      before.graph.representatives = some currentRows →
      Caller.GraphCustody allocator normalized currentRows before.memory →
      free (Publication.external host) allocator normalized before.memory = (.ok (), after) →
        parent { before with memory := after }) :
    let ran := (do
      let _ ← graph (fun slice => Publication.publish hostProbe host allocator source key slice id)
      let _ ← handoff
      pure id : Action (Publication.Effects σ) NodeId) ⟨world, ⟨some lookup, some normalized, false⟩⟩
    let logical := (do let _ ← model.publish key id; pure id : Interner.Action NodeId) world.graph
    Returns (GraphFrame safety allocator owner rows parent)
      (OwnedCall.finish (Publication.external host) allocator ran.1 ran.2)
      (logical.1.mapError Fault.language) logical.2 :=
  frame.publication_action hostProbe host key id lookup detached aligned model.publish matched publicationParent releaseParent

/-- Complete publication by a proper child with its actual enclosing call.
The native publication and release laws are derived from original provenance
and reached frames; only the next outer predicate retains local laws. -/
theorem CallFrame.publication_parent
    {safety : Bool} {allocator owner : Nat} {rows parentRows : List Storage.Cell}
    {source parentSource : View} {request : Interner.Request} {values parentValues : List NodeId}
    {normalized parentNormalized : ArgumentSlice} {lookup : Handle}
    {address parentAddress : Compiler.ZigAir.Memory.Address}
    {native parentNative : AssemblyClone.NativeFields.ItemValue}
    {outer : World (Publication.Effects σ) → Prop} {before world : World (Publication.Effects σ)}
    {taken : State (Publication.Effects σ)}
    (origin : Caller.Origin allocator source request values before taken normalized lookup)
    (initial : CallFrame safety allocator owner parentRows parentSource parentValues parentNormalized
      parentAddress parentNative outer before)
    (frame : CallFrame safety allocator owner rows source request.arguments normalized address native
      (CallFrame safety allocator owner parentRows parentSource parentValues parentNormalized parentAddress parentNative outer) world)
    (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ) (key : Key) (id : NodeId)
    (aligned : key.arguments = normalized.items) (model : Interner.Primitives)
    (matched : model.publish key id world.graph =
      Interner.publish (hostProbe key (Publication.forget world.memory)).1 key id world.graph)
    (publicationOuter : outer (Publication.publish hostProbe host allocator source key normalized id world).2)
    (releaseOuter : ∀ reached after currentRows, outer reached →
      reached.graph.representatives = some currentRows →
      Caller.GraphCustody allocator normalized currentRows reached.memory →
      free (Publication.external host) allocator normalized reached.memory = (.ok (), after) →
        outer { reached with memory := after }) :
    let ran := (do
      let _ ← graph (fun slice => Publication.publish hostProbe host allocator source key slice id)
      let _ ← handoff
      pure id : Action (Publication.Effects σ) NodeId) ⟨world, ⟨some lookup, some normalized, false⟩⟩
    let logical := (do let _ ← model.publish key id; pure id : Interner.Action NodeId) world.graph
    Returns (GraphFrame safety allocator owner rows
      (CallFrame safety allocator owner parentRows parentSource parentValues parentNormalized parentAddress parentNative outer))
      (OwnedCall.finish (Publication.external host) allocator ran.1 ran.2) (logical.1.mapError Fault.language) logical.2 := by
  exact frame.publication hostProbe host key id lookup origin.detached aligned model matched
    (CallFrame.publish_parent origin initial frame hostProbe host key id aligned publicationOuter)
    (fun reached after currentRows held projected custody freed =>
      CallFrame.release origin initial held host projected custody
        (fun after released => releaseOuter reached after currentRows held.parent projected custody released) after freed)

/-- The two native completions after successful dispatch: insertion after
handoff, and publication with conditional handoff. The generic composer accepts
both; the native taken step derives publication from the reached caller frame. -/
structure MissCompletions (external : External σ) (allocator : Nat) (p : Primitives σ)
    (model : Interner.Primitives) (ready frame : World σ → Prop)
    (key : Key) (slice : ArgumentSlice) (lookup : Handle) (deterministic simplifying : Bool) : Prop where
  insertion : ∀ world, ready world →
    let ran := (do let _ ← handoff; graph (fun slice => p.insert key slice deterministic) : Action σ NodeId)
      ⟨world, ⟨some lookup, some slice, false⟩⟩
    let logical := model.insert key deterministic world.graph
    Returns frame (OwnedCall.finish external allocator ran.1 ran.2) (logical.1.mapError Fault.language) logical.2
  publication : simplifying = true → ∀ world id, ready world →
    let ran := (do
      let _ ← graph (fun slice => p.publish key slice (Interner.findCode.published.run id))
      let _ ← handoff
      pure (Interner.findCode.simplified.run id) : Action σ NodeId)
      ⟨world, ⟨some lookup, some slice, false⟩⟩
    let logical := (do
      let _ ← model.publish key (Interner.findCode.published.run id)
      pure (Interner.findCode.simplified.run id) : Interner.Action NodeId) world.graph
    Returns frame (OwnedCall.finish external allocator ran.1 ran.2) (logical.1.mapError Fault.language) logical.2

/-- Simplifier entry additionally needs failure cleanup and publication.
Both are guarded by the source branch; a direct insertion needs neither.
The native deterministic step derives cleanup from `CallFrame.failure`. -/
structure MissSteps (external : External σ) (allocator : Nat) (p : Primitives σ)
    (model : Interner.Primitives) (ready frame : World σ → Prop)
    (key : Key) (slice : ArgumentSlice) (lookup : Handle) (deterministic simplifying : Bool) : Prop
    extends MissCompletions external allocator p model ready frame key slice lookup deterministic simplifying where
  failure : simplifying = true → ∀ world fault, ready world →
    Returns frame (OwnedCall.finish external allocator (.error fault : Except Fault NodeId)
      ⟨world, ⟨some lookup, some slice, false⟩⟩) (.error fault) world.graph

/-- Existing exact suffix proofs also supply the independent native frame
obligations. Their result/graph equations are not required for this projection. -/
theorem MissSteps.frames {external : External σ} {allocator : Nat} {p : Primitives σ}
    {model : Interner.Primitives} {ready frame : World σ → Prop}
    {key : Key} {slice : ArgumentSlice} {lookup : Handle} {deterministic simplifying : Bool}
    (steps : MissSteps external allocator p model ready frame key slice lookup deterministic simplifying) :
    MissFrames external allocator p ready frame key slice lookup deterministic simplifying where
  insertion := fun world ready => (steps.insertion world ready).framePost
  publication := fun branch world id ready => (steps.publication branch world id ready).framePost
  failure := fun branch world fault ready => (steps.failure branch world fault ready).framePost

/-- Existing exact suffix correspondence and logical word contracts supply
the local native semantic obligations. The observed-child path can instead
derive these from its recorded suffixes without raw heap correspondence. -/
theorem MissSteps.words {external : External σ} {allocator : Nat} {p : Primitives σ}
    {model : Interner.Primitives} {ready frame : World σ → Prop}
    {key : Key} {slice : ArgumentSlice} {lookup : Handle} {deterministic simplifying : Bool}
    (steps : MissSteps external allocator p model ready frame key slice lookup deterministic simplifying)
    (meaning : Meaning) (expected : Word)
    (insertWords : ∀ heap, Interner.Invariant meaning heap → key.eval meaning heap.read = some expected →
      Interner.Safe meaning (model.insert key deterministic) heap (fun id after => after.read id = some expected))
    (publishWords : simplifying = true → ∀ id heap, Interner.Invariant meaning heap →
      key.eval meaning heap.read = some expected → heap.read id = some expected →
      Interner.Safe meaning (model.publish key id) heap (fun _ _ => True)) :
    MissWords external allocator p ready meaning expected key slice lookup deterministic simplifying where
  insertion := by
    intro world held valid evaluated
    exact safe_at meaning world.graph _ _ (model.insert key deterministic) _
      (fun completed => (steps.insertion world held completed).2.2) (insertWords world.graph valid evaluated)
  publication := by
    intro branch world id held valid evaluated actual
    apply safe_at meaning world.graph _ _ _ _ (fun completed => (steps.publication branch world id held completed).2.2)
    apply Interner.Safe.bind meaning world.graph (model.publish key id) _ (fun _ _ => True) _
      (publishWords branch id world.graph valid evaluated actual)
    intro ignored after validAfter stableAfter _
    exact Interner.Safe.pure meaning after id _ validAfter (stableAfter id expected actual)
  failure := by
    intro branch world fault held valid
    dsimp only
    intro completed
    have checked := steps.failure branch world fault held completed
    rw [checked.2.2.1, checked.2.2.2]
    exact ⟨valid, fun _ _ found => found, trivial⟩

/-- One source-bound owned miss, under the proper-child dispatch result only
when the source enters simplification. Both successful dispatch outcomes and
ordinary child failure use the child's actual reached world. -/
theorem miss_step (external : External σ) (allocator : Nat) (p : Primitives σ)
    (model : Interner.Primitives) (ready frame : World σ → Prop)
    (request : Interner.Request) (key : Key) (slice : ArgumentSlice) (lookup : Handle)
    (deterministic : Bool) (before : World σ) (initial : ready before)
    (steps : MissSteps external allocator p model ready frame key slice lookup deterministic
      (deterministic && (request.item.kind == 1)))
    (simplifies : (deterministic && (request.item.kind == 1)) = true → ordinary (p.simplify key slice before).1 = true →
      ready (p.simplify key slice before).2 ∧
      (p.simplify key slice before).1 = (model.simplify key before.graph).1.mapError Fault.language ∧
      (p.simplify key slice before).2.graph = (model.simplify key before.graph).2) :
    let ran := Interner.findCode.controlMiss (OwnedCall.execution external allocator p) request key deterministic
      ⟨before, ⟨some lookup, some slice, false⟩⟩
    let logical := Interner.findCode.miss model request key deterministic before.graph
    Returns frame (OwnedCall.finish external allocator ran.1 ran.2) (logical.1.mapError Fault.language) logical.2 := by
  dsimp only
  apply Returns.of_framePost (miss_frame external allocator p ready frame request key slice lookup deterministic
    before initial steps.frames (fun branch completed => (simplifies branch completed).1))
  unfold Interner.FindCode.controlMiss Interner.FindCode.miss
  by_cases branch : (deterministic && (request.item.kind == 1)) = true
  · simp only [branch, ↓reduceIte, OwnedCall.execution]
    cases called : p.simplify key slice before with
    | mk result middle =>
      cases result with
      | error fault =>
        simp only [graph, called, bind, Effect.bind]
        intro completed
        have ordinaryChild : ordinary (.error fault : Except Fault (Option NodeId)) = true := by
          cases rejected : ordinary (.error fault : Except Fault NodeId) with
          | false => simp only [OwnedCall.finish, rejected, Bool.false_eq_true, ↓reduceIte] at completed
          | true => exact rejected
        have checked := simplifies branch (by rw [called]; exact ordinaryChild)
        simp only [called] at checked
        have result := steps.failure branch middle fault checked.1 completed
        cases modeled : model.simplify key before.graph with
        | mk logical reached =>
          rw [modeled] at checked
          dsimp only at checked
          cases logical with
          | ok value => cases checked.2.1
          | error error =>
            have equal : fault = Fault.language error := Except.error.inj checked.2.1
            simpa only [modeled, bind, Effect.bind, Except.mapError, ← equal, ← checked.2.2] using result.2.2
      | ok found =>
        have checked := simplifies branch (by rw [called]; rfl)
        simp only [called] at checked
        cases modeled : model.simplify key before.graph with
        | mk logical reached =>
          rw [modeled] at checked
          dsimp only at checked
          cases logical with
          | error error => cases checked.2.1
          | ok value =>
            have same : found = value := Except.ok.inj checked.2.1
            subst value
            cases found with
            | none =>
              simpa only [graph, called, modeled, bind, Effect.bind, pure, Effect.pure, ← checked.2.2] using
                (fun completed => (steps.insertion middle checked.1 completed).2.2)
            | some id =>
              simpa only [graph, called, modeled, bind, Effect.bind, pure, Effect.pure, ← checked.2.2] using
                (fun completed => (steps.publication branch middle id checked.1 completed).2.2)
  · simpa only [branch, Bool.false_eq_true, ↓reduceIte, OwnedCall.execution, bind, Effect.bind, pure, Effect.pure] using
      (fun completed => (steps.insertion before initial completed).2.2)


/-- Reached insertion inputs after proper children. There is no pre-child graph
equality or rebased freshness claim: these facts feed `prepare_owned` directly,
and publication admission uses the reached keys and representative operands. -/
theorem CallFrame.preparation {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {world : World (Publication.Effects σ)}
    (frame : CallFrame safety allocator owner rows source values normalized address native parent world)
    (key : Key) (aligned : key.arguments = normalized.items) :
    Valid world.memory ∧ SliceValid allocator world.memory.heap normalized ∧
      AssemblyClone.NativeFields.Represents world.memory.memory address native ∧
      Publication.Input allocator source key normalized world ∧
      OwnedKeys.Live allocator ⟨world.memory.effects.keys, world.memory.heap⟩ ∧
      OwnedKeys.Unique world.memory.effects.keys := by
  obtain ⟨added, data, capacity, facts, custody, privateSource⟩ := frame.1.1
  exact ⟨facts.valid, frame.1.2.2.1, frame.2.1,
    custody.publication source key aligned privateSource facts.live, facts.live, facts.unique⟩

/-- Successful insertion preparation consumes the reached proper-child frame.
The shared preparation theorem supplies the actual three callbacks, ownership
and old-allocation frames; those frames derive native graph correspondence.
Append/publication/rollback and the enclosing parent predicate remain separate
suffix obligations. No pre-child normalization origin is reconstructed. -/
theorem CallFrame.prepare_native {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {world : World (Publication.Effects σ)}
    (frame : CallFrame safety allocator owner rows source values normalized address native parent world)
    (ops : Insertion.Operations σ) (allocate : RepresentativeArray.Backing.Registry.Allocate σ) (object : Nat)
    (copied : AssemblyClone.NativeFields.ItemValue) (key : Key) (operands : ArgumentSlice) (remaining : Handle)
    (value : Word) (graph : Storage.State → Insertion.Native.Frame σ → Interner.Heap)
    (duplicated allocated middle : Session (Publication.Effects σ))
    (aligned : key.arguments = normalized.items) (admitted : Admitted ops.arguments)
    (duplicateCall : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ world.memory = (.ok (operands, remaining), duplicated))
    (createCall : AssemblyItem.Creation.create (Insertion.observe ops.create) allocator native.item duplicated = (.ok object, allocated))
    (cloneCall : AssemblyClone.Physical.run (Insertion.observe ops.copy) allocator native allocated = (.ok copied, middle)) :
    ∃ added data capacity installed,
      Insertion.Native.Preparation ops allocate safety allocator owner object source address native copied key normalized operands
        world (rows ++ added) value graph duplicated allocated middle installed ∧
      NativeGraph.Facts safety allocator owner data capacity { world with memory := installed } (rows ++ added) := by
  obtain ⟨added, data, capacity, facts, _, _⟩ := frame.1.1
  obtain ⟨valid, normalizedLive, represented, publication, live, unique⟩ := frame.preparation key aligned
  obtain ⟨installed, prepared⟩ := Insertion.Native.prepare_reached ops allocate safety allocator owner object source address
    native copied key normalized operands remaining world (rows ++ added) value graph duplicated allocated middle
    valid normalizedLive represented publication live unique admitted duplicateCall createCall cloneCall
  refine ⟨added, data, capacity, installed, prepared, ?_⟩
  obtain ⟨_, _, _, installedPost, _, _, _, _, _, _, _, _, keys, nativeFrame, registryFrame, _⟩ := prepared
  exact facts.frame installedPost.valid facts.projected rfl keys
    (fun id cell found _ => nativeFrame id cell found) registryFrame

/-- The same ordinary return passes through both actual local cleanups. The
remaining local-frame obligation concerns only those cleanups, not recursion. -/
theorem Returns.locals (frame : World σ → Prop) (actual : Except Fault α × State σ)
    (result : Except Fault α) (graph : Interner.Heap) (itemMark scratchMark : Nat)
    (checked : Returns frame actual result graph)
    (locals : ∀ world, frame world → frame (returnWorld itemMark scratchMark world)) :
    Returns frame
      (if ordinary actual.1 then
        (actual.1, { actual.2 with world := returnWorld itemMark scratchMark actual.2.world })
       else actual) result graph := by
  apply Returns.of_framePost (FramePost.locals frame actual itemMark scratchMark checked.framePost locals)
  cases completed : ordinary actual.1 with
  | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact fun held => (checked held).2.2
  | true =>
    simp only [↓reduceIte]
    intro _
    exact (checked completed).2.2

section
variable {σ : Type} (safety : Bool) (owner usizeBits : Nat)
    (base : PairInput.Context (Publication.Effects σ)) (children : Constructors (Publication.Effects σ))
    (modelChildren : Associative.Constructors AssemblyItem.Fields.Values) (modelSeed : Interner.Primitives)
    (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before constructed : World (Publication.Effects σ)) (address : Compiler.ZigAir.Memory.Address)
    (pointer : Compiler.ZigAir.Memory.Value) (memory : Compiler.ZigAir.Memory.State)
    (values : List NodeId) (prepared taken : State (Publication.Effects σ))
    (key : Key) (normalized : ArgumentSlice) (lookup : Handle) (rows : List Storage.Cell)
    {data : Compiler.ZigAir.Memory.Address} {capacity : Nat}
    (facts : NativeGraph.Facts safety base.allocator owner data capacity constructed rows)
    (entry : Insertion.Native.CallerInput base.allocator source address request values
      (input request.item debug) key constructed taken normalized lookup)
    (privateSource : Caller.SourcePrivate source constructed.memory.effects.keys)
    (array : ArraySource source constructed.memory.memory)
    (parent frame : World (Publication.Effects σ) → Prop) (kept : parent taken.world)
    (coupled : (projection (CallFrame safety base.allocator owner rows source request.arguments normalized
      address (input request.item debug) parent)).SourceConstructorsAt (Nested.storageReads rows) debug children modelChildren)
    (locals : ∀ world, frame world → frame
      (returnWorld before.memory.memory.nextId constructed.memory.memory.nextId world))
    (made : prepare request.item debug before = (.ok address, constructed))
    (room : base.queries.atCapacity constructed.graph = false)
    (allocated : Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) = .ok (pointer, memory))
    (initialized : Caller.initLookup base.external base.budget base.allocator source
      ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))
    (classified : base.queries.deterministic request.item = .ok true)
    (keyed : Interner.makeKey request values = .ok key) (missed : constructed.graph.table key = none)
    (transferred : take base.external base.allocator prepared = (.ok (), taken))

include facts entry privateSource array kept coupled locals made room allocated initialized classified keyed missed transferred

omit coupled locals made room allocated initialized classified keyed missed transferred in
/-- The complete native dispatcher retains the live caller under proper-child
frame hypotheses alone. Reached native facts bind source-backed child calls;
no logical child, observer, word law or final dispatcher frame is assumed. -/
theorem CallFrame.dispatch_kept
    (dispatchFrames : (keeping (CallFrame safety base.allocator owner rows source request.arguments normalized
      address (input request.item debug) parent)).SourceConstructorsAt (Nested.storageReads rows) debug children children) :
    let p := (context base owner usizeBits children debug).primitives source address (input request.item debug)
    let actual := p.simplify key normalized taken.world
    ordinary actual.1 = true →
      CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent actual.2 := by
  dsimp only
  have initial := CallFrame.caller entry facts privateSource array parent kept
  have takenFacts := facts.frame entry.origin.held.1.1
    (by rw [entry.origin.graph]; exact facts.projected)
    (congrArg Interner.Heap.table entry.origin.graph) entry.keys
    (fun id cell found _ => entry.origin.memory id cell found) entry.origin.registry
  exact dispatcher_keeps base owner usizeBits children debug source address (input request.item debug) key normalized
    _ taken.world initial (by
      rw [takenFacts.reads]
      simpa only [Interner.representativeReads, takenFacts.projected] using dispatchFrames)

omit coupled locals made room allocated initialized classified keyed missed transferred in
/-- One actual taken dispatcher supplies both native frame retention and
observed result correspondence. Indexed loads and the read snapshot come from
the reached native facts; only the proper-child relation uses the observer. -/
theorem CallFrame.dispatch_at (observe : World (Publication.Effects σ) → Interner.Heap)
    (dispatchCoupled : (projectionAt observe (CallFrame safety base.allocator owner rows source request.arguments normalized
      address (input request.item debug) parent)).SourceConstructorsAt (Nested.storageReads rows) debug children modelChildren) :
    let p := (context base owner usizeBits children debug).primitives source address (input request.item debug)
    let actual := p.simplify key normalized taken.world
    let logical := Dispatch.simplify (Interner.representativeReads taken.world.graph) modelChildren usizeBits
      key.instruction key.arguments debug (observe taken.world)
    ordinary actual.1 = true →
      CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent actual.2 ∧
      actual.1 = logical.1.mapError Fault.language ∧ observe actual.2 = logical.2 := by
  dsimp only
  have initial := CallFrame.caller entry facts privateSource array parent kept
  have takenFacts := facts.frame entry.origin.held.1.1
    (by rw [entry.origin.graph]; exact facts.projected)
    (congrArg Interner.Heap.table entry.origin.graph) entry.keys
    (fun id cell found _ => entry.origin.memory id cell found) entry.origin.registry
  rw [dispatcher_snapshot, takenFacts.reads]
  exact dispatch_projects_framed_at observe safety owner base usizeBits children modelChildren debug source request.arguments key
    normalized rows taken.world takenFacts.projected entry.publication.aligned _ (fun _ held => held.1)
    dispatchCoupled taken.world initial

omit coupled locals made room allocated initialized classified keyed missed transferred in
/-- The actual native dispatcher retains its live frame and word semantics
under the observed proper-child relation. Only the resource cursor changes in
the logical observation; the read snapshot remains the actual reached graph. -/
theorem CallFrame.dispatch_verified_cursor (cursor : World (Publication.Effects σ) → Nat)
    (dispatchCoupled : (projectionAt (cursorGraph cursor) (CallFrame safety base.allocator owner rows source request.arguments normalized
      address (input request.item debug) parent)).SourceConstructorsAt (Nested.storageReads rows) debug children modelChildren)
    (env : AddressMask.Environment) (other : Meaning) (expected : Word)
    (correct : Associative.ConstructorSound (Dispatch.wordBaseMeaning env other) modelChildren)
    (addresses : AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) modelChildren.operation)
    (shifts : ArithmeticShift.Constructs (AddressMask.addressMeaning env other) modelChildren.operation)
    (operation : key.kind = 1)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) taken.world.graph)
    (evaluated : key.eval (Dispatch.wordDispatchMeaning env other) taken.world.graph.read = some expected) :
    let p := (context base owner usizeBits children debug).primitives source address (input request.item debug)
    let actual := p.simplify key normalized taken.world
    (ordinary actual.1 = true → CallFrame safety base.allocator owner rows source request.arguments normalized
      address (input request.item debug) parent actual.2) ∧
    Semantic.Ensures (Dispatch.wordDispatchMeaning env other) taken.world.graph actual.1 actual.2.graph
      (fun found after => ∀ id, found = some id → after.read id = some expected) := by
  dsimp only
  have projected := CallFrame.dispatch_at safety owner usizeBits base children modelChildren source request debug constructed address
    values taken key normalized lookup rows facts entry privateSource array parent kept (cursorGraph cursor) dispatchCoupled
  have safe := Dispatch.default_key_simplify_safe env other (Interner.representativeReads taken.world.graph) modelChildren correct addresses shifts
    (cursorGraph cursor taken.world) (valid.with_cursor (cursor taken.world))
    (Interner.representative_reads_sound _ taken.world.graph valid) key operation expected debug usizeBits evaluated
  have words := safe_at (Dispatch.wordDispatchMeaning env other) (cursorGraph cursor taken.world) _ _ _ _
    (fun completed => (projected completed).2) safe
  exact ⟨fun completed => (projected completed).1,
    (Semantic.Ensures.cursor_iff _ _ _ _ _ _ (fun found read => ∀ id, found = some id → read id = some expected)).mp words⟩

omit coupled locals made room allocated initialized classified keyed missed transferred in
/-- Compose native child frames with the existing insertion, publication and
failure suffixes. The complete owned miss requires no logical child model,
resource observation or word contract to preserve its caller frame. -/
theorem taken_miss_frame (deterministic : Bool)
    (dispatchFrames : (deterministic && (request.item.kind == 1)) = true →
      (keeping (CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent)).SourceConstructorsAt (Nested.storageReads rows) debug children children)
    (frames : MissFrames base.external base.allocator
      ((context base owner usizeBits children debug).primitives source address (input request.item debug))
      (CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent) frame key normalized lookup deterministic
          (deterministic && (request.item.kind == 1))) :
    let p := (context base owner usizeBits children debug).primitives source address (input request.item debug)
    let ran := Interner.findCode.controlMiss (OwnedCall.execution base.external base.allocator p)
      request key deterministic ⟨taken.world, ⟨some lookup, some normalized, false⟩⟩
    let actual := OwnedCall.finish base.external base.allocator ran.1 ran.2
    FramePost frame actual := by
  let ready := CallFrame safety base.allocator owner rows source request.arguments normalized
    address (input request.item debug) parent
  let p := (context base owner usizeBits children debug).primitives source address (input request.item debug)
  exact miss_frame base.external base.allocator p ready frame request key normalized lookup deterministic
    taken.world (CallFrame.caller entry facts privateSource array parent kept) frames (fun branch =>
      CallFrame.dispatch_kept safety owner usizeBits base children source request debug constructed address
        values taken key normalized lookup rows facts entry privateSource array parent kept (dispatchFrames branch))

omit coupled classified missed in
/-- The complete taken invocation preserves native scope and frame under
proper-child native frames. No logical child model, observer or child word law
is needed; native suffix and return laws remain explicit. Both classifier outcomes use the actual source guard. -/
theorem invoke_step_frame (deterministic : Bool)
    (dispatchFrames : (deterministic && (request.item.kind == 1)) = true →
      (keeping (CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent)).SourceConstructorsAt (Nested.storageReads rows) debug children children)
    (steps : MissFrames base.external base.allocator
      ((context base owner usizeBits children debug).primitives source address (input request.item debug))
      (CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent) frame key normalized lookup deterministic
          (deterministic && (request.item.kind == 1)))
    (classifiedAs : base.queries.deterministic request.item = .ok deterministic)
    (missedIf : deterministic = true → constructed.graph.table key = none) :
    FramePost frame (invoke base.external base.budget base.allocator
      ((context base owner usizeBits children debug).primitives source) base.queries source request debug before) := by
  have completed := taken_miss_frame safety owner usizeBits base children source request debug constructed address
    values taken key normalized lookup rows facts entry privateSource array parent frame kept deterministic dispatchFrames steps
  have returned := FramePost.locals frame _ before.memory.memory.nextId constructed.memory.memory.nextId completed locals
  rw [invoke_after_take base.external base.budget base.allocator
    ((context base owner usizeBits children debug).primitives source) base.queries source request debug
    before constructed address pointer memory values prepared taken key deterministic made room allocated initialized classifiedAs keyed
    missedIf transferred]
  have sameState : taken = ⟨taken.world, ⟨some lookup, some normalized, false⟩⟩ := by
    cases taken; simp only [State.mk.injEq, true_and]; exact entry.origin.scope
  rw [sameState]
  exact returned


omit coupled classified missed in
/-- The complete taken invocation preserves native scope and frame under the
same observed proper-child relation used by protocol replay. It assumes no raw
heap/result correspondence or word theorem; local native suffix and return laws
remain explicit. Both classifier outcomes use the actual source guard. -/
theorem invoke_step_frame_at (observe : World (Publication.Effects σ) → Interner.Heap) (deterministic : Bool)
    (dispatchCoupled : (deterministic && (request.item.kind == 1)) = true →
      (projectionAt observe (CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent)).SourceConstructorsAt (Nested.storageReads rows) debug children modelChildren)
    (steps : MissFrames base.external base.allocator
      ((context base owner usizeBits children debug).primitives source address (input request.item debug))
      (CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent) frame key normalized lookup deterministic
          (deterministic && (request.item.kind == 1)))
    (classifiedAs : base.queries.deterministic request.item = .ok deterministic)
    (missedIf : deterministic = true → constructed.graph.table key = none) :
    FramePost frame (invoke base.external base.budget base.allocator
      ((context base owner usizeBits children debug).primitives source) base.queries source request debug before) := by
  apply invoke_step_frame safety owner usizeBits base children source request debug before constructed address pointer memory
    values prepared taken key normalized lookup rows facts entry privateSource array parent frame kept locals made room allocated
    initialized keyed transferred deterministic ?_ steps classifiedAs missedIf
  intro branch
  exact source_constructors_keep observe _ _ debug children modelChildren (dispatchCoupled branch)

omit coupled locals made room allocated initialized classified missed transferred in
/-- Observed proper children supply the actual owned-miss result. The shared
entry proof and complete taken-invocation proof consume this same result. -/
theorem taken_miss_verified_cursor (cursor : World (Publication.Effects σ) → Nat) (deterministic : Bool)
    (dispatchCoupled : (deterministic && (request.item.kind == 1)) = true →
      (projectionAt (cursorGraph cursor) (CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent)).SourceConstructorsAt (Nested.storageReads rows) debug children modelChildren)
    (env : AddressMask.Environment) (other : Meaning) (expected : Word)
    (frames : MissFrames base.external base.allocator
      ((context base owner usizeBits children debug).primitives source address (input request.item debug))
      (CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent) frame key normalized lookup deterministic
          (deterministic && (request.item.kind == 1)))
    (suffixWords : MissWords base.external base.allocator
      ((context base owner usizeBits children debug).primitives source address (input request.item debug))
      (CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent) (Dispatch.wordDispatchMeaning env other) expected
      key normalized lookup deterministic (deterministic && (request.item.kind == 1)))
    (correct : (deterministic && (request.item.kind == 1)) = true →
      Associative.ConstructorSound (Dispatch.wordBaseMeaning env other) modelChildren)
    (addresses : (deterministic && (request.item.kind == 1)) = true →
      AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) modelChildren.operation)
    (shifts : (deterministic && (request.item.kind == 1)) = true →
      ArithmeticShift.Constructs (AddressMask.addressMeaning env other) modelChildren.operation)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) taken.world.graph)
    (evaluated : key.eval (Dispatch.wordDispatchMeaning env other) taken.world.graph.read = some expected) :
    let p := (context base owner usizeBits children debug).primitives source address (input request.item debug)
    let ran := Interner.findCode.controlMiss (OwnedCall.execution base.external base.allocator p)
      request key deterministic ⟨taken.world, ⟨some lookup, some normalized, false⟩⟩
    let actual := OwnedCall.finish base.external base.allocator ran.1 ran.2
    FramePost frame actual ∧
      Semantic.Ensures (Dispatch.wordDispatchMeaning env other) taken.world.graph actual.1 actual.2.world.graph
        (fun id after => after.read id = some expected) := by
  let ready := CallFrame safety base.allocator owner rows source request.arguments normalized
    address (input request.item debug) parent
  let p := (context base owner usizeBits children debug).primitives source address (input request.item debug)
  have initial : ready taken.world := CallFrame.caller entry facts privateSource array parent kept
  have simplified : (deterministic && (request.item.kind == 1)) = true →
      (ordinary (p.simplify key normalized taken.world).1 = true → ready (p.simplify key normalized taken.world).2) ∧
      Semantic.Ensures (Dispatch.wordDispatchMeaning env other) taken.world.graph (p.simplify key normalized taken.world).1
        (p.simplify key normalized taken.world).2.graph (fun found after => ∀ id, found = some id → after.read id = some expected) := by
    intro branch
    have operation : key.kind = 1 := by
      rw [Compiler.Extraction.Recursive.make_key_kind request values key keyed]
      simpa using (Bool.and_eq_true_iff.mp branch).2
    exact CallFrame.dispatch_verified_cursor safety owner usizeBits base children modelChildren source request debug constructed address
      values taken key normalized lookup rows facts entry privateSource array parent kept cursor (dispatchCoupled branch)
      env other expected (correct branch) (addresses branch) (shifts branch) operation valid evaluated
  have words := miss_words base.external base.allocator p ready (Dispatch.wordDispatchMeaning env other) expected
    request key normalized lookup deterministic taken.world initial valid evaluated suffixWords
    (fun branch => (simplified branch).1) (fun branch => (simplified branch).2)
  exact ⟨taken_miss_frame safety owner usizeBits base children source request debug constructed address
    values taken key normalized lookup rows facts entry privateSource array parent frame kept deterministic
    (fun branch => source_constructors_keep (cursorGraph cursor) _ _ debug children modelChildren (dispatchCoupled branch)) frames, words⟩

omit coupled classified missed in
/-- Native frame and word preservation for one complete taken invocation under
observed proper children. Local completed suffixes supply native semantics, not
a whole-miss simulation or a raw logical-heap correspondence premise. -/
theorem invoke_step_verified_cursor (cursor : World (Publication.Effects σ) → Nat) (deterministic : Bool)
    (dispatchCoupled : (deterministic && (request.item.kind == 1)) = true →
      (projectionAt (cursorGraph cursor) (CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent)).SourceConstructorsAt (Nested.storageReads rows) debug children modelChildren)
    (env : AddressMask.Environment) (other : Meaning) (expected : Word)
    (frames : MissFrames base.external base.allocator
      ((context base owner usizeBits children debug).primitives source address (input request.item debug))
      (CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent) frame key normalized lookup deterministic
          (deterministic && (request.item.kind == 1)))
    (suffixWords : MissWords base.external base.allocator
      ((context base owner usizeBits children debug).primitives source address (input request.item debug))
      (CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent) (Dispatch.wordDispatchMeaning env other) expected
      key normalized lookup deterministic (deterministic && (request.item.kind == 1)))
    (classifiedAs : base.queries.deterministic request.item = .ok deterministic)
    (missedIf : deterministic = true → constructed.graph.table key = none)
    (item : Prepared request.item debug before constructed)
    (correct : (deterministic && (request.item.kind == 1)) = true →
      Associative.ConstructorSound (Dispatch.wordBaseMeaning env other) modelChildren)
    (addresses : (deterministic && (request.item.kind == 1)) = true →
      AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) modelChildren.operation)
    (shifts : (deterministic && (request.item.kind == 1)) = true →
      ArithmeticShift.Constructs (AddressMask.addressMeaning env other) modelChildren.operation)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read
      request.arguments request.sequence = some expected) :
    let actual := invoke base.external base.budget base.allocator
      ((context base owner usizeBits children debug).primitives source) base.queries source request debug before
    FramePost frame actual ∧
      Semantic.Ensures (Dispatch.wordDispatchMeaning env other) before.graph actual.1 actual.2.world.graph
        (fun id after => after.read id = some expected) := by
  have reached : (⟨constructed, address, pointer, memory, values, prepared, taken, key, normalized, lookup, deterministic⟩ :
      ProtocolTrace.TakenSite σ).Reached base source request debug before :=
    ⟨made, room, allocated, initialized, classifiedAs, keyed, missedIf, transferred, entry⟩
  have keyValue := reached.key_value item env other expected valid evaluated
  exact reached.return_verified children owner usizeBits (Dispatch.wordDispatchMeaning env other) expected frame
    (entry.origin.graph.trans item.graph) locals
    (taken_miss_verified_cursor safety owner usizeBits base children modelChildren source request debug constructed
      address values taken key normalized lookup rows facts entry privateSource array parent frame kept keyed
      cursor deterministic dispatchCoupled env other expected frames suffixWords correct addresses shifts keyValue.1 keyValue.2)

omit coupled classified missed in
/-- One complete constructor invocation on either taken miss path, with the
actual proper children of `step` only when simplification is entered. The
dispatcher theorem is derived here; prefix observations and named local
suffix/frame obligations remain, with failure/publication guarded likewise.
This is not yet the all-entry induction or the production RC endpoint. -/
theorem invoke_step (deterministic : Bool)
    (dispatchCoupled : (deterministic && (request.item.kind == 1)) = true →
      (projection (CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent)).SourceConstructorsAt (Nested.storageReads rows) debug children modelChildren)
    (steps : MissSteps base.external base.allocator
      ((context base owner usizeBits children debug).primitives source address (input request.item debug))
      modelSeed (CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent) frame key normalized lookup deterministic
          (deterministic && (request.item.kind == 1)))
    (classifiedAs : base.queries.deterministic request.item = .ok deterministic)
    (missedIf : deterministic = true → constructed.graph.table key = none) :
    let model : Interner.Primitives := { modelSeed with
      simplify := fun key => Dispatch.simplify (Interner.representativeReads taken.world.graph) modelChildren usizeBits
          key.instruction key.arguments debug }
    let logical := Interner.findCode.miss model request key deterministic taken.world.graph
    Returns frame
      (invoke base.external base.budget base.allocator
        ((context base owner usizeBits children debug).primitives source) base.queries source request debug before)
      (logical.1.mapError Fault.language) logical.2 := by
  dsimp only
  let ready := CallFrame safety base.allocator owner rows source request.arguments normalized
    address (input request.item debug) parent
  have initial : ready taken.world := CallFrame.caller entry facts privateSource array parent kept
  let p := (context base owner usizeBits children debug).primitives source address (input request.item debug)
  let model : Interner.Primitives := { modelSeed with
    simplify := fun key => Dispatch.simplify (Interner.representativeReads taken.world.graph) modelChildren usizeBits
        key.instruction key.arguments debug }
  have simplified : (deterministic && (request.item.kind == 1)) = true → ordinary (p.simplify key normalized taken.world).1 = true →
      ready (p.simplify key normalized taken.world).2 ∧
      (p.simplify key normalized taken.world).1 = (model.simplify key taken.world.graph).1.mapError Fault.language ∧
      (p.simplify key normalized taken.world).2.graph = (model.simplify key taken.world.graph).2 := by
    intro branch
    dsimp only [p, model]
    exact CallFrame.dispatch_at safety owner usizeBits base children modelChildren source request debug constructed address
      values taken key normalized lookup rows facts entry privateSource array parent kept World.graph (dispatchCoupled branch)
  have localSteps : MissSteps base.external base.allocator p model ready frame key normalized lookup deterministic
      (deterministic && (request.item.kind == 1)) :=
    { failure := steps.failure, insertion := steps.insertion, publication := steps.publication }
  have completed := miss_step base.external base.allocator p model ready frame request key normalized lookup deterministic
    taken.world initial localSteps simplified
  have returned := Returns.locals frame _ _ _ before.memory.memory.nextId constructed.memory.memory.nextId completed locals
  rw [invoke_after_take base.external base.budget base.allocator
    ((context base owner usizeBits children debug).primitives source) base.queries source request debug
    before constructed address pointer memory values prepared taken key deterministic made room allocated initialized classifiedAs keyed
    missedIf transferred]
  have sameState : taken = ⟨taken.world, ⟨some lookup, some normalized, false⟩⟩ := by
    cases taken; simp only [State.mk.injEq, true_and]; exact entry.origin.scope
  rw [sameState]
  exact returned


omit coupled classified missed in
include modelChildren in
/-- Direct insertion uses the same actual prefix and local return as recursive
simplification, but requires neither child simulation nor publication/failure
completions. The classifier result is retained by the insertion and model.
This includes nondeterministic operations and deterministic non-operations. -/
theorem invoke_direct (deterministic : Bool)
    (skipped : (deterministic && (request.item.kind == 1)) = false)
    (insertion : ∀ world,
      CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent world →
      let ran := (do
        let _ ← handoff
        graph (fun slice =>
          ((context base owner usizeBits children debug).primitives source address (input request.item debug)).insert
            key slice deterministic) : Action (Publication.Effects σ) NodeId)
        ⟨world, ⟨some lookup, some normalized, false⟩⟩
      let logical := modelSeed.insert key deterministic world.graph
      Returns frame (OwnedCall.finish base.external base.allocator ran.1 ran.2)
        (logical.1.mapError Fault.language) logical.2)
    (classifiedAs : base.queries.deterministic request.item = .ok deterministic)
    (missedIf : deterministic = true → constructed.graph.table key = none) :
    let logical := modelSeed.insert key deterministic taken.world.graph
    Returns frame
      (invoke base.external base.budget base.allocator
        ((context base owner usizeBits children debug).primitives source) base.queries source request debug before)
      (logical.1.mapError Fault.language) logical.2 := by
  have completed := invoke_step safety owner usizeBits base children modelChildren modelSeed source request debug before constructed
    address pointer memory values prepared taken key normalized lookup rows facts entry privateSource array parent frame kept locals
    made room allocated initialized keyed transferred deterministic
    (by intro branch; simp only [skipped, Bool.false_eq_true] at branch)
    { insertion := insertion
      publication := by intro branch; simp only [skipped, Bool.false_eq_true] at branch
      failure := by intro branch; simp only [skipped, Bool.false_eq_true] at branch }
    classifiedAs missedIf
  simpa only [Interner.FindCode.miss, skipped, Bool.false_eq_true, ↓reduceIte] using completed


omit coupled classified missed in
/-- Both classifier outcomes share the same native and word-preservation step.
Proper-child simulation and semantic contracts are needed only when the source
enters simplification. Local insertion/frame obligations remain explicit; this
theorem does not assume preservation of the enclosing constructor. -/
theorem invoke_step_verified (deterministic : Bool)
    (dispatchCoupled : (deterministic && (request.item.kind == 1)) = true →
      (projection (CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent)).SourceConstructorsAt (Nested.storageReads rows) debug children modelChildren)
    (steps : MissSteps base.external base.allocator
      ((context base owner usizeBits children debug).primitives source address (input request.item debug))
      modelSeed (CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent) frame key normalized lookup deterministic
          (deterministic && (request.item.kind == 1)))
    (classifiedAs : base.queries.deterministic request.item = .ok deterministic)
    (missedIf : deterministic = true → constructed.graph.table key = none)
    (env : AddressMask.Environment) (other : Meaning) (expected : Word)
    (item : Prepared request.item debug before constructed)
    (correct : (deterministic && (request.item.kind == 1)) = true →
      Associative.ConstructorSound (Dispatch.wordBaseMeaning env other) modelChildren)
    (addresses : (deterministic && (request.item.kind == 1)) = true →
      AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) modelChildren.operation)
    (shifts : (deterministic && (request.item.kind == 1)) = true →
      ArithmeticShift.Constructs (AddressMask.addressMeaning env other) modelChildren.operation)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read
      request.arguments request.sequence = some expected)
    (insertWords : ∀ heap, Interner.Invariant (Dispatch.wordDispatchMeaning env other) heap →
      key.eval (Dispatch.wordDispatchMeaning env other) heap.read = some expected →
      Interner.Safe (Dispatch.wordDispatchMeaning env other) (modelSeed.insert key deterministic) heap
        (fun id after => after.read id = some expected))
    (publishWords : (deterministic && (request.item.kind == 1)) = true →
      ∀ id heap, Interner.Invariant (Dispatch.wordDispatchMeaning env other) heap →
      key.eval (Dispatch.wordDispatchMeaning env other) heap.read = some expected → heap.read id = some expected →
      Interner.Safe (Dispatch.wordDispatchMeaning env other) (modelSeed.publish key id) heap (fun _ _ => True)) :
    let actual := invoke base.external base.budget base.allocator
      ((context base owner usizeBits children debug).primitives source) base.queries source request debug before
    let model : Interner.Primitives := { modelSeed with
      simplify := fun key => Dispatch.simplify (Interner.representativeReads taken.world.graph) modelChildren usizeBits
        key.instruction key.arguments debug }
    let logical := Interner.findCode.miss model request key deterministic taken.world.graph
    Returns frame actual (logical.1.mapError Fault.language) logical.2 ∧
      Semantic.Ensures (Dispatch.wordDispatchMeaning env other) before.graph actual.1 actual.2.world.graph
        (fun id after => after.read id = some expected) ∧
      (∀ opcode borrowed, request = Interner.constructorCode.operationRequest opcode borrowed.items → source = view borrowed →
        let ran := (step base owner usizeBits children).borrowedOperation borrowed.address opcode borrowed.items debug before
        ordinary ran.1 = true → frame ran.2 ∧ ran.1 = logical.1.mapError Fault.language ∧ ran.2.graph = logical.2 ∧
          Semantic.Ensures (Dispatch.wordDispatchMeaning env other) before.graph ran.1 ran.2.graph
            (fun id after => after.read id = some expected)) := by
  dsimp only
  let actual := invoke base.external base.budget base.allocator
    ((context base owner usizeBits children debug).primitives source) base.queries source request debug before
  have native := invoke_step safety owner usizeBits base children modelChildren modelSeed source request debug before constructed
    address pointer memory values prepared taken key normalized lookup rows facts entry privateSource array parent frame kept locals
    made room allocated initialized keyed transferred deterministic dispatchCoupled steps classifiedAs missedIf
  have joined := invoke_step_verified_cursor safety owner usizeBits base children modelChildren source request debug before constructed
    address pointer memory values prepared taken key normalized lookup rows facts entry privateSource array parent frame kept locals
    made room allocated initialized keyed transferred (fun world => world.graph.allocationCursor) deterministic dispatchCoupled
    env other expected steps.frames (steps.words (Dispatch.wordDispatchMeaning env other) expected insertWords publishWords)
    classifiedAs missedIf item correct addresses shifts valid evaluated
  have words : Semantic.Ensures (Dispatch.wordDispatchMeaning env other) before.graph actual.1 actual.2.world.graph
      (fun id after => after.read id = some expected) := joined.2
  refine ⟨native, words, ?_⟩
  intro opcode borrowed requestEq sourceEq
  have same : (step base owner usizeBits children).borrowedOperation borrowed.address opcode borrowed.items debug before =
      (actual.1, actual.2.world) := by
    subst request source
    rfl
  rw [same]
  intro completed
  have held := native completed
  exact ⟨held.2.1, held.2.2.1, held.2.2.2, words⟩

omit coupled classified missed in
include modelChildren in
/-- Direct insertion specializes the same native/semantic step. Neither
proper-child simulation nor child-word, failure-cleanup or publication contracts
are required on a branch that does not execute them. The local insertion still
supplies its exact native result/frame and word contract for the chosen flag. -/
theorem invoke_direct_verified (deterministic : Bool)
    (skipped : (deterministic && (request.item.kind == 1)) = false)
    (insertion : ∀ world,
      CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent world →
      let ran := (do
        let _ ← handoff
        graph (fun slice =>
          ((context base owner usizeBits children debug).primitives source address (input request.item debug)).insert
            key slice deterministic) : Action (Publication.Effects σ) NodeId)
        ⟨world, ⟨some lookup, some normalized, false⟩⟩
      let logical := modelSeed.insert key deterministic world.graph
      Returns frame (OwnedCall.finish base.external base.allocator ran.1 ran.2)
        (logical.1.mapError Fault.language) logical.2)
    (classifiedAs : base.queries.deterministic request.item = .ok deterministic)
    (missedIf : deterministic = true → constructed.graph.table key = none)
    (env : AddressMask.Environment) (other : Meaning) (expected : Word)
    (item : Prepared request.item debug before constructed)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read
      request.arguments request.sequence = some expected)
    (insertWords : ∀ heap, Interner.Invariant (Dispatch.wordDispatchMeaning env other) heap →
      key.eval (Dispatch.wordDispatchMeaning env other) heap.read = some expected →
      Interner.Safe (Dispatch.wordDispatchMeaning env other) (modelSeed.insert key deterministic) heap
        (fun id after => after.read id = some expected)) :
    let actual := invoke base.external base.budget base.allocator
      ((context base owner usizeBits children debug).primitives source) base.queries source request debug before
    let logical := modelSeed.insert key deterministic taken.world.graph
    Returns frame actual (logical.1.mapError Fault.language) logical.2 ∧
      Semantic.Ensures (Dispatch.wordDispatchMeaning env other) before.graph actual.1 actual.2.world.graph
        (fun id after => after.read id = some expected) ∧
      (∀ opcode borrowed, request = Interner.constructorCode.operationRequest opcode borrowed.items → source = view borrowed →
        let ran := (step base owner usizeBits children).borrowedOperation borrowed.address opcode borrowed.items debug before
        ordinary ran.1 = true → frame ran.2 ∧ ran.1 = logical.1.mapError Fault.language ∧ ran.2.graph = logical.2 ∧
          Semantic.Ensures (Dispatch.wordDispatchMeaning env other) before.graph ran.1 ran.2.graph
            (fun id after => after.read id = some expected)) := by
  have checked := invoke_step_verified safety owner usizeBits base children modelChildren modelSeed source request debug before constructed
    address pointer memory values prepared taken key normalized lookup rows facts entry privateSource array parent frame kept locals
    made room allocated initialized keyed transferred deterministic
    (by intro branch; simp only [skipped, Bool.false_eq_true] at branch)
    { insertion := insertion
      publication := by intro branch; simp only [skipped, Bool.false_eq_true] at branch
      failure := by intro branch; simp only [skipped, Bool.false_eq_true] at branch }
    classifiedAs missedIf env other expected item
    (by intro branch; simp only [skipped, Bool.false_eq_true] at branch)
    (by intro branch; simp only [skipped, Bool.false_eq_true] at branch)
    (by intro branch; simp only [skipped, Bool.false_eq_true] at branch)
    valid evaluated insertWords (by intro branch; simp only [skipped, Bool.false_eq_true] at branch)
  simpa only [Interner.FindCode.miss, skipped, Bool.false_eq_true, ↓reduceIte] using checked

omit locals in
/-- The taken deterministic entry of the actual recursive step: exact reached
result/graph, native and live-parent predicate, closed locals and requested word
preservation. The proper children supply simulation and the existing logical
word contracts. Failure cleanup, publication and capacity/preparation-OOM insertion
completion are derived. Later insertion result/graph correspondence follows from
actual callback observations. First, spare and no-remap relocated
publication success/refusal derive native frames, with separate enclosing-parent
laws; the remaining native-frame premise excludes capacity, preparation/backing OOM
and these publication cases. Callback/model
binding, local policy/preparation-candidate
equations, outer frame laws and other prefix cases remain obligations. This does not assert the all-entry induction. -/
theorem step_taken_verified
    (env : AddressMask.Environment) (other : Meaning)
    (ops : Insertion.Operations σ) (allocate : RepresentativeArray.Backing.Registry.Allocate σ)
    (growth : Option (RepresentativeArray.Growth.Registered.Callbacks σ))
    (admitted : Admitted ops.arguments)
    (candidate : Key → Interner.Heap → Storage.Cell)
    (succeeds : Key → Interner.Heap → Storage.Allocation → Bool)
    (inserts : (base.primitives source address (input request.item debug)).insert =
      fun key slice deterministic => Insertion.Native.insert ops allocate safety base.allocator owner source address
        (Dispatch.wordDispatchMeaning env other) (input request.item debug) key slice deterministic growth)
    (insertionModel : modelSeed.insert = fun key deterministic heap =>
      Interner.observedInsert (candidate key heap) key deterministic (succeeds key heap) heap)
    (insertionRepresented : ∀ world,
      CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent world →
      Interner.Represented (Dispatch.wordDispatchMeaning env other) world.graph)
    (insertionPolicy : ∀ world,
      CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent world →
      Insertion.Native.PreparationPolicy ops base.allocator (input request.item debug) normalized world.memory (succeeds key world.graph))
    (insertionParent : ∀ world,
      CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent world →
      ∀ after, Valid after → Insertion.Native.PrivateFrame normalized world.memory after → parent { world with memory := after })
    (laterPolicy : ∀ world,
      CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent world →
      (world.graph.representatives.getD []).length < 2 ^ 32 - 1 →
      ¬ Insertion.Native.PreparationOOM ops base.allocator (input request.item debug) normalized world.memory →
      succeeds key world.graph = Insertion.Native.observedPolicy ops allocate safety base.allocator owner source address
        (Dispatch.wordDispatchMeaning env other) (input request.item debug) key normalized true
        (world.graph.representatives.getD []) world growth)
    (laterCandidate : ∀ world,
      CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent world →
      (world.graph.representatives.getD []).length < 2 ^ 32 - 1 →
      ¬ Insertion.Native.PreparationOOM ops base.allocator (input request.item debug) normalized world.memory →
      let ran := Insertion.Native.execution ops allocate safety base.allocator owner source address
        (Dispatch.wordDispatchMeaning env other) (input request.item debug) key normalized true
        (world.graph.representatives.getD []) world growth
      ran.1.1 = .ok (some .success) →
        Insertion.Native.observedCandidate ops allocate safety base.allocator owner source address
          (Dispatch.wordDispatchMeaning env other) (input request.item debug) key normalized true
          (world.graph.representatives.getD []) world growth = candidate key world.graph)
    (publishedParent : ∀ world,
      CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent world →
      (world.graph.representatives.getD []).length < 2 ^ 32 - 1 →
      ¬ Insertion.Native.PreparationOOM ops base.allocator (input request.item debug) normalized world.memory →
      Insertion.Native.PublishedObservation ops allocate safety base.allocator owner (Dispatch.wordDispatchMeaning env other)
        (input request.item debug) key normalized growth world →
      parent ((base.primitives source address (input request.item debug)).insert key normalized true world).2)
    (rollbackParent : ∀ world,
      CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent world →
      (world.graph.representatives.getD []).length < 2 ^ 32 - 1 →
      ¬ Insertion.Native.PreparationOOM ops base.allocator (input request.item debug) normalized world.memory →
      Insertion.Native.RefusedObservation ops allocate safety base.allocator owner (Dispatch.wordDispatchMeaning env other)
        (input request.item debug) key normalized growth world →
      parent ((base.primitives source address (input request.item debug)).insert key normalized true world).2)
    (laterInsertion : ∀ world,
      CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent world →
      (world.graph.representatives.getD []).length < 2 ^ 32 - 1 →
      ¬ Insertion.Native.PreparationOOM ops base.allocator (input request.item debug) normalized world.memory →
      ¬ Insertion.Native.BackingAllocationOOM ops allocate base.allocator owner (input request.item debug) normalized growth world →
      ¬ Insertion.Native.PublishedObservation ops allocate safety base.allocator owner (Dispatch.wordDispatchMeaning env other)
        (input request.item debug) key normalized growth world →
      ¬ Insertion.Native.RefusedObservation ops allocate safety base.allocator owner (Dispatch.wordDispatchMeaning env other)
        (input request.item debug) key normalized growth world →
      let actual := (base.primitives source address (input request.item debug)).insert key normalized true world
      ordinary actual.1 = true → GraphFrame safety base.allocator owner rows parent actual.2)
    (hostProbe : OwnedKeys.Physical.Probe σ)
    (external : base.external = Publication.external ops.arguments)
    (publishes : (base.primitives source address (input request.item debug)).publish =
      Publication.publish hostProbe ops.arguments base.allocator source)
    (publicationModel : ∀ world id,
      CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent world →
      modelSeed.publish key id world.graph =
        Interner.publish (hostProbe key (Publication.forget world.memory)).1 key id world.graph)
    (publicationParent : ∀ world id,
      CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent world →
      parent (Publication.publish hostProbe ops.arguments base.allocator source key normalized id world).2)
    (releaseParent : ∀ world after currentRows, parent world →
      world.graph.representatives = some currentRows →
      Caller.GraphCustody base.allocator normalized currentRows world.memory →
      free base.external base.allocator normalized world.memory = (.ok (), after) →
        parent { world with memory := after })
    (ownerOlder : owner < before.memory.memory.nextId)
    (localParent : ∀ world, parent world → parent
      (returnWorld before.memory.memory.nextId constructed.memory.memory.nextId world))
    (expected : Word)
    (item : Prepared request.item debug before constructed)
    (correct : Associative.ConstructorSound (Dispatch.wordBaseMeaning env other) modelChildren)
    (addresses : AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) modelChildren.operation)
    (shifts : ArithmeticShift.Constructs (AddressMask.addressMeaning env other) modelChildren.operation)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read
      request.arguments request.sequence = some expected)
    (insertWords : ∀ heap, Interner.Invariant (Dispatch.wordDispatchMeaning env other) heap →
      key.eval (Dispatch.wordDispatchMeaning env other) heap.read = some expected →
      Interner.Safe (Dispatch.wordDispatchMeaning env other) (modelSeed.insert key true) heap
        (fun id after => after.read id = some expected))
    (publishWords : ∀ id heap, Interner.Invariant (Dispatch.wordDispatchMeaning env other) heap →
      key.eval (Dispatch.wordDispatchMeaning env other) heap.read = some expected → heap.read id = some expected →
      Interner.Safe (Dispatch.wordDispatchMeaning env other) (modelSeed.publish key id) heap (fun _ _ => True)) :
    let actual := invoke base.external base.budget base.allocator
      ((context base owner usizeBits children debug).primitives source) base.queries source request debug before
    let model : Interner.Primitives := { modelSeed with
      simplify := fun key => Dispatch.simplify (Interner.representativeReads taken.world.graph) modelChildren usizeBits
        key.instruction key.arguments debug }
    let logical := Interner.findCode.miss model request key true taken.world.graph
    Returns (GraphFrame safety base.allocator owner rows parent) actual (logical.1.mapError Fault.language) logical.2 ∧
      Semantic.Ensures (Dispatch.wordDispatchMeaning env other) before.graph actual.1 actual.2.world.graph
        (fun id after => after.read id = some expected) ∧
      (∀ opcode borrowed, request = Interner.constructorCode.operationRequest opcode borrowed.items → source = view borrowed →
        let ran := (step base owner usizeBits children).borrowedOperation borrowed.address opcode borrowed.items debug before
        ordinary ran.1 = true → GraphFrame safety base.allocator owner rows parent ran.2 ∧ ran.1 = logical.1.mapError Fault.language ∧ ran.2.graph = logical.2 ∧
          Semantic.Ensures (Dispatch.wordDispatchMeaning env other) before.graph ran.1 ran.2.graph
            (fun id after => after.read id = some expected)) := by
  dsimp only
  have nativeSteps : MissSteps base.external base.allocator
      ((context base owner usizeBits children debug).primitives source address (input request.item debug))
      modelSeed (CallFrame safety base.allocator owner rows source request.arguments normalized
        address (input request.item debug) parent)
      (GraphFrame safety base.allocator owner rows parent) key normalized lookup true
        (true && (request.item.kind == 1)) :=
    { insertion := by
        have complete := insertion_model safety base.allocator owner rows source request.arguments normalized
          address (input request.item debug) parent ops allocate growth (Dispatch.wordDispatchMeaning env other) key lookup
          entry.origin.detached admitted entry.publication.aligned (candidate key) (succeeds key)
          insertionRepresented insertionPolicy insertionParent laterPolicy laterCandidate
          (fun world frame room passed success => by simpa only [inserts] using publishedParent world frame room passed success)
          (fun world frame room passed refused => by simpa only [inserts] using rollbackParent world frame room passed refused)
          (fun world frame room passed backing unpublished noRollback => by
            simpa only [inserts, insertionModel, external] using laterInsertion world frame room passed backing unpublished noRollback)
        simpa only [context, inserts, insertionModel, external] using complete
      publication := by
        intro _ world id frame
        simpa only [context, publishes, external] using frame.publication hostProbe ops.arguments key id lookup
          entry.origin.detached entry.publication.aligned modelSeed (publicationModel world id frame)
          (publicationParent world id frame) (fun before after currentRows held projected custody freed =>
            releaseParent before after currentRows held projected custody (by simpa only [external] using freed))
      failure := by
        intro _ world fault frame
        rw [external]
        obtain ⟨added, data, capacity, facts, custody, _⟩ := frame.1.1
        exact frame.failure ops.arguments lookup entry.origin.detached fault (fun after freed =>
          releaseParent world after (rows ++ added) frame.parent facts.projected custody
            (by simpa only [external] using freed)) }
  exact invoke_step_verified safety owner usizeBits base children modelChildren modelSeed source request debug before constructed
    address pointer memory values prepared taken key normalized lookup rows facts entry privateSource array parent _ kept
    (GraphFrame.locals safety base.allocator owner rows parent before.memory.memory.nextId constructed.memory.memory.nextId
      ownerOlder (by rw [item.nextId]; omega) localParent)
    made room allocated initialized keyed transferred true (fun _ => coupled) nativeSteps classified (fun _ => missed)
    env other expected item (fun _ => correct) (fun _ => addresses) (fun _ => shifts) valid evaluated insertWords (fun _ => publishWords)

end
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
