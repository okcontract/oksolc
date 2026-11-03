/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorTakenSite
import Compiler.Extraction.InternerRecursiveJointEntries

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Caller.ProtocolTrace
open NativeRecursion Recursive Interner.InvocationTrace

variable (ops : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (allocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (safety : Bool) (owner usizeBits : Nat)
    (base : PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (growth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent)))
    (children : Constructors (Publication.Effects σ)) (observations : ChildTrace.Observations σ ProtocolEvent)
    (env : AddressMask.Environment) (other : Meaning) (debug : AssemblyItem.Fields.Values)
    (source : View) (request : Interner.Request) (rows : List Storage.Cell)
    (parent : ChildTrace.TracedWorld σ ProtocolEvent → Prop) (leading trailing : List ProtocolEvent)

local notation "nativeBase" => callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth
local notation "child" => ChildTrace.constructors children observations

abbrev sitePrefix (site : TakenSite (ChildTrace.Recorded σ ProtocolEvent)) :=
  takenPrefix (Publication.external ops.arguments) base.budget base.allocator source request site.constructed site.memory leading

/-- Existing proper-child laws at this actual prefix. The native package owns
the frame and word laws; recorded induction also needs projection for any
reached row prefix. No fixed replay-model equality is assumed here. -/
def SiteChildren (site : TakenSite (ChildTrace.Recorded σ ProtocolEvent)) : Prop :=
  let recorded := (sitePrefix ops base source request leading site).2
  let cursor := MissStream.childCursor recorded.events.length recorded.native.world
  ∃ childModel,
    ((site.deterministic && (request.item.kind == 1)) = true → ∀ rows,
      (projectionAt (cursorGraph cursor) (CallFrame safety base.allocator owner rows source request.arguments site.normalized
        site.address (input request.item debug) parent)).SourceConstructorsAt (Nested.storageReads rows) debug child childModel) ∧
    TakenFramesAt cursor safety owner usizeBits nativeBase child childModel source request debug rows parent
      site.address site.key site.normalized site.lookup site.deterministic env other

/-- Select the existing replay construction from the actual recorded token.
Absent tokens use the seed; they cannot satisfy a reached taken-token premise. -/
def siteReplay (site : TakenSite (ChildTrace.Recorded σ ProtocolEvent))
    (seed : Interner.Primitives) (childModel : Associative.Constructors AssemblyItem.Fields.Values)
    (mismatch : Insertion.Native.Fault) : Interner.Primitives :=
  let recorded := (sitePrefix ops base source request leading site).2
  match recorded.tokens.lookup with
  | none => seed
  | some token => replayModel ops allocate safety owner usizeBits base growth children observations env other debug source request
      site.address site.key site.normalized site.lookup site.deterministic recorded token trailing seed childModel mismatch

theorem siteReplay_queries (site : TakenSite (ChildTrace.Recorded σ ProtocolEvent))
    (seed : Interner.Primitives) (childModel : Associative.Constructors AssemblyItem.Fields.Values)
    (mismatch : Insertion.Native.Fault) :
    (siteReplay ops allocate safety owner usizeBits base growth children observations env other debug source request leading trailing site seed childModel mismatch).atCapacity = seed.atCapacity ∧
    (siteReplay ops allocate safety owner usizeBits base growth children observations env other debug source request leading trailing site seed childModel mismatch).deterministic = seed.deterministic := by
  unfold siteReplay
  dsimp only
  cases (sitePrefix ops base source request leading site).2.tokens.lookup <;> exact ⟨rfl, rfl⟩

theorem siteReplay_taken (site : TakenSite (ChildTrace.Recorded σ ProtocolEvent))
    (seed : Interner.Primitives) (childModel : Associative.Constructors AssemblyItem.Fields.Values)
    (mismatch : Insertion.Native.Fault)
    (coupled : (site.deterministic && (request.item.kind == 1)) = true → ∀ rows,
      (projectionAt (cursorGraph (MissStream.childCursor (sitePrefix ops base source request leading site).2.events.length
        (sitePrefix ops base source request leading site).2.native.world))
        (CallFrame safety base.allocator owner rows source request.arguments site.normalized site.address (input request.item debug) parent)).SourceConstructorsAt (Nested.storageReads rows) debug child childModel)
    (native : TakenFramesAt (MissStream.childCursor (sitePrefix ops base source request leading site).2.events.length
      (sitePrefix ops base source request leading site).2.native.world) safety owner usizeBits nativeBase child childModel
      source request debug rows parent site.address site.key site.normalized site.lookup site.deterministic env other) :
    TakenModel ops allocate safety owner usizeBits base growth children observations env other debug source request rows parent
      site.address site.key site.normalized site.lookup site.deterministic (sitePrefix ops base source request leading site).2
      (siteReplay ops allocate safety owner usizeBits base growth children observations env other debug source request leading trailing site seed childModel mismatch) trailing := by
  intro token tokens
  refine ⟨childModel, seed, mismatch, coupled, native.frames, native.correct, native.addresses, native.shifts, ?_⟩
  have lookup := congrArg (fun (tokens : Tokens) => tokens.lookup) tokens
  simp only [siteReplay, lookup]

variable (before : ChildTrace.TracedWorld σ ProtocolEvent) (seed : Interner.Primitives) (mismatch : Insertion.Native.Fault)
    (retained : ∀ after, Valid after.memory → after.graph = before.graph → Retains before after → parent after)
    (localParent : ∀ constructed address, prepare request.item debug before = (.ok address, constructed) →
      ∀ world, parent world → parent (returnWorld before.memory.memory.nextId constructed.memory.memory.nextId world))
    (laws : ∀ site : TakenSite (ChildTrace.Recorded σ ProtocolEvent),
      site.Reached (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth)
        source request debug before →
      SiteChildren ops allocate safety owner usizeBits base growth children observations env other debug source request rows parent leading site)

attribute [local irreducible] siteReplay replayModel takenPrefix

include mismatch retained localParent laws in
/-- Prefix determinacy constructs one fixed entry model. All reached misses
use that same model; earlier failures and cache hits keep the seed queries and
need no child witness. Only existing proper-child and native frame laws remain. -/
theorem JointEntry.exists_model : ∃ model : Interner.Primitives,
    model.atCapacity = seed.atCapacity ∧ model.deterministic = seed.deterministic ∧
    JointEntry ops allocate safety owner usizeBits base growth children observations env other debug source request rows parent
      model before leading trailing := by
  classical
  by_cases reached : ∃ site : TakenSite (ChildTrace.Recorded σ ProtocolEvent), site.Reached nativeBase source request debug before
  · obtain ⟨site, selected⟩ := reached
    obtain ⟨childModel, coupled, native⟩ := laws site selected
    let model := siteReplay ops allocate safety owner usizeBits base growth children observations env other debug source request leading trailing site seed childModel mismatch
    have queries := siteReplay_queries ops allocate safety owner usizeBits base growth children observations env other debug source request leading trailing site seed childModel mismatch
    refine ⟨model, queries.1, queries.2, retained, localParent, ?_⟩
    intro constructed address pointer memory values prepared taken key normalized lookup deterministic
      made room allocated initialized classified keyed missed transferred input
    have same : site = ⟨constructed, address, pointer, memory, values, prepared, taken, key, normalized, lookup, deterministic⟩ :=
      selected.unique ⟨made, room, allocated, initialized, classified, keyed, missed, transferred, input⟩
    cases same
    exact siteReplay_taken ops allocate safety owner usizeBits base growth children observations env other debug source request rows parent leading trailing
      _ seed childModel mismatch coupled native
  · refine ⟨seed, rfl, rfl, retained, localParent, ?_⟩
    intro constructed address pointer memory values prepared taken key normalized lookup deterministic
      made room allocated initialized classified keyed missed transferred input
    exact (reached ⟨⟨constructed, address, pointer, memory, values, prepared, taken, key, normalized, lookup, deterministic⟩,
      ⟨made, room, allocated, initialized, classified, keyed, missed, transferred, input⟩⟩).elim

include mismatch retained localParent laws in
/-- Construct the entry model and immediately consume it in the existing joint
item theorem. The seed supplies only the two source queries; the actual prefix
and suffix determine replay. This pointwise witness does not yet give one
coherent recursive model for every input and depth. -/
theorem item_replay_joint {capacity : Nat} {data : Compiler.ZigAir.Memory.Address}
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (represented : Represents before.memory.memory source request.arguments)
    (privateSource : Caller.SourcePrivate source before.memory.effects.keys)
    (array : ArraySource source before.memory.memory)
    (admitted : Admitted ops.arguments)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (capacityQuery : seed.atCapacity { before.graph with allocationCursor := leading.length } = base.queries.atCapacity before.graph)
    (classificationQuery : seed.deterministic request.item = base.queries.deterministic request.item)
    (expected : Word) (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read request.arguments request.sequence = some expected)
    (pushes : request.item.kind = 2#32 → Insertion.Native.PushValues other) :
    ∃ model : Interner.Primitives,
      model.atCapacity = seed.atCapacity ∧ model.deterministic = seed.deterministic ∧
      JointPost model request before.graph leading trailing (Dispatch.wordDispatchMeaning env other)
        (GraphFrame safety base.allocator owner rows parent)
        (item (jointContext ops allocate safety owner usizeBits base growth children observations env other debug)
          (jointPorts ops allocate safety owner usizeBits base growth children observations env other debug)
          source request debug before leading) expected := by
  obtain ⟨model, capacitySame, classificationSame, joint⟩ := JointEntry.exists_model ops allocate safety owner usizeBits base growth
    children observations env other debug source request rows parent leading trailing before seed mismatch
    retained localParent laws
  refine ⟨model, capacitySame, classificationSame, ?_⟩
  exact item_joint_verified ops allocate safety owner usizeBits base growth children observations env other debug source request rows parent
    joint facts represented privateSource array admitted domain typed (by rw [capacitySame]; exact capacityQuery)
    (by rw [classificationSame]; exact classificationQuery) expected valid evaluated pushes

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
