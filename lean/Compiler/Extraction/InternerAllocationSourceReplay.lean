/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeAllocationEntry

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Recursive
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Caller.ProtocolTrace (ProtocolEvent)
open ConstructorItem.ProtocolTrace (Capture mapConstructors prefixCapture)

abbrev Models := Associative.Constructors AssemblyItem.Fields.Values (fun α => Nat × Nat → Interner.Action α)

def replay (leading stream : List ProtocolEvent) (root : ChildTrace.TracedWorld σ ProtocolEvent)
    (models : Models) : Associative.Constructors AssemblyItem.Fields.Values :=
  mapConstructors (fun model => enter (rebase leading (ChildTrace.history root).length stream) >>= model) models

/-- One child family for the fixed complete caller stream. Actual native entry
observations supply each body's identities; no reached miss chooses a model. -/
def streamReplay (stream : List ProtocolEvent) (models : Models) : Associative.Constructors AssemblyItem.Fields.Values :=
  mapConstructors (fun model => enter stream >>= model) models

/-- Erasing the original raw history prefix and restoring the caller prefix
produces the same fixed child model, with the complete suffix retained. -/
theorem replay_appended (leading middle trailing : List ProtocolEvent) (root : ChildTrace.TracedWorld σ ProtocolEvent)
    (models : Models) :
    replay leading (ChildTrace.history root ++ middle ++ trailing) root models =
      streamReplay (leading ++ middle ++ trailing) models := by
  simp only [replay, streamReplay, rebase, List.append_assoc, List.drop_left]

/-- Body obligations retain the dispatcher's source-query guards. Allocation
identities are inputs to each body model, supplied by the common entry replay. -/
structure BodiesAt (leading stream : List ProtocolEvent) (root : ChildTrace.TracedWorld σ ProtocolEvent)
    (predicate : World (Publication.Effects σ) → Prop) (reads : Nested.Reads)
    (debug : AssemblyItem.Fields.Values) (captured : ProtocolTrace.Captures σ) (models : Models) : Prop where
  operation : ∀ opcode values, BodyReplay leading stream root predicate
    (captured.operation opcode values debug) (models.operation opcode values debug)
  constant : ∀ value, BodyReplay leading stream root predicate
    (captured.constant value debug) (models.constant value debug)
  materialize : ∀ id value, BodyReplay leading stream root predicate
    (captured.materialize id value debug) (models.materialize id value debug)
  borrowed : ∀ id queried (source : ArgumentSlice), reads.operation id queried = .ok (some source) → ∀ opcode,
    BodyReplay leading stream root predicate (captured.borrowedOperation source.address opcode source.items debug)
      (models.borrowedOperation source.address opcode source.items debug)
  namedLocal : ∀ id opcode (source : ArgumentSlice), reads.operation id opcode = .ok (some source) → source.items.length = 2 →
    ∀ selected, selected < 2 → ∀ repeated first,
      BodyReplay leading stream root predicate (captured.localOperation opcode source selected repeated first debug)
        (models.localOperation opcode source selected repeated first debug)

def Prefixes (captured : ProtocolTrace.Captures σ) : Prop :=
  ∀ earlier leading,
    mapConstructors (m := Capture (Publication.Effects σ))
      (n := fun _ => World (Publication.Effects σ) → Except Fault NodeId × Caller.ProtocolTrace.Recorded (Publication.Effects σ))
      (fun action before => action before (earlier ++ leading)) captured =
    mapConstructors (prefixCapture earlier leading) captured

/-- Derive the existing source-aware child contract from body replay only.
This uses one entry proof for every route, with the same actual source guards. -/
theorem source_projects (captured : ProtocolTrace.Captures σ) (prefixed : Prefixes captured)
    (leading stream : List ProtocolEvent) (root : ChildTrace.TracedWorld σ ProtocolEvent)
    (predicate : World (Publication.Effects σ) → Prop) (reads : Nested.Reads)
    (debug : AssemblyItem.Fields.Values) (models : Models)
    (bodies : BodiesAt leading stream root predicate reads debug captured models) :
    (Resource.projection ChildTrace.history stream (cursorGraph (MissStream.childCursor leading.length root))
      (Frame root predicate)).SourceConstructorsAt reads debug
      (mapConstructors (fun action => record (mark action)) captured) (replay leading stream root models) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro opcode values _
    refine marked_projects _ ?_ _ _ _ _ _ (bodies.operation opcode values)
    intro before earlier rest
    exact congrArg (fun family => family.operation opcode values debug before) (prefixed earlier rest)
  · intro value _
    refine marked_projects _ ?_ _ _ _ _ _ (bodies.constant value)
    intro before earlier rest
    exact congrArg (fun family => family.constant value debug before) (prefixed earlier rest)
  · intro id value _
    refine marked_projects _ ?_ _ _ _ _ _ (bodies.materialize id value)
    intro before earlier rest
    exact congrArg (fun family => family.materialize id value debug before) (prefixed earlier rest)
  · intro id queried source found opcode _
    refine marked_projects _ ?_ _ _ _ _ _ (bodies.borrowed id queried source found opcode)
    intro before earlier rest
    exact congrArg (fun family => family.borrowedOperation source.address opcode source.items debug before) (prefixed earlier rest)
  · intro id opcode source found shape selected bound repeated first _
    refine marked_projects _ ?_ _ _ _ _ _ (bodies.namedLocal id opcode source found shape selected bound repeated first)
    intro before earlier rest
    exact congrArg (fun family => family.localOperation opcode source selected repeated first debug before) (prefixed earlier rest)

variable (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner : Nat) (meaning : Meaning) (base : PairInput.Context (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (usizeBits : Nat)

/-- The existing native wrapper body with actual observations of proper
children. This is an alias of the existing capture, not a new execution path. -/
def body (depth : Nat) : ProtocolTrace.Captures σ :=
  step ops allocate safety owner meaning base growth usizeBits
    (NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth)
    (ProtocolTrace.observe (unfold ops allocate safety owner meaning base growth usizeBits depth))

theorem record_marked_map (captured : ProtocolTrace.Captures σ) :
    mapConstructors record (mapConstructors mark captured) =
      mapConstructors (fun action => record (mark action)) captured := rfl

theorem step_source_projects (depth : Nat)
    (leading stream : List ProtocolEvent) (root : ChildTrace.TracedWorld σ ProtocolEvent)
    (predicate : World (Publication.Effects σ) → Prop) (reads : Nested.Reads)
    (debug : AssemblyItem.Fields.Values) (models : Models)
    (bodies : BodiesAt leading stream root predicate reads debug
      (body ops allocate safety owner meaning base growth usizeBits depth) models) :
    (Resource.projection ChildTrace.history stream (cursorGraph (MissStream.childCursor leading.length root))
      (Frame root predicate)).SourceConstructorsAt reads debug
      (children ops allocate safety owner meaning base growth usizeBits (depth + 1)) (replay leading stream root models) := by
  rw [children_recorded]
  change (Resource.projection ChildTrace.history stream (cursorGraph (MissStream.childCursor leading.length root))
    (Frame root predicate)).SourceConstructorsAt reads debug
      (mapConstructors record (mapConstructors mark (body ops allocate safety owner meaning base growth usizeBits depth)))
      (replay leading stream root models)
  rw [record_marked_map]
  exact source_projects (body ops allocate safety owner meaning base growth usizeBits depth) (step_prefix ops allocate safety owner meaning base growth usizeBits _ _)
    leading stream root predicate reads debug models bodies

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
