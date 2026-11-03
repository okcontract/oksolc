/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCheckpointBodyReplay

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Native.CheckpointEntry
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ConstructorItem.NativeRecursion Recursive Interner.InvocationTrace

variable (depth : Nat) (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits : Nat) (meaning : Meaning)
    (base : ConstructorItem.PairInput.Context (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (outerOps : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (outerAllocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (outerBase : ConstructorItem.PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (outerGrowth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent)))
    (debug : AssemblyItem.Fields.Values) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue) (request : Interner.Request)
    (models : AllocationTrace.Models)
    (seed : Interner.Primitives) (incoming : Nat) (stream : List ProtocolEvent) (mismatch : Insertion.Native.Fault)

local notation "fixedChildren" => AllocationTrace.streamReplay stream models

local notation "nativeChildren" => AllocationTrace.children ops allocate safety owner meaning base growth usizeBits (depth + 1)
local notation "nativeObservations" => ChildTrace.liftObservations
  (ProtocolTrace.observe (AllocationTrace.unfold ops allocate safety owner meaning base growth usizeBits (depth + 1)))
local notation "physicalPorts" => physical outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
  nativeChildren debug source address input
local notation "recordedPorts" => AllocationTrace.graphObservations outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
  nativeChildren nativeObservations debug source address input

/-- The remaining local body obligations at a taken miss. Initial native
admission and proper-child bodies replace reached-state correspondence. The
fixed stream derives the child model by exact history rebasing; no completed result,
cleanup success or selected dispatcher projection is an input. -/
def BodyMiss (key : Key) (deterministic : Bool)
    (taken : Recorded (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent))) (trailing : List ProtocolEvent) : Prop :=
  ∀ (slice : ArgumentSlice) (handle : Handle) (lookup : NormalizationOwnership.State),
    taken.native.scope = ⟨some handle, some slice, false⟩ →
    taken.tokens = { lookup := some lookup, items := handle.values, phase := .cleanup } →
    key.arguments = slice.items →
    ∃ (rows : List Storage.Cell) (parent : World (Publication.Effects σ) → Prop),
      let decision := MissStream.selected physicalPorts request key slice deterministic taken.native.world
      let middle := if deterministic && request.item.kind == 1 then (recordedPorts).simplify key slice taken.native.world else []
      let observed := MissStream.segment outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
        nativeChildren debug source address input request key slice deterministic taken.native.world handle lookup
      let bodyEvents := match decision.1 with
        | .ok none => (recordedPorts).insert key slice deterministic decision.2
        | _ => observed.body
      let history := taken.events ++ middle ++ bodyEvents ++ observed.cleanup
      let rawStream := ChildTrace.history decision.2 ++ (bodyEvents ++ observed.cleanup ++ trailing)
      CallFrame safety outerBase.allocator owner rows source request.arguments slice address input parent (ChildTrace.erase taken.native.world) ∧
      history ++ trailing = stream ∧
      ((deterministic && (request.item.kind == 1)) = true → ∀ reachedRows,
        AllocationTrace.BodiesAt taken.events rawStream taken.native.world
          (fun world => CallFrame safety outerBase.allocator owner rows source request.arguments slice address input parent world ∧
            InputFrame safety outerBase.allocator owner reachedRows source request.arguments slice world)
          (Nested.storageReads reachedRows) debug (AllocationTrace.body ops allocate safety owner meaning base growth usizeBits depth) models)

/-- Both induction forms use the same actual initialization/take prefix and
six source guards. No caller outcome is presumed by this conversion. -/
def BodyInduction (buffer : View) (before : Recorded (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (trailing : List ProtocolEvent) : Prop :=
  AtMiss outerOps outerBase source request
    (fun key deterministic taken => BodyMiss depth ops allocate safety owner usizeBits meaning base growth
      outerOps outerAllocate outerBase outerGrowth debug source address input request models stream key deterministic taken trailing)
    buffer before

theorem miss_from_bodies (key : Key) (deterministic : Bool)
    (taken : Recorded (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent))) (trailing : List ProtocolEvent)
    (bodies : BodyMiss depth ops allocate safety owner usizeBits meaning base growth outerOps outerAllocate outerBase outerGrowth
      debug source address input request models stream key deterministic taken trailing) :
    Miss outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits nativeChildren nativeObservations
      debug source address input request fixedChildren seed incoming stream mismatch key deterministic taken trailing := by
  intro slice handle lookup locals tokens aligned
  obtain ⟨rows, parent, frame, history, proper⟩ := bodies slice handle lookup locals tokens aligned
  have checked := AllocationTrace.selected_from_bodies depth ops allocate safety owner usizeBits meaning base growth
    outerOps outerAllocate outerBase outerGrowth debug source address input request key slice deterministic taken.native.world models
    (AllocationTrace.inputGraphReplay seed input incoming meaning stream mismatch) request.arguments rows parent frame aligned taken.events _ (by with_reducible exact proper)
  refine ⟨rows, fun world => parent (ChildTrace.erase world),
    fun completed => (CallFrame.mapAllocator_iff Prod.fst).mp (checked.2 completed).1, history, fun completed => ?_⟩
  have same := (checked.2 completed).2
  rw [checked.1, AllocationTrace.replay_appended] at same
  have joined := history
  simp only [AllocationTrace.graphObservations, List.append_assoc] at joined
  simpa only [scopeView, middle, AllocationTrace.graphObservations, List.append_assoc, joined] using same

theorem induction_from_bodies (buffer : View) (before : Recorded (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (trailing : List ProtocolEvent)
    (bodies : BodyInduction depth ops allocate safety owner usizeBits meaning base growth outerOps outerAllocate outerBase outerGrowth
      debug source address input request models stream buffer before trailing) :
    Induction outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits nativeChildren nativeObservations
      debug source address input request fixedChildren seed incoming stream mismatch buffer before trailing := by
  exact AtMiss.mono outerOps outerBase source request _ _ buffer before
    (fun key deterministic taken => miss_from_bodies depth ops allocate safety owner usizeBits meaning base growth
      outerOps outerAllocate outerBase outerGrowth debug source address input request models seed incoming stream mismatch
      key deterministic taken trailing) bodies

omit incoming in
/-- The derived proper-child obligations reach the existing caller entry
continuation. Actual initialization/take derive alignment and transfer identity;
the original recorder, suffix and cleanup proofs supply the complete result. -/
theorem entry_continuation_from_bodies (before : ChildTrace.TracedWorld σ ProtocolEvent)
    (memory : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (leading trailing : List ProtocolEvent) (other : Meaning) (read : Read) (sequence : BitVec 32)
    (good : Good source request.arguments before) (admitted : Admitted outerOps.arguments)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (closedQuery : outerBase.queries.deterministic request.item = Interner.Queries.queries.deterministic request.item)
    (bodies : BodyInduction depth ops allocate safety owner usizeBits meaning base growth outerOps outerAllocate outerBase outerGrowth
      debug source address input request models stream ⟨before.memory.memory.nextId, 0, 2⟩
      ⟨⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩, {}, leading⟩ trailing) :
    MissContinuation (Publication.external outerOps.arguments) outerBase.budget outerBase.allocator physicalPorts outerBase.queries recordedPorts
      (dispatchModel (AllocationTrace.inputGraphReplay seed input (before.memory.memory.nextId + 1) meaning stream mismatch) fixedChildren usizeBits debug)
      source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩, {}, leading⟩ trailing :=
  entry_continuation outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits nativeChildren nativeObservations
    debug source address input request fixedChildren seed stream mismatch before memory pointer leading trailing other read sequence
    good admitted allocated closedQuery
    (induction_from_bodies depth ops allocate safety owner usizeBits meaning base growth outerOps outerAllocate outerBase outerGrowth
      debug source address input request models seed (before.memory.memory.nextId + 1) stream mismatch _ _ trailing bodies)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Native.CheckpointEntry
