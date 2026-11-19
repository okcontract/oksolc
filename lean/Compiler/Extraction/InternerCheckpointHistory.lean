/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeAllocationTrace
import Compiler.Extraction.InternerCallerProtocolMiss
import Compiler.Extraction.InternerNativeFrameInduction

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Native
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ConstructorItem.NativeRecursion Recursive Interner.InvocationTrace

/-- The native checkpoint and cleanup history is determined without a logical
model, stream-admission or selected-result correspondence premise. -/
theorem checkpoint_miss_history
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner : Nat) (meaning : Meaning)
    (base : ConstructorItem.PairInput.Context (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (usizeBits : Nat) (children : Constructors (Publication.Effects σ))
    (observations : ChildTrace.Observations σ ProtocolEvent) (debug : AssemblyItem.Fields.Values)
    (source buffer : View) (address : Compiler.ZigAir.Memory.Address) (input : AssemblyClone.NativeFields.ItemValue)
    (request : Interner.Request) (key : Key) (slice : ArgumentSlice) (deterministic : Bool)
    (before : World (Publication.Effects σ)) (handle : Handle) (lookup : NormalizationOwnership.State)
    (values : List NodeId) (rows : List Storage.Cell) (leading : List ProtocolEvent)
    (aligned : key.arguments = slice.items)
    (detached : handle.owned = none) (unowned : lookup.owned = false) (caller : lookup.owner = .caller) :
    let p := physical ops allocate safety owner meaning base growth usizeBits children debug source address input
    let ports := AllocationTrace.graphObservations ops allocate safety owner meaning base growth usizeBits children observations debug source address input
    let decision := MissStream.selected p request key slice deterministic before
    let middle := if deterministic && request.item.kind == 1 then ports.simplify key slice before else []
    let observed := MissStream.segment ops allocate safety owner meaning base growth usizeBits children debug source address input
      request key slice deterministic before handle lookup
    let bodyEvents := match decision.1 with
      | .ok none => ports.insert key slice deterministic decision.2
      | _ => observed.body
    let initialRecord : Recorded (Publication.Effects σ) :=
      ⟨⟨before, ⟨some handle, some slice, false⟩⟩, { lookup := some lookup, items := handle.values, phase := .cleanup }, leading⟩
    let body := missBody (Publication.external ops.arguments) base.budget base.allocator p base.queries ports source buffer
      request key deterministic initialRecord
    (ordinary decision.1 = true → InputFrame safety base.allocator owner rows source values slice decision.2) →
    ordinary body.1 = true →
    (finish (Publication.external ops.arguments) base.allocator body.1 body.2).2.events =
      leading ++ middle ++ bodyEvents ++ observed.cleanup := by
  intro p ports decision middle observed bodyEvents initialRecord body preserved completed
  classical
  by_cases chosen : decision.1 = .ok none
  · have recorded := miss_insert_recorded (Publication.external ops.arguments) base.budget base.allocator p base.queries ports source buffer
      request key slice deterministic before handle lookup leading chosen
    have cleanup : observed.cleanup = [] := by
      have nativeChosen := chosen
      dsimp only [decision, p, physical] at nativeChosen
      simp only [observed, MissStream.segment, nativeChosen]
    have closed := (Close.transferred_stream (Publication.external ops.arguments) base.allocator lookup handle slice
      (p.insert key slice deterministic decision.2).2 ([] : List ProtocolEvent) [] detached unowned caller).1
    dsimp only [decision] at closed
    change body = _ at recorded
    rw [recorded] at completed ⊢
    simp only [finish, completed, ↓reduceIte, record, closing, closed, List.map_nil, List.append_nil,
      bodyEvents, chosen, cleanup]
    rfl
  · have emitted : bodyEvents = observed.body := by
      cases result : decision.1 with
      | error fault => simp only [bodyEvents, result]
      | ok value => cases value with
        | none => exact False.elim (chosen result)
        | some id => simp only [bodyEvents, result]
    let originalPorts := graphObservations ops allocate safety owner meaning base growth usizeBits children observations debug source address input
    have same := miss_insert_irrelevant (Publication.external ops.arguments) base.budget base.allocator p base.queries
      ports originalPorts source buffer request key slice deterministic initialRecord rfl rfl rfl chosen
    have captured := miss_recorded ops allocate safety owner meaning base growth usizeBits children observations debug source buffer
      address input request key slice deterministic before handle lookup values rows leading aligned preserved
    have clean := miss_cleanup_segment ops allocate safety owner meaning base growth usizeBits children debug source
      address input request key slice deterministic before handle lookup detached unowned caller
    change body = _ at same
    rw [same, captured.1] at completed ⊢
    simp only [finish, completed, ↓reduceIte, record, closing, captured.2.1, captured.2.2.1,
      Option.isSome_some, ↓reduceIte, ← captured.2.2.2, clean completed, emitted]
    rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Native

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Recursive

/-- Native selected-miss frames follow from the finite frame induction alone.
The reached query snapshot is derived from native graph facts. -/
theorem Enclosing.unfold_selected_frame
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits : Nat) (base : PairInput.Context (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning)
    (debug : AssemblyItem.Fields.Values) (depth : Nat) (rows : List Storage.Cell)
    (source : View) (values : List NodeId) (normalized : ArgumentSlice)
    (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue)
    (parent : World (Publication.Effects σ) → Prop) (stack : Enclosing safety base.allocator owner parent)
    (admitted : Admitted ops.arguments) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (before : World (Publication.Effects σ))
    (initial : CallFrame safety base.allocator owner rows source values normalized address native parent before)
    (request : Interner.Request) (key : Key) (deterministic : Bool) :
    let children := unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth
    let p := Caller.ProtocolTrace.Native.physical ops allocate safety owner meaning base growth usizeBits children debug source address native
    let decision := MissStream.selected p request key normalized deterministic before
    ordinary decision.1 = true →
      CallFrame safety base.allocator owner rows source values normalized address native parent decision.2 := by
  intro children p decision
  dsimp only [decision, MissStream.selected]
  split
  · let frame := CallFrame safety base.allocator owner rows source values normalized address native parent
    obtain ⟨added, data, capacity, facts, custody, privateSource⟩ := initial.1.1
    let extended := CallFrame safety base.allocator owner (rows ++ added) source values normalized address native frame
    have ready : extended before :=
      ⟨⟨⟨[], data, capacity, by simpa only [List.append_nil] using facts,
        by simpa only [List.append_nil] using custody, privateSource⟩, initial.1.2⟩,
        initial.2.1, initial, initial.arraySource⟩
    have proper := (Enclosing.call stack).unfold_frames ops allocate safety owner usizeBits base growth meaning debug depth
      (rows ++ added) source values normalized address native frame admitted typed
    have kept := dispatcher_keeps (callerContext ops allocate safety owner meaning base growth) owner usizeBits children
      debug source address native key normalized extended before ready (by
        rw [facts.reads]
        simpa only [Interner.representativeReads, facts.projected] using proper)
    exact fun completed => (kept completed).parent
  · exact fun _ => initial

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Native
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ConstructorItem.NativeRecursion Recursive Interner.InvocationTrace

/-- Complete finite native miss history, including ordinary failure and deferred
cleanup. Existing native frame induction discharges the selected-frame premise;
no recursive replay, logical result, final graph or complete stream is assumed. -/
theorem unfold_checkpoint_miss_history
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner : Nat) (meaning : Meaning)
    (base : ConstructorItem.PairInput.Context (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (usizeBits depth : Nat)
    (debug : AssemblyItem.Fields.Values)
    (source buffer : View) (address : Compiler.ZigAir.Memory.Address) (input : AssemblyClone.NativeFields.ItemValue)
    (request : Interner.Request) (key : Key) (slice : ArgumentSlice) (deterministic : Bool)
    (before : World (Publication.Effects σ)) (handle : Handle) (lookup : NormalizationOwnership.State)
    (values : List NodeId) (rows : List Storage.Cell) (leading : List ProtocolEvent)
    (parent : World (Publication.Effects σ) → Prop) (stack : Enclosing safety base.allocator owner parent)
    (admitted : Admitted ops.arguments) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (initial : CallFrame safety base.allocator owner rows source values slice address input parent before)
    (aligned : key.arguments = slice.items)
    (detached : handle.owned = none) (unowned : lookup.owned = false) (caller : lookup.owner = .caller) :
    let children := unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth
    let observations := ProtocolTrace.observe (AllocationTrace.unfold ops allocate safety owner meaning base growth usizeBits depth)
    let p := physical ops allocate safety owner meaning base growth usizeBits children debug source address input
    let ports := AllocationTrace.graphObservations ops allocate safety owner meaning base growth usizeBits children observations debug source address input
    let decision := MissStream.selected p request key slice deterministic before
    let middle := if deterministic && request.item.kind == 1 then ports.simplify key slice before else []
    let observed := MissStream.segment ops allocate safety owner meaning base growth usizeBits children debug source address input
      request key slice deterministic before handle lookup
    let bodyEvents := match decision.1 with
      | .ok none => ports.insert key slice deterministic decision.2
      | _ => observed.body
    let initialRecord : Recorded (Publication.Effects σ) :=
      ⟨⟨before, ⟨some handle, some slice, false⟩⟩, { lookup := some lookup, items := handle.values, phase := .cleanup }, leading⟩
    let body := missBody (Publication.external ops.arguments) base.budget base.allocator p base.queries ports source buffer
      request key deterministic initialRecord
    ordinary body.1 = true →
    (finish (Publication.external ops.arguments) base.allocator body.1 body.2).2.events =
      leading ++ middle ++ bodyEvents ++ observed.cleanup := by
  intro children observations p ports decision middle observed bodyEvents initialRecord body completed
  exact checkpoint_miss_history ops allocate safety owner meaning base growth usizeBits children observations debug
    source buffer address input request key slice deterministic before handle lookup values rows leading aligned detached unowned caller
    (fun ordinaryResult => (stack.unfold_selected_frame ops allocate safety owner usizeBits base growth meaning debug depth
      rows source values slice address input parent admitted typed before initial request key deterministic ordinaryResult).1) completed

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Native
