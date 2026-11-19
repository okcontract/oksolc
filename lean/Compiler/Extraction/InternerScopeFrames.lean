/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.InternerScopeControl
import Compiler.Extraction.RecursiveFrames

namespace Compiler.Extraction.Interner.Scoped
open Compiler.Algebraic Compiler.Extraction.Cache

/-- Scope operations may change ownership and allocator state, but cannot
rewrite the graph or cache. This equality also retains partial word reads. -/
def LocalEffect (action : Action α) : Prop := ∀ before,
  (action before).2.heap = { before.heap with allocationCursor := (action before).2.heap.allocationCursor }

theorem initialize_local (r : Resources) (request : Request) : LocalEffect (initScope r request) := by
  intro before
  unfold initScope
  cases commutative request.item with
  | error error => rfl
  | ok commutes =>
    simp only []
    cases normalizationOwnershipCode.initWith commutes request.arguments.length 2
        (r.allocate .temporary request.arguments) before.heap.allocationCursor with
    | mk lookup cursor => cases lookup <;> rfl

theorem take_local (r : Resources) : LocalEffect (take r) := by
  intro before
  unfold take
  cases before.scope.lookup with
  | none => rfl
  | some lookup => rfl

theorem handoff_local : LocalEffect handoff := fun _ => rfl

theorem close_heap (r : Resources) (before : Session) :
    (close r before).heap = { before.heap with allocationCursor := (close r before).heap.allocationCursor } := by
  cases present : before.scope.lookup <;> simp [close, present]

/-- Structural preservation observes the existing representative graph through
the session. No semantic invariant or successful-result premise is required. -/
def Frames (action : Action α) : Prop := ∀ before, Extends before.heap (action before).2.heap

theorem Frames.pure (value : α) : Frames (pure value) := fun before => Extends.refl before.heap

theorem Frames.local (action : Action α) (localEffect : LocalEffect action) : Frames action := by
  intro before cells present
  rw [localEffect before]
  exact ⟨[], by simpa using present⟩

theorem Frames.graph (action : Interner.Action α) (framed : Interner.Frames action) : Frames (liftGraph action) :=
  fun before => framed before.heap

theorem Frames.bind (first : Action α) (next : α → Action β)
    (firstFrames : Frames first) (nextFrames : ∀ value, Frames (next value)) : Frames (first >>= next) := by
  intro before
  have framed := firstFrames before
  change Extends before.heap (Effect.bind first next before).2.heap
  unfold Effect.bind
  cases step : first before with
  | mk result middle =>
    rw [step] at framed
    cases result with
    | error error => exact framed
    | ok value => exact framed.trans (nextFrames value middle)

theorem miss_frames (code : FindCode) (r : Resources) (p : Primitives)
    (primitive : Recursive.PrimitiveFrames p) (simplify : ∀ key, Interner.Frames (p.simplify key))
    (request : Request) (key : Key) (deterministic : Bool) :
    Frames (code.controlMiss (execution r p) request key deterministic) := by
  unfold FindCode.controlMiss
  simp only [execution]
  split
  · apply Frames.bind _ _ (Frames.graph _ (simplify key))
    intro result
    cases result with
    | none =>
      exact Frames.bind _ _ (Frames.local _ handoff_local)
        (fun _ => Frames.graph _ (primitive.insert key deterministic))
    | some id =>
      apply Frames.bind _ _ (Frames.graph _ (primitive.publish _ _))
      intro ignored
      exact Frames.bind _ _ (Frames.local _ handoff_local) (fun _ => Frames.pure _)
  · exact Frames.bind _ _ (Frames.local _ handoff_local)
      (fun _ => Frames.graph _ (primitive.insert key deterministic))

theorem owned_frames (code : FindCode) (r : Resources) (p : Primitives)
    (primitive : Recursive.PrimitiveFrames p) (simplify : ∀ key, Interner.Frames (p.simplify key))
    (request : Request) (args : List NodeId) (deterministic : Bool) :
    Frames (code.controlOwned (execution r p) request args deterministic) := by
  unfold FindCode.controlOwned
  simp only [execution]
  apply Frames.bind _ _ (Frames.local _ (take_local r))
  intro ignored
  exact Frames.bind _ _ (Frames.graph _ (Interner.Frames.lift _))
    (fun key => miss_frames code r p primitive simplify request key deterministic)

theorem control_find_frames (code : FindCode) (r : Resources) (p : Primitives)
    (primitive : Recursive.PrimitiveFrames p) (simplify : ∀ key, Interner.Frames (p.simplify key))
    (request : Request) : Frames (code.controlRun (execution r p) request) := by
  unfold FindCode.controlRun
  simp only [execution]
  apply Frames.bind _ _ (Frames.graph _ Interner.Frames.get)
  intro before
  split
  · exact Frames.graph _ (Interner.Frames.lift _)
  · apply Frames.bind _ _ (Frames.local _ (initialize_local r request))
    intro args
    apply Frames.bind _ _ (Frames.graph _ (Interner.Frames.lift _))
    intro deterministic
    cases deterministic with
    | false => exact owned_frames code r p primitive simplify request args false
    | true =>
      apply Frames.bind _ _ (Frames.graph _ (Interner.Frames.lift _))
      intro key
      split
      · exact Frames.pure _
      · exact owned_frames code r p primitive simplify request args true

theorem control_force_frames (code : ForceCode) (r : Resources) (p : Primitives)
    (publication : ∀ key id, Interner.Frames (p.publish key id))
    (validate : NodeId → Heap → Except Error Unit) (id : NodeId) (item : Item) (arguments : List NodeId) :
    Frames (code.controlRun (execution r p) validate id item arguments) := by
  unfold ForceCode.controlRun ForceCode.controlOwned
  simp only [execution]
  apply Frames.bind _ _ (Frames.graph _ Interner.Frames.get)
  intro before
  apply Frames.bind _ _ (Frames.graph _ (Interner.Frames.lift _))
  intro ignored
  apply Frames.bind _ _ (Frames.local _ (initialize_local r _))
  intro args
  apply Frames.bind _ _ (Frames.graph _ (Interner.Frames.lift _))
  intro key
  split
  · exact Frames.pure _
  · apply Frames.bind _ _ (Frames.local _ (take_local r))
    intro ignored
    apply Frames.bind _ _ (Frames.graph _ (Interner.Frames.lift _))
    intro ownedKey
    exact Frames.bind _ _ (Frames.graph _ (publication _ _)) (fun _ => Frames.local _ handoff_local)

theorem finish_frames (r : Resources) (action : Action α) (framed : Frames action) (before : Heap) :
    Extends before (finish r action before).2.heap := by
  have retained := framed ⟨{}, before⟩
  unfold finish
  cases ran : action ⟨{}, before⟩ with
  | mk result after =>
    rw [ran] at retained
    intro cells present
    obtain ⟨suffix, appended⟩ := retained cells present
    exact ⟨suffix, (close_frame r after).2.2.trans appended⟩

/-- Local cleanup retains all graph growth reached before an error. -/
theorem find_frames (r : Resources) (p : Primitives) (primitive : Recursive.PrimitiveFrames p)
    (simplify : ∀ key, Interner.Frames (p.simplify key)) (request : Request) :
    Interner.Frames (find r p request) :=
  finish_frames r _ (control_find_frames findCode r p primitive simplify request)

theorem force_frames (r : Resources) (p : Primitives)
    (publication : ∀ key id, Interner.Frames (p.publish key id))
    (validate : NodeId → Heap → Except Error Unit) (id : NodeId) (item : Item) (arguments : List NodeId) :
    Interner.Frames (force r p validate id item arguments) :=
  finish_frames r _ (control_force_frames forceCode r p publication validate id item arguments)

end Compiler.Extraction.Interner.Scoped
