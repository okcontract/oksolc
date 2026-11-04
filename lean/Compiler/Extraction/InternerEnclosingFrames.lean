/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeLeafFrame
import Compiler.Extraction.InternerNativeParentPublication

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray

/-- Finite nesting of the existing live-call predicates. This describes proof
frames only; it adds no compiler state, execution or alternate memory model. -/
inductive Enclosing (safety : Bool) (allocator owner : Nat) :
    (World (Publication.Effects σ) → Prop) → Prop where
  | root : Enclosing safety allocator owner (fun _ => True)
  | call {rows : List Storage.Cell} {source : View} {values : List NodeId} {normalized : ArgumentSlice}
      {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
      {parent : World (Publication.Effects σ) → Prop}
      (outer : Enclosing safety allocator owner parent) :
      Enclosing safety allocator owner (CallFrame safety allocator owner rows source values normalized address native parent)

variable {safety : Bool} {allocator owner : Nat} {parent : World (Publication.Effects σ) → Prop}

/-- The unchanged-graph prefix retains every enclosing call. No outer
preservation law remains once the nesting is rooted in the empty frame. -/
theorem Enclosing.retained (stack : Enclosing safety allocator owner parent)
    {before after : World (Publication.Effects σ)} (initial : parent before)
    (valid : Valid after.memory) (graph : after.graph = before.graph) (kept : Retains before after) :
    parent after := by
  induction stack with
  | root => trivial
  | call outer ih =>
    exact initial.frame valid graph kept.1 kept.2.1 kept.2.2 (ih initial.parent)

/-- Original entry liveness makes both child-local marks safe for every
ancestor. The reached graph may have grown; each call retains its own source,
normalized owner and typed item through the existing cleanup proof. -/
theorem Enclosing.locals (stack : Enclosing safety allocator owner parent)
    {before : World (Publication.Effects σ)} (initial : parent before)
    (itemMark scratchMark : Nat) (itemOrdered : before.memory.memory.nextId ≤ itemMark)
    (scratchOrdered : before.memory.memory.nextId ≤ scratchMark) :
    ∀ world, parent world → parent (returnWorld itemMark scratchMark world) := by
  induction stack with
  | root => intros; trivial
  | call outer ih =>
    exact initial.locals itemMark scratchMark itemOrdered scratchOrdered (ih initial.parent)

/-- The literal argument wrapper retires one original mark after the complete
child returns. Every enclosing input and item follows the same cleanup proof. -/
theorem Enclosing.cleanup (stack : Enclosing safety allocator owner parent)
    {before : World (Publication.Effects σ)} (initial : parent before)
    (mark : Nat) (ordered : before.memory.memory.nextId ≤ mark) :
    ∀ world, parent world →
      parent { world with memory := { world.memory with memory := Compiler.ZigAir.Memory.cleanup mark world.memory.memory } } := by
  induction stack with
  | root => intros; trivial
  | call outer ih =>
    intro world reached
    exact initial.cleanup reached mark ordered (ih initial.parent world reached.parent)

/-- Releasing the child's private owner retains all enclosing calls. The
child's original origin and reached graph custody provide separation; the
actual free equation supplies its reached effects and memory. -/
theorem Enclosing.release (stack : Enclosing safety allocator owner parent)
    {before world : World (Publication.Effects σ)} (initial : parent before) (reached : parent world)
    {source : View} {request : Interner.Request} {values : List NodeId}
    {taken : State (Publication.Effects σ)} {owned : ArgumentSlice} {lookup : Handle}
    (origin : Caller.Origin allocator source request values before taken owned lookup)
    (host : External σ) {rows : List Storage.Cell} (projected : world.graph.representatives = some rows)
    (custody : Caller.GraphCustody allocator owned rows world.memory)
    {after : Session (Publication.Effects σ)}
    (freed : free (Publication.external host) allocator owned world.memory = (.ok (), after)) :
    parent { world with memory := after } := by
  induction stack with
  | root => trivial
  | call outer ih =>
    apply CallFrame.release origin initial reached host projected custody _ after freed
    intro selected released
    have same : selected = after := congrArg Prod.snd (released.symm.trans freed)
    subst selected
    exact ih initial.parent reached.parent

/-- Native probe refusal and successful publication/replacement preserve the
entire enclosing chain. The current child's frame supplies private custody;
no ancestor's final state is an input premise. -/
theorem Enclosing.publish (stack : Enclosing safety allocator owner parent)
    {before world : World (Publication.Effects σ)} (initial : parent before)
    {source : View} {request : Interner.Request} {values : List NodeId}
    {taken : State (Publication.Effects σ)} {owned : ArgumentSlice} {lookup : Handle}
    (origin : Caller.Origin allocator source request values before taken owned lookup)
    {rows : List Storage.Cell} {address : Compiler.ZigAir.Memory.Address}
    {native : AssemblyClone.NativeFields.ItemValue}
    (frame : CallFrame safety allocator owner rows source request.arguments owned address native parent world)
    (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ) (key : Key) (id : NodeId)
    (aligned : key.arguments = owned.items) :
    parent (Publication.publish hostProbe host allocator source key owned id world).2 := by
  induction stack with
  | root => trivial
  | call outer ih =>
    exact CallFrame.publish_parent origin initial frame hostProbe host key id aligned
      (ih initial.parent ⟨frame.1, frame.2.1, frame.parent.parent, frame.arraySource⟩)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
