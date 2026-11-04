/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerProduction

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Semantic
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray

/-- Word preservation for admitted outcomes of the actual physical execution.
Semantic faults remain rejected observations; they are not ordinary errors
with an invented valid graph or an invented cleanup path. -/
def Ensures (meaning : Meaning) (before : Interner.Heap) (result : Except Fault α)
    (after : Interner.Heap) (post : α → Interner.Heap → Prop) : Prop :=
  ordinary result = true → Interner.Invariant meaning after ∧ Interner.Stable before after ∧
    match result with | .error _ => True | .ok value => post value after

/-- Resource positions do not change represented graph values, cache validity
or stability. Transfer only read-based postconditions; this does not erase a
cursor from an exact state simulation or claim that allocation effects stop. -/
theorem Ensures.cursor_iff (meaning : Meaning) (before after : Interner.Heap)
    (result : Except Fault α) (initial final : Nat) (post : α → Read → Prop) :
    Ensures meaning { before with allocationCursor := initial } result { after with allocationCursor := final }
      (fun value heap => post value heap.read) ↔
    Ensures meaning before result after (fun value heap => post value heap.read) := by
  constructor <;> intro checked completed
  all_goals
    obtain ⟨valid, stable, proved⟩ := checked completed
    exact ⟨⟨valid.cache, valid.representation⟩, stable, proved⟩

theorem Ensures.error (meaning : Meaning) (before : Interner.Heap) (fault : Fault)
    (post : α → Interner.Heap → Prop) (valid : Interner.Invariant meaning before) :
    Ensures meaning before (.error fault) before post := fun _ => ⟨valid, fun _ _ found => found, trivial⟩

theorem Ensures.pure (meaning : Meaning) (before : Interner.Heap) (value : α)
    (post : α → Interner.Heap → Prop) (valid : Interner.Invariant meaning before) (fact : post value before) :
    Ensures meaning before (.ok value) before post := fun _ => ⟨valid, fun _ _ found => found, fact⟩

theorem Ensures.extend (meaning : Meaning) (before middle after : Interner.Heap) (result : Except Fault α)
    (post : α → Interner.Heap → Prop) (stable : Interner.Stable before middle)
    (checked : Ensures meaning middle result after post) : Ensures meaning before result after post := by
  intro completed
  exact ⟨(checked completed).1, stable.trans (checked completed).2.1, (checked completed).2.2⟩

/-- These are semantic obligations on the same physical callbacks used by the
memory theorem. The exact slice/key and reached world are part of each premise;
no normalization, recursive correctness or final caller result is assumed. -/
structure GraphContracts (allocator : Nat) (source : View) (values : List NodeId)
    (meaning : Meaning) (p : Primitives σ) : Prop where
  insert : ∀ key slice deterministic before value, key.arguments = slice.items →
    Held allocator source values slice before → Interner.Invariant meaning before.graph →
    key.eval meaning before.graph.read = some value →
    let executed := p.insert key slice deterministic before
    Ensures meaning before.graph executed.1 executed.2.graph (fun id after => after.read id = some value)
  publish : ∀ key slice id before value, key.arguments = slice.items →
    Held allocator source values slice before → Interner.Invariant meaning before.graph →
    key.eval meaning before.graph.read = some value → before.graph.read id = some value →
    let executed := p.publish key slice id before
    Ensures meaning before.graph executed.1 executed.2.graph (fun _ _ => True)

structure Contracts (allocator : Nat) (source : View) (values : List NodeId)
    (meaning : Meaning) (p : Primitives σ) : Prop extends GraphContracts allocator source values meaning p where
  simplify : ∀ key slice before value, key.kind = 1 → key.arguments = slice.items →
    Held allocator source values slice before → Interner.Invariant meaning before.graph →
    key.eval meaning before.graph.read = some value →
    let executed := p.simplify key slice before
    Ensures meaning before.graph executed.1 executed.2.graph (fun found after => ∀ id, found = some id → after.read id = some value)

theorem insert_safe (allocator : Nat) (p : Primitives σ) (source : View) (values : List NodeId)
    (meaning : Meaning) (contracts : GraphContracts allocator source values meaning p)
    (key : Key) (slice : ArgumentSlice) (handle : Handle) (deterministic : Bool) (before : World σ) (value : Word)
    (aligned : key.arguments = slice.items) (held : Held allocator source values slice before)
    (valid : Interner.Invariant meaning before.graph) (evaluated : key.eval meaning before.graph.read = some value) :
    let executed := ((do let _ ← handoff; graph (fun slice => p.insert key slice deterministic) : Action σ NodeId)
      ⟨before, ⟨some handle, some slice, false⟩⟩)
    Ensures meaning before.graph executed.1 executed.2.world.graph (fun id after => after.read id = some value) :=
  contracts.insert key slice deterministic before value aligned held valid evaluated

theorem publish_safe (allocator : Nat) (p : Primitives σ) (source : View) (values : List NodeId)
    (meaning : Meaning) (contracts : GraphContracts allocator source values meaning p)
    (key : Key) (slice : ArgumentSlice) (handle : Handle) (id : NodeId) (before : World σ) (value : Word)
    (aligned : key.arguments = slice.items) (held : Held allocator source values slice before)
    (valid : Interner.Invariant meaning before.graph) (evaluated : key.eval meaning before.graph.read = some value)
    (actual : before.graph.read id = some value) :
    let executed := ((do let _ ← graph (fun slice => p.publish key slice id); handoff : Action σ Unit)
      ⟨before, ⟨some handle, some slice, false⟩⟩)
    Ensures meaning before.graph executed.1 executed.2.world.graph (fun _ _ => True) := by
  have checked := contracts.publish key slice id before value aligned held valid evaluated actual
  cases ran : p.publish key slice id before with
  | mk result after =>
    rw [ran] at checked
    cases result with
    | error fault => simpa only [bind, Effect.bind, graph, ran] using checked
    | ok returned =>
      cases returned
      simpa only [bind, Effect.bind, graph, ran, handoff] using checked

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Semantic
