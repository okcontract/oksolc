/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPhysicalMeaning

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Semantic
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray

/-- Pointwise publication semantics supply the actual handoff and returned ID.
The read at the reached graph follows from publication stability. -/
theorem publish_return_safe_at (p : Primitives σ) (meaning : Meaning)
    (key : Key) (slice : ArgumentSlice) (handle : Handle) (id : NodeId) (before : World σ) (value : Word)
    (actual : before.graph.read id = some value)
    (checked : let ran := p.publish key slice id before
      Ensures meaning before.graph ran.1 ran.2.graph (fun _ _ => True)) :
    let executed := ((do let _ ← graph (fun slice => p.publish key slice id); let _ ← handoff; pure id : Action σ NodeId)
      ⟨before, ⟨some handle, some slice, false⟩⟩)
    Ensures meaning before.graph executed.1 executed.2.world.graph (fun id after => after.read id = some value) := by
  cases ran : p.publish key slice id before with
  | mk result after =>
    rw [ran] at checked
    cases result with
    | error fault => simpa only [bind, Effect.bind, graph, ran] using checked
    | ok returned =>
      cases returned
      simp only [bind, Effect.bind, graph, ran, handoff, pure, Effect.pure]
      exact fun _ => ⟨(checked rfl).1, (checked rfl).2.1, (checked rfl).2.1 id value actual⟩

theorem publish_return_safe (allocator : Nat) (p : Primitives σ) (source : View) (values : List NodeId)
    (meaning : Meaning) (contracts : GraphContracts allocator source values meaning p)
    (key : Key) (slice : ArgumentSlice) (handle : Handle) (id : NodeId) (before : World σ) (value : Word)
    (aligned : key.arguments = slice.items) (held : Held allocator source values slice before)
    (valid : Interner.Invariant meaning before.graph) (evaluated : key.eval meaning before.graph.read = some value)
    (actual : before.graph.read id = some value) :
    let executed := ((do let _ ← graph (fun slice => p.publish key slice id); let _ ← handoff; pure id : Action σ NodeId)
      ⟨before, ⟨some handle, some slice, false⟩⟩)
    Ensures meaning before.graph executed.1 executed.2.world.graph (fun id after => after.read id = some value) :=
  publish_return_safe_at p meaning key slice handle id before value actual
    (contracts.publish key slice id before value aligned held valid evaluated actual)

theorem miss_safe (external : External σ) (allocator : Nat) (p : Primitives σ) (source : View) (values : List NodeId)
    (meaning : Meaning) (memory : OwnedCall.Contracts allocator source values p)
    (contracts : Contracts allocator source values meaning p) (request : Interner.Request) (key : Key)
    (slice : ArgumentSlice) (handle : Handle) (deterministic : Bool) (before : World σ) (value : Word)
    (kind : key.kind = request.item.kind) (aligned : key.arguments = slice.items) (held : Held allocator source values slice before)
    (valid : Interner.Invariant meaning before.graph) (evaluated : key.eval meaning before.graph.read = some value) :
    let executed := Interner.findCode.controlMiss (OwnedCall.execution external allocator p) request key deterministic
      ⟨before, ⟨some handle, some slice, false⟩⟩
    Ensures meaning before.graph executed.1 executed.2.world.graph (fun id after => after.read id = some value) := by
  unfold Interner.FindCode.controlMiss
  simp only [OwnedCall.execution]
  by_cases branch : (deterministic && (request.item.kind == 1)) = true
  · simp only [branch, ↓reduceIte]
    have operation : key.kind = 1 := by
      rw [kind]
      simpa using (Bool.and_eq_true_iff.mp branch).2
    cases simplified : p.simplify key slice before with
    | mk result middle =>
      have words := contracts.simplify key slice before value operation aligned held valid evaluated
      have borrowed := memory.simplify key slice before aligned held
      rw [simplified] at words borrowed
      cases result with
      | error fault => simpa only [bind, Effect.bind, graph, simplified] using words
      | ok found =>
        have middleValid := (words rfl).1
        have stable := (words rfl).2.1
        have middleHeld := borrowed rfl
        have keyMiddle := key_stable meaning before.graph.read middle.graph.read stable key value evaluated
        cases found with
        | none =>
          have checked := insert_safe allocator p source values meaning contracts.toGraphContracts key slice handle deterministic
            middle value aligned middleHeld middleValid keyMiddle
          simpa only [bind, Effect.bind, graph, simplified, pure, Effect.pure] using
            Ensures.extend meaning before.graph middle.graph _ _ _ stable checked
        | some id =>
          have checked := publish_return_safe allocator p source values meaning contracts.toGraphContracts key slice handle id
            middle value aligned middleHeld middleValid keyMiddle ((words rfl).2.2 id rfl)
          simpa only [bind, Effect.bind, graph, simplified, Interner.findCode, Interner.ResultId.run] using
            Ensures.extend meaning before.graph middle.graph _ _ _ stable checked
  · simpa only [branch, Bool.false_eq_true, ↓reduceIte, pure, Effect.pure, bind, Effect.bind] using
      insert_safe allocator p source values meaning contracts.toGraphContracts key slice handle deterministic before value aligned held valid evaluated

theorem owned_safe (external : External σ) (allocator : Nat) (p : Primitives σ) (request : Interner.Request)
    (deterministic : Bool) (handle : Handle) (source : View) (values : List NodeId) (before : World σ)
    (meaning : Meaning) (value : Word) (ready : Ready allocator source values handle before.memory)
    (admitted : Admitted external) (memory : OwnedCall.Contracts allocator source values p)
    (contracts : Contracts allocator source values meaning p) (valid : Interner.Invariant meaning before.graph)
    (evaluated : request.item.eval meaning before.graph.read handle.values request.sequence = some value) :
    let executed := body external allocator p request handle.values deterministic ⟨before, { lookup := some handle }⟩
    Ensures meaning before.graph executed.1 executed.2.world.graph (fun id after => after.read id = some value) := by
  rw [body_split]
  obtain ⟨result, reached, taken, post⟩ := take_refines external allocator source values handle before.memory ready admitted
  rw [taken]
  cases result with
  | error failure =>
    cases failure with
    | outOfMemory => exact Ensures.error meaning before.graph _ _ valid
    | allocation | preparation | release => exact False.elim post
  | ok pair =>
    rcases pair with ⟨slice, remaining⟩
    cases keyed : Interner.makeKey request handle.values with
    | error error => exact Ensures.error meaning before.graph _ _ valid
    | ok key =>
      exact miss_safe external allocator p source values meaning memory contracts request key slice remaining deterministic
        { before with memory := reached } value (Compiler.Extraction.Recursive.make_key_kind request handle.values key keyed)
        ((key_arguments request handle.values key keyed).trans post.values.symm)
        ⟨⟨post.ready.valid, post.ready.source⟩, post.live, post.separate⟩ valid
        (Interner.makeKey_sound meaning before.graph request handle.values value key evaluated keyed)

theorem force_owned_safe (external : External σ) (allocator : Nat) (p : Primitives σ) (request : Interner.Request)
    (id : NodeId) (handle : Handle) (source : View) (values : List NodeId) (before : World σ)
    (meaning : Meaning) (value : Word) (ready : Ready allocator source values handle before.memory)
    (admitted : Admitted external) (contracts : GraphContracts allocator source values meaning p)
    (valid : Interner.Invariant meaning before.graph)
    (evaluated : request.item.eval meaning before.graph.read handle.values request.sequence = some value)
    (actual : before.graph.read id = some value) :
    let executed := Interner.forceCode.controlOwned (OwnedCall.execution external allocator p) request handle.values id
      ⟨before, { lookup := some handle }⟩
    Ensures meaning before.graph executed.1 executed.2.world.graph (fun _ _ => True) := by
  rw [Caller.force_owned_split]
  obtain ⟨result, reached, taken, post⟩ := take_refines external allocator source values handle before.memory ready admitted
  rw [taken]
  cases result with
  | error failure =>
    cases failure with
    | outOfMemory => exact Ensures.error meaning before.graph _ _ valid
    | allocation | preparation | release => exact False.elim post
  | ok pair =>
    rcases pair with ⟨slice, remaining⟩
    cases keyed : Interner.makeKey request handle.values with
    | error error => exact Ensures.error meaning before.graph _ _ valid
    | ok key =>
      exact publish_safe allocator p source values meaning contracts key slice remaining id { before with memory := reached } value
        ((key_arguments request handle.values key keyed).trans post.values.symm)
        ⟨⟨post.ready.valid, post.ready.source⟩, post.live, post.separate⟩ valid
        (Interner.makeKey_sound meaning before.graph request handle.values value key evaluated keyed) actual

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Semantic
