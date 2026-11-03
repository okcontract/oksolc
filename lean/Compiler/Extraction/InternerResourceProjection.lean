/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPhysicalDispatchPreservation

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Recursive.Resource
open Compiler.Algebraic Compiler.Extraction.Cache

/-- Resource history is append-only on the actual execution, including failed
returns. This does not assert memory validity or correctness of recorded events. -/
def Grows (history : Native → List Event) (physical : Effect Native Fault α) : Prop :=
  ∀ before, history before <+: history (physical before).2

/-- Admission binds this action's actual resource history to one fixed stream.
It contains no returned-value, graph-correspondence or successful-allocation
premise. Capturing a whole invocation supplies the stream; composition must
derive admission of each reached child from it. -/
def Admitted (history : Native → List Event) (stream : List Event)
    (physical : Effect Native Fault α) (before : Native) : Prop :=
  history (physical before).2 <+: stream

theorem Admitted.captured (history : Native → List Event) (physical : Effect Native Fault α)
    (before : Native) (trailing : List Event) :
    Admitted history (history (physical before).2 ++ trailing) physical before := ⟨trailing, rfl⟩

theorem Admitted.entry (history : Native → List Event) (stream : List Event)
    (physical : Effect Native Fault α) (grows : Grows history physical)
    (before : Native) (admitted : Admitted history stream physical before) :
    history before <+: stream := (grows before).trans admitted

theorem Grows.bind (history : Native → List Event) (first : Effect Native Fault α)
    (next : α → Effect Native Fault β) (initial : Grows history first)
    (following : ∀ value, Grows history (next value)) : Grows history (first >>= next) := by
  intro before
  cases ran : first before with
  | mk result middle =>
    have kept := initial before
    rw [ran] at kept
    cases result with
    | error fault => simpa only [Bind.bind, Effect.bind, ran] using kept
    | ok value => simpa only [Bind.bind, Effect.bind, ran] using kept.trans (following value middle)

/-- The complete run's admission supplies the first child's admission, even
when a later action fails. It does not discard events emitted before failure. -/
theorem Admitted.first (history : Native → List Event) (stream : List Event)
    (first : Effect Native Fault α) (next : α → Effect Native Fault β)
    (following : ∀ value, Grows history (next value)) (before : Native)
    (admitted : Admitted history stream (first >>= next) before) :
    Admitted history stream first before := by
  cases ran : first before with
  | mk result middle =>
    cases result with
    | error fault => simpa only [Admitted, Bind.bind, Effect.bind, ran] using admitted
    | ok value =>
      have tail : Admitted history stream (next value) middle := by
        simpa only [Admitted, Bind.bind, Effect.bind, ran] using admitted
      simpa only [Admitted, ran] using (following value middle).trans tail

theorem Admitted.next (history : Native → List Event) (stream : List Event)
    (first : Effect Native Fault α) (next : α → Effect Native Fault β)
    (before middle : Native) (value : α) (ran : first before = (.ok value, middle))
    (admitted : Admitted history stream (first >>= next) before) :
    Admitted history stream (next value) middle := by
  simpa only [Admitted, Bind.bind, Effect.bind, ran] using admitted

/-- Exact correspondence is conditional on this action's resource admission,
not on a structural frame admitting every possible future allocator outcome.
The same fixed stream and observation are used by every sequential child. -/
structure Projects (history : Native → List Event) (stream : List Event)
    (observe : Native → Model) (predicate : Native → Prop)
    (physical : Effect Native Fault α) (logical : Effect Model Interner.Error α) : Prop where
  grows : Grows history physical
  run : ∀ before, predicate before → Admitted history stream physical before →
    ordinary (physical before).1 = true →
    predicate (physical before).2 ∧
    (physical before).1 = (logical (observe before)).1.mapError Fault.language ∧
    observe (physical before).2 = (logical (observe before)).2

theorem Projects.of_projects (history : Native → List Event) (stream : List Event)
    (observe : Native → Model) (predicate : Native → Prop)
    (physical : Effect Native Fault α) (logical : Effect Model Interner.Error α)
    (grows : Grows history physical) (related : ProjectsAt observe predicate physical logical) :
    Projects history stream observe predicate physical logical :=
  ⟨grows, fun before held _ => related before held⟩

theorem Projects.bind (history : Native → List Event) (stream : List Event)
    (observe : Native → Model) (predicate : Native → Prop)
    (first : Effect Native Fault α) (model : Effect Model Interner.Error α)
    (next : α → Effect Native Fault β) (nextModel : α → Effect Model Interner.Error β)
    (initial : Projects history stream observe predicate first model)
    (following : ∀ value, Projects history stream observe predicate (next value) (nextModel value)) :
    Projects history stream observe predicate (first >>= next) (model >>= nextModel) := by
  refine ⟨initial.grows.bind history first next (fun value => (following value).grows), ?_⟩
  intro before held admitted completed
  have firstIn := Admitted.first history stream first next (fun value => (following value).grows) before admitted
  cases ran : first before with
  | mk result middle =>
    cases modelRan : model (observe before) with
    | mk modelResult modelMiddle =>
      cases result with
      | error fault =>
        have checked := initial.run before held firstIn (by simpa only [Bind.bind, Effect.bind, ran] using completed)
        simp only [ran, modelRan] at checked
        cases modelResult with
        | ok value => cases checked.2.1
        | error error => simpa only [Bind.bind, Effect.bind, ran, modelRan, Except.mapError, Except.error.injEq] using checked
      | ok value =>
        have checked := initial.run before held firstIn (by rw [ran]; rfl)
        simp only [ran, modelRan] at checked
        cases modelResult with
        | error error => cases checked.2.1
        | ok modelValue =>
          have equal : value = modelValue := Except.ok.inj checked.2.1
          subst modelValue
          have tailIn := Admitted.next history stream first next before middle value ran admitted
          have final := (following value).run middle checked.1 tailIn
            (by simpa only [Bind.bind, Effect.bind, ran] using completed)
          simpa only [Bind.bind, Effect.bind, ran, modelRan, checked.2.2] using final

/-- Instantiate the existing dispatcher effect algebra. Resource admission is
split by bind, so an unreachable continuation needs no admitted execution. -/
def projection (history : World σ → List Event) (stream : List Event)
    (observe : World σ → Interner.Heap) (predicate : World σ → Prop) :
    Dispatch.Effects (GraphAction σ) Interner.Action where
  related := Projects history stream observe predicate
  pure := fun _ => ⟨fun _ => List.prefix_refl _, fun _ held _ _ => ⟨held, rfl, rfl⟩⟩
  bind := fun first following => Projects.bind history stream observe predicate _ _ _ _ first following
  lift := fun _ => ⟨fun _ => List.prefix_refl _, fun _ held _ _ => ⟨held, rfl, rfl⟩⟩

/-- Reuse the existing word-law transfer on the admitted actual execution.
Resource admission alone never establishes semantic preservation. -/
theorem Projects.safe (history : World σ → List Event) (stream : List Event)
    (observe : World σ → Interner.Heap) (predicate : World σ → Prop)
    (physical : GraphAction σ α) (logical : Interner.Action α)
    (related : Projects history stream observe predicate physical logical)
    (meaning : Meaning) (before : World σ) (held : predicate before)
    (admitted : Admitted history stream physical before) (post : α → Interner.Heap → Prop)
    (safe : Interner.Safe meaning logical (observe before) post) :
    Semantic.Ensures meaning (observe before) (physical before).1 (observe (physical before).2) post :=
  safe_at meaning (observe before) (observe (physical before).2) (physical before).1 logical post
    (fun completed => (related.run before held admitted completed).2) safe

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Recursive.Resource
