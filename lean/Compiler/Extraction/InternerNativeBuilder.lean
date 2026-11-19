/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPhysicalMeaning
import Compiler.Extraction.InternerPhysicalDispatch
import Compiler.Extraction.DispatchAlgebraicProofs

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Semantic
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul

/-- Native construction retains the caller's predicate and graph semantics on
every ordinary outcome. Its postcondition sees the complete reached world. -/
def NativeSafe (meaning : Meaning) (ready : World σ → Prop) (action : GraphAction σ α)
    (before : World σ) (post : α → World σ → Prop) : Prop :=
  let ran := action before
  ordinary ran.1 = true → ready ran.2 ∧ Interner.Invariant meaning ran.2.graph ∧
    Interner.Stable before.graph ran.2.graph ∧
    match ran.1 with | .error _ => True | .ok value => post value ran.2

theorem NativeSafe.of_ensures (meaning : Meaning) (ready : World σ → Prop) (action : GraphAction σ α)
    (before : World σ) (post : α → Interner.Heap → Prop)
    (frame : ordinary (action before).1 = true → ready (action before).2)
    (words : Ensures meaning before.graph (action before).1 (action before).2.graph post) :
    NativeSafe meaning ready action before (fun value after => post value after.graph) :=
  fun ordinary => ⟨frame ordinary, words ordinary⟩

theorem NativeSafe.ensures (meaning : Meaning) (ready : World σ → Prop) (action : GraphAction σ α)
    (before : World σ) (post : α → Interner.Heap → Prop)
    (checked : NativeSafe meaning ready action before (fun value after => post value after.graph)) :
    Ensures meaning before.graph (action before).1 (action before).2.graph post :=
  fun ordinary => (checked ordinary).2

theorem NativeSafe.pure (meaning : Meaning) (ready : World σ → Prop) (before : World σ)
    (value : α) (post : α → World σ → Prop) (valid : ready before ∧ Interner.Invariant meaning before.graph)
    (fact : post value before) : NativeSafe meaning ready (pure value) before post :=
  fun _ => ⟨valid.1, valid.2, fun _ _ found => found, fact⟩

/-- Ordinary failure of either child preserves its actual reached state.
Successful prefixes pass both native validity and stable old reads onward. -/
theorem NativeSafe.bind (meaning : Meaning) (ready : World σ → Prop) (before : World σ)
    (first : GraphAction σ α) (next : α → GraphAction σ β) (middle : α → World σ → Prop)
    (post : β → World σ → Prop) (checked : NativeSafe meaning ready first before middle)
    (continuation : ∀ value after, (ready after ∧ Interner.Invariant meaning after.graph) →
      Preserves (fun world : World σ => world.graph.read) before after → middle value after →
      NativeSafe meaning ready (next value) after post) :
    NativeSafe meaning ready (first >>= next) before post := by
  change NativeSafe meaning ready (Effect.bind first next) before post
  cases ran : first before with
  | mk result after =>
    cases result with
    | error fault =>
      simpa only [NativeSafe, Effect.bind, ran, ordinary] using checked
    | ok value =>
      have prior := checked (by rw [ran]; rfl)
      simp only [ran] at prior
      have suffix := continuation value after ⟨prior.1, prior.2.1⟩ prior.2.2.1 prior.2.2.2
      simp only [NativeSafe, Effect.bind, ran]
      intro ordinary
      have final := suffix ordinary
      exact ⟨final.1, final.2.1, prior.2.2.1.trans final.2.2.1, final.2.2.2⟩

/-- The same construction proof now ranges over full native worlds and their
actual fault classification, with no graph-only action or allocation model. -/
def builderLogic (meaning : Meaning) (ready : World σ → Prop) : BuilderLogic (GraphAction σ) (World σ) where
  read := fun world => world.graph.read
  valid := fun world => ready world ∧ Interner.Invariant meaning world.graph
  safe := NativeSafe meaning ready
  pure := NativeSafe.pure meaning ready
  bind := NativeSafe.bind meaning ready

/-- Native query errors retain their exact classification and unchanged world.
In particular an ordinary invalid-ID result still has preservation duties. -/
def readRules (meaning : Meaning) (ready : World σ → Prop) :
    Dispatch.Preservation.ReadRules (builderLogic meaning ready) where
  bind := by
    intro α β before result next post valid continuation
    cases result with
    | ok value => exact continuation value rfl
    | error error =>
      cases error <;> exact fun _ => ⟨valid.1, valid.2, fun _ _ found => found, trivial⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Semantic
