/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.InternerScopeProofs

namespace Compiler.Extraction.Interner.Scoped
open Compiler.Algebraic Compiler.Extraction.Cache

theorem graph_preserves (action : Interner.Action α) (scope : Scope) (post : Scope → Prop)
    (live : Live scope) (fact : post scope) : Checked (liftGraph action) scope (fun _ after => post after) :=
  Checked.weaken _ _ _ _ (lift_graph_checked action scope live)
    (fun _ _after same => same ▸ fact)

theorem failure_checked (error : Error) (scope : Scope) (post : α → Scope → Prop) (live : Live scope) :
    Checked (liftGraph (Interner.lift (.error error))) scope post := by
  intro heap result _after ran
  cases ran
  exact ⟨live, trivial⟩

theorem handoff_insert_checked (p : Primitives) (key : Key) (deterministic : Bool) (scope : Scope)
    (taken : Taken scope) :
    Checked (handoff >>= fun _ => liftGraph (p.insert key deterministic)) scope (fun _ after => Transferred after) := by
  apply Checked.bind _ _ _ (fun _ after => Transferred after) _ (handoff_checked scope taken)
  intro _ after live transferred
  exact graph_preserves _ after Transferred live transferred

theorem miss_checked (code : FindCode) (r : Resources) (p : Primitives) (request : Request)
    (key : Key) (deterministic : Bool) (scope : Scope) (taken : Taken scope) :
    Checked (code.controlMiss (execution r p) request key deterministic) scope (fun _ after => Transferred after) := by
  unfold FindCode.controlMiss
  simp only [execution]
  by_cases branch : (deterministic && (request.item.kind == 1)) = true
  · simp only [branch, ↓reduceIte]
    apply Checked.bind _ _ _ (fun _ after => after = scope) _
      (lift_graph_checked _ scope (Or.inr (Or.inr (Or.inl taken))))
    intro result current live same
    subst current
    cases result with
    | none => exact handoff_insert_checked p key deterministic scope taken
    | some id =>
      apply Checked.bind _ _ _ (fun _ after => after = scope) _ (lift_graph_checked _ scope live)
      intro _ current live same
      subst current
      apply Checked.bind _ _ _ (fun _ after => Transferred after) _ (handoff_checked scope taken)
      intro _ after live transferred
      exact Checked.pure after _ _ live transferred
  · simp only [branch]
    exact handoff_insert_checked p key deterministic scope taken

theorem owned_checked (code : FindCode) (r : Resources) (p : Primitives) (request : Request)
    (args : List NodeId) (deterministic : Bool) (scope : Scope) (ready : Ready scope) :
    Checked (code.controlOwned (execution r p) request args deterministic) scope (fun _ after => Transferred after) := by
  unfold FindCode.controlOwned
  simp only [execution]
  apply Checked.bind _ _ _ (fun _ after => Taken after) _ (take_checked r scope ready)
  intro _ current live taken
  apply Checked.bind _ _ _ (fun _ after => after = current) _ (lift_graph_checked _ current live)
  intro key after live same
  subst after
  exact miss_checked code r p request key deterministic current taken

theorem find_checked (code : FindCode) (r : Resources) (p : Primitives) (request : Request)
    (scope : Scope) (empty : scope.lookup = none) (phase : scope.phase = .lookup) :
    Checked (code.controlRun (execution r p) request) scope (fun _ after => Ready after ∨ Transferred after) := by
  unfold FindCode.controlRun
  simp only [execution]
  apply Checked.bind _ _ _ (fun _ after => after = scope) _ (lift_graph_checked _ scope (Or.inl ⟨empty, phase⟩))
  intro before current live same
  subst current
  by_cases capacity : p.atCapacity before = true
  · simp only [capacity, ↓reduceIte]
    exact failure_checked .capacity scope _ live
  · simp only [capacity]
    apply Checked.bind _ _ _ (fun _ after => Ready after) _ (initialize_checked r request scope empty phase)
    intro args current live ready
    apply Checked.bind _ _ _ (fun _ after => after = current) _ (lift_graph_checked _ current live)
    intro deterministic after live same
    subst after
    cases deterministic with
    | false =>
      exact Checked.weaken _ _ _ _ (owned_checked code r p request args false current ready)
        (fun _ _ transferred => Or.inr transferred)
    | true =>
      apply Checked.bind _ _ _ (fun _ after => after = current) _ (lift_graph_checked _ current live)
      intro key after live same
      subst after
      cases before.table key with
      | none =>
        exact Checked.weaken _ _ _ _ (owned_checked code r p request args true current ready)
          (fun _ _ transferred => Or.inr transferred)
      | some id =>
        exact Checked.pure current _ _ live (Or.inl ready)

theorem force_checked (code : ForceCode) (r : Resources) (p : Primitives)
    (validate : NodeId → Heap → Except Error Unit) (id : NodeId) (item : Item) (arguments : List NodeId)
    (scope : Scope) (empty : scope.lookup = none) (phase : scope.phase = .lookup) :
    Checked (code.controlRun (execution r p) validate id item arguments) scope (fun _ after => Ready after ∨ Transferred after) := by
  unfold ForceCode.controlRun ForceCode.controlOwned
  simp only [execution]
  apply Checked.bind _ _ _ (fun _ after => after = scope) _ (lift_graph_checked _ scope (Or.inl ⟨empty, phase⟩))
  intro before current live same
  subst current
  apply Checked.bind _ _ _ (fun _ after => after = scope) _ (lift_graph_checked _ scope live)
  intro _ current live same
  subst current
  apply Checked.bind _ _ _ (fun _ after => Ready after) _
    (initialize_checked r ⟨item, arguments, 0⟩ scope empty phase)
  intro args current live ready
  apply Checked.bind _ _ _ (fun _ after => after = current) _ (lift_graph_checked _ current live)
  intro key after live same
  subst after
  cases before.table key with
  | some cached =>
    exact Checked.pure current () _ live (Or.inl ready)
  | none =>
    apply Checked.bind _ _ _ (fun _ after => Taken after) _ (take_checked r current ready)
    intro _ current live taken
    apply Checked.bind _ _ _ (fun _ after => after = current) _ (lift_graph_checked _ current live)
    intro key after live same
    subst after
    apply Checked.bind _ _ _ (fun _ after => after = current) _ (lift_graph_checked _ current live)
    intro _ after live same
    subst after
    exact Checked.weaken _ _ _ _ (handoff_checked current taken) (fun _ _ transferred => Or.inr transferred)

theorem finish_closed (r : Resources) (action : Action α) (post : α → Scope → Prop)
    (checked : Checked action {} post) (before : Heap) : Closed (finish r action before).2.scope := by
  cases ran : action ⟨{}, before⟩ with
  | mk result after =>
    simpa only [finish, ran] using close_closed r after (checked before result after ran).1

/-- Includes capacity/validation failures, allocation failure, cache hits,
recursive failure, failed publication, and insertion's all-outcome handoff. -/
theorem find_closed (r : Resources) (p : Primitives) (request : Request) (before : Heap) :
    Closed (findDetailed r p request before).2.scope :=
  finish_closed r _ _ (find_checked findCode r p request {} rfl rfl) before

theorem force_closed (r : Resources) (p : Primitives) (validate : NodeId → Heap → Except Error Unit)
    (id : NodeId) (item : Item) (arguments : List NodeId) (before : Heap) :
    Closed (forceDetailed r p validate id item arguments before).2.scope :=
  finish_closed r _ _ (force_checked forceCode r p validate id item arguments {} rfl rfl) before

end Compiler.Extraction.Interner.Scoped
