/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MachineObservations

/-! Closed primitive-site coverage for every reachable machine configuration.
Both arms, loop bodies and all saved continuations are included. This inventory
is not a proof about the runtime addresses used at those sites. -/
namespace Compiler.ZigAir.Control

def Code.bindings : Code Ty Prim Ref loops → List (Nat × Ty × Prim)
  | .bind id ty prim next => (id, ty, prim) :: next.bindings
  | .branch _ yes no => yes.bindings ++ no.bindings
  | .block _ _ body next => body.bindings ++ next.bindings
  | .loop _ _ body => body.bindings
  | .repeat .. | .jump .. | .ret .. => []

def Code.Covered (allowed : Nat × Ty × Prim → Prop) (code : Code Ty Prim Ref loops) : Prop :=
  ∀ site ∈ code.bindings, allowed site

namespace Machine

def Frame.covered (allowed : Nat × Ty × Prim → Prop) : Frame Ty Prim Ref → Prop
  | .block _ _ next | .loop _ next => next.Covered allowed

def Execution.covered (allowed : Nat × Ty × Prim → Prop) : Execution Ty Prim Ref Value Fault State → Prop
  | .finished _ => True
  | .suspended config => config.code.Covered allowed ∧ ∀ frame ∈ config.frames, frame.covered allowed

variable (sem : Semantics Ty Prim Ref Value Fault State) (args : List Value)
    (allowed : Nat × Ty × Prim → Prop)

theorem jump_covered (target : Nat) (value : Value) (env : Env Value) (state : State)
    (frames : List (Frame Ty Prim Ref)) (covered : ∀ frame ∈ frames, frame.covered allowed) :
    (jump sem target value env state frames).covered allowed := by
  induction frames with
  | nil => trivial
  | cons frame frames ih =>
    have head := covered frame (by simp)
    have tail : ∀ item ∈ frames, item.covered allowed := fun item present => covered item (by simp [present])
    cases frame with
    | block id ty next =>
      by_cases catches : target = id
      · simp only [jump, if_pos catches]
        split
        · exact ⟨head, tail⟩
        · trivial
      · simpa only [jump, if_neg catches] using ih tail
    | loop id body =>
      by_cases catches : target = id
      · simp only [jump, if_pos catches]; trivial
      · simpa only [jump, if_neg catches] using ih tail

theorem backedge_covered (target : Nat) (env : Env Value) (state : State)
    (frames : List (Frame Ty Prim Ref)) (covered : ∀ frame ∈ frames, frame.covered allowed) :
    (backedge sem target env state frames).covered allowed := by
  induction frames with
  | nil => trivial
  | cons frame frames ih =>
    have head := covered frame (by simp)
    have tail : ∀ item ∈ frames, item.covered allowed := fun item present => covered item (by simp [present])
    cases frame with
    | block id ty next =>
      by_cases catches : target = id
      · simp only [backedge, if_pos catches]; trivial
      · simpa only [backedge, if_neg catches] using ih tail
    | loop id body =>
      by_cases catches : target = id
      · simp only [backedge, if_pos catches]
        exact ⟨head, covered⟩
      · simpa only [backedge, if_neg catches] using ih tail

theorem step_covered (config : Config Ty Prim Ref Value State)
    (covered : (Execution.suspended (Fault := Fault) config).covered allowed) : (step sem args config).covered allowed := by
  obtain ⟨code, env, state, frames⟩ := config
  obtain ⟨codeCovered, framesCovered⟩ := covered
  cases code with
  | bind id ty prim next =>
    have rest : next.Covered allowed := fun site present => codeCovered site (by simp [Code.bindings, present])
    cases evaluated : sem.evalPrim prim args env state with
    | mk result after =>
      cases result <;> simp only [step, evaluated]
      · trivial
      · split
        · exact ⟨rest, framesCovered⟩
        · trivial
  | branch ref yes no =>
    have left : yes.Covered allowed := fun site present => codeCovered site (by simp [Code.bindings, present])
    have right : no.Covered allowed := fun site present => codeCovered site (by simp [Code.bindings, present])
    cases evaluated : sem.evalRef ref env with
    | error => simp only [step, evaluated]; trivial
    | ok value =>
      cases flag : sem.truth value with
      | none => simp only [step, evaluated, flag]; trivial
      | some flagValue =>
        cases flagValue <;> simp only [step, evaluated, flag, Bool.false_eq_true, ↓reduceIte]
        · exact ⟨right, framesCovered⟩
        · exact ⟨left, framesCovered⟩
  | block id ty body next =>
    have inner : body.Covered allowed := fun site present => codeCovered site (by simp [Code.bindings, present])
    have rest : next.Covered allowed := fun site present => codeCovered site (by simp [Code.bindings, present])
    exact ⟨inner, by simpa only [List.mem_cons, forall_eq_or_imp, Frame.covered] using And.intro rest framesCovered⟩
  | loop enabled id body =>
    exact ⟨codeCovered, by simpa only [List.mem_cons, forall_eq_or_imp, Frame.covered] using And.intro codeCovered framesCovered⟩
  | «repeat» enabled target => exact backedge_covered sem allowed target env state frames framesCovered
  | jump target ref =>
    cases evaluated : sem.evalRef ref env with
    | error => simp only [step, evaluated]; trivial
    | ok value => simpa only [step, evaluated] using jump_covered sem allowed target value env state frames framesCovered
  | ret ref => cases evaluated : sem.evalRef ref env <;> simp only [step, evaluated] <;> trivial

theorem trace_covered (fuel : Nat) (execution : Execution Ty Prim Ref Value Fault State)
    (covered : execution.covered allowed) :
    ∀ event ∈ (trace sem args fuel execution).1, allowed event.site := by
  induction fuel generalizing execution with
  | zero => simp [trace]
  | succ fuel ih =>
    cases execution with
    | finished => simp [trace]
    | suspended config =>
      intro event present
      have member : event ∈ observe config ∨ event ∈ (trace sem args fuel (step sem args config)).1 := by
        simpa only [trace, List.mem_append] using present
      rcases member with here | later
      · cases code : config.code <;> simp only [observe, code, List.mem_singleton, List.not_mem_nil] at here
        all_goals first
          | contradiction
          | subst event; exact covered.1 _ (by simp [code, Code.bindings])
      · exact ih _ (step_covered sem args allowed config covered) event later

/-- Every attempted primitive belongs to the complete root body inventory,
for arbitrary inputs, states and fuel, including faults and suspension. -/
theorem root_trace_covered (code : Code Ty Prim Ref true) (env : Env Value) (state : State) (fuel : Nat) :
    ∀ event ∈ (trace sem args fuel (.suspended ⟨code, env, state, []⟩)).1, event.site ∈ code.bindings :=
  trace_covered sem args (fun site => site ∈ code.bindings) fuel _ ⟨fun _ present => present, by simp⟩

end Machine
end Compiler.ZigAir.Control
