/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPhysicalDispatchPreservation

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Recursive.Uniform
open Compiler.Algebraic Compiler.Extraction.Cache

/-- A fixed observation can support one model only if admitted ordinary runs
with equal observed inputs have equal results and observed outputs. Stream
admission must establish this property; graph/frame validity alone does not. -/
def Agrees (observe : Native → Interner.Heap) (admitted : Native → Prop)
    (action : Effect Native Fault α) : Prop :=
  ∀ left right, admitted left → admitted right →
    ordinary (action left).1 = true → ordinary (action right).1 = true →
    observe left = observe right →
    (action left).1 = (action right).1 ∧ observe (action left).2 = observe (action right).2

def language : Fault → Interner.Error
  | .language error => error
  | _ => .unsupported

theorem ordinary_language (result : Except Fault α) (completed : ordinary result = true) :
    (result.mapError language).mapError Fault.language = result := by
  cases result with
  | ok value => rfl
  | error fault =>
    cases fault with
    | language error => rfl
    | memory failure => cases completed
    | missingHandle => cases completed
    | outsideOwnedContinuation => cases completed

/-- Select an actual admitted ordinary run at the observed input. Absent inputs
reject without changing the graph. This is a mathematical model construction,
not an executor or a substitute for proving admission of actual native calls. -/
noncomputable def action (observe : Native → Interner.Heap) (admitted : Native → Prop)
    (physical : Effect Native Fault α) : Interner.Action α := fun before => by
  classical
  exact if found : ∃ native, admitted native ∧ observe native = before ∧ ordinary (physical native).1 = true then
    let chosen := Classical.choose found
    ((physical chosen).1.mapError language, observe (physical chosen).2)
  else (.error .unsupported, before)

theorem action_at (observe : Native → Interner.Heap) (admitted : Native → Prop)
    (physical : Effect Native Fault α) (agrees : Agrees observe admitted physical)
    (before : Native) (inside : admitted before) (completed : ordinary (physical before).1 = true) :
    action observe admitted physical (observe before) =
      ((physical before).1.mapError language, observe (physical before).2) := by
  classical
  have found : ∃ native, admitted native ∧ observe native = observe before ∧ ordinary (physical native).1 = true :=
    ⟨before, inside, rfl, completed⟩
  simp only [action, dif_pos found]
  have picked := Classical.choose_spec found
  obtain ⟨result, after⟩ := agrees (Classical.choose found) before picked.1 inside picked.2.2 completed picked.2.1
  rw [result, after]

/-- Admission can be broader than a particular live parent frame. The model
is chosen once over the whole admitted domain; frame preservation is checked
on the actual child action and never inferred from the choice of a witness. -/
theorem projects (observe : Native → Interner.Heap) (admitted predicate : Native → Prop)
    (physical : Effect Native Fault α) (agrees : Agrees observe admitted physical)
    (inside : ∀ before, predicate before → admitted before)
    (kept : ∀ before, predicate before → ordinary (physical before).1 = true → predicate (physical before).2) :
    ProjectsAt observe predicate physical (action observe admitted physical) := by
  intro before frame completed
  rw [action_at observe admitted physical agrees before (inside before frame) completed]
  exact ⟨kept before frame completed, (ordinary_language _ completed).symm, rfl⟩

/-- Agreement is necessary, not an extra semantic guarantee obtained for free
from recording events. Different hidden allocation outcomes can violate it. -/
theorem agrees_of_projects (observe : Native → Interner.Heap) (admitted : Native → Prop)
    (physical : Effect Native Fault α) (model : Interner.Action α)
    (coupled : ProjectsAt observe admitted physical model) : Agrees observe admitted physical := by
  intro left right leftIn rightIn leftDone rightDone same
  have one := coupled left leftIn leftDone
  have two := coupled right rightIn rightDone
  rw [same] at one
  exact ⟨one.2.1.trans two.2.1.symm, one.2.2.trans two.2.2.symm⟩

/-- Exact criterion for a uniform model on an admitted native domain. The
remaining requirements concern concrete executions, not chosen model terms. -/
theorem exists_iff (observe : Native → Interner.Heap) (admitted : Native → Prop)
    (physical : Effect Native Fault α) :
    (∃ model : Interner.Action α, ProjectsAt observe admitted physical model) ↔
      Agrees observe admitted physical ∧
      ∀ before, admitted before → ordinary (physical before).1 = true → admitted (physical before).2 := by
  constructor
  · rintro ⟨model, coupled⟩
    exact ⟨agrees_of_projects observe admitted physical model coupled, fun before inside completed =>
      (coupled before inside completed).1⟩
  · rintro ⟨agrees, kept⟩
    exact ⟨action observe admitted physical, projects observe admitted admitted physical agrees (fun _ inside => inside) kept⟩

/-- Native word preservation supplies the chosen model's semantic law at every
logical input. Unrepresented inputs use the explicit unsupported result. -/
theorem safe (observe : Native → Interner.Heap) (admitted : Native → Prop)
    (physical : Effect Native Fault α) (meaning : Meaning) (before : Interner.Heap)
    (post : α → Interner.Heap → Prop) (valid : Interner.Invariant meaning before)
    (native : ∀ world, admitted world → observe world = before →
      Semantic.Ensures meaning (observe world) (physical world).1 (observe (physical world).2) post) :
    Interner.Safe meaning (action observe admitted physical) before post := by
  classical
  intro result after ran
  unfold action at ran
  split at ran
  · rename_i found
    have picked := Classical.choose_spec found
    have checked := native (Classical.choose found) picked.1 picked.2.1 picked.2.2
    cases ran
    refine ⟨checked.1, ?_, ?_⟩
    · simpa only [picked.2.1] using checked.2.1
    · cases outcome : (physical (Classical.choose found)).1 with
      | error fault => trivial
      | ok value => simpa only [outcome] using checked.2.2
  · exact Interner.Safe.fail meaning before .unsupported post valid result after ran

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Recursive.Uniform
