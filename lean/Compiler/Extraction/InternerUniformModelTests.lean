/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorUniformInduction
import Compiler.Extraction.DispatchSourceConstructorsTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Recursive.Uniform.Tests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul

/-- An effect-level allocation decision hidden by the graph observation. Both outcomes are
ordinary; rejecting unsupported observations cannot hide their disagreement. -/
def allocation : Effect Bool Fault NodeId := fun permitted =>
  (if permitted then .ok 7 else .error (.language .outOfMemory), permitted)

theorem no_model_without_agreement (heap : Interner.Heap) :
    ¬ ∃ model : Interner.Action NodeId, ProjectsAt (fun _ : Bool => heap) (fun _ => True) allocation model := by
  rintro ⟨model, coupled⟩
  have conflict := agrees_of_projects (fun _ : Bool => heap) (fun _ => True) allocation model coupled
    true false trivial trivial rfl rfl rfl
  cases conflict.1

theorem selected_agrees (heap : Interner.Heap) (permitted : Bool) :
    Agrees (fun _ : Bool => heap) (fun selected => selected = permitted) allocation := by
  intro left right one two _ _ _
  cases one
  cases two
  exact ⟨rfl, rfl⟩

theorem selected_model (heap : Interner.Heap) (permitted : Bool) :
    action (fun _ : Bool => heap) (fun selected => selected = permitted) allocation heap =
      (if permitted then .ok 7 else .error .outOfMemory, heap) := by
  have projected := action_at (fun _ : Bool => heap) (fun selected => selected = permitted) allocation
    (selected_agrees heap permitted) permitted rfl (by cases permitted <;> rfl)
  cases permitted <;> exact projected

theorem unadmitted_rejected (heap : Interner.Heap) :
    action (fun _ : Bool => heap) (fun _ => False) allocation heap = (.error .unsupported, heap) := by
  simp only [action, false_and, exists_false, ↓reduceDIte]

theorem selected_safe (heap : Interner.Heap) (meaning : Meaning) (value : Word)
    (valid : Interner.Invariant meaning heap) (read : heap.read 7 = some value) (permitted : Bool) :
    Interner.Safe meaning (action (fun _ : Bool => heap) (fun selected => selected = permitted) allocation) heap
      (fun id after => after.read id = some value) := by
  apply safe _ _ _ meaning heap _ valid
  intro selected _ _
  cases selected with
  | false => exact Semantic.Ensures.error meaning heap (.language .outOfMemory) _ valid
  | true => exact Semantic.Ensures.pure meaning heap 7 _ valid read

/-- The family regression keeps arbitrary native states, observations, parent
predicates, source snapshots and debug values. It exercises an ordinary child
failure, whose reached graph/frame still has to be retained. -/
def refused : Associative.Constructors Debug (GraphAction σ) where
  operation := fun _ _ _ before => (.error (.language .outOfMemory), before)
  constant := fun _ _ before => (.error (.language .outOfMemory), before)
  materialize := fun _ _ _ before => (.error (.language .outOfMemory), before)

def admitted : Domains σ Debug where
  operation := fun _ _ _ _ => True
  constant := fun _ _ _ => True
  materialize := fun _ _ _ _ => True

theorem refused_agrees (observe : World σ → Interner.Heap) :
    Agreement observe (admitted : Domains σ Debug) refused := by
  constructor <;> intros <;> exact fun _ _ _ _ _ _ same => ⟨rfl, same⟩

theorem refused_words (observe : World σ → Interner.Heap) (meaning : Meaning) :
    Words observe meaning (admitted : Domains σ Debug) refused := by
  constructor <;> intros <;> (try unfold RequestWords) <;> intros <;> apply Semantic.Ensures.error <;> assumption

theorem source_admitted (debug : Debug) (reads : Nested.Reads) (frame : World σ → Prop) :
    SourceAdmission admitted debug reads frame := by
  constructor <;> intros <;> trivial

theorem frames (debug : Debug) (reads : Nested.Reads) (frame : World σ → Prop) :
    (keeping frame).SourceConstructorsAt reads debug (refused : Associative.Constructors Debug (GraphAction σ)) refused := by
  constructor <;> intros <;> exact fun _ held _ => held

theorem proper_children {Index : Type} (observe : World σ → Interner.Heap) (env : AddressMask.Environment) (other : Meaning)
    (debug : Debug) (selected : Prop) (reads : Index → Nested.Reads) (frame : Index → World σ → Prop) :
    ∃ model : Associative.Constructors Debug,
      (selected → ∀ index, (projectionAt observe (frame index)).SourceConstructorsAt (reads index) debug refused model) ∧
      (selected → Associative.ConstructorSound (Dispatch.wordBaseMeaning env other) model) ∧
      (selected → AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) model.operation) ∧
      (selected → ArithmeticShift.Constructs (AddressMask.addressMeaning env other) model.operation) := by
  exact proper observe admitted refused env other debug selected reads frame (fun _ =>
    ⟨refused_agrees observe, refused_words observe _, fun index =>
      ⟨source_admitted debug (reads index) (frame index), frames debug (reads index) (frame index)⟩⟩)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Recursive.Uniform.Tests
