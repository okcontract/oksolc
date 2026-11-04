/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPhysicalDispatch
import Compiler.Extraction.DispatchEffects
import Lean

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Recursive.QueryTiming
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.Extraction.Nested Compiler.Extraction.Dispatch

/-- Exact execution correspondence, with the additional fact needed to enter a
later dispatcher stage: a miss has performed no mutation of the world. -/
def Related (before : World σ) (left right : GraphAction σ (Option NodeId)) : Prop :=
  left before = right before ∧ ∀ after, left before = (.ok none, after) → after = before

/-- A selected constructor continuation cannot resume the surrounding search.
Its failures may retain arbitrary mutations; no rollback premise is imposed. -/
def Terminal (action : GraphAction σ (Option NodeId)) : Prop :=
  ∀ before after, action before ≠ (.ok none, after)

theorem pure_related (before : World σ) (value : Option NodeId) :
    Related before (pure value) (pure value) := by
  refine ⟨rfl, ?_⟩
  intro after equal
  exact (Prod.mk.inj equal).2.symm

theorem some_terminal (id : NodeId) : Terminal (pure (some id) : GraphAction σ _) := by
  intro before after equal
  cases equal

theorem terminal_bind (first : GraphAction σ α) (next : α → GraphAction σ (Option NodeId))
    (following : ∀ value, Terminal (next value)) : Terminal (first >>= next) := by
  intro before after equal
  cases ran : first before with
  | mk result middle =>
    cases result with
    | error fault => simp only [bind, Effect.bind, ran] at equal; cases equal
    | ok value => exact following value middle after (by simpa only [bind, Effect.bind, ran] using equal)

theorem terminal_return (action : GraphAction σ (Option NodeId))
    (terminal : Terminal action) : Terminal (action >>= pure) := by
  intro before after equal
  apply terminal before after
  cases ran : action before with
  | mk result reached => cases result <;> simpa only [bind, Effect.bind, pure, Effect.pure, ran] using equal

theorem terminal_related (before : World σ) (action : GraphAction σ (Option NodeId))
    (terminal : Terminal action) : Related before action action :=
  ⟨rfl, fun after equal => False.elim (terminal before after equal)⟩

theorem prefix_bind (before : World σ) (left right : GraphAction σ α)
    (nextLeft nextRight : α → GraphAction σ (Option NodeId))
    (equal : left before = right before) (unchanged : (right before).2 = before)
    (following : ∀ value, Related before (nextLeft value) (nextRight value)) :
    Related before (left >>= nextLeft) (right >>= nextRight) := by
  cases ran : right before with
  | mk result middle =>
    have same : middle = before := by simpa only [ran] using unchanged
    subst middle
    cases result with
    | error fault =>
      refine ⟨?_, ?_⟩
      · simp only [bind, Effect.bind, equal, ran]
      · intro after finished
        simp only [bind, Effect.bind, equal, ran] at finished
        cases finished
    | ok value =>
      simpa only [Related, bind, Effect.bind, equal, ran] using following value

theorem pure_bind (before : World σ) (value : α)
    (nextLeft nextRight : α → GraphAction σ (Option NodeId))
    (following : Related before (nextLeft value) (nextRight value)) :
    Related before (pure value >>= nextLeft) (pure value >>= nextRight) := following

theorem read_unchanged (before : World σ) (result : Except ReadError α) :
    ((readAction result : GraphAction σ α) before).2 = before := by
  cases result with
  | ok value => rfl
  | error fault => cases fault <;> rfl

theorem query_bind (before : World σ) (reads : Reads) (query : QueryRead (GraphAction σ))
    (observed : ∀ {α} (action : Reads → Except ReadError α),
      query action before = (readAction (action reads) : GraphAction σ α) before)
    (action : Reads → Except ReadError α) (nextLeft nextRight : α → GraphAction σ (Option NodeId))
    (following : ∀ value, Related before (nextLeft value) (nextRight value)) :
    Related before (query action >>= nextLeft) (readAction (action reads) >>= nextRight) :=
  prefix_bind before _ _ _ _ (observed action) (read_unchanged before _) following

theorem read_bind (before : World σ) (result : Except ReadError α)
    (nextLeft nextRight : α → GraphAction σ (Option NodeId))
    (following : ∀ value, Related before (nextLeft value) (nextRight value)) :
    Related before (readAction result >>= nextLeft) (readAction result >>= nextRight) :=
  prefix_bind before _ _ _ _ rfl (read_unchanged before _) following

theorem arithmetic_bind (before : World σ) (result : Except Folding.Fault α)
    (nextLeft nextRight : α → GraphAction σ (Option NodeId))
    (following : ∀ value, Related before (nextLeft value) (nextRight value)) :
    Related before (arithmetic result >>= nextLeft) (arithmetic result >>= nextRight) := by
  apply prefix_bind before _ _ _ _ rfl _ following
  cases result <;> rfl

theorem search_bind (before : World σ) (left right : GraphAction σ (Option NodeId))
    (nextLeft nextRight : Option NodeId → GraphAction σ (Option NodeId))
    (stage : Related before left right)
    (following : Related before (nextLeft none) (nextRight none))
    (foundLeft : ∀ id, nextLeft (some id) = pure (some id))
    (foundRight : ∀ id, nextRight (some id) = pure (some id)) :
    Related before (left >>= nextLeft) (right >>= nextRight) := by
  obtain ⟨equal, unchanged⟩ := stage
  cases ran : left before with
  | mk result middle =>
    have other := equal.symm.trans ran
    cases result with
    | error fault =>
      refine ⟨?_, ?_⟩
      · simp only [bind, Effect.bind, ran, other]
      · intro after finished
        simp only [bind, Effect.bind, ran] at finished
        cases finished
    | ok found =>
      cases found with
      | none =>
        have same := unchanged middle ran
        subst middle
        simpa only [Related, bind, Effect.bind, ran, other] using following
      | some id =>
        refine ⟨?_, ?_⟩
        · simp only [bind, Effect.bind, ran, other, foundLeft, foundRight]
        · intro after finished
          simp only [bind, Effect.bind, ran, foundLeft, pure, Effect.pure] at finished
          cases finished

theorem or_next (before : World σ) (left right nextLeft nextRight : GraphAction σ (Option NodeId))
    (stage : Related before left right) (following : Related before nextLeft nextRight) :
    Related before (orNext left nextLeft) (orNext right nextRight) := by
  exact search_bind before left right _ _ stage following (fun _ => rfl) (fun _ => rfl)

theorem add_word_bind (before : World σ) (a b : Contract.Yul.Word)
    (nextLeft nextRight : Contract.Yul.Word → GraphAction σ (Option NodeId))
    (following : ∀ value, Related before (nextLeft value) (nextRight value)) :
    Related before (addWord a b >>= nextLeft) (addWord a b >>= nextRight) := by
  apply prefix_bind before _ _ _ _ rfl _ following
  unfold addWord
  cases Folding.Zig.checkedAdd 256 a.toNat b.toNat <;> rfl

theorem sub_word_bind (before : World σ) (a b : Contract.Yul.Word)
    (nextLeft nextRight : Contract.Yul.Word → GraphAction σ (Option NodeId))
    (following : ∀ value, Related before (nextLeft value) (nextRight value)) :
    Related before (subWord a b >>= nextLeft) (subWord a b >>= nextRight) := by
  apply prefix_bind before _ _ _ _ rfl _ following
  unfold subWord
  cases Folding.Zig.checkedSub a.toNat b.toNat <;> rfl

open Lean Meta Elab Tactic in
elab "timing_intro" : tactic => withMainContext do
  unless (← instantiateMVars (← getMainTarget)).headBeta.isForall do throwError "expected a continuation binder"
  evalTactic (← `(tactic| intro value))

open Lean Meta Elab Tactic in
elab "terminal_step" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).headBeta.consumeMData
  unless target.isAppOf ``Terminal do throwError "expected a terminal continuation"
  let action := target.getAppArgs.back!.headBeta.consumeMData
  if let .letE _ _ value body _ := action then
    let args := target.getAppArgs
    replaceMainGoal [← (← getMainGoal).change
      (mkAppN target.getAppFn (args.set! (args.size - 1) (body.instantiate1 value)))]
  else if action.isAppOf ``Pure.pure then
    evalTactic (← `(tactic| exact some_terminal _))
  else if action.isAppOf ``Bind.bind then
    evalTactic (← `(tactic| apply terminal_bind))
  else throwError "not a terminal value or bind"

macro "terminal_steps" : tactic => `(tactic|
  repeat first
    | terminal_step | timing_intro | split)

theorem max_terminal (constructors : Associative.Constructors Debug (GraphAction σ))
    (parity : NodeId → Debug → GraphAction σ NodeId) (debug : Debug) :
    Terminal (maxExponent constructors parity debug) := by
  unfold maxExponent
  terminal_steps

open Lean Meta Elab Tactic in
/-- An identical query-free continuation may run after a child has changed the
world. Keep its code equality instead of weakening it to entry-only equality. -/
elab "timing_same_let " query:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).headBeta.consumeMData
  unless target.isAppOf ``Related do throwError "expected query correspondence"
  let args := target.getAppArgs
  let .letE _ _ leftValue leftBody _ := args[args.size - 2]!.headBeta.consumeMData |
    throwError "expected a left let"
  let .letE _ _ rightValue rightBody _ := args.back!.headBeta.consumeMData |
    throwError "expected a right let"
  let q ← getFVarId query
  if leftValue.containsFVar q then throwError "query-dependent continuation"
  unless (← isDefEq leftValue rightValue) do throwError "different continuations"
  let reduced := mkAppN target.getAppFn <| (args.set! (args.size - 2) (leftBody.instantiate1 leftValue))
    |>.set! (args.size - 1) (rightBody.instantiate1 rightValue)
  replaceMainGoal [← (← getMainGoal).change reduced]

open Lean Meta Elab Tactic in
elab "timing_terminal " query:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).headBeta.consumeMData
  unless target.isAppOf ``Related do throwError "expected query correspondence"
  let args := target.getAppArgs
  let left := args[args.size - 2]!
  let q ← getFVarId query
  if left.containsFVar q then throwError "query-dependent continuation"
  unless (← isDefEq left args.back!) do throwError "different continuations"
  evalTactic (← `(tactic| solve | apply terminal_related; first | exact max_terminal _ _ _ | (apply terminal_return; exact max_terminal _ _ _) | terminal_steps))

open Lean Meta Elab Tactic in
elab "timing_prefix " before:ident reads:ident query:ident observed:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).headBeta.consumeMData
  unless target.isAppOf ``Related do throwError "expected query correspondence"
  let args := target.getAppArgs
  let action := args[args.size - 2]!.headBeta.consumeMData
  if action.isAppOf ``Pure.pure then
    evalTactic (← `(tactic| exact pure_related $before _))
  else if action.isAppOf ``Dispatch.orNext then
    evalTactic (← `(tactic| apply or_next $before))
  else
    unless action.isAppOf ``Bind.bind do throwError "expected a prefix bind"
    let bindArgs := action.getAppArgs
    let first := bindArgs[bindArgs.size - 2]!.headBeta.consumeMData
    let q ← getFVarId query
    if first.getAppFn == mkFVar q then
      evalTactic (← `(tactic| apply query_bind $before $reads $query $observed))
    else if first.isAppOf ``Pure.pure then
      evalTactic (← `(tactic| apply pure_bind $before))
    else if first.isAppOf ``readAction then
      evalTactic (← `(tactic| apply read_bind $before))
    else if first.isAppOf ``arithmetic then
      evalTactic (← `(tactic| apply arithmetic_bind $before))
    else if first.isAppOf ``addWord then
      evalTactic (← `(tactic| apply add_word_bind $before))
    else if first.isAppOf ``subWord then
      evalTactic (← `(tactic| apply sub_word_bind $before))
    else if [``dropRepeatedLocal, ``Associative.reassociate, ``ShiftMasks.removeCoveredShiftMask,
        ``ShiftMasks.powerOfTwoShiftProductWithInputs, ``SignExtendMask.stripRedundantSignExtendMaskWithInputs,
        ``AlternatingMask.distributeAlternatingMaskWithInputs].any first.isAppOf then
      evalTactic (← `(tactic| apply search_bind $before))
    else throwError "not a read-only prefix or a checked search helper"

macro "query_step " before:ident reads:ident query:ident observed:ident : tactic => `(tactic|
  first
    | timing_same_let $query
    | effect_let
    | effect_value
    | timing_terminal $query
    | timing_prefix $before $reads $query $observed
    | solve_by_elim (config := { maxDepth := 2 }) only [*]
    | timing_intro
    | rfl
    | split)

macro "query_steps " before:ident reads:ident query:ident observed:ident : tactic => `(tactic|
  repeat query_step $before $reads $query $observed)

variable (before : World σ) (reads : Reads) (query : QueryRead (GraphAction σ))
  (observed : ∀ {α} (action : Reads → Except ReadError α),
    query action before = (readAction (action reads) : GraphAction σ α) before)
  (constructors : Associative.Constructors Debug (GraphAction σ)) (operand : OperandRead (GraphAction σ))

include observed in
theorem drop_repeated (build : LocalOperationBuilder Debug (GraphAction σ))
    (instruction : Opcode) (nested repeated : NodeId) (first : Bool) (debug : Debug) :
    Related before (dropRepeatedLocal reads build instruction nested repeated first debug query)
      (dropRepeatedLocal reads build instruction nested repeated first debug) := by
  unfold dropRepeatedLocal
  query_steps before reads query observed

include observed in
theorem reassociate (instruction : Opcode) (nested other : NodeId) (right : Bool) (debug : Debug) :
    Related before (Associative.reassociate reads constructors instruction nested other right debug query)
      (Associative.reassociate reads constructors instruction nested other right debug) := by
  unfold Associative.reassociate
  query_steps before reads query observed

include observed in
theorem shift_mask (mask shifted : NodeId) (debug : Debug) :
    Related before (ShiftMasks.removeCoveredShiftMask reads constructors mask shifted debug query)
      (ShiftMasks.removeCoveredShiftMask reads constructors mask shifted debug) := by
  unfold ShiftMasks.removeCoveredShiftMask
  query_steps before reads query observed

include observed in
theorem shift_product (build : OperationBuilder Debug (GraphAction σ)) (value shift : NodeId) (debug : Debug) :
    Related before (ShiftMasks.powerOfTwoShiftProductWithInputs reads build value shift debug operand query)
      (ShiftMasks.powerOfTwoShiftProductWithInputs reads build value shift debug operand) := by
  unfold ShiftMasks.powerOfTwoShiftProductWithInputs
  query_steps before reads query observed

include observed in
theorem signextend (constant extended : NodeId) (debug : Debug) :
    Related before (SignExtendMask.stripRedundantSignExtendMaskWithInputs reads constructors constant extended debug operand query)
      (SignExtendMask.stripRedundantSignExtendMaskWithInputs reads constructors constant extended debug operand) := by
  unfold SignExtendMask.stripRedundantSignExtendMaskWithInputs
  query_steps before reads query observed

include observed in
theorem alternating_search (a b : NodeId) (debug : Debug) (choices : List AlternatingMask.Choice) :
    Related before (AlternatingMask.searchWithInputs reads constructors a b debug choices operand query)
      (AlternatingMask.searchWithInputs reads constructors a b debug choices operand) := by
  induction choices with
  | nil => exact pure_related before none
  | cons choice rest ih =>
    unfold AlternatingMask.searchWithInputs
    query_steps before reads query observed

include observed in
theorem alternating (a b : NodeId) (debug : Debug) :
    Related before (AlternatingMask.distributeAlternatingMaskWithInputs reads constructors a b debug operand query)
      (AlternatingMask.distributeAlternatingMaskWithInputs reads constructors a b debug operand) :=
  alternating_search before reads query observed constructors operand a b debug _

include observed in
theorem constant_stage (instruction : Opcode) (arguments : List NodeId) (debug : Debug) :
    Related before (constantStage reads constructors instruction arguments debug query)
      (constantStage reads constructors instruction arguments debug) := by
  unfold constantStage
  query_steps before reads query observed

include observed in
theorem unary_stage (instruction : Opcode) (value : NodeId) (debug : Debug) :
    Related before (unaryStageWithInputs reads constructors instruction value debug operand query)
      (unaryStageWithInputs reads constructors instruction value debug operand) := by
  unfold unaryStageWithInputs
  query_steps before reads query observed

include observed in
theorem evm_stage (usizeBits : Nat) (instruction : Opcode) (arguments : List NodeId)
    (debug : Debug) (version : Version) (address : Nat) :
    Related before (evmStageWithInputs reads constructors usizeBits instruction arguments debug version operand address query)
      (evmStageWithInputs reads constructors usizeBits instruction arguments debug version operand address) := by
  unfold evmStageWithInputs
  query_steps before reads query observed

open Lean Meta Elab Tactic in
elab "timing_helper " before:ident reads:ident query:ident observed:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).headBeta.consumeMData
  unless target.isAppOf ``Related do throwError "expected query correspondence"
  let args := target.getAppArgs
  let action := args[args.size - 2]!.headBeta.consumeMData
  let rules := [(``dropRepeatedLocal, ``drop_repeated),
    (``Associative.reassociate, ``reassociate),
    (``ShiftMasks.removeCoveredShiftMask, ``shift_mask),
    (``ShiftMasks.powerOfTwoShiftProductWithInputs, ``shift_product),
    (``SignExtendMask.stripRedundantSignExtendMaskWithInputs, ``signextend),
    (``AlternatingMask.distributeAlternatingMaskWithInputs, ``alternating)]
  let some rule := rules.find? (fun rule => action.isAppOf rule.1) |
    throwError "not a checked query helper"
  let lemma := mkIdent rule.2
  evalTactic (← `(tactic| apply $lemma $before $reads $query $observed))

include observed in
theorem binary_stage (usizeBits : Nat) (instruction : Opcode) (left right : NodeId)
    (debug : Debug) (options : Options) :
    Related before (binaryStageWithInputs reads constructors usizeBits instruction left right debug options operand query)
      (binaryStageWithInputs reads constructors usizeBits instruction left right debug options operand) := by
  unfold binaryStageWithInputs
  repeat first
    | timing_helper before reads query observed
    | query_step before reads query observed

include observed in
theorem simplify_options (usizeBits : Nat) (instruction : Opcode) (arguments : List NodeId)
    (debug : Debug) (options : Options) (address : Nat) :
    Related before (simplifyOptionsWithInputs reads constructors usizeBits instruction arguments debug options operand address query)
      (simplifyOptionsWithInputs reads constructors usizeBits instruction arguments debug options operand address) := by
  unfold simplifyOptionsWithInputs
  apply or_next before _ _ _ _ (constant_stage before reads query observed constructors _ _ _)
  apply or_next
  · split
    · exact binary_stage before reads query observed constructors operand _ _ _ _ _ _
    · exact pure_related before none
  · apply or_next
    · split
      · exact unary_stage before reads query observed constructors operand _ _ _
      · exact pure_related before none
    · split
      · exact evm_stage before reads query observed constructors operand _ _ _ _ _ _
      · exact pure_related before none

include observed in
/-- Every read-only query in the complete shared dispatcher can use the entry
snapshot. Constructor/operand actions remain at their source positions, may
mutate or fail, and are not required to preserve that snapshot. -/
theorem simplify (usizeBits : Nat) (instruction : Opcode) (arguments : List NodeId)
    (debug : Debug) (address : Nat) :
    Related before (simplifyWithInputs reads constructors usizeBits instruction arguments debug operand address query)
      (simplifyWithInputs reads constructors usizeBits instruction arguments debug operand address) :=
  simplify_options before reads query observed constructors operand usizeBits instruction arguments debug defaultOptions address

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Recursive.QueryTiming
