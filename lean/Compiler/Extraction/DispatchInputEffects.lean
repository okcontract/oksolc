/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.DispatchSourceConstructors
import Compiler.Extraction.AlternatingMaskProofs

namespace Compiler.Extraction.Dispatch
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul

namespace Effects
variable {m n : Type → Type} [Monad m] [Monad n]
  [MonadLift (Except Interner.Error) m] [MonadLift (Except Interner.Error) n]

/-- Retain a read's returned-value equation across bind. This is an additional
proved effect law, not a consequence assumed from the Monad interface. -/
structure ReadBind (r : Effects m n) : Prop where
  bind : ∀ {α β} (result : Except Storage.ReadError α)
    (nextLeft : α → m β) (nextRight : α → n β),
    (∀ value, result = .ok value → r.related (nextLeft value) (nextRight value)) →
    r.related (readAction result >>= nextLeft) (readAction result >>= nextRight)

/-- Only an in-bounds load with its actual source annotation is related to the
logical reader. Native implementations must derive this from reached memory. -/
def SliceInput (r : Effects m n) (operand : OperandRead m) (source : Storage.ArgumentSlice) : Prop :=
  ∀ index annotation, source.items[index]? = some annotation →
    r.related (operand source index annotation) (logicalOperand source index annotation)

structure Inputs (r : Effects m n) (reads : Reads) (operand : OperandRead m) : Prop where
  queried : ∀ id opcode source, reads.operation id opcode = .ok (some source) → SliceInput r operand source

variable (r : Effects m n) (rb : ReadBind r) (reads : Reads) (operand : OperandRead m)
  (inputs : Inputs r reads operand)
  {left : Associative.Constructors Debug m} {right : Associative.Constructors Debug n}
  (c : Constructors r left right)

include inputs in
theorem Inputs.load (id : NodeId) (opcode : Opcode) (source : Storage.ArgumentSlice)
    (query : reads.operation id opcode = .ok (some source)) (index : Nat) (annotation : NodeId)
    (item : source.items[index]? = some annotation) :
    r.related (operand source index annotation) (logicalOperand source index annotation) :=
  inputs.queried id opcode source query index annotation item

include inputs in
theorem alternating_inputs (choice : AlternatingMask.Choice) (a b : NodeId)
    (capture : AlternatingMask.Capture)
    (found : AlternatingMask.matchCandidate reads choice a b = .ok (some capture)) :
    r.related (operand capture.inner capture.expressionIndex capture.expression)
      (logicalOperand capture.inner capture.expressionIndex capture.expression) ∧
    r.related (operand capture.alternatives capture.otherIndex capture.otherExpression)
      (logicalOperand capture.alternatives capture.otherIndex capture.otherExpression) := by
  obtain ⟨alternatives, inner, al, ar, il, ir, innerMask, outerMask,
    _, alternativesQuery, alternativesItems, innerQuery, innerItems, _, rfl⟩ :=
    AlternatingMask.candidate_found reads choice a b capture found
  constructor
  · apply inputs.load r reads operand _ _ _ innerQuery
    cases choice.constantFirst <;> simp [AlternatingMask.pick, innerItems]
  · apply inputs.load r reads operand _ _ _ alternativesQuery
    cases choice.innerSecond <;> simp [AlternatingMask.pick, alternativesItems]

include c in
theorem alternating_build_inputs (capture : AlternatingMask.Capture) (debug : Debug)
    (expression : r.related (operand capture.inner capture.expressionIndex capture.expression)
      (logicalOperand capture.inner capture.expressionIndex capture.expression))
    (other : r.related (operand capture.alternatives capture.otherIndex capture.otherExpression)
      (logicalOperand capture.alternatives capture.otherIndex capture.otherExpression)) :
    r.related (AlternatingMask.buildCandidateWithInputs left capture debug operand)
      (AlternatingMask.buildCandidate right capture debug) := by
  unfold AlternatingMask.buildCandidate AlternatingMask.buildCandidateWithInputs
  effect_steps r c

include rb inputs c in
theorem alternating_search_inputs (a b : NodeId) (debug : Debug) (choices : List AlternatingMask.Choice) :
    r.related (AlternatingMask.searchWithInputs reads left a b debug choices operand)
      (AlternatingMask.search reads right a b debug choices) := by
  induction choices with
  | nil => exact r.pure _
  | cons choice rest ih =>
    unfold AlternatingMask.search AlternatingMask.searchWithInputs
    apply rb.bind
    intro capture found
    cases capture with
    | none => exact ih
    | some capture =>
      have loaded := alternating_inputs r reads operand inputs choice a b capture found
      exact r.bind (alternating_build_inputs r operand c capture debug loaded.1 loaded.2) (fun _ => r.pure _)

include rb inputs c in
theorem alternating_with_inputs (a b : NodeId) (debug : Debug) :
    r.related (AlternatingMask.distributeAlternatingMaskWithInputs reads left a b debug operand)
      (AlternatingMask.distributeAlternatingMask reads right a b debug) :=
  alternating_search_inputs r rb reads operand inputs c a b debug _

open Lean Meta Elab Tactic in
/-- Use the read equation only for an actual read bind. All other binds retain
the ordinary effect rule, including its failure short-circuiting semantics. -/
elab "input_read " laws:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).headBeta.consumeMData
  unless target.isAppOf ``Effects.related do throwError "expected an effect relation"
  let args := target.getAppArgs
  let program := args[args.size - 2]!.headBeta.consumeMData
  unless program.isAppOf ``Bind.bind do throwError "expected a bind"
  let bindArgs := program.getAppArgs
  unless bindArgs[bindArgs.size - 2]!.headBeta.getAppFn.isConstOf ``readAction do
    throwError "expected a read action"
  let law ← elabTerm laws none
  let proof ← mkAppM ``ReadBind.bind #[law]
  replaceMainGoal (← (← getMainGoal).apply proof)

open Lean Meta Elab Tactic in
elab "input_load " r:ident reads:ident operand:ident inputs:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).headBeta.consumeMData
  unless target.isAppOf ``Effects.related do throwError "expected an effect relation"
  let args := target.getAppArgs
  let program := args[args.size - 2]!.headBeta.consumeMData
  unless program.getAppFn == (← elabTerm operand none) do throwError "expected an indexed input load"
  evalTactic (← `(tactic|
    (solve | apply Inputs.load $r $reads $operand $inputs <;>
      first | assumption | simp_all only [List.getElem?_cons_zero, List.getElem?_cons_succ])))

macro "input_steps " r:ident rb:ident reads:ident operand:ident inputs:ident c:ident : tactic => `(tactic|
  repeat first
    | effect_let
    | effect_value
    | input_load $r $reads $operand $inputs
    | input_read $rb
    | effect_call $c
    | solve_by_elim (config := { maxDepth := 2 }) only [*]
    | (intro value)
    | split)

include rb inputs c in
theorem signextend_with_inputs (a b : NodeId) (debug : Debug) :
    r.related (SignExtendMask.stripRedundantSignExtendMaskWithInputs reads left a b debug operand)
      (SignExtendMask.stripRedundantSignExtendMask reads right a b debug) := by
  unfold SignExtendMask.stripRedundantSignExtendMask SignExtendMask.stripRedundantSignExtendMaskWithInputs
  input_steps r rb reads operand inputs c

include rb inputs c in
theorem shift_product_with_inputs (a b : NodeId) (debug : Debug) :
    r.related (ShiftMasks.powerOfTwoShiftProductWithInputs reads left.operation a b debug operand)
      (ShiftMasks.powerOfTwoShiftProduct reads right.operation a b debug) := by
  unfold ShiftMasks.powerOfTwoShiftProduct ShiftMasks.powerOfTwoShiftProductWithInputs
  input_steps r rb reads operand inputs c

include rb in
theorem drop_repeated_inputs (c : SourceConstructors r reads left right)
    (instruction : Opcode) (nestedId repeated : NodeId) (first : Bool) (debug : Debug) :
    r.related (dropRepeatedLocal reads left.localOperation instruction nestedId repeated first debug)
      (dropRepeatedLocal reads right.localOperation instruction nestedId repeated first debug) := by
  have bounded : ∀ a b selected, repeatedIndex reads a b repeated = some selected → selected < 2 := by
    intro a b selected found
    unfold repeatedIndex at found
    split at found
    · cases found; decide
    · split at found
      · cases found; decide
      · cases found
  unfold dropRepeatedLocal
  repeat first
    | (solve | apply c.localOperation <;>
        first | assumption | (solve | simp_all) | solve_by_elim only [bounded, *])
    | exact r.pure _
    | input_read rb
    | apply r.bind
    | (intro value)
    | split

include rb in
theorem shift_mask_inputs (c : SourceConstructors r reads left right)
    (a b : NodeId) (debug : Debug) :
    r.related (ShiftMasks.removeCoveredShiftMask reads left a b debug)
      (ShiftMasks.removeCoveredShiftMask reads right a b debug) := by
  unfold ShiftMasks.removeCoveredShiftMask
  repeat first
    | (solve | apply c.borrowedOperation <;> assumption)
    | exact r.pure _
    | input_read rb
    | apply r.bind
    | exact r.read _
    | (intro value)
    | split

open Lean Meta Elab Tactic in
elab "source_helper " laws:ident reads:ident constructors:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).headBeta.consumeMData
  unless target.isAppOf ``Effects.related do throwError "expected an effect relation"
  let args := target.getAppArgs
  let effect := args[args.size - 4]!
  let program := args[args.size - 2]!.headBeta.consumeMData
  let rules : List (Name × Name) := [
    (``dropRepeatedLocal, ``drop_repeated_inputs),
    (``ShiftMasks.removeCoveredShiftMask, ``shift_mask_inputs)]
  let some (_, lemma) := rules.find? (fun rule => some rule.1 == program.getAppFn.constName?) |
    throwError "no source rule for this head"
  let values ← #[laws, reads, constructors].mapM (fun id => elabTerm id none)
  replaceMainGoal (← (← getMainGoal).apply (← mkAppM lemma (#[effect] ++ values)))

include rb inputs in
theorem unary_with_inputs (c : SourceConstructors r reads left right) (instruction : Opcode) (value : NodeId) (debug : Debug) :
    r.related (unaryStageWithInputs reads left instruction value debug operand)
      (unaryStage reads right instruction value debug) := by
  unfold unaryStage unaryStageWithInputs
  have scalar := c.scalars
  repeat first
    | (solve | apply c.borrowedOperation <;> assumption)
    | effect_let
    | effect_value
    | input_load r reads operand inputs
    | input_read rb
    | effect_call scalar
    | solve_by_elim (config := { maxDepth := 2 }) only [*]
    | (intro value)
    | split

open Lean Meta Elab Tactic in
elab "input_helper " laws:ident reads:ident operand:ident inputs:ident constructors:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).headBeta.consumeMData
  unless target.isAppOf ``Effects.related do throwError "expected an effect relation"
  let args := target.getAppArgs
  let effect := args[args.size - 4]!
  let program := args[args.size - 2]!.headBeta.consumeMData
  let rules : List (Name × Name) := [
    (``AlternatingMask.distributeAlternatingMaskWithInputs, ``alternating_with_inputs),
    (``SignExtendMask.stripRedundantSignExtendMaskWithInputs, ``signextend_with_inputs),
    (``ShiftMasks.powerOfTwoShiftProductWithInputs, ``shift_product_with_inputs)]
  let some (_, lemma) := rules.find? (fun rule => some rule.1 == program.getAppFn.constName?) |
    throwError "no input rule for this head"
  let values ← #[laws, reads, operand, inputs, constructors].mapM (fun id => elabTerm id none)
  replaceMainGoal (← (← getMainGoal).apply (← mkAppM lemma (#[effect] ++ values)))

include rb inputs in
set_option maxHeartbeats 1000000 in
theorem binary_with_inputs (c : SourceConstructors r reads left right) (usizeBits : Nat) (instruction : Opcode) (a b : NodeId)
    (debug : Debug) (options : Options) :
    r.related (binaryStageWithInputs reads left usizeBits instruction a b debug options operand)
      (binaryStage reads right usizeBits instruction a b debug options) := by
  have scalar := c.scalars
  unfold binaryStage binaryStageWithInputs
  repeat first
    | effect_let
    | effect_value
    | (solve | apply c.borrowedOperation <;> assumption)
    | source_helper rb reads c
    | input_helper rb reads operand inputs scalar
    | input_load r reads operand inputs
    | input_read rb
    | effect_call scalar
    | solve_by_elim (config := { maxDepth := 2 }) only [*]
    | (intro value)
    | split

include c in
theorem shift_with_input (first : Bool) (instruction : Opcode) (value : Word)
    (inputLeft : m NodeId) (inputRight : n NodeId) (debug : Debug)
    (input : r.related inputLeft inputRight) :
    r.related (shiftInput left first instruction value inputLeft debug)
      (shiftInput right first instruction value inputRight debug) := by
  cases first <;> unfold shiftInput <;> simp only [Bool.false_eq_true, if_false, if_true]
  all_goals effect_steps r c

include c in
theorem max_with_input (parityLeft : NodeId → Debug → m NodeId)
    (parityRight : NodeId → Debug → n NodeId) (debug : Debug)
    (input : ∀ one location, r.related (parityLeft one location) (parityRight one location)) :
    r.related (maxExponent left parityLeft debug) (maxExponent right parityRight debug) := by
  unfold maxExponent
  effect_steps r c

open Lean Meta Elab Tactic in
elab "input_literal " constructors:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).headBeta.consumeMData
  unless target.isAppOf ``Effects.related do throwError "expected an effect relation"
  let args := target.getAppArgs
  let effect := args[args.size - 4]!
  let program := args[args.size - 2]!.headBeta.consumeMData
  let rules : List (Name × Name) := [(``shiftInput, ``shift_with_input), (``maxExponent, ``max_with_input)]
  let some (_, lemma) := rules.find? (fun rule => some rule.1 == program.getAppFn.constName?) |
    throwError "no literal rule for this head"
  let c ← elabTerm constructors none
  replaceMainGoal (← (← getMainGoal).apply (← mkAppM lemma #[effect, c]))

include rb c in
theorem evm_with_inputs (usizeBits : Nat) (instruction : Opcode) (arguments : List NodeId)
    (debug : Debug) (version : Version) (address : Nat)
    (root : SliceInput r operand ⟨address, arguments⟩) :
    r.related (evmStageWithInputs reads left usizeBits instruction arguments debug version operand address)
      (evmStage reads right usizeBits instruction arguments debug version) := by
  unfold evmStage evmStageWithInputs
  repeat first
    | effect_let
    | effect_value
    | (solve | apply root <;> simp_all only [List.getElem?_cons_zero, List.getElem?_cons_succ])
    | input_literal c
    | input_read rb
    | effect_call c
    | solve_by_elim (config := { maxDepth := 2 }) only [*]
    | (intro value)
    | split

include rb inputs in
/-- The same complete generated body with native indexed inputs and logical
inputs. Its only constructor premise concerns proper recursive children; query
provenance and initializer positions are derived through every source branch. -/
theorem simplify_options_with_inputs (c : SourceConstructors r reads left right) (usizeBits : Nat) (instruction : Opcode) (arguments : List NodeId)
    (debug : Debug) (options : Options) (address : Nat)
    (root : SliceInput r operand ⟨address, arguments⟩) :
    r.related (simplifyOptionsWithInputs reads left usizeBits instruction arguments debug options operand address)
      (simplifyWithOptions reads right usizeBits instruction arguments debug options) := by
  have scalar := c.scalars
  unfold simplifyWithOptions simplifyOptionsWithInputs
  simp only [← binaryStage.eq_def, ← unaryStage.eq_def, ← evmStage.eq_def]
  repeat first
    | apply r.or_next
    | exact r.constant_stage scalar _ _ _ _
    | exact binary_with_inputs r rb reads operand inputs c _ _ _ _ _ _
    | exact unary_with_inputs r rb reads operand inputs c _ _ _
    | exact evm_with_inputs r rb reads operand scalar _ _ _ _ _ _ root
    | effect_step r scalar

include rb inputs in
theorem simplify_with_inputs (c : SourceConstructors r reads left right) (usizeBits : Nat) (instruction : Opcode) (arguments : List NodeId)
    (debug : Debug) (address : Nat) (root : SliceInput r operand ⟨address, arguments⟩) :
    r.related (simplifyWithInputs reads left usizeBits instruction arguments debug operand address)
      (Dispatch.simplify reads right usizeBits instruction arguments debug) :=
  simplify_options_with_inputs r rb reads operand inputs c usizeBits instruction arguments debug defaultOptions address root

end Effects
end Compiler.Extraction.Dispatch
