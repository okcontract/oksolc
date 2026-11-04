/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.DispatchProgram
import Lean

namespace Compiler.Extraction.Dispatch
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul

/-- A proved relation on effects. Its laws must be discharged for an execution
model; polymorphism alone is not a preservation proof. Bind relates the same
returned value and therefore keeps subsequent constructor arguments aligned. -/
structure Effects (m n : Type → Type) [Monad m] [Monad n]
    [MonadLift (Except Interner.Error) m] [MonadLift (Except Interner.Error) n] where
  related : {α : Type} → m α → n α → Prop
  pure : ∀ {α} (value : α), related (pure value) (pure value)
  bind : ∀ {α β} {left : m α} {right : n α} {nextLeft : α → m β} {nextRight : α → n β},
    related left right → (∀ value, related (nextLeft value) (nextRight value)) →
    related (left >>= nextLeft) (right >>= nextRight)
  lift : ∀ {α} (result : Except Interner.Error α), related (monadLift result) (monadLift result)

namespace Effects
variable {m n : Type → Type} [Monad m] [Monad n]
  [MonadLift (Except Interner.Error) m] [MonadLift (Except Interner.Error) n]

structure Constructors (r : Effects m n) (left : Associative.Constructors Debug m)
    (right : Associative.Constructors Debug n) : Prop where
  operation : ∀ opcode ids debug, r.related (left.operation opcode ids debug) (right.operation opcode ids debug)
  constant : ∀ value debug, r.related (left.constant value debug) (right.constant value debug)
  materialize : ∀ id value debug, r.related (left.materialize id value debug) (right.materialize id value debug)
  borrowedOperation : ∀ address opcode ids debug,
    r.related (left.borrowedOperation address opcode ids debug) (right.borrowedOperation address opcode ids debug)
  localOperation : ∀ opcode source selected repeated first debug,
    r.related (left.localOperation opcode source selected repeated first debug)
      (right.localOperation opcode source selected repeated first debug)

variable (r : Effects m n)

theorem read (result : Except Storage.ReadError α) : r.related (readAction result) (readAction result) := by
  cases result with
  | ok value => exact r.pure value
  | error error => cases error <;> exact r.lift _

theorem logical_operand (source : Storage.ArgumentSlice) (index : Nat) (value : NodeId) :
    r.related (logicalOperand source index value) (logicalOperand source index value) := r.pure value

/-- Paired indexed readers return the same value or failure under the effect
relation. Native readers must derive this from their reached memory; no logical
annotation, validity or successful-load premise is imposed here. -/
structure Operands (r : Effects m n) (left : OperandRead m) (right : OperandRead n) : Prop where
  load : ∀ source index annotation, r.related (left source index annotation) (right source index annotation)

theorem logical_operands : Operands r logicalOperand logicalOperand := ⟨r.logical_operand⟩

variable {inputLeft : OperandRead m} {inputRight : OperandRead n}

theorem arithmetic (result : Except Folding.Fault α) :
    r.related (Dispatch.arithmetic result) (Dispatch.arithmetic result) := by
  cases result with
  | ok value => exact r.pure value
  | error error => exact r.lift _

theorem add_word (a b : Word) : r.related (addWord a b) (addWord a b) := by
  unfold addWord
  exact r.bind (r.arithmetic _) (fun value => r.pure _)

theorem sub_word (a b : Word) : r.related (subWord a b) (subWord a b) := by
  unfold subWord
  exact r.bind (r.arithmetic _) (fun value => r.pure _)

theorem or_next {left nextLeft : m (Option NodeId)} {right nextRight : n (Option NodeId)}
    (stage : r.related left right) (next : r.related nextLeft nextRight) :
    r.related (orNext left nextLeft) (orNext right nextRight) := by
  apply r.bind stage
  intro value
  cases value with
  | none => exact next
  | some id => exact r.pure _

/-- Preserve a shared continuation instead of expanding it at every branch. -/
theorem let_related (rel : γ → δ → Prop) (f : α) (g : β) (relation : α → β → Prop)
    (bodyLeft : α → γ) (bodyRight : β → δ)
    (values : relation f g)
    (bodies : ∀ x y, relation x y → rel (bodyLeft x) (bodyRight y)) :
    rel (bodyLeft f) (bodyRight g) := bodies f g values

open Lean Meta Elab Tactic in
/-- The generated do-blocks share continuations as unary local functions.
Expose two ordinary proof obligations (continuation and body); every generated
term is checked by Lean. Other let shapes fail explicitly. -/
elab "effect_let" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).headBeta.consumeMData
  let args := target.getAppArgs
  if args.size < 2 then throwError "expected a binary relation"
  let rel := mkAppN target.getAppFn (args.extract 0 (args.size - 2))
  let .letE leftName leftType leftValue leftBody _ := args[args.size - 2]!.headBeta.consumeMData |
    throwError "expected a shared left continuation"
  let .letE rightName rightType rightValue rightBody _ := args[args.size - 1]!.headBeta.consumeMData |
    throwError "expected a shared right continuation"
  let .forallE argName domain leftResult _ := leftType.consumeMData |
    throwError "expected a unary left continuation"
  let .forallE _ rightDomain rightResult _ := rightType.consumeMData |
    throwError "expected a unary right continuation"
  unless (← isDefEq domain rightDomain) do throwError "different continuation domains"
  if leftResult.hasLooseBVars || rightResult.hasLooseBVars then
    throwError "dependent continuation results are unsupported"
  let relation ← withLocalDeclD leftName leftType fun f => withLocalDeclD rightName rightType fun g => do
    let pointwise ← withLocalDeclD argName domain fun value => do
      mkForallFVars #[value] (mkApp2 rel (mkApp f value) (mkApp g value))
    mkLambdaFVars #[f, g] pointwise
  let values ← mkFreshExprMVar (mkApp2 relation leftValue rightValue)
  let bodiesType ← withLocalDeclD leftName leftType fun f => withLocalDeclD rightName rightType fun g => do
    withLocalDeclD `related (mkApp2 relation f g) fun h => do
      mkForallFVars #[f, g, h] (mkApp2 rel (leftBody.instantiate1 f) (rightBody.instantiate1 g))
  let bodies ← mkFreshExprMVar bodiesType
  let proof ← mkAppM ``Effects.let_related #[rel, leftValue, rightValue, relation,
    .lam leftName leftType leftBody .default, .lam rightName rightType rightBody .default, values, bodies]
  (← getMainGoal).assign proof
  replaceMainGoal [values.mvarId!, bodies.mvarId!]

open Lean Meta Elab Tactic in
elab "effect_value" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).headBeta.consumeMData
  let args := target.getAppArgs
  if args.size < 2 then throwError "expected a binary relation"
  let .letE _ leftType leftValue leftBody _ := args[args.size - 2]!.headBeta.consumeMData |
    throwError "expected a left value let"
  let .letE _ rightType rightValue rightBody _ := args[args.size - 1]!.headBeta.consumeMData |
    throwError "expected a right value let"
  if leftType.isForall || rightType.isForall then throwError "retain function sharing"
  let reduced := mkAppN target.getAppFn <| (args.set! (args.size - 2) (leftBody.instantiate1 leftValue))
    |>.set! (args.size - 1) (rightBody.instantiate1 rightValue)
  let next ← (← getMainGoal).change reduced
  replaceMainGoal [next]

variable {left : Associative.Constructors Debug m} {right : Associative.Constructors Debug n}
  (c : Constructors r left right)
include c

theorem pair_scalars (opcode : Opcode) (a b : NodeId) (debug : Debug) :
    r.related (ConstructorPair.scalars left opcode a b debug)
      (ConstructorPair.scalars right opcode a b debug) := c.operation opcode [a, b] debug

theorem double_iszero (id : NodeId) (debug : Debug) :
    r.related (doubleIsZero left.operation id debug) (doubleIsZero right.operation id debug) := by
  unfold doubleIsZero
  exact r.bind (c.operation _ _ _) (fun value => c.operation _ _ _)

theorem drop_repeated (reads : Reads) (instruction : Opcode) (nestedId repeated : NodeId)
    (first : Bool) (debug : Debug) :
    r.related (dropRepeatedLocal reads left.localOperation instruction nestedId repeated first debug)
      (dropRepeatedLocal reads right.localOperation instruction nestedId repeated first debug) := by
  unfold dropRepeatedLocal
  repeat first
    | exact r.pure _
    | exact r.read _
    | exact c.localOperation _ _ _ _ _ _
    | apply r.bind
    | (intro value)
    | split

/-- Only proof-producing introduction and case-split rules are used. The tactic
neither evaluates native code nor admits a branch. -/
macro "effect_step " r:ident c:ident : tactic => `(tactic|
  first
    | effect_let
    | solve_by_elim (config := { maxDepth := 2 }) only [*]
    | exact Effects.pure $r _
    | exact Effects.read $r _
    | exact Effects.arithmetic $r _
    | exact Effects.add_word $r _ _
    | exact Effects.sub_word $r _ _
    | exact Constructors.operation $c _ _ _
    | exact Constructors.constant $c _ _
    | exact Constructors.materialize $c _ _ _
    | exact Constructors.borrowedOperation $c _ _ _ _
    | exact Constructors.localOperation $c _ _ _ _ _ _
    | apply Effects.bind $r
    | (intro value)
    | split)

macro "effect_steps " r:ident c:ident : tactic => `(tactic| repeat effect_step $r $c)

theorem apply_replacement (replacement : Replacement) (a b : NodeId) (debug : Debug) :
    r.related (zigApply replacement (algebraicBuilder left) a b debug)
      (zigApply replacement (algebraicBuilder right) a b debug) := by
  cases replacement <;> dsimp only [zigApply, algebraicBuilder]
  all_goals effect_steps r c

theorem reassociate (reads : Reads) (instruction : Opcode) (nestedId other : NodeId)
    (nestedIsRight : Bool) (debug : Debug) :
    r.related (Associative.reassociate reads left instruction nestedId other nestedIsRight debug)
      (Associative.reassociate reads right instruction nestedId other nestedIsRight debug) := by
  unfold Associative.reassociate
  effect_steps r c

theorem alternating_build_operands (inputs : Operands r inputLeft inputRight)
    (capture : AlternatingMask.Capture) (debug : Debug) :
    r.related (AlternatingMask.buildCandidateWithInputs left capture debug inputLeft)
      (AlternatingMask.buildCandidateWithInputs right capture debug inputRight) := by
  have loads := inputs.load
  unfold AlternatingMask.buildCandidateWithInputs
  effect_steps r c

theorem alternating_build (capture : AlternatingMask.Capture) (debug : Debug) :
    r.related (AlternatingMask.buildCandidate left capture debug) (AlternatingMask.buildCandidate right capture debug) :=
  r.alternating_build_operands c r.logical_operands capture debug

theorem alternating_search_operands (inputs : Operands r inputLeft inputRight) (reads : Reads)
    (a b : NodeId) (debug : Debug) (choices : List AlternatingMask.Choice) :
    r.related (AlternatingMask.searchWithInputs reads left a b debug choices inputLeft)
      (AlternatingMask.searchWithInputs reads right a b debug choices inputRight) := by
  induction choices with
  | nil => exact r.pure _
  | cons choice rest ih =>
    unfold AlternatingMask.searchWithInputs
    apply r.bind (r.read _)
    intro capture
    cases capture with
    | none => exact ih
    | some capture => exact r.bind (r.alternating_build_operands c inputs capture debug) (fun id => r.pure _)

theorem alternating_search (reads : Reads) (a b : NodeId) (debug : Debug) (choices : List AlternatingMask.Choice) :
    r.related (AlternatingMask.search reads left a b debug choices) (AlternatingMask.search reads right a b debug choices) :=
  r.alternating_search_operands c r.logical_operands reads a b debug choices

theorem alternating_operands (inputs : Operands r inputLeft inputRight) (reads : Reads)
    (a b : NodeId) (debug : Debug) :
    r.related (AlternatingMask.distributeAlternatingMaskWithInputs reads left a b debug inputLeft)
      (AlternatingMask.distributeAlternatingMaskWithInputs reads right a b debug inputRight) :=
  r.alternating_search_operands c inputs reads a b debug _

theorem alternating (reads : Reads) (a b : NodeId) (debug : Debug) :
    r.related (AlternatingMask.distributeAlternatingMask reads left a b debug)
      (AlternatingMask.distributeAlternatingMask reads right a b debug) :=
  r.alternating_operands c r.logical_operands reads a b debug

theorem signextend_mask_operands (inputs : Operands r inputLeft inputRight) (reads : Reads)
    (a b : NodeId) (debug : Debug) :
    r.related (SignExtendMask.stripRedundantSignExtendMaskWithInputs reads left a b debug inputLeft)
      (SignExtendMask.stripRedundantSignExtendMaskWithInputs reads right a b debug inputRight) := by
  have loads := inputs.load
  unfold SignExtendMask.stripRedundantSignExtendMaskWithInputs
  effect_steps r c

theorem signextend_mask (reads : Reads) (a b : NodeId) (debug : Debug) :
    r.related (SignExtendMask.stripRedundantSignExtendMask reads left a b debug)
      (SignExtendMask.stripRedundantSignExtendMask reads right a b debug) :=
  r.signextend_mask_operands c r.logical_operands reads a b debug

theorem opposite_net (opcode : Opcode) (outer inner : Word) (id : NodeId) (debug : Debug) :
    r.related (OppositeShifts.buildNet left opcode outer inner id debug)
      (OppositeShifts.buildNet right opcode outer inner id debug) := by
  unfold OppositeShifts.buildNet
  effect_steps r c

theorem opposite (opcode : Opcode) (outer inner : Word) (id : NodeId) (debug : Debug) :
    r.related (OppositeShifts.combineOppositeShifts left opcode outer inner id debug)
      (OppositeShifts.combineOppositeShifts right opcode outer inner id debug) := by
  unfold OppositeShifts.combineOppositeShifts
  exact r.bind (r.read _) (fun _ => r.bind (r.opposite_net c opcode outer inner id debug)
    (fun _ => r.bind (c.constant _ _) (fun _ => c.operation _ _ _)))

theorem shift_mask (reads : Reads) (a b : NodeId) (debug : Debug) :
    r.related (ShiftMasks.removeCoveredShiftMask reads left a b debug)
      (ShiftMasks.removeCoveredShiftMask reads right a b debug) := by
  unfold ShiftMasks.removeCoveredShiftMask
  effect_steps r c

theorem shift_product_operands (inputs : Operands r inputLeft inputRight) (reads : Reads)
    (a b : NodeId) (debug : Debug) :
    r.related (ShiftMasks.powerOfTwoShiftProductWithInputs reads left.operation a b debug inputLeft)
      (ShiftMasks.powerOfTwoShiftProductWithInputs reads right.operation a b debug inputRight) := by
  have loads := inputs.load
  unfold ShiftMasks.powerOfTwoShiftProductWithInputs
  effect_steps r c

theorem shift_product (reads : Reads) (a b : NodeId) (debug : Debug) :
    r.related (ShiftMasks.powerOfTwoShiftProduct reads left.operation a b debug)
      (ShiftMasks.powerOfTwoShiftProduct reads right.operation a b debug) :=
  r.shift_product_operands c r.logical_operands reads a b debug

open Lean Meta Elab Tactic in
/-- Select a proved effect rule by the program's head symbol. Avoid attempting
unification against unrelated helper bodies and expanding shared code. -/
private def effectCall (constructors : Syntax) (inputs : Option Syntax) : TacticM Unit := withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).headBeta.consumeMData
  unless target.isAppOf ``Effects.related do throwError "expected an effect relation"
  let args := target.getAppArgs
  let effect := args[args.size - 4]!
  let program := args[args.size - 2]!.headBeta.consumeMData
  let name := program.getAppFn.constName?
  let rules : List (Name × Name × Bool) := [
    (``Pure.pure, ``Effects.pure, false), (``logicalOperand, ``Effects.logical_operand, false), (``Bind.bind, ``Effects.bind, false),
    (``readAction, ``Effects.read, false), (``Dispatch.arithmetic, ``Effects.arithmetic, false),
    (``addWord, ``Effects.add_word, false), (``subWord, ``Effects.sub_word, false),
    (``Associative.Constructors.operation, ``Constructors.operation, true),
    (``Associative.Constructors.constant, ``Constructors.constant, true),
    (``Associative.Constructors.materialize, ``Constructors.materialize, true),
    (``Associative.Constructors.borrowedOperation, ``Constructors.borrowedOperation, true),
    (``Associative.Constructors.localOperation, ``Constructors.localOperation, true),
    (``ConstructorPair.scalars, ``Effects.pair_scalars, true),
    (``zigApply, ``Effects.apply_replacement, true), (``doubleIsZero, ``Effects.double_iszero, true),
    (``dropRepeatedLocal, ``Effects.drop_repeated, true), (``Associative.reassociate, ``Effects.reassociate, true),
    (``AlternatingMask.distributeAlternatingMask, ``Effects.alternating, true),
    (``AlternatingMask.distributeAlternatingMaskWithInputs, ``Effects.alternating, true),
    (``SignExtendMask.stripRedundantSignExtendMask, ``Effects.signextend_mask, true),
    (``SignExtendMask.stripRedundantSignExtendMaskWithInputs, ``Effects.signextend_mask, true),
    (``OppositeShifts.combineOppositeShifts, ``Effects.opposite, true),
    (``ShiftMasks.removeCoveredShiftMask, ``Effects.shift_mask, true),
    (``ShiftMasks.powerOfTwoShiftProduct, ``Effects.shift_product, true),
    (``ShiftMasks.powerOfTwoShiftProductWithInputs, ``Effects.shift_product, true)]
  let operandRules : List (Name × Name × Bool) := [
    (``AlternatingMask.distributeAlternatingMaskWithInputs, ``Effects.alternating_operands, true),
    (``SignExtendMask.stripRedundantSignExtendMaskWithInputs, ``Effects.signextend_mask_operands, true),
    (``ShiftMasks.powerOfTwoShiftProductWithInputs, ``Effects.shift_product_operands, true)]
  let rules := if inputs.isSome then operandRules ++ rules else rules
  let some (_, lemma, needsConstructors) := rules.find? (fun rule => some rule.1 == name) |
    throwError "no effect rule for this head"
  let c ← elabTerm constructors none
  let constructorRule := [``Constructors.operation, ``Constructors.constant, ``Constructors.materialize,
    ``Constructors.borrowedOperation, ``Constructors.localOperation].contains lemma
  let ruleArgs := if constructorRule then #[c] else if needsConstructors then #[effect, c] else #[effect]
  let ruleArgs ← if operandRules.any (fun rule => rule.2.1 == lemma) then do
    let some inputs := inputs | throwError "missing paired operand proof"
    Pure.pure (ruleArgs.push (← elabTerm inputs none))
  else Pure.pure ruleArgs
  let proof ← mkAppM lemma ruleArgs
  let goals ← (← getMainGoal).apply proof
  replaceMainGoal goals

elab "effect_call " constructors:ident : tactic => effectCall constructors none
elab "effect_operand_call " constructors:ident inputs:ident : tactic => effectCall constructors (some inputs)

theorem constant_stage (reads : Reads) (instruction : Opcode) (arguments : List NodeId) (debug : Debug) :
    r.related (constantStage reads left instruction arguments debug) (constantStage reads right instruction arguments debug) := by
  unfold constantStage
  effect_steps r c

theorem unary_stage_operands (inputs : Operands r inputLeft inputRight) (reads : Reads)
    (instruction : Opcode) (value : NodeId) (debug : Debug) :
    r.related (unaryStageWithInputs reads left instruction value debug inputLeft)
      (unaryStageWithInputs reads right instruction value debug inputRight) := by
  have loads := inputs.load
  unfold unaryStageWithInputs
  effect_steps r c

theorem unary_stage (reads : Reads) (instruction : Opcode) (value : NodeId) (debug : Debug) :
    r.related (unaryStage reads left instruction value debug) (unaryStage reads right instruction value debug) :=
  r.unary_stage_operands c r.logical_operands reads instruction value debug

theorem evm_stage_operands (inputs : Operands r inputLeft inputRight) (reads : Reads)
    (usizeBits : Nat) (instruction : Opcode) (arguments : List NodeId)
    (debug : Debug) (version : Version) (address : Nat) :
    r.related (evmStageWithInputs reads left usizeBits instruction arguments debug version inputLeft address)
      (evmStageWithInputs reads right usizeBits instruction arguments debug version inputRight address) := by
  have loads := inputs.load
  unfold evmStageWithInputs
  effect_steps r c

theorem evm_stage (reads : Reads) (usizeBits : Nat) (instruction : Opcode) (arguments : List NodeId)
    (debug : Debug) (version : Version) :
    r.related (evmStage reads left usizeBits instruction arguments debug version)
      (evmStage reads right usizeBits instruction arguments debug version) :=
  r.evm_stage_operands c r.logical_operands reads usizeBits instruction arguments debug version 0

theorem binary_stage_operands (inputs : Operands r inputLeft inputRight) (reads : Reads)
    (usizeBits : Nat) (instruction : Opcode) (a b : NodeId) (debug : Debug) (options : Options) :
    r.related (binaryStageWithInputs reads left usizeBits instruction a b debug options inputLeft)
      (binaryStageWithInputs reads right usizeBits instruction a b debug options inputRight) := by
  unfold binaryStageWithInputs
  repeat first
    | effect_let
    | effect_value
    | exact inputs.load _ _ _
    | effect_operand_call c inputs
    | solve_by_elim (config := { maxDepth := 2 }) only [*]
    | (intro value)
    | split

theorem binary_stage (reads : Reads) (usizeBits : Nat) (instruction : Opcode) (a b : NodeId)
    (debug : Debug) (options : Options) :
    r.related (binaryStage reads left usizeBits instruction a b debug options)
      (binaryStage reads right usizeBits instruction a b debug options) :=
  r.binary_stage_operands c r.logical_operands reads usizeBits instruction a b debug options

/-- The same complete dispatcher transports paired operand readers at their
actual source positions, including after children mutate or fail. This does
not assume that an indexed read returns its source annotation. -/
theorem simplify_options_operands (inputs : Operands r inputLeft inputRight) (reads : Reads)
    (usizeBits : Nat) (instruction : Opcode) (arguments : List NodeId)
    (debug : Debug) (options : Options) (address : Nat) :
    r.related (simplifyOptionsWithInputs reads left usizeBits instruction arguments debug options inputLeft address)
      (simplifyOptionsWithInputs reads right usizeBits instruction arguments debug options inputRight address) := by
  unfold simplifyOptionsWithInputs
  repeat first
    | apply r.or_next
    | exact r.constant_stage c _ _ _ _
    | exact r.binary_stage_operands c inputs _ _ _ _ _ _ _
    | exact r.unary_stage_operands c inputs _ _ _ _
    | exact r.evm_stage_operands c inputs _ _ _ _ _ _ _
    | effect_step r c

/-- The complete ordered dispatcher, for all instructions, argument lists,
options and related constructors. No bounded input corpus is a premise. -/
theorem simplify_options (reads : Reads) (usizeBits : Nat) (instruction : Opcode) (arguments : List NodeId)
    (debug : Debug) (options : Options) :
    r.related (simplifyWithOptions reads left usizeBits instruction arguments debug options)
      (simplifyWithOptions reads right usizeBits instruction arguments debug options) :=
  r.simplify_options_operands c r.logical_operands reads usizeBits instruction arguments debug options 0

theorem simplify_operands (inputs : Operands r inputLeft inputRight) (reads : Reads)
    (usizeBits : Nat) (instruction : Opcode) (arguments : List NodeId) (debug : Debug) (address : Nat) :
    r.related (simplifyWithInputs reads left usizeBits instruction arguments debug inputLeft address)
      (simplifyWithInputs reads right usizeBits instruction arguments debug inputRight address) :=
  r.simplify_options_operands c inputs reads usizeBits instruction arguments debug defaultOptions address

theorem simplify (reads : Reads) (usizeBits : Nat) (instruction : Opcode) (arguments : List NodeId) (debug : Debug) :
    r.related (Dispatch.simplify reads left usizeBits instruction arguments debug)
      (Dispatch.simplify reads right usizeBits instruction arguments debug) :=
  r.simplify_options c reads usizeBits instruction arguments debug defaultOptions

end Effects
end Compiler.Extraction.Dispatch
