/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Validation.Graph
import Contract.Evm.Machine

/-! Cancun straight-line word-block bytecode validator bridged directly to the
unified `Contract.Evm` raw-byte machine (`Contract.Evm.WordOp`, `decodeWordOpAt`,
`step`, `run`, `runMetered`).

Numeric byte decoding delegates directly to `Contract.Evm.decodeWordOpAt` (zero
duplicated instruction tables). Unsupported instructions, truncated `PUSH`
immediates, stack overflows (`> 1024`), stack underflows, and exhausted checking
fuel all reject (`false`).

In addition to bytecode equivalence, `WordBlock` defines the canonical Solidity
word-DAG source semantics (`evalSource`) and lowering (`lowerSourceNodes`), where
Solidity shifts use `(value, shift)` operand order while Yul/EVM `Node` uses
`(shift, value)` operand order, matching `src/compiler_word_export.zig`. -/
namespace Compiler.Validation.WordBlock
open Contract Contract.Yul Contract.Evm

/-- Abstract interpretation of a canonical `Contract.Evm.WordOp` over any `Algebra α`
(concrete `Word`s or symbolic `Expression`s), enforcing the 1024-word stack limit. -/
def stepOp (algebra : Algebra α) (stack : List α) : WordOp → Option (List α)
  | .push _ v =>
    if stack.length < 1024 then some (algebra.literal v.toNat :: stack) else none
  | .dup i =>
    if stack.length < 1024 then do return (← stack[i]?) :: stack else none
  | .swap i => match stack with
    | top :: rest => do return (← rest[i]?) :: rest.set i top
    | _ => none
  | .pop => match stack with
    | _ :: rest => some rest
    | _ => none
  | .nullary op =>
    if stack.length < 1024 then some (algebra.nullary op :: stack) else none
  | .unary op => match stack with
    | a :: rest => some (algebra.unary op a :: rest)
    | _ => none
  | .binary op => match stack with
    | a :: b :: rest => some (algebra.binary op a b :: rest)
    | _ => none
  | .ternary op => match stack with
    | a :: b :: c :: rest => some (algebra.ternary op a b c :: rest)
    | _ => none

/-- Concrete `stepOp` over `words ctx locals` agrees identically with `WordOp.evalStack`. -/
theorem stepOp_words_eq_evalStack (ctx : Context) (locals : String → Word)
    (stack : List Word) (op : WordOp) :
    stepOp (words ctx locals) stack op = op.evalStack ctx stack := by
  cases op with
  | push _ v =>
    simp [stepOp, WordOp.evalStack, words]
  | dup i =>
    rfl
  | swap i =>
    cases stack <;> rfl
  | pop =>
    cases stack <;> rfl
  | nullary op =>
    rfl
  | unary op =>
    cases stack <;> rfl
  | binary op =>
    cases stack with
    | nil => rfl
    | cons a rest => cases rest <;> rfl
  | ternary op =>
    cases stack with
    | nil => rfl
    | cons a r1 =>
      cases r1 with
      | nil => rfl
      | cons b r2 => cases r2 <;> rfl

/-- Symbolic/abstract straight-line block runner over `code` starting at `pc` using
the canonical `Contract.Evm.decodeWordOpAt` decoder. Requires `stack.length ≤ 1024`
at every point and reaches `pc = code.length` cleanly without jumping past `code.length`. -/
def runBlock (algebra : Algebra α) (code : List UInt8) : Nat → Nat → List α → Option (List α)
  | 0, pc, stack =>
    if stack.length > 1024 then none
    else if pc = code.length then some stack
    else none
  | fuel + 1, pc, stack =>
    if stack.length > 1024 then none
    else if pc = code.length then some stack
    else do
      let (op, width) ← decodeWordOpAt code pc
      let next ← stepOp algebra stack op
      runBlock algebra code fuel (pc + width) next

def evalExpr (ctx : Context) (locals : String → Word) (e : Expression) : Word :=
  e.eval ctx locals

theorem stepOp_map (op : WordOp) (stack : List Expression) (ctx : Context) (locals : String → Word) :
    stepOp (words ctx locals) (stack.map (evalExpr ctx locals)) op =
      (stepOp expressions stack op).map (List.map (evalExpr ctx locals)) := by
  cases op with
  | push _ v =>
    simp only [stepOp, List.length_map]
    split
    · simp [expressions, words, evalExpr, Expression.eval]
    · rfl
  | dup i =>
    simp only [stepOp, List.length_map]
    split
    · cases h : stack[i]? <;> simp [h, List.getElem?_map]
    · rfl
  | swap i =>
    cases stack with
    | nil => rfl
    | cons top rest =>
      cases h : rest[i]? <;> simp [stepOp, h, List.getElem?_map, List.map_set]
  | pop =>
    cases stack <;> rfl
  | nullary op =>
    simp only [stepOp, List.length_map]
    split
    · simp [expressions, words, evalExpr, Expression.eval]
    · rfl
  | unary op =>
    cases stack <;> simp [stepOp, expressions, words, evalExpr, Expression.eval]
  | binary op =>
    cases stack with
    | nil => rfl
    | cons a rest =>
      cases rest <;> simp [stepOp, expressions, words, evalExpr, Expression.eval]
  | ternary op =>
    cases stack with
    | nil => rfl
    | cons a r1 =>
      cases r1 with
      | nil => rfl
      | cons b r2 =>
        cases r2 <;> simp [stepOp, expressions, words, evalExpr, Expression.eval]

theorem runBlock_map (code : List UInt8) (fuel pc : Nat) (stack : List Expression)
    (ctx : Context) (locals : String → Word) :
    runBlock (words ctx locals) code fuel pc (stack.map (evalExpr ctx locals)) =
      (runBlock expressions code fuel pc stack).map (List.map (evalExpr ctx locals)) := by
  induction fuel generalizing pc stack with
  | zero =>
    unfold runBlock
    simp only [List.length_map]
    split
    · rfl
    · split <;> rfl
  | succ fuel ih =>
    unfold runBlock
    simp only [List.length_map]
    split
    · rfl
    · split
      · rfl
      · cases hd : decodeWordOpAt code pc with
        | none => simp
        | some decoded =>
          rcases decoded with ⟨op, width⟩
          simp only [bind, Option.bind, stepOp_map]
          cases hs : stepOp expressions stack op with
          | none => simp
          | some next =>
            simp only [Option.map_some]
            exact ih (pc + width) next

/-! ## Canonical Solidity Word-Projection Source Semantics & Lowering -/

def validParamName (s : String) : Bool :=
  let cs := s.toList
  match cs with
  | [] => false
  | c0 :: _ =>
    cs.length ≤ 64 &&
    (c0.isAlpha || c0 == '_') &&
    cs.all (fun c => c.isAlphanum || c == '_')

/-- Direct operational semantics of a raw Solidity unchecked word-DAG node:
`shl` and `shr` follow Solidity's `(value, shift)` operand order (`value <<< shift`,
`value >>> shift`), whereas EVM `SHL`/`SHR` pop `(shift, value)`. Rejects any
undeclared input parameter or unsupported source operation. -/
def stepSourceNode (parameters : List String) (locals : String → Word)
    (values : List Word) : Node → Option Word
  | .literal n => some (BitVec.ofNat 256 n)
  | .input name =>
    if name ∈ parameters then some (locals name) else none
  | .unary .bitnot arg => do
    return Unary.eval .bitnot (← values[arg]?)
  | .binary op left right => do
    let l ← values[left]?
    let r ← values[right]?
    match op with
    | .add => some (Binary.eval .add l r)
    | .sub => some (Binary.eval .sub l r)
    | .mul => some (Binary.eval .mul l r)
    | .and => some (Binary.eval .and l r)
    | .or => some (Binary.eval .or l r)
    | .xor => some (Binary.eval .xor l r)
    | .shl => some (Binary.eval .shl r l)
    | .shr => some (Binary.eval .shr r l)
    | _ => none
  | _ => none

def runSourceNodes (parameters : List String) (locals : String → Word) :
    List Node → List Word → Option (List Word)
  | [], values => some values
  | node :: rest, values => do
    let v ← stepSourceNode parameters locals values node
    runSourceNodes parameters locals rest (values ++ [v])

/-- Evaluate a raw Solidity word-DAG request directly under Solidity operand order,
enforcing parameter count (`≤ 16`), identifier validity, and parameter uniqueness. -/
def evalSource (parameters : List String) (nodes : List Node) (root : Nat)
    (locals : String → Word) : Option Word :=
  if parameters.length ≤ 16 ∧ parameters.all validParamName = true ∧ parameters.Nodup then do
    let values ← runSourceNodes parameters locals nodes []
    values[root]?
  else none

/-- Source node lowering matching `src/compiler_word_export.zig`:
validates input membership in `parameters`, rejects unsupported source operations
even in unreachable nodes, and swaps `(value, shift)` to EVM `(shift, value)` for
`shl` and `shr`. -/
def lowerSourceNode (parameters : List String) : Node → Option Node
  | .literal n => some (.literal n)
  | .input name => if name ∈ parameters then some (.input name) else none
  | .unary .bitnot a => some (.unary .bitnot a)
  | .binary op l r =>
    match op with
    | .add | .sub | .mul | .and | .or | .xor => some (.binary op l r)
    | .shl | .shr => some (.binary op r l)
    | _ => none
  | _ => none

/-- Lower a full Solidity word-DAG request, enforcing parameter count (`≤ 16`),
identifier syntax, and parameter uniqueness matching `src/compiler_word_export.zig`. -/
def lowerSourceNodes (parameters : List String) (nodes : List Node) : Option (List Node) :=
  if parameters.length ≤ 16 ∧ parameters.all validParamName = true ∧ parameters.Nodup then
    nodes.mapM (lowerSourceNode parameters)
  else none

private theorem lowerSourceNode_step (parameters : List String) (ctx : Context)
    (locals : String → Word) (values : List Word) (raw lowered : Node)
    (hlow : lowerSourceNode parameters raw = some lowered) :
    lowered.run (words ctx locals) values = stepSourceNode parameters locals values raw := by
  cases raw with
  | literal n =>
    simp [lowerSourceNode] at hlow
    subst hlow
    rfl
  | input name =>
    simp only [lowerSourceNode] at hlow
    split at hlow
    · rename_i hmem
      simp only [Option.some.injEq] at hlow
      subst hlow
      simp [Node.run, words, stepSourceNode, hmem]
    · cases hlow
  | nullary _ =>
    cases hlow
  | unary op arg =>
    cases op <;> simp [lowerSourceNode] at hlow
    subst hlow
    simp [Node.run, words, stepSourceNode]
  | binary op l r =>
    cases op <;> simp [lowerSourceNode] at hlow <;> subst hlow
    all_goals
      cases hl : values[l]? <;> cases hr : values[r]? <;>
        simp [Node.run, words, stepSourceNode, hl, hr]
  | ternary _ _ _ _ =>
    cases hlow

private theorem lowerSourceNodes_run (parameters : List String) (ctx : Context)
    (locals : String → Word) (raw lowered : List Node) (values : List Word)
    (hmap : raw.mapM (lowerSourceNode parameters) = some lowered) :
    run (words ctx locals) lowered values = runSourceNodes parameters locals raw values := by
  induction raw generalizing lowered values with
  | nil =>
    simp at hmap
    subst hmap
    rfl
  | cons hd tl ih =>
    simp only [List.mapM_cons, bind, Option.bind] at hmap
    cases hhd : lowerSourceNode parameters hd with
    | none => simp [hhd] at hmap
    | some lhd =>
      simp only [hhd] at hmap
      cases htl : tl.mapM (lowerSourceNode parameters) with
      | none => simp [htl] at hmap
      | some ltl =>
        simp only [htl, pure, Option.some.injEq] at hmap
        subst hmap
        simp only [run, runSourceNodes, lowerSourceNode_step parameters ctx locals values hd lhd hhd]
        cases stepSourceNode parameters locals values hd with
        | none => rfl
        | some v => exact ih ltl (values ++ [v]) htl

/-- Soundness of Solidity-to-EVM word-DAG source lowering: whenever `lowerSourceNodes`
and `expand` accept `(parameters, rawNodes, root)`, evaluating the expanded Yul/EVM
`Expression` agrees identically with direct Solidity `evalSource` (including shift
operand-order inversion and parameter bounds/uniqueness). -/
theorem lowerSourceNodes_sound (parameters : List String) (rawNodes loweredNodes : List Node)
    (root : Nat) (source : Expression) (ctx : Context) (locals : String → Word)
    (hlow : lowerSourceNodes parameters rawNodes = some loweredNodes)
    (hexp : expand loweredNodes root = some source) :
    evalSource parameters rawNodes root locals = some (evalExpr ctx locals source) := by
  unfold lowerSourceNodes at hlow
  split at hlow
  · rename_i hparams
    have hrun := lowerSourceNodes_run parameters ctx locals rawNodes loweredNodes [] hlow
    have heval := evaluate_expand loweredNodes root ctx locals
    rw [hexp] at heval
    simp only [Option.map_some] at heval
    unfold evalSource
    rw [if_pos hparams]
    unfold evaluate at heval
    rw [← hrun]
    exact heval
  · cases hlow

/-! ## Word-Block Bytecode Validation & EVM Machine Bridge -/

def validate (fuel : Nat) (code : List UInt8) (parameters : List String)
    (source : Expression) : Bool :=
  parameters.length ≤ 16 &&
  parameters.Nodup &&
  !code.isEmpty &&
  code.length ≤ 4096 &&
  match runBlock expressions code code.length 0 (parameters.map Expression.variable) with
  | some (result :: frame) =>
    equivalent fuel source result && decide (frame = parameters.map Expression.variable)
  | _ => false

def execute (code : List UInt8) (ctx : Context) (stack : List Word) : Option (List Word) :=
  runBlock (words ctx (fun _ => 0#256)) code code.length 0 stack

theorem runBlock_words_irrel_locals (code : List UInt8) (fuel pc : Nat) (stack : List Word)
    (ctx : Context) (l1 l2 : String → Word) :
    runBlock (words ctx l1) code fuel pc stack = runBlock (words ctx l2) code fuel pc stack := by
  induction fuel generalizing pc stack with
  | zero => rfl
  | succ fuel ih =>
    unfold runBlock
    split
    · rfl
    · split
      · rfl
      · cases hd : decodeWordOpAt code pc with
        | none => rfl
        | some decoded =>
          rcases decoded with ⟨op, width⟩
          have hstep : stepOp (words ctx l1) stack op = stepOp (words ctx l2) stack op := by
            rw [stepOp_words_eq_evalStack, stepOp_words_eq_evalStack]
          simp only [bind, Option.bind, hstep]
          cases stepOp (words ctx l2) stack op with
          | none => rfl
          | some next => exact ih (pc + width) next

/-- Any accepted `runBlock` execution steps faithfully in `Contract.Evm.run`
when followed by `0x00` (`STOP`), halting cleanly with `.returned []`, identical
cost = sentry (`needed = used`, since no `SSTORE` executes), and final stack `out`. -/
theorem runBlock_evm (code : List UInt8) (fuel pc : Nat) (input : Input)
    (env : Environment) (s : State) (out : List Word)
    (hsp : s.machine.pc = pc)
    (hrun : runBlock (words env.ctx (fun _ => 0#256)) code fuel pc s.machine.stack = some out) :
    ∃ cost, Contract.Evm.run (code ++ [0x00]) input env (fuel + 1) s =
      .finished cost cost ⟨.returned [], { s with machine := { s.machine with pc := code.length, stack := out } }⟩ := by
  induction fuel generalizing pc s with
  | zero =>
    unfold runBlock at hrun
    split at hrun
    · cases hrun
    · split at hrun
      · rename_i hpc
        simp only [Option.some.injEq] at hrun
        subst hrun
        refine ⟨0, ?_⟩
        unfold Contract.Evm.run Guarded.run Contract.Evm.step
        have hstop : ((code ++ [0x00])[s.machine.pc]?).getD 0 = 0 := by
          rw [hsp, hpc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
          rfl
        have hnone : decodeWordOp (code ++ [0x00]) s.machine.pc 0 = none := rfl
        simp only [hstop, hnone, UInt8.toNat_zero]
        have hs : { s with machine := { s.machine with pc := code.length, stack := s.machine.stack } } = s := by
          cases s with | mk m st wm rf =>
          cases m; simp at hsp hpc; subst hsp; subst hpc; rfl
        rw [hs]
      · cases hrun
  | succ fuel ih =>
    unfold runBlock at hrun
    split at hrun
    · cases hrun
    · split at hrun
      · rename_i hpc
        simp only [Option.some.injEq] at hrun
        subst hrun
        refine ⟨0, ?_⟩
        unfold Contract.Evm.run Guarded.run Contract.Evm.step
        have hstop : ((code ++ [0x00])[s.machine.pc]?).getD 0 = 0 := by
          rw [hsp, hpc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
          rfl
        have hnone : decodeWordOp (code ++ [0x00]) s.machine.pc 0 = none := rfl
        simp only [hstop, hnone, UInt8.toNat_zero]
        have hs : { s with machine := { s.machine with pc := code.length, stack := s.machine.stack } } = s := by
          cases s with | mk m st wm rf =>
          cases m; simp at hsp hpc; subst hsp; subst hpc; rfl
        rw [hs]
      · cases hd : decodeWordOpAt code pc with
        | none => simp [hd] at hrun
        | some decoded =>
          rcases decoded with ⟨op, width⟩
          simp only [hd, bind, Option.bind] at hrun
          cases hop : stepOp (words env.ctx (fun _ => 0#256)) s.machine.stack op with
          | none => simp [hop] at hrun
          | some nextStack =>
            simp only [hop] at hrun
            have heval : op.evalStack env.ctx s.machine.stack = some nextStack := by
              rwa [← stepOp_words_eq_evalStack env.ctx (fun _ => 0#256)]
            have hstep := decodeWordOpAt_step_append code [0x00] pc op width input env s nextStack hsp hd heval
            let c1 := op.gasCost s.machine.stack
            let s' : State := { s with machine := { s.machine with pc := pc + width, stack := nextStack } }
            obtain ⟨c2, hrest⟩ := ih (pc + width) s' rfl hrun
            refine ⟨c1 + c2, ?_⟩
            rw [Contract.Evm.run, Guarded.run, hstep]
            change (Contract.Evm.run (code ++ [0x00]) input env (fuel + 1) s').charge c1 0 = _
            rw [hrest]
            simp only [Guarded.Trace.charge, Nat.zero_max]
            rfl

/-- Master soundness theorem for straight-line word blocks:
if `validate fuel code parameters source = true`, then for every execution
environment `env`, input `input`, initial state `s` starting at `pc = 0` with
`s.machine.stack = parameters.map locals`, and local assignment `locals`:
1. Abstract word execution returns `evalExpr env.ctx locals source :: parameters.map locals`.
2. Real `Contract.Evm` execution on `code ++ [0x00]` finishes cleanly with exact
   cost `cost`, returning `evalExpr env.ctx locals source :: parameters.map locals`.
3. `Contract.Evm.runMetered` matches for every gas budget `gas`. -/
theorem validate_sound (fuel : Nat) (code : List UInt8) (parameters : List String)
    (source : Expression) (accepted : validate fuel code parameters source = true)
    (input : Input) (env : Environment) (locals : String → Word) (s : State)
    (hpc : s.machine.pc = 0) (hstack : s.machine.stack = parameters.map locals) :
    let expectedStack := evalExpr env.ctx locals source :: parameters.map locals
    execute code env.ctx (parameters.map locals) = some expectedStack ∧
    ∃ cost,
      Contract.Evm.run (code ++ [0x00]) input env (code.length + 1) s =
        .finished cost cost ⟨.returned [], { s with machine := { s.machine with pc := code.length, stack := expectedStack } }⟩ ∧
      ∀ gas, Contract.Evm.runMetered (code ++ [0x00]) input env (code.length + 1) gas s =
        if cost ≤ gas then
          .finished (gas - cost) ⟨.returned [], { s with machine := { s.machine with pc := code.length, stack := expectedStack } }⟩
        else .exceptional := by
  unfold validate at accepted
  simp only [Bool.and_eq_true, decide_eq_true_eq] at accepted
  rcases accepted with ⟨⟨⟨_, _⟩, _⟩, hblk⟩
  cases h : runBlock expressions code code.length 0 (parameters.map Expression.variable) with
  | none => simp [h] at hblk
  | some resStack =>
    cases resStack with
    | nil => simp [h] at hblk
    | cons result frame =>
      simp only [h, Bool.and_eq_true, decide_eq_true_eq] at hblk
      rcases hblk with ⟨heq, hframe⟩
      have same := equivalent_sound fuel source result heq env.ctx locals
      have mapped := runBlock_map code code.length 0 (parameters.map Expression.variable) env.ctx locals
      rw [h] at mapped
      simp only [Option.map_some, List.map_cons, hframe, List.map_map] at mapped
      have hmap_in : List.map (evalExpr env.ctx locals ∘ Expression.variable) parameters = parameters.map locals := by
        apply List.map_congr_left; intro _ _; rfl
      rw [hmap_in] at mapped
      have hirrel := runBlock_words_irrel_locals code code.length 0 (parameters.map locals) env.ctx locals (fun _ => 0#256)
      have hexec : execute code env.ctx (parameters.map locals) =
          some (evalExpr env.ctx locals source :: parameters.map locals) := by
        unfold execute
        rw [← hirrel, mapped]
        simp only [evalExpr, same]
      refine ⟨hexec, ?_⟩
      have hsrun : runBlock (words env.ctx (fun _ => 0#256)) code code.length 0 s.machine.stack =
          some (evalExpr env.ctx locals source :: parameters.map locals) := by
        rw [hstack]; exact hexec
      obtain ⟨cost, hevm⟩ := runBlock_evm code code.length 0 input env s
        (evalExpr env.ctx locals source :: parameters.map locals) hpc hsrun
      refine ⟨cost, hevm, ?_⟩
      intro gas
      exact Guarded.metered_of_run (Contract.Evm.step (code ++ [0x00]) input env)
        (code.length + 1) s cost cost _ gas hevm

/-- End-to-end Solidity word-request validation theorem: combining `lowerSourceNodes`,
`expand`, and `WordBlock.validate` certifies that executing `code ++ [0x00]` on
`Contract.Evm.run` computes the exact Solidity `evalSource` result on top of the
preserved caller parameter frame. -/
theorem validateSource_sound (fuel : Nat) (code : List UInt8) (parameters : List String)
    (rawNodes loweredNodes : List Node) (root : Nat) (source : Expression)
    (hlow : lowerSourceNodes parameters rawNodes = some loweredNodes)
    (hexp : expand loweredNodes root = some source)
    (hval : validate fuel code parameters source = true)
    (input : Input) (env : Environment) (locals : String → Word) (s : State)
    (hpc : s.machine.pc = 0) (hstack : s.machine.stack = parameters.map locals) :
    ∃ result cost,
      evalSource parameters rawNodes root locals = some result ∧
      Contract.Evm.run (code ++ [0x00]) input env (code.length + 1) s =
        .finished cost cost
          ⟨.returned [], { s with machine := { s.machine with pc := code.length, stack := result :: parameters.map locals } }⟩ := by
  have hsrc := lowerSourceNodes_sound parameters rawNodes loweredNodes root source env.ctx locals hlow hexp
  obtain ⟨_, cost, hevm, _⟩ := validate_sound fuel code parameters source hval input env locals s hpc hstack
  exact ⟨evalExpr env.ctx locals source, cost, hsrc, hevm⟩

#audit_contract_proof Compiler.Validation.WordBlock.lowerSourceNodes_sound
#audit_contract_proof Compiler.Validation.WordBlock.validate_sound
#audit_contract_proof Compiler.Validation.WordBlock.validateSource_sound

end Compiler.Validation.WordBlock
