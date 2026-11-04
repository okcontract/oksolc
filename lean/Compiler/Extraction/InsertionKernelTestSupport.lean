/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Lean.Elab.Tactic.Decide

/- Closed function-containing states do not have decidable equality. Submit
an Eq.refl term to the same kernel-checked auxiliary-lemma path used by Lean
4.29's decide +kernel. No native evaluator, axiom or raised proof limit is used.
Free variables/metavariables are rejected; the kernel checks the claimed type. -/
open Lean Elab Tactic Meta in
elab "insertion_kernel_rfl" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    unless target.isAppOfArity ``Eq 3 && !target.hasFVar && !target.hasMVar do
      throwError "insertion_kernel_rfl requires a closed equality"
    let proof ← mkEqRefl target.appArg!
    let levelsInType := (collectLevelParams {} target).params
    let levels := (← Term.getLevelNames).reverse.filter levelsInType.contains
    try
      let name ← withOptions (Elab.async.set · false) (mkAuxLemma levels target proof)
      goal.assign (mkConst name (levels.map .param))
    catch reason =>
      throwError "Type mismatch: kernel reflexivity rejected the claimed equality\n{reason.toMessageData}"
  replaceMainGoal []
