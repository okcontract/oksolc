/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Axiom dependency audit for kernel-checked theorems. Verifies that a theorem
depends strictly on Lean's standard logical foundations (`propext`,
`Classical.choice`, `Quot.sound`) and zero custom axioms, `sorryAx`, or
`Lean.ofReduceBool` / `Lean.trustCompiler` shortcuts. -/
open Lean Elab Command in
elab "#audit_contract_proof " id:ident : command => do
  let name ← resolveGlobalConstNoOverload id
  let info ← getConstInfo name
  unless info matches .thmInfo _ do
    throwError "{name} is not a theorem"
  let axioms ← collectAxioms name
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in axioms do
    unless allowed.contains axiomName do
      throwError "{name} depends on disallowed axiom {axiomName}"
  logInfo m!"{name}: {info.type}\nlogical axioms: {axioms}"
