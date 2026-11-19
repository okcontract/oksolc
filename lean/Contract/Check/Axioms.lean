/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Dependency audit for honest development builds. This is not an independent
artifact certificate or protection against hostile metaprograms. Replay the
compiled modules separately with the pinned leanchecker. -/
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
