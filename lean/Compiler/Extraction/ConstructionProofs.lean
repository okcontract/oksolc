/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.Construction
import Compiler.Extraction.Graph
import Compiler.Extraction.Proofs

namespace Compiler.Algebraic
open Contract.Yul

/-- Equality for arbitrary callback effects, including state, allocation failure
and traces. Captures, debug arguments and callback order are preserved. -/
theorem zigApply_eq {m : Type → Type} [Monad m] {Debug : Type}
    (replacement : Replacement) (classes : Builder m Debug)
    (left right : NodeId) (debug : Debug) :
    zigApply replacement classes left right debug = replacement.build classes left right debug := by
  cases replacement <;> rfl

/-- Connect the extracted body to successful graph construction, with all
callback obligations and valid operand references visible in the statement. -/
theorem zigApply_sound {Heap Error Debug : Type}
    (classes : Builder (Effect Heap Error) Debug) (read : Heap → NodeId → Option Word)
    (valid : classes.Valid read) (replacement : Replacement) (before : Heap)
    (left right : NodeId) (a b : Word) (debug : Debug)
    (ha : read before left = some a) (hb : read before right = some b) :
    Ensures read (zigApply replacement classes left right debug) before (replacement.eval a b) := by
  rw [zigApply_eq]
  exact replacement_build_sound classes read valid replacement before left right a b debug ha hb

/-- Selection and construction compose at the actual extracted implementation
boundary. Fact reliability and the graph callback contract remain explicit. -/
theorem zigRewrite_sound {Heap Error Debug : Type}
    (classes : Builder (Effect Heap Error) Debug) (read : Heap → NodeId → Option Word)
    (valid : classes.Valid read) (op : Binary) (stage : Stage) (facts : Facts)
    (a b : Word) (reliable : facts.Reliable a b) (replacement : Replacement)
    (selected : zigSelect (productionOpcode op) stage facts = some replacement)
    (before : Heap) (left right : NodeId) (debug : Debug)
    (ha : read before left = some a) (hb : read before right = some b) :
    Ensures read (zigApply replacement classes left right debug) before (op.eval a b) := by
  rw [zigSelect_sound op stage facts a b reliable replacement selected]
  exact zigApply_sound classes read valid replacement before left right a b debug ha hb

end Compiler.Algebraic
