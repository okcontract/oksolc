/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerUniformModel
import Compiler.Extraction.InternerNativeDispatch

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Recursive.Uniform
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.Extraction.Nested

abbrev Domains (σ Debug : Type) := Associative.Constructors Debug (fun _ => World σ → Prop)

/-- One model family is chosen over the admitted native domains, independently
of the current row snapshot or live parent predicate. All five native calling
conventions retain their own arguments and admission requirements. -/
noncomputable def constructors (observe : World σ → Interner.Heap) (domains : Domains σ Debug)
    (children : Associative.Constructors Debug (GraphAction σ)) : Associative.Constructors Debug where
  operation := fun op ids debug => action observe (domains.operation op ids debug) (children.operation op ids debug)
  constant := fun value debug => action observe (domains.constant value debug) (children.constant value debug)
  materialize := fun id value debug => action observe (domains.materialize id value debug) (children.materialize id value debug)
  borrowedOperation := fun address op ids debug =>
    action observe (domains.borrowedOperation address op ids debug) (children.borrowedOperation address op ids debug)
  localOperation := fun op source selected repeated first debug =>
    action observe (domains.localOperation op source selected repeated first debug)
      (children.localOperation op source selected repeated first debug)

structure Agreement (observe : World σ → Interner.Heap) (domains : Domains σ Debug)
    (children : Associative.Constructors Debug (GraphAction σ)) : Prop where
  operation : ∀ op ids debug, Agrees observe (domains.operation op ids debug) (children.operation op ids debug)
  constant : ∀ value debug, Agrees observe (domains.constant value debug) (children.constant value debug)
  materialize : ∀ id value debug, Agrees observe (domains.materialize id value debug) (children.materialize id value debug)
  borrowedOperation : ∀ address op ids debug,
    Agrees observe (domains.borrowedOperation address op ids debug) (children.borrowedOperation address op ids debug)
  localOperation : ∀ op source selected repeated first debug,
    Agrees observe (domains.localOperation op source selected repeated first debug)
      (children.localOperation op source selected repeated first debug)

/-- Admission follows the dispatcher's actual source-query contract. It does
not assume projection, a model, a final result, or successful allocation. -/
structure SourceAdmission (domains : Domains σ Debug) (debug : Debug) (reads : Reads)
    (predicate : World σ → Prop) : Prop where
  operation : ∀ op ids before, predicate before → domains.operation op ids debug before
  constant : ∀ value before, predicate before → domains.constant value debug before
  materialize : ∀ id value before, predicate before → domains.materialize id value debug before
  borrowedOperation : ∀ id queried source, reads.operation id queried = .ok (some source) →
    ∀ op before, predicate before → domains.borrowedOperation source.address op source.items debug before
  localOperation : ∀ id op source, reads.operation id op = .ok (some source) → source.items.length = 2 →
    ∀ selected, selected < 2 → ∀ repeated first before, predicate before →
      domains.localOperation op source selected repeated first debug before

theorem source_projects (observe : World σ → Interner.Heap) (domains : Domains σ Debug)
    (children : Associative.Constructors Debug (GraphAction σ)) (agreement : Agreement observe domains children)
    (debug : Debug) (reads : Reads) (predicate : World σ → Prop)
    (admission : SourceAdmission domains debug reads predicate)
    (frames : (keeping predicate).SourceConstructorsAt reads debug children children) :
    (projectionAt observe predicate).SourceConstructorsAt reads debug children (constructors observe domains children) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro op ids tag
    exact projects observe _ _ _ (agreement.operation op ids debug) (admission.operation op ids) (frames.operation op ids tag)
  · intro value tag
    exact projects observe _ _ _ (agreement.constant value debug) (admission.constant value) (frames.constant value tag)
  · intro id value tag
    exact projects observe _ _ _ (agreement.materialize id value debug) (admission.materialize id value) (frames.materialize id value tag)
  · intro id queried source found op tag
    exact projects observe _ _ _ (agreement.borrowedOperation source.address op source.items debug)
      (admission.borrowedOperation id queried source found op) (frames.borrowedOperation id queried source found op tag)
  · intro id op source found shape selected bounded repeated first tag
    exact projects observe _ _ _ (agreement.localOperation op source selected repeated first debug)
      (admission.localOperation id op source found shape selected bounded repeated first)
      (frames.localOperation id op source found shape selected bounded repeated first tag)

/-- The native induction statement for an operation request, before choosing
any logical constructor. Rejection remains explicit through Ensures. -/
def RequestWords (observe : World σ → Interner.Heap) (meaning : Meaning) (request : Interner.Request)
    (admitted : World σ → Prop) (physical : GraphAction σ NodeId) : Prop :=
  ∀ before value, admitted before → Interner.Invariant meaning (observe before) →
    request.item.eval meaning (observe before).read request.arguments request.sequence = some value →
    Semantic.Ensures meaning (observe before) (physical before).1 (observe (physical before).2)
      (fun id after => after.read id = some value)

structure Words (observe : World σ → Interner.Heap) (meaning : Meaning) (domains : Domains σ Debug)
    (children : Associative.Constructors Debug (GraphAction σ)) : Prop where
  operation : ∀ op ids debug, RequestWords observe meaning (Interner.constructorCode.operationRequest op ids)
    (domains.operation op ids debug) (children.operation op ids debug)
  constant : ∀ value debug before, domains.constant value debug before → Interner.Invariant meaning (observe before) →
    Semantic.Ensures meaning (observe before) (children.constant value debug before).1 (observe (children.constant value debug before).2)
      (fun id after => after.read id = some value)
  materialize : ∀ id value debug before, domains.materialize id value debug before → Interner.Invariant meaning (observe before) →
    Semantic.Ensures meaning (observe before) (children.materialize id value debug before).1 (observe (children.materialize id value debug before).2)
      (fun id after => after.read id = some value)
  borrowedOperation : ∀ address op ids debug, RequestWords observe meaning (Interner.constructorCode.operationRequest op ids)
    (domains.borrowedOperation address op ids debug) (children.borrowedOperation address op ids debug)
  localOperation : ∀ op source selected repeated first debug,
    RequestWords observe meaning (Interner.constructorCode.operationRequest op (localArguments source selected repeated first))
      (domains.localOperation op source selected repeated first debug) (children.localOperation op source selected repeated first debug)

theorem request_safe (observe : World σ → Interner.Heap) (meaning : Meaning) (request : Interner.Request)
    (admitted : World σ → Prop) (physical : GraphAction σ NodeId)
    (words : RequestWords observe meaning request admitted physical)
    (before : Interner.Heap) (value : Word) (valid : Interner.Invariant meaning before)
    (evaluated : request.item.eval meaning before.read request.arguments request.sequence = some value) :
    Interner.Safe meaning (action observe admitted physical) before (fun id after => after.read id = some value) := by
  apply safe observe admitted physical meaning before _ valid
  intro world inside same
  exact words world value inside (same ▸ valid) (same ▸ evaluated)

theorem constructors_sound (observe : World σ → Interner.Heap) (domains : Domains σ Debug)
    (children : Associative.Constructors Debug (GraphAction σ)) (other : Meaning)
    (words : Words observe (Folding.wordMeaning other) domains children) :
    Associative.ConstructorSound other (constructors observe domains children) := by
  constructor
  · intro op ids values value debug before valid arguments evaluated
    exact request_safe observe _ _ _ _ (words.operation op.opcode ids debug) before value valid
      (word_operation_request_sound other before.read op ids values value arguments evaluated)
  · intro value debug before valid
    exact safe observe _ _ _ before _ valid (fun world inside same => words.constant value debug world inside (same ▸ valid))
  · intro id value debug before valid
    exact safe observe _ _ _ before _ valid (fun world inside same => words.materialize id value debug world inside (same ▸ valid))
  · intro address op ids values value debug before valid arguments evaluated
    exact request_safe observe _ _ _ _ (words.borrowedOperation address op.opcode ids debug) before value valid
      (word_operation_request_sound other before.read op ids values value arguments evaluated)
  · intro op source selected repeated first values value debug before valid arguments evaluated
    exact request_safe observe _ _ _ _ (words.localOperation op.opcode source selected repeated first debug) before value valid
      (word_operation_request_sound other before.read op _ values value arguments evaluated)

theorem constructors_address (observe : World σ → Interner.Heap) (domains : Domains σ Debug)
    (children : Associative.Constructors Debug (GraphAction σ)) (env : AddressMask.Environment) (other : Meaning)
    (words : Words observe (AddressMask.meaning env other) domains children) :
    AddressMask.Constructs env other (constructors observe domains children).operation := by
  intro kind debug before valid
  apply request_safe observe _ _ _ _ (words.operation kind.opcode [] debug) before (kind.value env) valid
  change (AddressMask.meaning env other).operation kind.opcode 0 [] = some (kind.value env)
  exact AddressMask.address_operation env other kind 0 []

theorem constructors_sar (observe : World σ → Interner.Heap) (domains : Domains σ Debug)
    (children : Associative.Constructors Debug (GraphAction σ)) (other : Meaning)
    (words : Words observe (ArithmeticShift.meaning other) domains children) :
    ArithmeticShift.Constructs other (constructors observe domains children).operation := by
  intro left right amount value debug before valid lhs rhs
  apply request_safe observe _ _ _ _ (words.operation ArithmeticShift.opcode [left, right] debug) before
    (ArithmeticShift.value amount value) valid
  simpa [Interner.constructorCode, Interner.ConstructorCode.operationRequest, Scalar.run, Item.eval,
    readArguments, lhs, rhs, ArithmeticShift.eval] using ArithmeticShift.operation other 0 [amount, value]

/-- Construct the single witness used by all reached row snapshots and by all
three semantic contracts. Only selected dispatch paths require native laws. -/
theorem proper {Index : Type} (observe : World σ → Interner.Heap) (domains : Domains σ Debug)
    (children : Associative.Constructors Debug (GraphAction σ)) (env : AddressMask.Environment) (other : Meaning)
    (debug : Debug) (selected : Prop) (reads : Index → Reads) (frame : Index → World σ → Prop)
    (native : selected → Agreement observe domains children ∧ Words observe (Dispatch.wordDispatchMeaning env other) domains children ∧
      ∀ index, SourceAdmission domains debug (reads index) (frame index) ∧
        (keeping (frame index)).SourceConstructorsAt (reads index) debug children children) :
    ∃ model : Associative.Constructors Debug,
      (selected → ∀ index, (projectionAt observe (frame index)).SourceConstructorsAt (reads index) debug children model) ∧
      (selected → Associative.ConstructorSound (Dispatch.wordBaseMeaning env other) model) ∧
      (selected → AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) model.operation) ∧
      (selected → ArithmeticShift.Constructs (AddressMask.addressMeaning env other) model.operation) := by
  refine ⟨constructors observe domains children, ?_, ?_, ?_, ?_⟩
  · intro chosen index
    exact source_projects observe domains children (native chosen).1 debug (reads index) (frame index)
      ((native chosen).2.2 index).1 ((native chosen).2.2 index).2
  · intro chosen
    exact constructors_sound observe domains children _ (native chosen).2.1
  · intro chosen
    exact constructors_address observe domains children env _
      (by simpa only [Dispatch.word_dispatch_address_model] using (native chosen).2.1)
  · intro chosen
    exact constructors_sar observe domains children _ (native chosen).2.1

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Recursive.Uniform
