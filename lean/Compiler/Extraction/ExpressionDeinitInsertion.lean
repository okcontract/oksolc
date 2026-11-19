/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionDeinitProofs
import Compiler.Extraction.InsertionExecution

namespace Compiler.Extraction.ExpressionDeinit
open Compiler.Extraction.Storage Compiler.Extraction.Memory
open Compiler.Extraction.Memory.Arguments.Normalization
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul

/-- Replace insertion's last-representative destructor with the source-bound
operation. Descriptor lookup and other insertion operations remain explicit
compiler obligations. Reuse of an invalidated descriptor is rejected. -/
def insertionWith (items : Operations σ ε) (external : External σ) (allocator : Nat)
    (last : Storage.State → State σ → Descriptor) (rest : Storage.Operations (State σ) (Fault ε)) :
    Storage.Operations (State σ) (Fault ε) :=
  { rest with release := fun action ownership before => match action with
      | .lastValue => execute items external allocator (last ownership before) expressionDeinitCode before
      | _ => rest.release action ownership before }

def insertionOperations (items : Items σ ε) (external : External σ) (allocator : Nat)
    (last : Storage.State → State σ → Descriptor) (rest : Storage.Operations (State σ) (Fault ε)) :
    Storage.Operations (State σ) (Fault ε) :=
  insertionWith items.operations external allocator last rest

theorem last_value_memory_equation (items : Operations σ ε) (external : External σ) (allocator : Nat)
    (last : Storage.State → State σ → Descriptor) (rest : Storage.Operations (State σ) (Fault ε))
    (ownership : Storage.State) (before : State σ) :
    Storage.Release.lastValue.execute (insertionWith items external allocator last rest) ownership before =
      let (result, reached) := execute items external allocator (last ownership before) expressionDeinitCode before
      ((result, match result with | .error _ => ownership | .ok () => Storage.Release.lastValue.run ownership), reached) := by
  cases called : execute items external allocator (last ownership before) expressionDeinitCode before with
  | mk result reached => cases result with
    | error fault => simp only [Storage.Release.execute, insertionWith, called]
    | ok returned => cases returned; simp only [Storage.Release.execute, insertionWith, called]

theorem last_value_equation (items : Items σ ε) (external : External σ) (allocator : Nat)
    (last : Storage.State → State σ → Descriptor) (rest : Storage.Operations (State σ) (Fault ε))
    (ownership : Storage.State) (before : State σ) :
    Storage.Release.lastValue.execute (insertionOperations items external allocator last rest) ownership before =
      let (result, reached) := execute items.operations external allocator (last ownership before) expressionDeinitCode before
      ((result, match result with | .error _ => ownership | .ok () => Storage.Release.lastValue.run ownership), reached) := by
  exact last_value_memory_equation items.operations external allocator last rest ownership before

/-- The exact callback used by insertion has checked argument lifetime/frame
behavior. It requires the reached descriptor to be live; establishing that
from all preceding native insertion operations is still an open obligation. -/
theorem last_value_preserved (items : Items σ ε) (external : External σ) (allocator : Nat)
    (last : Storage.State → State σ → Descriptor) (rest : Storage.Operations (State σ) (Fault ε))
    (ownership : Storage.State) (before : State σ) (ready : before.invalidated = false)
    (valid : Valid before.memory) (live : SliceValid allocator before.memory.heap (last ownership before).arguments) :
    let executed := Storage.Release.lastValue.execute (insertionOperations items external allocator last rest) ownership before
    Post (last ownership before) before.memory (executed.1.1, executed.2) := by
  rcases before with ⟨memory, invalidated⟩
  cases ready
  have checked := run_verified items external allocator (last ownership ⟨memory, false⟩) memory valid live
  rw [last_value_equation]
  cases executed : execute items.operations external allocator (last ownership ⟨memory, false⟩) expressionDeinitCode ⟨memory, false⟩ with
  | mk result reached =>
    change Post _ memory (run items external allocator (last ownership ⟨memory, false⟩) memory) at checked
    rw [show run items external allocator (last ownership ⟨memory, false⟩) memory = (result, reached) from executed] at checked
    exact checked

/-- The same complete source insertion execution preserves word meaning and
uses the checked physical argument destructor on rollback. The second conjunct
states the reached-state precondition each rollback must establish; it does
not assert that arbitrary native insertion callbacks establish it. -/
theorem insertion_verified (meaning : Meaning) (cells : List Cell) (table : Table)
    (cell : Cell) (key : Key) (deterministic : Bool) (items : Items σ ε) (external : External σ)
    (allocator : Nat) (last : Storage.State → State σ → Descriptor)
    (rest : Storage.Operations (State σ) (Fault ε)) (before : State σ) (outcome : Option Storage.Outcome)
    (valid : Interner.Invariant meaning (Interner.observedHeap cells table))
    (binding : keyCode.run cell.item cell.arguments cell.sequence = some key)
    (denotation : key.eval meaning (readValue cells) = some cell.value)
    (completed : (insertProgram.execute ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩
      (insertionOperations items external allocator last rest) {} before).1.1 = .ok outcome) :
    (let executed := insertProgram.execute ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩
        (insertionOperations items external allocator last rest) {} before;
      SafeResult deterministic (outcome, executed.1.2) ∧
        Interner.Invariant meaning (Interner.InsertionExecution.project cells table cell key executed.1.2) ∧
        Interner.Stable (Interner.observedHeap cells table) (Interner.InsertionExecution.project cells table cell key executed.1.2) ∧
        match Interner.insertionOutcome cells outcome with
        | .error _ => True
        | .ok id => (Interner.InsertionExecution.project cells table cell key executed.1.2).read id = some cell.value) ∧
    (∀ ownership reached, reached.invalidated = false → Valid reached.memory →
      SliceValid allocator reached.memory.heap (last ownership reached).arguments →
      let executed := Storage.Release.lastValue.execute (insertionOperations items external allocator last rest) ownership reached
      Post (last ownership reached) reached.memory (executed.1.1, executed.2)) :=
  ⟨Interner.InsertionExecution.verified meaning cells table cell key deterministic
      (insertionOperations items external allocator last rest) before outcome valid binding denotation completed,
    last_value_preserved items external allocator last rest⟩

end Compiler.Extraction.ExpressionDeinit
