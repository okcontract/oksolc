/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.CacheIR

namespace Compiler.Algebraic
open Compiler.Extraction.Cache Contract.Yul

/-- The validity and bind rules needed by construction. Instances retain their
own states and failure policies; no projection to a logical heap is required. -/
structure BuilderLogic (m : Type → Type) [Monad m] (State : Type) where
  read : State → Read
  valid : State → Prop
  safe : {α : Type} → m α → State → (α → State → Prop) → Prop
  pure : ∀ {α} before (value : α) post, valid before → post value before → safe (pure value) before post
  bind : ∀ {α β} before (first : m α) (next : α → m β) middle post,
    safe first before middle →
    (∀ value after, valid after → Preserves read before after → middle value after → safe (next value) after post) →
    safe (first >>= next) before post

/-- Only the caller's supplied debug value and valid reached states are needed. -/
structure BuilderRules {m : Type → Type} [Monad m] {State Debug : Type}
    (logic : BuilderLogic m State) (builder : Builder m Debug) (debug : Debug) : Prop where
  constant : ∀ value before, logic.valid before →
    logic.safe (builder.makeConstant value debug) before (fun id after => logic.read after id = some value)
  operation : ∀ op ids values value before, logic.valid before →
    readArguments (logic.read before) ids = some values → op.eval values = some value →
    logic.safe (builder.makeOperation op ids debug) before (fun id after => logic.read after id = some value)

namespace BuilderRules
variable {m : Type → Type} [Monad m] {State Debug : Type}
    {logic : BuilderLogic m State} {builder : Builder m Debug} {debug : Debug}
    (correct : BuilderRules logic builder debug)
include correct

theorem bitnot (before : State) (valid : logic.valid before) (id : NodeId) (value : Word)
    (actual : logic.read before id = some value) :
    logic.safe (builder.makeOperation .NOT [id] debug) before
      (fun result after => logic.read after result = some (Unary.bitnot.eval value)) :=
  correct.operation .NOT [id] [value] _ before valid (by simp [readArguments, actual]) rfl

theorem sub (before : State) (valid : logic.valid before) (left right : NodeId) (a b : Word)
    (lhs : logic.read before left = some a) (rhs : logic.read before right = some b) :
    logic.safe (builder.makeOperation .SUB [left, right] debug) before
      (fun result after => logic.read after result = some (Binary.sub.eval a b)) :=
  correct.operation .SUB [left, right] [a, b] _ before valid (by simp [readArguments, lhs, rhs]) rfl

theorem iszero (before : State) (valid : logic.valid before) (id : NodeId) (value : Word)
    (actual : logic.read before id = some value) :
    logic.safe (builder.makeOperation .ISZERO [id] debug) before
      (fun result after => logic.read after result = some (Unary.iszero.eval value)) :=
  correct.operation .ISZERO [id] [value] _ before valid (by simp [readArguments, actual]) rfl

/-- One replacement proof for logical and native construction. Each sequential
child receives the actual reached state, including newly returned IDs and the
preserved original operands. The instance determines ordinary failure duties. -/
theorem replacement (before : State) (valid : logic.valid before)
    (replacement : Replacement) (left right : NodeId) (a b : Word)
    (lhs : logic.read before left = some a) (rhs : logic.read before right = some b) :
    logic.safe (replacement.build builder left right debug) before
      (fun id after => logic.read after id = some (replacement.eval a b)) := by
  cases replacement <;> simp only [Replacement.build, Replacement.eval]
  · exact logic.pure before left _ valid lhs
  · exact logic.pure before right _ valid rhs
  · exact correct.constant _ before valid
  · exact correct.constant _ before valid
  · exact correct.constant _ before valid
  · exact correct.bitnot before valid right b rhs
  · apply logic.bind before _ _ (fun id state => logic.read state id = some 0) _ (correct.constant 0 before valid)
    intro zero middle validMiddle stable value
    exact correct.sub middle validMiddle zero left 0 a value (stable left a lhs)
  · apply logic.bind before _ _ (fun id state => logic.read state id = some 0) _ (correct.constant 0 before valid)
    intro zero middle validMiddle stable value
    exact correct.sub middle validMiddle zero right 0 b value (stable right b rhs)
  · exact correct.iszero before valid left a lhs
  · exact correct.iszero before valid right b rhs
  · apply logic.bind before _ _ (fun id state => logic.read state id = some (Unary.iszero.eval a)) _
      (correct.iszero before valid left a lhs)
    intro first middle validMiddle _ value
    exact correct.iszero middle validMiddle first _ value
  · apply logic.bind before _ _ (fun id state => logic.read state id = some (Unary.iszero.eval b)) _
      (correct.iszero before valid right b rhs)
    intro first middle validMiddle _ value
    exact correct.iszero middle validMiddle first _ value

end BuilderRules
end Compiler.Algebraic
