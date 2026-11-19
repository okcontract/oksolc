/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.Builder
import Compiler.Algebraic.Rules

/-! Typed data for the admitted, specialized Zig fragment. There are no arbitrary
Lean-function escape hatches in expressions. Lexical variables carry a type and
scope proof. Finite enum branches are syntax families, not semantic callbacks.
Parsing and specialization into this language remain a separate trust boundary. -/
namespace Compiler.Extraction.IR
open Compiler.Algebraic Contract.Yul

inductive Ty where
  | boolean | word | opcode | node | guard | stage | replacement | rule | facts
  | optional (element : Ty) | array (element : Ty)

abbrev Ty.Value : Ty → Type
  | .boolean => Bool
  | .word => Word
  | .opcode => BitVec 8
  | .node => NodeId
  | .guard => Guard
  | .stage => Stage
  | .replacement => Replacement
  | .rule => Rule
  | .facts => Facts
  | .optional t => Option t.Value
  | .array t => List t.Value

inductive Var : List Ty → Ty → Type where
  | here : Var (t :: Γ) t
  | there : Var Γ t → Var (s :: Γ) t

abbrev Env (Γ : List Ty) := {t : Ty} → Var Γ t → t.Value

def Env.cons (value : t.Value) (env : Env Γ) : Env (t :: Γ)
  | _, .here => value
  | _, .there index => env index

def Env.empty : Env [] := fun index => nomatch index

inductive EqType : Ty → Type where
  | boolean : EqType .boolean
  | word : EqType .word
  | opcode : EqType .opcode
  | node : EqType .node
  | guard : EqType .guard
  | stage : EqType .stage
  | replacement : EqType .replacement
  | optional : EqType t → EqType (.optional t)

def EqType.equal : EqType t → t.Value → t.Value → Bool
  | .boolean, a, b => a == b
  | .word, a, b => a == b
  | .opcode, a, b => a == b
  | .node, a, b => a == b
  | .guard, a, b => a == b
  | .stage, a, b => a == b
  | .replacement, a, b => a == b
  | .optional _, none, none => true
  | .optional eq, some a, some b => eq.equal a b
  | .optional _, _, _ => false

inductive Expr : List Ty → Ty → Type where
  | var : Var Γ t → Expr Γ t
  | boolean : Bool → Expr Γ .boolean
  | word : Word → Expr Γ .word
  | opcode : BitVec 8 → Expr Γ .opcode
  | node : NodeId → Expr Γ .node
  | guard : Guard → Expr Γ .guard
  | stage : Stage → Expr Γ .stage
  | replacement : Replacement → Expr Γ .replacement
  | none : Expr Γ (.optional t)
  | some : Expr Γ t → Expr Γ (.optional t)
  | nil : Expr Γ (.array t)
  | cons : Expr Γ t → Expr Γ (.array t) → Expr Γ (.array t)
  | eq : EqType t → Expr Γ t → Expr Γ t → Expr Γ .boolean
  | not : Expr Γ .boolean → Expr Γ .boolean
  | and : Expr Γ .boolean → Expr Γ .boolean → Expr Γ .boolean
  | or : Expr Γ .boolean → Expr Γ .boolean → Expr Γ .boolean
  | ite : Expr Γ .boolean → Expr Γ t → Expr Γ t → Expr Γ t
  | letE : Expr Γ a → Expr (a :: Γ) b → Expr Γ b
  | left : Expr Γ .facts → Expr Γ (.optional .word)
  | right : Expr Γ .facts → Expr Γ (.optional .word)
  | equal : Expr Γ .facts → Expr Γ .boolean
  | ruleOpcode : Expr Γ .rule → Expr Γ .opcode
  | ruleGuard : Expr Γ .rule → Expr Γ .guard
  | ruleReplacement : Expr Γ .rule → Expr Γ .replacement
  | matches : Expr Γ .guard → Expr Γ .facts → Expr Γ .boolean
  | guardSwitch : Expr Γ .guard → (Guard → Expr Γ t) → Expr Γ t
  | replacementSwitch : Expr Γ .replacement → (Replacement → Expr Γ t) → Expr Γ t
  | stageSwitch : Expr Γ .stage → (Stage → Expr Γ t) → Expr Γ t

def Expr.eval (callMatcher : Guard → Facts → Bool) : Expr Γ t → Env Γ → t.Value
  | .var index, env => env index
  | .boolean value, _ => value
  | .word value, _ => value
  | .opcode value, _ => value
  | .node value, _ => value
  | .guard value, _ => value
  | .stage value, _ => value
  | .replacement value, _ => value
  | .none, _ => Option.none
  | .some value, env => Option.some (value.eval callMatcher env)
  | .nil, _ => []
  | .cons head tail, env => head.eval callMatcher env :: tail.eval callMatcher env
  | .eq kind a b, env => kind.equal (a.eval callMatcher env) (b.eval callMatcher env)
  | .not value, env => !(value.eval callMatcher env)
  | .and a b, env => if a.eval callMatcher env then b.eval callMatcher env else false
  | .or a b, env => if a.eval callMatcher env then true else b.eval callMatcher env
  | .ite condition yes no, env =>
    if condition.eval callMatcher env then yes.eval callMatcher env else no.eval callMatcher env
  | .letE value body, env => body.eval callMatcher (env.cons (value.eval callMatcher env))
  | .left facts, env => (facts.eval callMatcher env).left
  | .right facts, env => (facts.eval callMatcher env).right
  | .equal facts, env => (facts.eval callMatcher env).equal
  | .ruleOpcode rule, env => productionOpcode (rule.eval callMatcher env).op
  | .ruleGuard rule, env => (rule.eval callMatcher env).guard
  | .ruleReplacement rule, env => (rule.eval callMatcher env).replacement
  | .matches condition facts, env => callMatcher (condition.eval callMatcher env) (facts.eval callMatcher env)
  | .guardSwitch subject arms, env => (arms (subject.eval callMatcher env)).eval callMatcher env
  | .replacementSwitch subject arms, env => (arms (subject.eval callMatcher env)).eval callMatcher env
  | .stageSwitch subject arms, env => (arms (subject.eval callMatcher env)).eval callMatcher env

/-- Fallthrough and `return null` are different outcomes. -/
inductive Flow where
  | next
  | returned (value : Option Replacement)
  deriving DecidableEq, Repr

def each (values : List α) (body : α → Flow) : Flow :=
  match values with
  | [] => .next
  | value :: rest => match body value with
    | .next => each rest body
    | .returned result => .returned result

inductive Block : List Ty → Type where
  | done : Block Γ
  | ret : Expr Γ (.optional .replacement) → Block Γ
  | letE : Expr Γ t → Block (t :: Γ) → Block Γ
  | branch : Expr Γ .boolean → Block Γ → Block Γ → Block Γ → Block Γ
  | loop : Expr Γ (.array .rule) → Block (.rule :: Γ) → Block Γ → Block Γ

def Flow.thenDo (flow : Flow) (next : Unit → Flow) : Flow :=
  match flow with
  | .next => next ()
  | .returned result => .returned result

def Block.eval (callMatcher : Guard → Facts → Bool) : Block Γ → Env Γ → Flow
  | .done, _ => .next
  | .ret value, env => .returned (value.eval callMatcher env)
  | .letE value body, env => body.eval callMatcher (env.cons (value.eval callMatcher env))
  | .branch condition yes no rest, env =>
    (if condition.eval callMatcher env then yes.eval callMatcher env else no.eval callMatcher env).thenDo
      (fun _ => rest.eval callMatcher env)
  | .loop values body rest, env =>
    (each (values.eval callMatcher env) (fun rule => body.eval callMatcher (env.cons rule))).thenDo
      (fun _ => rest.eval callMatcher env)

/-- Construction has only the admitted callbacks. The debug value is an opaque
borrow passed unchanged; it cannot be synthesized or inspected by this IR. -/
inductive Build : List Ty → Type where
  | ret : Expr Γ .node → Build Γ
  | constant : Expr Γ .word → Build Γ
  | operation : BuildOp → Expr Γ (.array .node) → Build Γ
  | bind : Build Γ → Build (.node :: Γ) → Build Γ
  | branch : Expr Γ .boolean → Build Γ → Build Γ → Build Γ
  | switch : Expr Γ .replacement → (Replacement → Build Γ) → Build Γ

def Build.eval {m : Type → Type} [Monad m] (classes : Builder m Debug) (debug : Debug)
    (callMatcher : Guard → Facts → Bool) : Build Γ → Env Γ → m NodeId
  | .ret value, env => pure (value.eval callMatcher env)
  | .constant value, env => classes.makeConstant (value.eval callMatcher env) debug
  | .operation op ids, env => classes.makeOperation op (ids.eval callMatcher env) debug
  | .bind action next, env => action.eval classes debug callMatcher env >>= fun id =>
    next.eval classes debug callMatcher (env.cons id)
  | .branch condition yes no, env =>
    if condition.eval callMatcher env then yes.eval classes debug callMatcher env
    else no.eval classes debug callMatcher env
  | .switch subject arms, env => (arms (subject.eval callMatcher env)).eval classes debug callMatcher env

theorem each_return_null (rest : List α) (body : α → Flow) (value : α)
    (returned : body value = .returned none) :
    each (value :: rest) body = .returned none := by simp [each, returned]

end Compiler.Extraction.IR
