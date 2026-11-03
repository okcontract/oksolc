/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Lean.Environment
import Lean.Util.FoldConsts
import Lean.Data.Json.FromToJson

namespace Contract.Check.Declarations
open Lean

private def node (tag : String) (args : List Json := []) : Json := .arr (.str tag :: args).toArray
private def number (n : Nat) : Json := .str (toString n)
private def names (ns : List Name) : Json := toJson (ns.map Name.toString)
private def binder : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instance"

def level : Level → Json
  | .zero => node "zero"
  | .succ x => node "succ" [level x]
  | .max x y => node "max" [level x, level y]
  | .imax x y => node "imax" [level x, level y]
  | .param p => node "param" [.str p.toString]
  | .mvar p => node "invalidMetavariable" [.str p.name.toString]

private structure ExpressionDag where
  /- Structural equality preserves binder names and annotations. Ordinary
  ExprMap equality ignores binder names, which this artifact retains. -/
  seen : ExprStructMap Nat := {}
  nodes : Array Json := #[]
  encoded : Std.HashMap String Nat := {}

private def internExpression (term : Lean.Expr) : StateM ExpressionDag Json := do
  -- Metadata is nonsemantic and omitted, as in the original tree encoding.
  if let .mdata _ e := term then return ← internExpression e
  if let some id := (← get).seen.get? ⟨term⟩ then return toJson id
  let encoded ← match term with
    | .bvar i => pure <| node "bound" [number i]
    | .fvar i => pure <| node "invalidFreeVariable" [.str i.name.toString]
    | .mvar i => pure <| node "invalidMetavariable" [.str i.name.toString]
    | .sort u => pure <| node "sort" [level u]
    | .const n us => pure <| node "const" [.str n.toString, .arr (us.map level).toArray]
    | .app f a => pure <| node "app" [← internExpression f, ← internExpression a]
    | .lam n t b bi => pure <| node "lambda" [.str n.toString, .str (binder bi),
        ← internExpression t, ← internExpression b]
    | .forallE n t b bi => pure <| node "forall" [.str n.toString, .str (binder bi),
        ← internExpression t, ← internExpression b]
    | .letE n t v b nondep => pure <| node "let" [.str n.toString,
        ← internExpression t, ← internExpression v, ← internExpression b, .bool nondep]
    | .lit (.natVal n) => pure <| node "natural" [number n]
    | .lit (.strVal s) => pure <| node "string" [.str s]
    | .mdata _ e => internExpression e
    | .proj n i e => pure <| node "projection" [.str n.toString, number i, ← internExpression e]
  let key := encoded.compress
  if let some id := (← get).encoded.get? key then
    modify fun s => { s with seen := s.seen.insert ⟨term⟩ id }
    return toJson id
  let id := (← get).nodes.size
  modify fun s => { seen := s.seen.insert ⟨term⟩ id, nodes := s.nodes.push encoded, encoded := s.encoded.insert key id }
  return toJson id

/-- A deterministic, postorder DAG keeps shared proof subterms shared. Node IDs
are local to this expression and never depend on hash-map iteration order. -/
def expression (term : Lean.Expr) : Json :=
  let (root, dag) := (internExpression term).run {}
  Json.mkObj [("encoding", .str "kernelExprDag-v1"), ("root", root), ("nodes", .arr dag.nodes)]

def encode (ci : ConstantInfo) : Json :=
  let extra : List (String × Json) := match ci with
    | .axiomInfo _ => [("kind", .str "axiom")]
    | .defnInfo v => [("kind", .str "definition"), ("value", expression v.value),
        ("mutual", names v.all)]
    | .thmInfo v => [("kind", .str "theorem"), ("value", expression v.value), ("mutual", names v.all)]
    | .opaqueInfo v => [("kind", .str "opaque"), ("value", expression v.value), ("mutual", names v.all)]
    | .inductInfo v => [("kind", .str "inductive"), ("mutual", names v.all),
        ("constructors", names v.ctors), ("parameters", number v.numParams), ("indices", number v.numIndices)]
    | .ctorInfo v => [("kind", .str "constructor"), ("inductive", .str v.induct.toString),
        ("index", number v.cidx), ("parameters", number v.numParams), ("fields", number v.numFields)]
    | .recInfo v => [("kind", .str "recursor"), ("mutual", names v.all),
        ("parameters", number v.numParams), ("indices", number v.numIndices),
        ("motives", number v.numMotives), ("minors", number v.numMinors), ("k", .bool v.k),
        ("rules", .arr <| v.rules.toArray.map fun r => Json.mkObj [
          ("constructor", .str r.ctor.toString), ("fields", number r.nfields), ("rhs", expression r.rhs)])]
    | .quotInfo v => [("kind", .str "quotient"), ("rule", .str (match v.kind with
        | .type => "type" | .ctor => "constructor" | .lift => "lift" | .ind => "induction"))]
  Json.mkObj ([("name", .str ci.name.toString), ("type", expression ci.type),
    ("levels", names ci.levelParams)] ++ extra)

/-- Extend Lean's expression dependency traversal with complete mutual blocks,
constructor ownership and recursor rules. Missing dependencies are errors. -/
def dependencies (ci : ConstantInfo) : NameSet := Id.run do
  let mut ds := ci.getUsedConstantsAsSet
  match ci with
  | .inductInfo v => for n in v.all ++ v.ctors do ds := ds.insert n
  | .ctorInfo v => ds := ds.insert v.induct
  | .recInfo v =>
    for rule in v.rules do
      ds := ds.insert rule.ctor
      for n in rule.rhs.getUsedConstants do ds := ds.insert n
  | .quotInfo _ => ds := ds.insert ``Eq
  | _ => pure ()
  return ds

def closed (term : Lean.Expr) : Bool := !term.hasMVar && !term.hasFVar && !term.hasLooseBVars

/-- Optional kernel weak-head reduction of selected definition values removes
non-semantic constructor fields behind projections (for example source spans).
The ordinary audit/replay callers retain the original complete declarations. -/
def closure (env : Environment) (roots : Array Name) (reduceValues : Array Name := #[]) :
    Except String (Array ConstantInfo) := do
  let mut pending := roots.toList
  let mut seen : NameSet := {}
  let mut records := #[]
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if seen.contains name then continue
    if records.size ≥ 100000 then throw "dependency closure limit exceeded"
    let some ci := env.checked.get.find? name | throw s!"missing dependency {name}"
    if ci.isUnsafe || ci.isPartial then throw s!"unsupported unsafe/partial dependency {name}"
    unless closed ci.type && (ci.value? true).all closed do throw s!"non-closed dependency {name}"
    let ci ← if reduceValues.contains name then
      match ci with
      | .defnInfo value => match Kernel.whnf env {} value.value with
        | .ok reduced => pure (.defnInfo { value with value := reduced })
        | .error _ => throw s!"kernel definition reduction failed: {name}"
      | _ => throw s!"requested definition reduction for a non-definition: {name}"
    else pure ci
    seen := seen.insert name
    records := records.push ci
    for n in dependencies ci do
      unless seen.contains n do pending := n :: pending
  return records.qsort fun a b => a.name.toString < b.name.toString

def axioms (records : Array ConstantInfo) : Except String (Array String) := do
  let mut result := #[]
  for ci in records do
    if ci matches .axiomInfo _ then
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ci.name do
        throw s!"disallowed axiom {ci.name}"
      result := result.push ci.name.toString
  return result

end Contract.Check.Declarations
