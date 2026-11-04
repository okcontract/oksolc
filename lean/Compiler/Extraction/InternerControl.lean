/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.Interner

/-! The closed find/forceEqual profile interpreted with explicit ownership
handoffs. The value interpretation erases only those handoffs and is proved
equal to the existing semantic projection. A scope-aware
interpretation can retain local resources without putting them on the graph's
global state or exposing them to recursive callbacks. -/
namespace Compiler.Extraction.Interner
open Compiler.Algebraic Compiler.Extraction.Cache

structure Execution (m : Type → Type) where
  get : m Heap
  lift : {α : Type} → Except Error α → m α
  atCapacity : Heap → Bool
  normalize : Request → m (List NodeId)
  deterministic : Item → Except Error Bool
  takeOwned : List NodeId → m Unit
  handoff : m Unit
  simplify : Key → m (Option NodeId)
  insert : Key → Bool → m NodeId
  publish : Key → NodeId → m Unit

def FindCode.controlMiss [Monad m] (code : FindCode) (e : Execution m) (request : Request)
    (key : Key) (deterministic : Bool) : m NodeId := do
  if deterministic && (request.item.kind == 1) then
    let simplified ← e.simplify key
    match simplified with
    | some id =>
      let _ ← e.publish key (code.published.run id)
      let _ ← e.handoff
      return code.simplified.run id
    | none => pure ()
  let _ ← e.handoff
  e.insert key deterministic

def FindCode.controlOwned [Monad m] (code : FindCode) (e : Execution m) (request : Request)
    (args : List NodeId) (deterministic : Bool) : m NodeId := do
  let _ ← e.takeOwned args
  let key ← e.lift (makeKey request args)
  code.controlMiss e request key deterministic

/-- The capacity check precedes initialization. Lookup cleanup is registered
only after successful initialization by the scope interpretation. -/
def FindCode.controlRun [Monad m] (code : FindCode) (e : Execution m) (request : Request) : m NodeId := do
  let before ← e.get
  if e.atCapacity before then e.lift (.error .capacity) else do
    let args ← e.normalize request
    let deterministic ← e.lift (e.deterministic request.item)
    if deterministic then
      let key ← e.lift (makeKey request args)
      match before.table key with
      | some id => return code.hit.run id
      | none => pure ()
    code.controlOwned e request args deterministic

def ForceCode.controlOwned [Monad m] (code : ForceCode) (e : Execution m)
    (request : Request) (args : List NodeId) (id : NodeId) : m Unit := do
  let _ ← e.takeOwned args
  let key ← e.lift (makeKey request args)
  let _ ← e.publish key (code.published.run id)
  e.handoff

def ForceCode.controlRun [Monad m] (code : ForceCode) (e : Execution m)
    (validate : NodeId → Heap → Except Error Unit) (id : NodeId)
    (item : Item) (arguments : List NodeId) : m Unit := do
  let before ← e.get
  let _ ← e.lift (validate id before)
  let request : Request := ⟨item, arguments, 0⟩
  let args ← e.normalize request
  let key ← e.lift (makeKey request args)
  match before.table key with
  | some _ => return ()
  | none => pure ()
  code.controlOwned e request args id

def valueExecution (p : Primitives) : Execution Action where
  get := Interner.get
  lift := Interner.lift
  atCapacity := p.atCapacity
  normalize := fun request => liftLocal (p.normalize request)
  deterministic := p.deterministic
  takeOwned := fun args => liftLocal (p.takeOwned args)
  handoff := pure ()
  simplify := p.simplify
  insert := p.insert
  publish := p.publish

theorem control_miss_projection (code : FindCode) (p : Primitives) (request : Request)
    (key : Key) (deterministic : Bool) :
    code.controlMiss (valueExecution p) request key deterministic = code.miss p request key deterministic := rfl

theorem control_owned_projection (code : FindCode) (p : Primitives) (request : Request)
    (args : List NodeId) (deterministic : Bool) :
    code.controlOwned (valueExecution p) request args deterministic = code.owned p request args deterministic := rfl

theorem control_find_projection (code : FindCode) (p : Primitives) (request : Request) :
    code.controlRun (valueExecution p) request = code.run p request := rfl

theorem control_force_projection (code : ForceCode) (p : Primitives)
    (validate : NodeId → Heap → Except Error Unit) (id : NodeId) (item : Item) (arguments : List NodeId) :
    code.controlRun (valueExecution p) validate id item arguments = code.run p validate id item arguments := by
  have finish (action : Action Unit) : (action >>= fun _ => pure ()) = action := by
    funext before
    cases step : action before with
    | mk result after => cases result with
      | error error => simp only [bind, Effect.bind, step]
      | ok ignored => cases ignored; simp only [bind, Effect.bind, step, pure, Effect.pure]
  unfold ForceCode.controlRun ForceCode.controlOwned ForceCode.run
  simp only [valueExecution]
  simp only [finish]
  rfl

end Compiler.Extraction.Interner
