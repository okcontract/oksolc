/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryAir

/-! Applied equations for symbolic execution of memory AIR. Keeping these
equations at fully applied constructors avoids unfolding an entire evaluator
under function-valued arguments while proving a generated program. -/
namespace Compiler.ZigAir.MemoryAir
open Memory

theorem value_valid_of_hasType (value : Value) (type : Ty) (typed : value.hasType type = true) :
    value.valid = true := by
  simp only [Value.hasType, Bool.and_eq_true] at typed
  exact typed.2

theorem Ref.eval_local (id : Nat) (env : Env) : (Ref.local id).eval env =
    match env id with
    | none => .error .malformed
    | some value => if value.valid then .ok value else .error .malformed := by
  cases found : env id <;> simp [Ref.eval, found, bind, Except.bind]

theorem Ref.eval_constant (value : Value) (env : Env) : (Ref.constant value).eval env =
    if value.valid then .ok value else .error .malformed := rfl

theorem Ref.eval_constant_of_valid (value : Value) (env : Env) (valid : value.valid = true) :
    (Ref.constant value).eval env = .ok value := by
  rw [Ref.eval_constant, if_pos valid]

theorem Ref.natural_of_eval (ref : Ref) (env : Env) (number : Int)
    (evaluated : ref.eval env = .ok (.scalar (.int false 64 number))) :
    ref.natural env = .ok number.toNat := by
  simp only [Ref.natural, evaluated, bind, Except.bind]

theorem Ref.natural_eq (ref : Ref) (env : Env) : ref.natural env =
    match ref.eval env with
    | .ok value => match value with
      | .scalar (.int false 64 number) => .ok number.toNat
      | _ => .error .malformed
    | .error fault => .error fault := by
  cases h : ref.eval env <;> simp [Ref.natural, h, bind, Except.bind] <;>
    (split <;> simp_all)

theorem Prim.eval_argument (index : Nat) (args : List Value) (env : Env) (state : State) :
    (Prim.argument index).eval args env state =
      (match args[index]? with | some value => .ok value | none => .error .malformed, state) := by
  cases found : args[index]? <;> simp [Prim.eval, Prim.transition, found, bind, Except.bind]

theorem Prim.eval_alloc_ok (child : Ty) (args : List Value) (env : Env) (state after : State) (value : Value)
    (allocated : allocate state child = .ok (value, after)) :
    (Prim.alloc child).eval args env state = (.ok value, after) := by
  simp only [Prim.eval, Prim.transition, allocated]

theorem Prim.eval_alloc_fault (child : Ty) (args : List Value) (env : Env) (state : State) (fault : Fault)
    (failed : allocate state child = .error fault) :
    (Prim.alloc child).eval args env state = (.error fault, state) := by
  simp only [Prim.eval, Prim.transition, failed]

theorem Prim.eval_cast (target : Ty) (pointer : Ref) (args : List Value) (env : Env) (state : State) :
    (Prim.pointerCast target pointer).eval args env state =
      (pointer.eval env >>= Memory.pointerCast state target, state) := by
  cases h : pointer.eval env with
  | error => simp [Prim.eval, Prim.transition, h, bind, Except.bind]
  | ok value =>
    cases checked : Memory.pointerCast state target value <;>
      simp [Prim.eval, Prim.transition, h, checked, bind, Except.bind]

theorem Prim.eval_offset (subtract : Bool) (pointer count : Ref) (args : List Value) (env : Env) (state : State) :
    (Prim.offsetPointer subtract pointer count).eval args env state =
      ((do Memory.offsetPointer state subtract (← pointer.eval env) (← count.natural env)), state) := by
  cases h : pointer.eval env with
  | error => simp [Prim.eval, Prim.transition, h, bind, Except.bind]
  | ok value =>
    cases n : count.natural env with
    | error => simp [Prim.eval, Prim.transition, h, n, bind, Except.bind]
    | ok number =>
      cases checked : Memory.offsetPointer state subtract value number <;>
        simp [Prim.eval, Prim.transition, h, n, checked, bind, Except.bind]

theorem Prim.eval_load (pointer : Ref) (args : List Value) (env : Env) (state : State) :
    (Prim.load pointer).eval args env state = (pointer.eval env >>= Memory.load state, state) := by
  cases h : pointer.eval env with
  | error => simp [Prim.eval, Prim.transition, h, bind, Except.bind]
  | ok value =>
    cases checked : Memory.load state value <;>
      simp [Prim.eval, Prim.transition, h, checked, bind, Except.bind]

theorem Prim.eval_element (pointer index : Ref) (args : List Value) (env : Env) (state : State) :
    (Prim.elementPointer pointer index).eval args env state =
      ((do Memory.elementPointer state (← pointer.eval env) (← index.natural env)), state) := by
  cases p : pointer.eval env with
  | error => simp [Prim.eval, Prim.transition, p, bind, Except.bind]
  | ok value =>
    cases n : index.natural env with
    | error => simp [Prim.eval, Prim.transition, p, n, bind, Except.bind]
    | ok number =>
      cases checked : Memory.elementPointer state value number <;>
        simp [Prim.eval, Prim.transition, p, n, checked, bind, Except.bind]

theorem Prim.eval_slice_element (view index : Ref) (args : List Value) (env : Env) (state : State) :
    (Prim.sliceElementPointer view index).eval args env state =
      ((do Memory.sliceElementPointer state (← view.eval env) (← index.natural env)), state) := by
  cases p : view.eval env with
  | error => simp [Prim.eval, Prim.transition, p, bind, Except.bind]
  | ok value =>
    cases n : index.natural env with
    | error => simp [Prim.eval, Prim.transition, p, n, bind, Except.bind]
    | ok number =>
      cases checked : Memory.sliceElementPointer state value number <;>
        simp [Prim.eval, Prim.transition, p, n, checked, bind, Except.bind]

theorem Prim.eval_slice (target : Ty) (pointer length : Ref) (args : List Value) (env : Env) (state : State) :
    (Prim.slice target pointer length).eval args env state =
      ((do Memory.makeSlice state target (← pointer.eval env) (← length.natural env)), state) := by
  cases p : pointer.eval env with
  | error => simp [Prim.eval, Prim.transition, p, bind, Except.bind]
  | ok value =>
    cases n : length.natural env with
    | error => simp [Prim.eval, Prim.transition, p, n, bind, Except.bind]
    | ok number =>
      cases checked : Memory.makeSlice state target value number <;>
        simp [Prim.eval, Prim.transition, p, n, checked, bind, Except.bind]

theorem Prim.eval_bounds (start finish : Ref) (upper : Bound) (args : List Value) (env : Env) (state : State) :
    (Prim.checkBounds start finish upper).eval args env state =
      ((do Memory.checkSliceBounds (← start.natural env) (← finish.natural env) (← upper.eval env)
           pure (.scalar .unit)), state) := by
  cases a : start.natural env <;> cases b : finish.natural env <;> cases c : upper.eval env <;>
    simp only [Prim.eval, Prim.transition, a, b, c, bind, Except.bind]
  rename_i x y z
  cases Memory.checkSliceBounds x y z <;> rfl

theorem Prim.eval_scalar (operation : Scalar.Prim) (args : List Value) (env : Env) (state : State) :
    (Prim.scalar operation).eval args env state =
      (match operation.eval [] (scalarEnv env) with
        | .ok value => .ok (.scalar value)
        | .error fault => .error (.scalar fault), state) := by
  cases h : operation.eval [] (scalarEnv env) <;>
    simp [Prim.eval, Prim.transition, h, bind, Except.bind]

theorem Prim.eval_store (pointer value : Ref) (args : List Value) (env : Env) (state : State) :
    (Prim.store pointer value).eval args env state =
      match (do Memory.store state (← pointer.eval env) (← value.eval env)) with
      | .ok after => (.ok (.scalar .unit), after)
      | .error fault => (.error fault, state) := by
  cases p : pointer.eval env with
  | error => simp [Prim.eval, Prim.transition, p, bind, Except.bind]
  | ok address =>
    cases v : value.eval env with
    | error => simp [Prim.eval, Prim.transition, p, v, bind, Except.bind]
    | ok contents =>
      cases checked : Memory.store state address contents <;>
        simp [Prim.eval, Prim.transition, p, v, checked, bind, Except.bind]

theorem Prim.eval_store_ok (pointerRef valueRef : Ref) (args : List Value) (env : Env)
    (state after : State) (pointer value : Value)
    (readPointer : pointerRef.eval env = .ok pointer) (readValue : valueRef.eval env = .ok value)
    (stored : Memory.store state pointer value = .ok after) :
    (Prim.store pointerRef valueRef).eval args env state = (.ok (.scalar .unit), after) := by
  simp only [Prim.eval_store, readPointer, readValue, bind, Except.bind, stored]

theorem Prim.eval_store_fault (pointerRef valueRef : Ref) (args : List Value) (env : Env)
    (state : State) (pointer value : Value) (fault : Fault)
    (readPointer : pointerRef.eval env = .ok pointer) (readValue : valueRef.eval env = .ok value)
    (failed : Memory.store state pointer value = .error fault) :
    (Prim.store pointerRef valueRef).eval args env state = (.error fault, state) := by
  simp only [Prim.eval_store, readPointer, readValue, bind, Except.bind, failed]

theorem Code.eval_bind (id : Nat) (type : Ty) (prim : Prim) (next : Code)
    (args : List Value) (env : Env) (state : State) :
    (Control.Code.bind id type prim next).eval semantics args env state =
      let (result, after) := prim.eval args env state
      match result with
      | .error fault => .fault fault after
      | .ok value => if value.hasType type then next.eval semantics args (env.set id value) after
        else .fault .malformed after := by
  cases h : prim.eval args env state with
  | mk result after => cases result <;> simp [Control.Code.eval, semantics, h]

theorem Code.eval_ret (ref : Ref) (args : List Value) (env : Env) (state : State) :
    (Control.Code.ret ref : Code).eval semantics args env state =
      match ref.eval env with
      | .error fault => .fault fault state
      | .ok value => .returned value state := by
  cases h : ref.eval env <;> simp [Control.Code.eval, semantics, h]

theorem Code.eval_branch (ref : Ref) (yes no : Code) (args : List Value) (env : Env) (state : State) :
    (Control.Code.branch ref yes no).eval semantics args env state =
      match ref.eval env with
      | .error fault => .fault fault state
      | .ok value => match value with
        | .scalar (.bool flag) => (if flag then yes else no).eval semantics args env state
        | _ => .fault .malformed state := by
  cases h : ref.eval env with
  | error => simp [Control.Code.eval, semantics, h]
  | ok value =>
    cases value with
    | scalar value =>
      cases value with
      | bool flag => cases flag <;> simp [Control.Code.eval, semantics, h]
      | _ => simp [Control.Code.eval, semantics, h]
    | _ => simp [Control.Code.eval, semantics, h]

theorem Code.eval_jump (target : Nat) (ref : Ref) (args : List Value) (env : Env) (state : State) :
    (Control.Code.jump target ref : Code).eval semantics args env state =
      match ref.eval env with
      | .error fault => .fault fault state
      | .ok value => .jumped target value env state := by
  cases h : ref.eval env <;> simp [Control.Code.eval, semantics, h]

theorem Code.eval_bind_ok {id : Nat} {type : Ty} {prim : Prim} {next : Code}
    {args : List Value} {env : Env} {state after : State} {value : Value}
    (evaluated : prim.eval args env state = (.ok value, after))
    (typed : value.hasType type = true) :
    (Control.Code.bind id type prim next).eval semantics args env state =
      next.eval semantics args (env.set id value) after := by
  simp only [Code.eval_bind, evaluated, typed, ↓reduceIte]

theorem Code.eval_branch_bool {ref : Ref} {yes no : Code} {args : List Value}
    {env : Env} {state : State} {flag : Bool}
    (evaluated : ref.eval env = .ok (.scalar (.bool flag))) :
    (Control.Code.branch ref yes no).eval semantics args env state =
      (if flag then yes else no).eval semantics args env state := by
  simp only [Code.eval_branch, evaluated]

def Code.afterStore (next : Code) (id : Nat) (args : List Value) (env : Env) (state : State) :
    Except Fault State → Control.Outcome Value Fault State
  | .error fault => .fault fault state
  | .ok after => next.eval semantics args (env.set id (.scalar .unit)) after

def Code.afterValue (next : Code) (id : Nat) (type : Ty) (args : List Value) (env : Env) (state : State) :
    Except Fault Value → Control.Outcome Value Fault State
  | .error fault => .fault fault state
  | .ok value => if value.hasType type then next.eval semantics args (env.set id value) state
      else .fault .malformed state

theorem Code.eval_bind_pure {id : Nat} {type : Ty} {prim : Prim} {next : Code}
    {args : List Value} {env : Env} {state : State} {result : Except Fault Value}
    (evaluated : prim.eval args env state = (result, state)) :
    (Control.Code.bind id type prim next).eval semantics args env state =
      Code.afterValue next id type args env state result := by
  cases result <;> simp only [Code.eval_bind, evaluated, Code.afterValue]

theorem Code.eval_store {id : Nat} {pointerRef valueRef : Ref} {next : Code}
    {args : List Value} {env : Env} {state : State} {pointer value : Value}
    (readPointer : pointerRef.eval env = .ok pointer) (readValue : valueRef.eval env = .ok value) :
    (Control.Code.bind id (.scalar .unit) (.store pointerRef valueRef) next).eval semantics args env state =
      Code.afterStore next id args env state (Memory.store state pointer value) := by
  cases stored : Memory.store state pointer value <;>
    simp only [Code.eval_bind, Prim.eval_store, readPointer, readValue, bind, Except.bind, stored, Code.afterStore] <;> rfl

theorem Program.run_of_valid_inputs (program : Program) (args : List Value) (state : State)
    (initial : state.valid = true) (arity : args.length = program.parameters.length)
    (typed : (args.zip program.parameters).all (fun (value, type) => value.hasType type) = true) :
    program.run args state =
      match program.body.eval semantics args (fun _ => none) state with
      | .returned value after =>
        (if value.hasType program.returnType then .ok value else .error .malformed, cleanup state.nextId after)
      | .fault fault after => (.error fault, cleanup state.nextId after)
      | .jumped _ _ _ after => (.error .malformed, cleanup state.nextId after) := by
  simp only [Program.run, Program.accepts, initial, arity, typed, decide_true, Bool.and_self, ↓reduceIte] <;>
    (cases program.body.eval semantics args (fun _ => none) state <;> rfl)

end Compiler.ZigAir.MemoryAir
