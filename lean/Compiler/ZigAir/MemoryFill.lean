/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.ControlProjection
import Compiler.ZigAir.GeneratedMemoryLoops
import Compiler.ZigAir.MemoryPointers
import Compiler.ZigAir.MemoryAirLaws
import Compiler.ZigAir.MachineRefinement

/-! A source-bound functional model of the captured fill loop. The scratch
counter is part of the checked heap; buffer stores and counter stores retain
their order and all partial effects on failure. -/
namespace Compiler.ZigAir.MemoryFill
open Memory MemoryAir GeneratedMemory

abbrev word : Ty := .scalar (.int false 32)
def size (n : Nat) : Value := .scalar (.int false 64 n)
def buffer (address : Address) : Value := .pointer (.pointer true true word) address
def saved (address : Address) : Value := .pointer (.pointer false false (.pointer true true word)) address
def counter (address : Address) : Value := .pointer (.pointer true false usize) address
def unitRef : Ref := .constant (.scalar .unit)

def head : Code :=
  ((fn_fill.body.blockBody? 10).bind Control.Code.finite?).getD (.ret unitRef)

def body : Control.Code Ty Prim Ref true :=
  .block 10 (.scalar .unit) head.enableLoops (.repeat rfl 9)

theorem generated_loop_body : fn_fill.body.blockBody? 8 = some (.loop rfl 9 body) := by rfl
theorem generated_head : fn_fill.body.blockBody? 10 = some head.enableLoops := by rfl

def Locals (env : Env) (length : Nat) (value : Scalar.Value) (pointerSlot indexSlot : Address) : Prop :=
  env 1 = some (size length) ∧ env 2 = some (.scalar value) ∧
    env 5 = some (saved pointerSlot) ∧ env 6 = some (counter indexSlot)

def counterResult (state : State) : Except Fault State → Except Fault Unit × State
  | .error fault => (.error fault, state)
  | .ok after => (.ok (), after)

def advanceCounter (state : State) (indexSlot : Address) (index : Nat) : Except Fault Unit × State :=
  counterResult state (store state (counter indexSlot) (size (index + 1)))

def storeResult (state : State) (indexSlot : Address) (index : Nat) : Except Fault State → Except Fault Unit × State
  | .error fault => (.error fault, state)
  | .ok middle => advanceCounter middle indexSlot index

def elementResult (state : State) (indexSlot : Address) (index : Nat) (value : Scalar.Value) :
    Except Fault Value → Except Fault Unit × State
  | .error fault => (.error fault, state)
  | .ok pointer => storeResult state indexSlot index (store state pointer (.scalar value))

/-- One high-level iteration, including its scratch-counter effect. A failed
counter write retains the successful preceding buffer write. -/
def step (state : State) (address indexSlot : Address) (index : Nat) (value : Scalar.Value) :
    Except Fault Unit × State :=
  elementResult state indexSlot index value (elementPointer state (buffer address) index)

/-- Ordered fill effects, indexed by remaining elements, not machine fuel. -/
def effects (address indexSlot : Address) (value : Scalar.Value) : Nat → Nat → State → Except Fault Unit × State
  | 0, _, state => (.ok (), state)
  | remaining + 1, index, state => match step state address indexSlot index value with
    | (.error fault, after) => (.error fault, after)
    | (.ok (), after) => effects address indexSlot value remaining (index + 1) after

theorem size_valid (n : Nat) (bounded : n < addressLimit) : (size n).valid = true := by
  simp [size, Value.valid, Scalar.Value.valid, Scalar.Ty.contains, Scalar.Ty.lower,
    Scalar.Ty.upper, addressLimit] at *
  omega

theorem size_typed (n : Nat) (bounded : n < addressLimit) : (size n).hasType usize = true := by
  simp [Value.hasType, size, Value.type, Scalar.Value.type, usize]
  exact size_valid n bounded

theorem normalize_size (n : Nat) (bounded : n < addressLimit) : Scalar.normalize false 64 n = n := by
  have bound : (n : Int) < 2 ^ 64 := by exact_mod_cast bounded
  simp only [Scalar.normalize, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  exact Int.emod_eq_of_lt (Int.natCast_nonneg n) bound

private theorem value_typed (value : Scalar.Value) (typed : (Value.scalar value).hasType word = true) :
    (Value.scalar value).valid = true := value_valid_of_hasType _ _ typed

theorem scalar_read_size (env : Env) (id n : Nat) (bounded : n < addressLimit)
    (found : env id = some (size n)) :
    (Scalar.Ref.local id).eval (scalarEnv env) = .ok (.int false 64 n) := by
  have valid := size_valid n bounded
  change (Scalar.Value.int false 64 n).valid = true at valid
  simp [Scalar.Ref.eval, scalarEnv, found, size, valid]

theorem cast_size_eval (ref : Scalar.Ref) (args : List Value) (env : Env) (state : State)
    (n : Nat) (bounded : n < addressLimit)
    (read : ref.eval (scalarEnv env) = .ok (.int false 64 n)) :
    (Prim.scalar (.cast .bitcast (.int false 64) ref)).eval args env state = (.ok (size n), state) := by
  rw [Prim.eval_scalar]
  simp only [Scalar.Prim.eval, read, bind, Except.bind, Scalar.integer,
    ↓reduceIte, normalize_size n bounded]
  rfl

theorem less_size_eval (left right : Scalar.Ref) (args : List Value) (env : Env) (state : State)
    (a b : Nat) (readLeft : left.eval (scalarEnv env) = .ok (.int false 64 a))
    (readRight : right.eval (scalarEnv env) = .ok (.int false 64 b)) :
    (Prim.scalar (.comparison .lt left right)).eval args env state =
      (.ok (.scalar (.bool (decide (a < b)))), state) := by
  rw [Prim.eval_scalar]
  simp only [Scalar.Prim.eval, readLeft, readRight, bind, Except.bind,
    and_self, ↓reduceIte, Scalar.Comparison.eval, Int.ofNat_lt]

attribute [local simp] Code.eval_bind Code.eval_branch Code.eval_jump Prim.eval_scalar
  Prim.eval_load Prim.eval_element Prim.eval_store Ref.eval_local Ref.eval_constant
  Ref.natural_eq Control.Env.set

def condition (yes no : Code) : Code :=
  .bind 11 usize (.load (.local 6))
    (.bind 12 usize (.scalar (.cast .bitcast (.int false 64) (.local 11)))
      (.bind 13 usize (.scalar (.cast .bitcast (.int false 64) (.local 1)))
        (.bind 14 (.scalar .bool) (.scalar (.comparison .lt (.local 12) (.local 13)))
          (.branch (.local 14) yes no))))

def conditionEnv (env : Env) (length index : Nat) : Env :=
  (((env.set 11 (size index)).set 12 (size index)).set 13 (size length)).set 14
    (.scalar (.bool (decide (index < length))))

def writeHead : Code := match head with
  | .bind _ _ _ (.bind _ _ _ (.bind _ _ _ (.bind _ _ _ (.branch _ yes _)))) => yes
  | _ => .ret unitRef

theorem head_shape : head = condition writeHead (.jump 8 unitRef) := by rfl

theorem eval_condition (yes no : Code) (args : List Value) (env : Env) (state : State)
    (length index : Nat) (indexSlot : Address)
    (h1 : env 1 = some (size length)) (h6 : env 6 = some (counter indexSlot))
    (indexBound : index < addressLimit) (lengthBound : length < addressLimit)
    (readIndex : load state (counter indexSlot) = .ok (size index)) :
    (condition yes no).eval semantics args env state =
      (if index < length then yes else no).eval semantics args (conditionEnv env length index) state := by
  have it := size_typed index indexBound
  have nt := size_typed length lengthBound
  have loadIndex : (Prim.load (.local 6)).eval args env state = (.ok (size index), state) := by
    rw [Prim.eval_load]
    simp [Ref.eval_local, h6, counter, Value.valid, bind, Except.bind]
    exact readIndex
  have castIndex := cast_size_eval (.local 11) args (env.set 11 (size index)) state index indexBound
    (scalar_read_size _ 11 index indexBound (by simp))
  have castLength := cast_size_eval (.local 1) args ((env.set 11 (size index)).set 12 (size index))
    state length lengthBound (scalar_read_size _ 1 length lengthBound (by simp [h1]))
  have less := less_size_eval (.local 12) (.local 13) args
    (((env.set 11 (size index)).set 12 (size index)).set 13 (size length)) state index length
    (scalar_read_size _ 12 index indexBound (by simp))
    (scalar_read_size _ 13 length lengthBound (by simp))
  have boolTyped (flag : Bool) : (Value.scalar (.bool flag)).hasType (.scalar .bool) = true := rfl
  unfold condition
  rw [Code.eval_bind_ok loadIndex it, Code.eval_bind_ok castIndex it,
    Code.eval_bind_ok castLength nt, Code.eval_bind_ok less (boolTyped _)]
  have readFlag : (Ref.local 14).eval (conditionEnv env length index) =
      .ok (.scalar (.bool (decide (index < length)))) := by rfl
  change (Control.Code.branch (.local 14) yes no).eval semantics args (conditionEnv env length index) state = _
  rw [Code.eval_branch_bool readFlag]
  simp only [decide_eq_true_eq]

theorem condition_locals (env : Env) (length index : Nat) (value : Scalar.Value)
    (pointerSlot indexSlot : Address) (locals : Locals env length value pointerSlot indexSlot) :
    Locals (conditionEnv env length index) length value pointerSlot indexSlot := by
  simpa [Locals, conditionEnv] using locals

theorem head_stop (args : List Value) (env : Env) (state : State) (length index : Nat)
    (value : Scalar.Value) (pointerSlot indexSlot : Address)
    (locals : Locals env length value pointerSlot indexSlot)
    (indexBound : index < addressLimit) (lengthBound : length < addressLimit)
    (stopped : length ≤ index) (readIndex : load state (counter indexSlot) = .ok (size index)) :
    ∃ afterEnv, head.eval semantics args env state = .jumped 8 (.scalar .unit) afterEnv state := by
  rw [head_shape, eval_condition _ _ args env state length index indexSlot
    locals.1 locals.2.2.2 indexBound lengthBound readIndex, if_neg (by omega)]
  exact ⟨_, rfl⟩

theorem add_size_eval (left right : Scalar.Ref) (args : List Value) (env : Env) (state : State)
    (a b : Nat) (bounded : a + b < addressLimit)
    (readLeft : left.eval (scalarEnv env) = .ok (.int false 64 a))
    (readRight : right.eval (scalarEnv env) = .ok (.int false 64 b)) :
    (Prim.scalar (.arithmetic .add .unchecked left right)).eval args env state =
      (.ok (size (a + b)), state) := by
  have valid := size_valid (a + b) bounded
  change (Scalar.Ty.int false 64).contains (↑(a + b)) = true at valid
  rw [Int.natCast_add] at valid
  rw [Prim.eval_scalar]
  simp only [Scalar.Prim.eval, readLeft, readRight, bind, Except.bind, and_self, ↓reduceIte,
    Scalar.Arithmetic.eval, Scalar.integer, reduceCtorEq, ↓reduceIte,
    valid, size, Int.natCast_add]

theorem add_one_eval (ref : Scalar.Ref) (args : List Value) (env : Env) (state : State)
    (n : Nat) (bounded : n + 1 < addressLimit)
    (read : ref.eval (scalarEnv env) = .ok (.int false 64 n)) :
    (Prim.scalar (.arithmetic .add .unchecked ref (.constant (.int false 64 1)))).eval args env state =
      (.ok (size (n + 1)), state) :=
  add_size_eval ref (.constant (.int false 64 1)) args env state n 1 bounded read rfl

inductive Matches (envLength : Nat) (value : Scalar.Value) (pointerSlot indexSlot : Address) :
    (Except Fault Unit × State) → Control.Outcome Value Fault State → Prop
  | fault (reason : Fault) (after : State) :
      Matches envLength value pointerSlot indexSlot (.error reason, after) (.fault reason after)
  | next (env : Env) (after : State) (locals : Locals env envLength value pointerSlot indexSlot) :
      Matches envLength value pointerSlot indexSlot (.ok (), after) (.jumped 10 (.scalar .unit) env after)

private theorem ref_of_local (env : Env) (id : Nat) (value : Value)
    (found : env id = some value) (valid : value.valid = true) :
    (Ref.local id).eval env = .ok value := by simp [found, valid]

def finishCode : Code :=
  .bind 21 usize (.load (.local 6))
    (.bind 22 usize (.scalar (.arithmetic .add .unchecked (.local 21) (.constant (.int false 64 1))))
      (.bind 23 (.scalar .unit) (.store (.local 6) (.local 22)) (.jump 10 unitRef)))

def storeCode : Code := .bind 19 (.scalar .unit) (.store (.local 18) (.local 2)) finishCode

def writeCode : Code :=
  .bind 16 usize (.load (.local 6))
    (.bind 17 (.pointer true true word) (.load (.local 5))
      (.bind 18 (.pointer true false word) (.elementPointer (.local 17) (.local 16))
        storeCode))

theorem write_head_shape : writeHead = writeCode := by rfl

theorem matches_counter (result : Except Fault State) (args : List Value) (state : State) (env : Env)
    (length : Nat) (value : Scalar.Value) (pointerSlot indexSlot : Address)
    (locals : Locals (env.set 23 (.scalar .unit)) length value pointerSlot indexSlot) :
    Matches length value pointerSlot indexSlot (counterResult state result)
      (Code.afterStore (.jump 10 unitRef) 23 args env state result) := by
  cases result with
  | error reason => exact .fault reason state
  | ok after => exact .next (env.set 23 (.scalar .unit)) after locals

theorem finish_head (args : List Value) (env : Env) (state : State) (length index : Nat)
    (value : Scalar.Value) (pointerSlot indexSlot : Address)
    (locals : Locals env length value pointerSlot indexSlot)
    (bounded : index + 1 < addressLimit)
    (readIndex : load state (counter indexSlot) = .ok (size index)) :
    Matches length value pointerSlot indexSlot (advanceCounter state indexSlot index)
      (finishCode.eval semantics args env state) := by
  have indexBound : index < addressLimit := by omega
  have it := size_typed index indexBound
  rcases locals with ⟨h1, h2, h5, h6⟩
  let eR := env.set 21 (size index)
  let eA := eR.set 22 (size (index + 1))
  have loadAgain : (Prim.load (.local 6)).eval args env state = (.ok (size index), state) := by
    rw [Prim.eval_load, ref_of_local env 6 (counter indexSlot) h6 rfl]
    simpa only [bind, Except.bind] using congrArg (fun x => (x, state)) readIndex
  have addOne := add_one_eval (.local 21) args eR state index bounded
    (scalar_read_size eR 21 index indexBound (by simp [eR]))
  unfold finishCode
  rw [Code.eval_bind_ok loadAgain it,
    Code.eval_bind_ok addOne (size_typed (index + 1) bounded),
    Code.eval_store (ref_of_local eA 6 (counter indexSlot) (by simp [eA, eR, h6]) rfl)
      (ref_of_local eA 22 (size (index + 1)) (by simp [eA]) (size_valid (index + 1) bounded))]
  have nextLocals : Locals (eA.set 23 (.scalar .unit)) length value pointerSlot indexSlot := by
    simp [Locals, eA, eR, h1, h2, h5, h6]
  rw [advanceCounter]
  exact matches_counter (store state (counter indexSlot) (size (index + 1))) args state
      eA length value pointerSlot indexSlot nextLocals

theorem matches_store (result : Except Fault State) (args : List Value) (env : Env) (state : State)
    (length index : Nat) (value : Scalar.Value) (pointerSlot indexSlot : Address)
    (locals : Locals env length value pointerSlot indexSlot) (bounded : index + 1 < addressLimit)
    (readIndex : ∀ middle, result = .ok middle → load middle (counter indexSlot) = .ok (size index)) :
    Matches length value pointerSlot indexSlot (storeResult state indexSlot index result)
      (Code.afterStore finishCode 19 args env state result) := by
  cases result with
  | error fault => exact .fault fault state
  | ok middle =>
    have nextLocals : Locals (env.set 19 (.scalar .unit)) length value pointerSlot indexSlot := by
      simpa [Locals] using locals
    exact finish_head args _ middle length index value pointerSlot indexSlot nextLocals bounded (readIndex middle rfl)

theorem store_code (args : List Value) (env : Env) (state : State) (length index : Nat)
    (value : Scalar.Value) (targetAddress pointerSlot indexSlot : Address)
    (locals : Locals env length value pointerSlot indexSlot)
    (bounded : index + 1 < addressLimit) (typed : (Value.scalar value).hasType word = true)
    (targetLocal : env 18 = some (.pointer (.pointer true false word) targetAddress))
    (readIndex : load state (counter indexSlot) = .ok (size index))
    (apart : indexSlot.allocation ≠ targetAddress.allocation) :
    Matches length value pointerSlot indexSlot
      (storeResult state indexSlot index (store state (.pointer (.pointer true false word) targetAddress) (.scalar value)))
      (storeCode.eval semantics args env state) := by
  unfold storeCode
  rw [Code.eval_store (ref_of_local env 18 _ targetLocal rfl)
    (ref_of_local env 2 _ locals.2.1 (value_typed value typed))]
  apply matches_store _ args env state length index value pointerSlot indexSlot locals bounded
  intro middle written
  exact (load_other_after_store state true false word targetAddress (.scalar value) middle
    true false usize indexSlot written apart).trans readIndex

theorem matches_element (result : Except Fault Value) (args : List Value) (env : Env) (state : State)
    (length index : Nat) (value : Scalar.Value) (pointerSlot indexSlot : Address)
    (locals : Locals env length value pointerSlot indexSlot)
    (bounded : index + 1 < addressLimit) (typed : (Value.scalar value).hasType word = true)
    (readIndex : load state (counter indexSlot) = .ok (size index))
    (geometry : ∀ target, result = .ok target → ∃ address,
      target = .pointer (.pointer true false word) address ∧ indexSlot.allocation ≠ address.allocation) :
    Matches length value pointerSlot indexSlot (elementResult state indexSlot index value result)
      (Code.afterValue storeCode 18 (.pointer true false word) args env state result) := by
  cases result with
  | error fault => exact .fault fault state
  | ok target =>
    obtain ⟨address, rfl, apart⟩ := geometry target rfl
    let nextEnv := env.set 18 (.pointer (.pointer true false word) address)
    have nextLocals : Locals nextEnv length value pointerSlot indexSlot := by
      simpa [Locals, nextEnv] using locals
    exact store_code args nextEnv state length index value address pointerSlot indexSlot
      nextLocals bounded typed (by simp [nextEnv]) readIndex apart

theorem write_code (args : List Value) (env : Env) (state : State) (length index : Nat)
    (value : Scalar.Value) (address pointerSlot indexSlot : Address)
    (locals : Locals env length value pointerSlot indexSlot)
    (bounded : index + 1 < addressLimit) (typed : (Value.scalar value).hasType word = true)
    (readIndex : load state (counter indexSlot) = .ok (size index))
    (readPointer : load state (saved pointerSlot) = .ok (buffer address))
    (apart : indexSlot.allocation ≠ address.allocation) :
    Matches length value pointerSlot indexSlot (step state address indexSlot index value)
      (writeCode.eval semantics args env state) := by
  have indexBound : index < addressLimit := by omega
  have it := size_typed index indexBound
  have iv := size_valid index indexBound
  rcases locals with ⟨h1, h2, h5, h6⟩
  let eI := env.set 16 (size index)
  let eP := eI.set 17 (buffer address)
  have loadI : (Prim.load (.local 6)).eval args env state = (.ok (size index), state) := by
    rw [Prim.eval_load, ref_of_local env 6 _ h6 rfl]
    simpa only [bind, Except.bind] using congrArg (fun x => (x, state)) readIndex
  have loadP : (Prim.load (.local 5)).eval args eI state = (.ok (buffer address), state) := by
    rw [Prim.eval_load, ref_of_local eI 5 (saved pointerSlot) (by simp [eI, h5]) rfl]
    simpa only [bind, Except.bind] using congrArg (fun x => (x, state)) readPointer
  have naturalI : (Ref.local 16).natural eP = .ok index := by
    have decoded := Ref.natural_of_eval (.local 16) eP index
      (ref_of_local eP 16 (size index) (by simp [eP, eI]) iv)
    simpa only [Int.toNat_natCast] using decoded
  have elem : (Prim.elementPointer (.local 17) (.local 16)).eval args eP state =
      (elementPointer state (buffer address) index, state) := by
    rw [Prim.eval_element, ref_of_local eP 17 (buffer address) (by simp [eP]) rfl, naturalI]
    rfl
  unfold writeCode
  rw [Code.eval_bind_ok loadI it,
    Code.eval_bind_ok loadP (show (buffer address).hasType (.pointer true true word) = true from rfl)]
  rw [Code.eval_bind_pure elem]
  have nextLocals : Locals eP length value pointerSlot indexSlot := by
    simp [Locals, eP, eI, h1, h2, h5, h6]
  apply matches_element _ args eP state length index value pointerSlot indexSlot nextLocals bounded typed readIndex
  intro target indexed
  obtain ⟨layout, _, _, position⟩ := elementPointer_address state true word address index target indexed
  exact ⟨_, position, apart⟩

theorem write_head (args : List Value) (env : Env) (state : State) (length index : Nat)
    (value : Scalar.Value) (address pointerSlot indexSlot : Address)
    (locals : Locals env length value pointerSlot indexSlot)
    (bounded : index + 1 < addressLimit) (typed : (Value.scalar value).hasType word = true)
    (readIndex : load state (counter indexSlot) = .ok (size index))
    (readPointer : load state (saved pointerSlot) = .ok (buffer address))
    (apart : indexSlot.allocation ≠ address.allocation) :
    Matches length value pointerSlot indexSlot (step state address indexSlot index value)
      (writeHead.eval semantics args env state) := by
  rw [write_head_shape]
  exact write_code args env state length index value address pointerSlot indexSlot locals bounded typed readIndex readPointer apart

theorem head_continue (args : List Value) (env : Env) (state : State) (length index : Nat)
    (value : Scalar.Value) (address pointerSlot indexSlot : Address)
    (locals : Locals env length value pointerSlot indexSlot)
    (bounded : length < addressLimit) (continuing : index < length)
    (typed : (Value.scalar value).hasType word = true)
    (readIndex : load state (counter indexSlot) = .ok (size index))
    (readPointer : load state (saved pointerSlot) = .ok (buffer address))
    (apart : indexSlot.allocation ≠ address.allocation) :
    Matches length value pointerSlot indexSlot (step state address indexSlot index value)
      (head.eval semantics args env state) := by
  rw [head_shape, eval_condition _ _ args env state length index indexSlot
    locals.1 locals.2.2.2 (by omega) bounded readIndex, if_pos continuing]
  exact write_head args _ state length index value address pointerSlot indexSlot
    (condition_locals env length index value pointerSlot indexSlot locals)
    (by omega) typed readIndex readPointer apart

theorem counterResult_success (result : Except Fault State) (state after : State)
    (success : counterResult state result = (.ok (), after)) : result = .ok after := by
  cases result with
  | error fault => cases success
  | ok final =>
    have same : final = after := congrArg Prod.snd success
    exact congrArg Except.ok same

theorem storeResult_success (result : Except Fault State) (state after : State) (indexSlot : Address)
    (index : Nat) (success : storeResult state indexSlot index result = (.ok (), after)) :
    ∃ middle, result = .ok middle ∧ store middle (counter indexSlot) (size (index + 1)) = .ok after := by
  cases result with
  | error fault => cases success
  | ok middle =>
    exact ⟨middle, rfl, counterResult_success _ middle after success⟩

theorem elementResult_success (result : Except Fault Value) (state after : State) (indexSlot : Address)
    (index : Nat) (value : Scalar.Value)
    (success : elementResult state indexSlot index value result = (.ok (), after)) :
    ∃ target middle, result = .ok target ∧ store state target (.scalar value) = .ok middle ∧
      store middle (counter indexSlot) (size (index + 1)) = .ok after := by
  cases result with
  | error fault => cases success
  | ok target =>
    obtain ⟨middle, written, counted⟩ := storeResult_success _ state after indexSlot index success
    exact ⟨target, middle, rfl, written, counted⟩

theorem step_success (state after : State) (address indexSlot : Address) (index : Nat)
    (value : Scalar.Value) (success : step state address indexSlot index value = (.ok (), after)) :
    ∃ target middle, elementPointer state (buffer address) index = .ok target ∧
      store state target (.scalar value) = .ok middle ∧
      store middle (counter indexSlot) (size (index + 1)) = .ok after :=
  elementResult_success _ state after indexSlot index value success

/-- Scratch reads survive each successful iteration. Their separate allocation
identities are explicit; address inequality alone would not suffice. -/
theorem step_reads (state after : State) (address pointerSlot indexSlot : Address) (index : Nat)
    (value : Scalar.Value) (success : step state address indexSlot index value = (.ok (), after))
    (readPointer : load state (saved pointerSlot) = .ok (buffer address))
    (pointerApart : pointerSlot.allocation ≠ address.allocation)
    (slotsApart : pointerSlot.allocation ≠ indexSlot.allocation) :
    load after (counter indexSlot) = .ok (size (index + 1)) ∧
      load after (saved pointerSlot) = .ok (buffer address) := by
  obtain ⟨target, middle, indexed, written, counted⟩ := step_success state after address indexSlot index value success
  obtain ⟨layout, _, _, rfl⟩ := elementPointer_address state true word address index target indexed
  constructor
  · exact load_after_store middle (counter indexSlot) (size (index + 1)) after counted
  · have first := load_other_after_store state true false word _ (.scalar value) middle
      false false (.pointer true true word) pointerSlot written pointerApart
    have second := load_other_after_store middle true false usize indexSlot (size (index + 1)) after
      false false (.pointer true true word) pointerSlot counted slotsApart
    exact second.trans (first.trans readPointer)

end Compiler.ZigAir.MemoryFill
