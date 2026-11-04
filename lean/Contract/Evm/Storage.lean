/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Evm.Subset
import Contract.Evm.Guarded

namespace Contract.Evm.Stateful
open Interaction (Word)
abbrev Slots := Word → Word

structure Environment where
  original : Slots
  isStatic : Bool := false

structure State where
  machine : Machine := {}
  storage : Slots := fun _ => 0
  warm : Word → Bool := fun _ => false
  refund : Int := 0

structure Result where
  halt : Halt
  state : State

def write (storage : Slots) (key value : Word) : Slots :=
  fun other => if other = key then value else storage other

def warmKey (warm : Word → Bool) (key : Word) : Word → Bool :=
  fun other => if other = key then true else warm other

/-- EIP-2200 parameters as modified by EIP-2929; cold access is charged once. -/
def storeCost (original current value : Word) (warm : Bool) : Nat :=
  (if warm then 0 else 2100) +
    if current = value then 100
    else if original = current then (if original = 0 then 20000 else 2900)
    else 100

/-- Signed frame refund delta, with EIP-3529's 4,800 clearing refund.
Refund settlement and its one-fifth transaction cap are outside execution. -/
def refundDelta (original current value : Word) : Int :=
  if current = value then 0 else
    (if original ≠ 0 ∧ current ≠ 0 ∧ value = 0 then 4800 else 0) -
    (if original ≠ 0 ∧ current = 0 then 4800 else 0) +
    (if original = value then (if original = 0 then 19900 else 2800) else 0)

theorem store_cost_bounds (original current value : Word) (warm : Bool) :
    100 ≤ storeCost original current value warm ∧ storeCost original current value warm ≤ 22100 := by
  unfold storeCost
  split <;> split <;> (try split) <;> (try split) <;> omega

/-- Read-only instructions share one decoder and gas/memory semantics with
artifact verification. Storage-specific steps below add their own effects. -/
def coreStep (code : List UInt8) (input : Input) (s : Machine) : Evm.Step :=
  Evm.step code input s

def step (code : List UInt8) (input : Input) (env : Environment) (s : State) : Guarded.Step State Result :=
  match (code[s.machine.pc]?.getD 0).toNat with
  | 0x54 => match s.machine.stack with
    | key :: rest =>
      .next (if s.warm key then 100 else 2100) 0
        { s with
          machine := { s.machine with pc := s.machine.pc + 1, stack := s.storage key :: rest },
          warm := warmKey s.warm key }
    | _ => .fault
  | 0x55 => match s.machine.stack with
    | key :: value :: rest =>
      if env.isStatic then .fault else
        .next (storeCost (env.original key) (s.storage key) value (s.warm key)) 2301
          { s with
            machine := { s.machine with pc := s.machine.pc + 1, stack := rest },
            storage := write s.storage key value, warm := warmKey s.warm key,
            refund := s.refund + refundDelta (env.original key) (s.storage key) value }
    | _ => .fault
  | _ => match coreStep code input s.machine with
    | .next cost machine => .next cost 0 { s with machine }
    | .halt cost halt => .halt cost ⟨halt, s⟩
    | .fault => .fault
    | .unsupported op => .unsupported op

def run (code : List UInt8) (input : Input) (env : Environment) := Guarded.run (step code input env)
def runMetered (code : List UInt8) (input : Input) (env : Environment) := Guarded.runMetered (step code input env)

end Contract.Evm.Stateful
