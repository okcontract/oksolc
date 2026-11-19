/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.AssociativeProofs

namespace Compiler.Extraction.AddressMask
open Compiler.Extraction.Cache Contract.Yul

inductive Kind where
  | address | caller | origin | coinbase
  deriving DecidableEq, Repr

/-- One fixed execution frame and transaction/block environment. Reuse the
typed language context; origin and beneficiary are separate, required bindings.
No account state, gas, or arbitrary word is silently treated as an address. -/
structure Environment where
  frame : Contract.Context
  origin : BitVec 160
  coinbase : BitVec 160

def Kind.opcode : Kind → Opcode
  | .address => 0x30 | .caller => 0x33 | .origin => 0x32 | .coinbase => 0x41

def Kind.addressValue (env : Environment) : Kind → BitVec 160
  | .address => env.frame.self | .caller => env.frame.caller
  | .origin => env.origin | .coinbase => env.coinbase

def Kind.value (env : Environment) (kind : Kind) : Word := (kind.addressValue env).setWidth 256
def Kind.eval (env : Environment) (kind : Kind) (arguments : List Word) : Option Word :=
  if arguments.isEmpty then some (kind.value env) else none

def decode (opcode : Opcode) : Option Kind :=
  if opcode == Kind.address.opcode then some .address
  else if opcode == Kind.caller.opcode then some .caller
  else if opcode == Kind.origin.opcode then some .origin
  else if opcode == Kind.coinbase.opcode then some .coinbase else none

def addressMeaning (env : Environment) (other : Meaning) : Meaning where
  operation := fun opcode sequence values =>
    match decode opcode with
    | some kind => kind.eval env values
    | none => other.operation opcode sequence values
  atom := other.atom

def meaning (env : Environment) (other : Meaning) : Meaning :=
  Folding.wordMeaning (addressMeaning env other)

theorem address_operation (env : Environment) (other : Meaning) (kind : Kind)
    (sequence : BitVec 32) (arguments : List Word) :
    (meaning env other).operation kind.opcode sequence arguments = kind.eval env arguments := by
  cases kind <;> rfl

theorem other_operation (env : Environment) (other : Meaning) (opcode : Opcode)
    (sequence : BitVec 32) (arguments : List Word)
    (notWord : Folding.decodeWord opcode = none) (notAddress : decode opcode = none) :
    (meaning env other).operation opcode sequence arguments = other.operation opcode sequence arguments := by
  simp [meaning, Folding.wordMeaning, notWord, addressMeaning, notAddress]

def mask : Word := BitVec.ofNat 256 (2 ^ 160 - 1)

theorem address_mask (address : BitVec 160) : address.setWidth 256 &&& mask = address.setWidth 256 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_setWidth_of_le (by decide : 160 ≤ 256)]
  change address.toNat &&& (2 ^ 160 - 1) = address.toNat
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt address.isLt]

theorem kind_mask (env : Environment) (kind : Kind) :
    kind.value env &&& mask = kind.value env ∧ mask &&& kind.value env = kind.value env := by
  have kept := address_mask (kind.addressValue env)
  exact ⟨kept, (BitVec.and_comm _ _).trans kept⟩

theorem context_address (env : Environment) (storage : Word → Word) (locals : String → Word) :
    Kind.address.value env = Expression.self.eval storage env.frame locals := by
  simp [Kind.value, Kind.addressValue, Expression.eval, BitVec.ofNat_toNat]

theorem context_caller (env : Environment) (storage : Word → Word) (locals : String → Word) :
    Kind.caller.value env = Expression.caller.eval storage env.frame locals := by
  simp [Kind.value, Kind.addressValue, Expression.eval, BitVec.ofNat_toNat]

end Compiler.Extraction.AddressMask
