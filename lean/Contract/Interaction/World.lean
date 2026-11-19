/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Interaction.Basic

namespace Contract.Interaction

abbrev Address := BitVec 160

/-- The account observations required by value transfer and creation. Storage
remains in the existing account-indexed map. Transaction gas/access-list state
and account deletion are not silently identified with these observations. -/
structure Account where
  balance : Word := 0
  nonce : UInt64 := 0
  code : List UInt8 := []
  deriving DecidableEq, Repr

structure Event where
  emitter : Word
  topics : List Word
  data : List UInt8
  deriving DecidableEq, Repr

/-- Persistent and transaction-local storage, logs and account observations. Unknown CALL
may change all fields. `other` retains effects outside this account projection;
it is not a substitute for balances, nonces or installed code. -/
structure World where
  storage : Word → Word → Word := fun _ _ => 0
  logs : List Event := []
  other : Nat → Word := fun _ => 0
  accounts : Address → Account := fun _ => {}
  /-- Shared by all frames of an owning account within one transaction. This
  separate map is neither persistent storage nor frame-local byte memory. -/
  transient : Address → Word → Word := fun _ _ => 0

def World.store (w : World) (address slot value : Word) : World :=
  { w with storage := fun a s => if a = address && s = slot then value else w.storage a s }

def World.tload (w : World) (owner slot : Word) : Word :=
  w.transient (owner.setWidth 160) slot

def World.tstore (w : World) (owner slot value : Word) : World :=
  { w with transient := fun a s =>
      if a = owner.setWidth 160 && s = slot then value else w.transient a s }

/-- Root transaction lifecycle only. Successful nested calls do not clear the
  map; reverting frames restore their shared-world entry snapshot instead. -/
def World.clearTransient (w : World) : World :=
  { w with transient := fun _ _ => 0 }

/-- Account operands use their low 160 bits. Keeping the map's key typed avoids
requiring an invariant that every 256-bit alias has a duplicated entry. -/
def World.account (w : World) (address : Word) : Account :=
  w.accounts (address.setWidth 160)

def World.setAccount (w : World) (address : Word) (value : Account) : World :=
  { w with accounts := fun a => if a = address.setWidth 160 then value else w.accounts a }

def World.codeSize (w : World) (address : Word) : Word :=
  BitVec.ofNat 256 (w.account address).code.length

@[simp] theorem World.codeSize_empty_accounts (storage : Word → Word → Word)
    (logs : List Event) (other : Nat → Word) (address : Word) :
    ({storage, logs, other} : World).codeSize address = 0 := rfl

inductive TransferError where
  | insufficientBalance
  /-- No valid balance transfer may overflow a recipient. This signals an
  inconsistent model world, not a Solidity revert or an EVM status code. -/
  | invalidBalance
  deriving DecidableEq, Repr

/-- Persistent balance transition only; the caller owns the transaction/call
snapshot and its rollback. Even a self-transfer checks available funds. A zero
transfer makes no account-existence or touched-account assertion. -/
def World.transfer (w : World) (sender recipient amount : Word) : Except TransferError World :=
  let debit := w.account sender
  if debit.balance < amount then .error .insufficientBalance
  else if amount = 0 ∨ sender.setWidth 160 = recipient.setWidth 160 then .ok w
  else
    let credit := w.account recipient
    if credit.balance.toNat + amount.toNat ≥ 2^256 then .error .invalidBalance
    else .ok ((w.setAccount sender {debit with balance := debit.balance - amount}).setAccount recipient
      {credit with balance := credit.balance + amount})

end Contract.Interaction
