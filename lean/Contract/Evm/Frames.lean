/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Evm.Subset
import Contract.Semantics.Eval

namespace Contract.Evm
open Interaction (Word)
abbrev Address := BitVec 160

/-- The read-only opcode subset transports the entire persistent world. Explicit
balances/code are needed for incoming-value rollback and code installation;
the interaction model's opaque `other` field does not provide that boundary. -/
structure World where
  storage : Address → Word → Word := fun _ _ => 0
  balances : Address → Nat := fun _ => 0
  code : Address → List UInt8 := fun _ => []
  nonces : Address → Nat := fun _ => 0
  logs : List Interaction.Event := []
  other : Nat → Word := fun _ => 0

/-- Incoming value is staged at frame entry and committed only on success.
Message admission (including sender funds) precedes this frame semantics. -/
def World.transfer (world : World) (caller target : Address) (value : Word) : World :=
  if value = 0#256 ∨ caller = target then world
  else { world with balances := fun a =>
    if a = caller then world.balances a - value.toNat
    else if a = target then world.balances a + value.toNat else world.balances a }

def World.install (world : World) (target : Address) (bytes : List UInt8) : World :=
  { world with code := fun a => if a = target then bytes else world.code a }

inductive Status where
  | returned | reverted | exceptional | unsupported | exhausted
  deriving DecidableEq, Repr

structure Observation where
  status : Status
  bytes : List UInt8
  world : World
  gasRemaining : Nat

def observeCall (world : World) (ctx : Contract.Context) (input : Input) : Metered → Observation
  | .finished gas (.returned bytes) => ⟨.returned, bytes, world.transfer ctx.caller ctx.self input.value, gas⟩
  | .finished gas (.reverted bytes) => ⟨.reverted, bytes, world, gas⟩
  | .exceptional => ⟨.exceptional, [], world, 0⟩
  | .unsupported _ => ⟨.unsupported, [], world, 0⟩
  | .exhausted => ⟨.exhausted, [], world, 0⟩

/-- The actual code stored at the executing account is used, not a separate
assumed-good function body. Transaction fee settlement is outside this frame. -/
def executeCall (world : World) (ctx : Contract.Context) (input : Input) (fuel gas : Nat) : Observation :=
  observeCall world ctx input (runMetered (world.code ctx.self) input fuel gas {})

/-- Admission supplies a fresh target, possibly with a pre-existing balance.
Address derivation, creator nonce and transaction validity precede this stage. -/
def Fresh (world : World) (target : Address) : Prop :=
  world.code target = [] ∧ world.nonces target = 0 ∧ ∀ slot, world.storage target slot = 0

/-- EIP-161 initial contract nonce. The rollback snapshot precedes this change. -/
def World.prepare (world : World) (target : Address) : World :=
  { world with nonces := fun a => if a = target then 1 else world.nonces a }

/-- Cancun EIP-170 / EIP-3541 code checks and code-deposit charge. Incoming value
commits only after successful installation. Initcode word/intrinsic charges have
already been deducted when the caller supplies the frame gas budget. -/
def finishDeployment (before prepared : World) (ctx : Contract.Context) (input : Input) : Metered → Observation
  | .finished gas (.returned bytes) =>
    if bytes.length ≤ 24576 ∧ bytes.head? ≠ some 0xef ∧ 200 * bytes.length ≤ gas then
      ⟨.returned, bytes, (prepared.transfer ctx.caller ctx.self input.value).install ctx.self bytes,
        gas - 200 * bytes.length⟩
    else ⟨.exceptional, [], before, 0⟩
  | other => observeCall before ctx input other

def executeCreation (code : List UInt8) (world : World) (ctx : Contract.Context)
    (_fresh : Fresh world ctx.self) (input : Input) (fuel gas : Nat) : Observation :=
  if code.length ≤ 49152 then finishDeployment world (world.prepare ctx.self) ctx input (runMetered code input fuel gas {})
  else ⟨.exceptional, [], world, 0⟩

end Contract.Evm
