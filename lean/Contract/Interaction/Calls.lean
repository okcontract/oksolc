/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Interaction.World

namespace Contract.Interaction

structure CallRequest where
  kind : CallKind
  caller : Word
  target : Word
  value : Word
  gas : Word
  input : List UInt8
  /-- Funded message calls supply the entered frame's depth. Older abstract
  external calls do not claim to supply an EVM execution frame. -/
  depth : Option Nat := none
  /-- ADDRESS, storage/transient storage and log owner of the entered frame.
  `target` selects code (and its immutable bindings), not necessarily this owner. -/
  executionAddress : Word := target
  /-- Independent of opcode kind: static context propagates through delegation. -/
  readOnly : Bool := kind == .staticcall
  /-- Inherited transaction identity, never inferred from caller or target. -/
  origin : Option Address := none
  /-- Effective transaction price, inherited even when the child transfers value. -/
  gasPrice : Option Word := none
  /-- Current block's base fee, unchanged across message/delegated frames.
  This is independent of the transaction price or gas forwarded to the child. -/
  baseFee : Option Word := none

structure CallResponse where
  success : Bool
  world : World
  output : List UInt8

/-- An arbitrary environment transition, including reentrant execution. CALL
success is allowed to change all world state. The statement owns commit and
rollback; no token, account-conservation or foreign-code trust is implicit. -/
abbrev Oracle := CallRequest → World → CallResponse

/-- Account/depth prelude for a message call. The foreign executor receives the
funded world and child depth, and must not transfer the call value a second time.
The shared external-statement evaluator owns response commit, rollback and
return-buffer copying. A foreign failure may contain a speculative world;
that world is never committed by the statement. Gas remains opaque: entry gas,
EIP-150 forwarding, stipends, warming and gas-dependent outcomes are not proved.
Invalid account arithmetic is a model fault, never an EVM failure status. -/
def Calls.funded (oracle : Oracle) (depth : Nat) (request : CallRequest) (before : World) :
    Except Fault CallResponse :=
  if request.kind == .staticcall && request.value != 0 then .error .invalidProgram
  else if depth ≥ 1024 then .ok ⟨false,before,[]⟩
  else if request.kind == .delegatecall then
    .ok (oracle {request with depth := some (depth+1)} before)
  else match before.transfer request.caller request.target request.value with
    | .error .insufficientBalance => .ok ⟨false,before,[]⟩
    | .error .invalidBalance => .error .invalidProgram
    | .ok entered => .ok (oracle {request with depth := some (depth+1)} entered)

end Contract.Interaction
