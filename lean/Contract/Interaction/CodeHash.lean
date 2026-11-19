/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Interaction.World
import Contract.Interaction.Bytes
import Contract.Export.Keccak

namespace Contract.Interaction

/-- EIP-161 emptiness. EXTCODEHASH intentionally does not distinguish an absent
account from an existing empty account; neither is a funded or nonce-bearing EOA.
Creation must reserve the nonce before executing the initializer. Precompile
behavior remains conditional on the explicit account-world binding. -/
def Account.empty (a : Account) : Bool :=
  a.balance == 0 && a.nonce == 0 && a.code.isEmpty

/-- EIP-1052 over installed code, not the current frame's creation code. Gas and
access-list warming are outside the interaction model's observations. -/
def Account.codeHash (a : Account) : Word :=
  if a.empty then 0
  else bytesWord (Contract.Export.Keccak.hash ⟨a.code.toArray⟩).data.toList

def World.codeHash (w : World) (address : Word) : Word :=
  (w.account address).codeHash

end Contract.Interaction
