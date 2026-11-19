/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Interaction.World
import Contract.Interaction.Bytes
import Contract.Export.Keccak

namespace Contract.Interaction.Creation

/-- EIP-684 collision/reset semantics. EIP-7610's additional storage collision
test is a distinct, currently unsupported policy; it cannot be silently assumed.
These forks share EIP-170, EIP-161 and the EIP-2681 nonce bound. -/
inductive Fork where
  | istanbul | london | shanghai | cancun | osaka
  deriving DecidableEq, Repr

def Fork.initCodeLimit : Fork → Option Nat
  | .istanbul | .london => none
  | .shanghai | .cancun | .osaka => some 49152

def Fork.rejectEF : Fork → Bool
  | .istanbul => false
  | _ => true

def Fork.hasBaseFee : Fork → Bool
  | .istanbul => false
  | _ => true

def Fork.hasTransientStorage : Fork → Bool
  | .cancun | .osaka => true
  | _ => false

def Fork.hasMemoryCopy : Fork → Bool
  | .cancun | .osaka => true
  | _ => false

def hash (bytes : List UInt8) : List UInt8 :=
  (Contract.Export.Keccak.hash ⟨bytes.toArray⟩).data.toList

/-- Exact EIP-1014 bytes, with no collision-freedom hypothesis. -/
def address (creator salt : Word) (initCode : List UInt8) : Address :=
  (bytesWord (hash ([0xff] ++ (wordBytes creator).drop 12 ++ wordBytes salt ++ hash initCode))).setWidth 160

/-- RLP integer encoding at the EIP-2681 nonce bound. Zero is the empty byte
string, small nonzero integers encode themselves, and larger integers use the
minimal big-endian bytes. There are at most eight payload bytes. -/
def nonceRlp (nonce : UInt64) : List UInt8 :=
  let bytes := ((wordBytes (BitVec.ofNat 256 nonce.toNat)).drop 24).dropWhile (· == 0)
  if nonce == 0 then [0x80]
  else if nonce < 128 then [nonce.toUInt8]
  else UInt8.ofNat (0x80 + bytes.length) :: bytes

/-- CREATE uses the nonce before reservation. Both RLP elements and their list
fit the short encoding; no hash injectivity or nonzero-address premise is used. -/
def nonceAddress (creator : Word) (nonce : UInt64) : Address :=
  let payload := [0x94] ++ (wordBytes creator).drop 12 ++ nonceRlp nonce
  (bytesWord (hash (UInt8.ofNat (0xc0 + payload.length) :: payload))).setWidth 160

inductive Kind where
  | nonce | salted
  deriving DecidableEq, Repr

structure Input where
  creator : Word
  value : Word
  /-- Used only by CREATE2; ordinary CREATE derives its address from the world. -/
  salt : Word
  initCode : List UInt8
  /-- Root frame is depth zero; child entry would increment it. -/
  depth : Nat
  readOnly : Bool
  /-- Explicit abstraction of opcode, memory-expansion and initcode/hash gas.
  This model does not calculate or prove EIP-150 forwarding or gas equivalence. -/
  entryGasAvailable : Bool
  /-- Inherited by the initializer, independently of the creating contract. -/
  origin : Option Address := none
  gasPrice : Option Word := none
  baseFee : Option Word := none

def target (kind : Kind) (input : Input) (nonce : UInt64) : Address :=
  match kind with
  | .nonce => nonceAddress input.creator nonce
  | .salted => address input.creator input.salt input.initCode

structure Request where
  creator : Address
  target : Address
  value : Word
  initCode : List UInt8
  depth : Nat
  origin : Option Address := none
  gasPrice : Option Word := none
  baseFee : Option Word := none
  deriving DecidableEq, Repr

inductive Exit where
  | returned (runtime : List UInt8)
  | reverted (data : List UInt8)
  deriving DecidableEq, Repr

structure Response where
  world : World
  exit : Exit
  /-- Remaining initializer gas must pay code deposit. Supplied by the same
  execution environment; it is not inferred from source correctness. -/
  depositGasAvailable : Bool

/-- The initializer may call back and change the entire world. It executes the
exact requested initcode in the shared block environment, with empty calldata,
the requested caller/value/self, depth, transaction origin, effective gas price
and block base fee. Proving this relation is a separate
executor obligation. Concrete exceptional halt is a failed creation; invalid
program and host resource limits remain explicit inconclusive model outcomes. -/
abbrev Executor := Request → World → Except Fault Response

/-- A creation-capable frame names its policy and exact initializer executor.
Gas admission is an explicit assumption for each execution of the instruction. -/
structure Environment where
  fork : Fork
  execute : Executor
  entryGasAvailable : Bool

/-- Shared admission before materializing memory or executing an initializer.
Fork exceptional limits precede host limits and lightweight failures. -/
def preflight (fork : Fork) (readOnly gas : Bool) (length : Nat) : Option Fault :=
  if readOnly || !gas then some .exceptionalHalt
  else if fork.initCodeLimit.any (length > ·) then some .exceptionalHalt
  else if length > 1048576 then some .resourceLimit
  else none

structure Result where
  address : Word
  world : World
  returndata : List UInt8

def failed (world : World) (data : List UInt8 := []) : Result := ⟨0,world,data⟩

/-- EIP-684 creation replaces preexisting storage, even at a prefunded target.
Only the canonical address is cleared; ordinary EVM storage uses that address. -/
def prepareAccount (world : World) (target : Address) : World :=
  let pointer := target.setWidth 256
  let fresh := world.setAccount pointer {balance := (world.account pointer).balance, nonce := 1}
  {fresh with storage := fun a slot => if a = pointer then 0 else world.storage a slot}

def runtimeAllowed (fork : Fork) (code : List UInt8) : Bool :=
  code.length ≤ 24576 && !(fork.rejectEF && code.head? == some 0xef)

/-- Finish against the snapshot taken after reserving the creator nonce.
Successful initialization may have changed any account through callbacks. -/
def complete (fork : Fork) (target : Address) (reserved : World)
    (execution : Except Fault Response) : Except Fault Result :=
  match execution with
  | .error .exceptionalHalt => .ok (failed reserved)
  | .error fault => .error fault
  | .ok response =>
    match response.exit with
    | .reverted data => .ok (failed reserved data)
    | .returned runtime =>
      if runtimeAllowed fork runtime && response.depositGasAvailable then
        let installed := response.world.setAccount (target.setWidth 256)
          {response.world.accounts target with code := runtime}
        .ok ⟨target.setWidth 256,installed,[]⟩
      else .ok (failed reserved)

/-- Shared account and return-buffer effects under the named fork/policy.
The caller owns the outer snapshot: an eventual parent revert restores even the
creator nonce. An initializer failure restores the nonce-incremented world. -/
def createWith (kind : Kind) (fork : Fork) (execute : Executor) (input : Input) (world : World) : Except Fault Result :=
  match preflight fork input.readOnly input.entryGasAvailable input.initCode.length with
  | some fault => .error fault
  | none =>
    let creator := input.creator.setWidth 160
    let pointer := creator.setWidth 256
    let account := world.account pointer
    if input.depth ≥ 1024 || account.balance < input.value || account.nonce == 18446744073709551615 then
      .ok (failed world)
    else
      let reserved := world.setAccount pointer {account with nonce := account.nonce+1}
      let target := target kind input account.nonce
      let existing := reserved.accounts target
      if existing.nonce != 0 || !existing.code.isEmpty then .ok (failed reserved)
      else
        match (prepareAccount reserved target).transfer pointer (target.setWidth 256) input.value with
        | .error _ => .error .invalidProgram
        | .ok entered =>
          let request : Request := ⟨creator,target,input.value,input.initCode,input.depth+1,input.origin,input.gasPrice,input.baseFee⟩
          complete fork target reserved (execute request entered)

/-- Ordinary CREATE ignores the salt field; its operands have no salt. -/
def create := createWith .nonce

/-- Preserve the existing CREATE2 model entry point. -/
def create2 := createWith .salted

end Contract.Interaction.Creation
