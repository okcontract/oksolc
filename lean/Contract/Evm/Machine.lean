/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Yul.Expression
import Contract.Evm.Guarded

/-! Unified Cancun EVM bytecode semantics covering all pure arithmetic/bitwise/
shift/signed/modular opcodes, environmental context opcodes, byte-addressed
memory with quadratic expansion gas, JUMPDEST scanning, and EIP-2200/2929/3529
storage with gas sentries and clearing refunds. Unimplemented opcodes return
`unsupported`, never silent success. -/
namespace Contract.Evm

abbrev Slots := Word → Word

structure Input where
  calldata : List UInt8 := []
  value : Word := 0#256

structure Environment where
  ctx : Context := {}
  original : Slots := fun _ => 0#256
  isStatic : Bool := false

structure Machine where
  pc : Nat := 0
  stack : List Word := []
  memory : Memory := fun _ => 0
  memoryWords : Nat := 0

structure State where
  machine : Machine := {}
  storage : Slots := fun _ => 0#256
  warm : Word → Bool := fun _ => false
  refund : Int := 0

inductive Halt where
  | returned (bytes : List UInt8)
  | reverted (bytes : List UInt8)
  deriving DecidableEq, Repr

structure Result where
  halt : Halt
  state : State

def writeSlot (storage : Slots) (key value : Word) : Slots :=
  fun other => if other = key then value else storage other

def warmKey (warm : Word → Bool) (key : Word) : Word → Bool :=
  fun other => if other = key then true else warm other

/-- EIP-2200 + EIP-2929 SSTORE gas cost; cold slot access adds 2,100 once. -/
def storeCost (original current value : Word) (warm : Bool) : Nat :=
  (if warm then 0 else 2100) +
    if current = value then 100
    else if original = current then (if original = 0#256 then 20000 else 2900)
    else 100

/-- EIP-2200 + EIP-3529 signed SSTORE refund delta (4,800 clearing refund). -/
def refundDelta (original current value : Word) : Int :=
  if current = value then 0 else
    (if original ≠ 0#256 ∧ current ≠ 0#256 ∧ value = 0#256 then 4800 else 0) -
    (if original ≠ 0#256 ∧ current = 0#256 then 4800 else 0) +
    (if original = value then (if original = 0#256 then 19900 else 2800) else 0)

theorem store_cost_bounds (original current value : Word) (warm : Bool) :
    100 ≤ storeCost original current value warm ∧ storeCost original current value warm ≤ 22100 := by
  unfold storeCost
  split <;> split <;> (try split) <;> (try split) <;> omega

def padded (bytes : List UInt8) (offset size : Nat) : List UInt8 :=
  readBytesPadded bytes offset size

def loadWord (bytes : List UInt8) (offset : Nat) : Word :=
  bytesWord (padded bytes offset 32)

def pushWidth (opcode : UInt8) : Nat :=
  if 0x60 ≤ opcode.toNat ∧ opcode.toNat ≤ 0x7f then opcode.toNat - 0x5f else 0

/-- Decode valid JUMPDEST positions, skipping PUSH1..PUSH32 immediate bytes. -/
def scanJumps (code : List UInt8) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, pc =>
    if pc < code.length then
      let opcode := code[pc]?.getD 0
      let rest := scanJumps code fuel (pc + 1 + pushWidth opcode)
      if opcode = 0x5b then pc :: rest else rest
    else []

def jumpDestinations (code : List UInt8) : List Nat :=
  scanJumps code code.length 0

def memoryCost (words : Nat) : Nat := 3 * words + words * words / 512

def expandedWords (old offset size : Nat) : Nat :=
  if size = 0 then old else max old ((offset + size + 31) / 32)

def expansionCost (old offset size : Nat) : Nat :=
  memoryCost (expandedWords old offset size) - memoryCost old

/-- Byte length of an unsigned 256-bit exponent for EIP-160 EXP gas (`50 * bytes`). -/
def expByteLenAux : Nat → Nat → Nat
  | 0, _ => 0
  | _ + 1, 0 => 0
  | fuel + 1, n => 1 + expByteLenAux fuel (n / 256)

def expByteLen (w : Word) : Nat := expByteLenAux 32 w.toNat

def push (s : State) (cost width : Nat) (value : Word) : Guarded.Step State Result :=
  if s.machine.stack.length < 1024 then
    .next cost 0 { s with machine := { s.machine with pc := s.machine.pc + width, stack := value :: s.machine.stack } }
  else .fault

def unary (s : State) (f : Word → Word) (cost : Nat := 3) : Guarded.Step State Result :=
  match s.machine.stack with
  | a :: rest =>
    .next cost 0 { s with machine := { s.machine with pc := s.machine.pc + 1, stack := f a :: rest } }
  | _ => .fault

def binary (s : State) (f : Word → Word → Word) (cost : Nat := 3) : Guarded.Step State Result :=
  match s.machine.stack with
  | a :: b :: rest =>
    .next cost 0 { s with machine := { s.machine with pc := s.machine.pc + 1, stack := f a b :: rest } }
  | _ => .fault

def ternary (s : State) (f : Word → Word → Word → Word) (cost : Nat := 8) : Guarded.Step State Result :=
  match s.machine.stack with
  | a :: b :: c :: rest =>
    .next cost 0 { s with machine := { s.machine with pc := s.machine.pc + 1, stack := f a b c :: rest } }
  | _ => .fault

def step (code : List UInt8) (input : Input) (env : Environment) (s : State) : Guarded.Step State Result :=
  let m := s.machine
  let opcode := code[m.pc]?.getD 0
  match opcode.toNat with
  | 0x00 => .halt 0 ⟨.returned [], s⟩
  | 0x01 => binary s (· + ·) 3
  | 0x02 => binary s (· * ·) 5
  | 0x03 => binary s (· - ·) 3
  | 0x04 => binary s evmDiv 5
  | 0x05 => binary s evmSdiv 5
  | 0x06 => binary s evmMod 5
  | 0x07 => binary s evmSmod 5
  | 0x08 => ternary s evmAddmod 8
  | 0x09 => ternary s evmMulmod 8
  | 0x0a => match m.stack with
    | a :: b :: rest =>
      .next (10 + 50 * expByteLen b) 0
        { s with machine := { m with pc := m.pc + 1, stack := evmExp a b :: rest } }
    | _ => .fault
  | 0x0b => binary s evmSignextend 5
  | 0x10 => binary s (fun a b => boolWord (a.ult b)) 3
  | 0x11 => binary s (fun a b => boolWord (b.ult a)) 3
  | 0x12 => binary s (fun a b => boolWord (a.slt b)) 3
  | 0x13 => binary s (fun a b => boolWord (b.slt a)) 3
  | 0x14 => binary s (fun a b => boolWord (a == b)) 3
  | 0x15 => unary s (fun a => boolWord (a == 0#256)) 3
  | 0x16 => binary s (· &&& ·) 3
  | 0x17 => binary s (· ||| ·) 3
  | 0x18 => binary s (· ^^^ ·) 3
  | 0x19 => unary s (~~~·) 3
  | 0x1a => binary s evmByte 3
  | 0x1b => binary s evmShl 3
  | 0x1c => binary s evmShr 3
  | 0x1d => binary s evmSar 3
  | 0x30 => push s 2 1 env.ctx.self.toWord
  | 0x32 => push s 2 1 env.ctx.origin.toWord
  | 0x33 => push s 2 1 env.ctx.caller.toWord
  | 0x34 => push s 2 1 input.value
  | 0x35 => match m.stack with
    | offset :: rest =>
      .next 3 0 { s with machine := { m with pc := m.pc + 1, stack := loadWord input.calldata offset.toNat :: rest } }
    | _ => .fault
  | 0x36 => push s 2 1 (BitVec.ofNat 256 input.calldata.length)
  | 0x37 => match m.stack with
    | dest :: source :: size :: rest =>
      .next (3 + 3 * ((size.toNat + 31) / 32) + expansionCost m.memoryWords dest.toNat size.toNat) 0
        { s with machine := { m with
            pc := m.pc + 1, stack := rest,
            memory := m.memory.write dest.toNat (padded input.calldata source.toNat size.toNat),
            memoryWords := expandedWords m.memoryWords dest.toNat size.toNat } }
    | _ => .fault
  | 0x38 => push s 2 1 (BitVec.ofNat 256 code.length)
  | 0x39 => match m.stack with
    | dest :: source :: size :: rest =>
      .next (3 + 3 * ((size.toNat + 31) / 32) + expansionCost m.memoryWords dest.toNat size.toNat) 0
        { s with machine := { m with
            pc := m.pc + 1, stack := rest,
            memory := m.memory.write dest.toNat (padded code source.toNat size.toNat),
            memoryWords := expandedWords m.memoryWords dest.toNat size.toNat } }
    | _ => .fault
  | 0x41 => push s 2 1 env.ctx.coinbase.toWord
  | 0x50 => match m.stack with
    | _ :: rest => .next 2 0 { s with machine := { m with pc := m.pc + 1, stack := rest } }
    | _ => .fault
  | 0x51 => match m.stack with
    | offset :: rest =>
      .next (3 + expansionCost m.memoryWords offset.toNat 32) 0
        { s with machine := { m with
            pc := m.pc + 1, stack := bytesWord (m.memory.read offset.toNat 32) :: rest,
            memoryWords := expandedWords m.memoryWords offset.toNat 32 } }
    | _ => .fault
  | 0x52 => match m.stack with
    | offset :: value :: rest =>
      .next (3 + expansionCost m.memoryWords offset.toNat 32) 0
        { s with machine := { m with
            pc := m.pc + 1, stack := rest,
            memory := m.memory.write offset.toNat (wordBytes value),
            memoryWords := expandedWords m.memoryWords offset.toNat 32 } }
    | _ => .fault
  | 0x53 => match m.stack with
    | offset :: value :: rest =>
      .next (3 + expansionCost m.memoryWords offset.toNat 1) 0
        { s with machine := { m with
            pc := m.pc + 1, stack := rest,
            memory := m.memory.write offset.toNat [UInt8.ofBitVec (value.truncate 8)],
            memoryWords := expandedWords m.memoryWords offset.toNat 1 } }
    | _ => .fault
  | 0x54 => match m.stack with
    | key :: rest =>
      .next (if s.warm key then 100 else 2100) 0
        { s with
          machine := { m with pc := m.pc + 1, stack := s.storage key :: rest },
          warm := warmKey s.warm key }
    | _ => .fault
  | 0x55 => match m.stack with
    | key :: value :: rest =>
      if env.isStatic then .fault else
        .next (storeCost (env.original key) (s.storage key) value (s.warm key)) 2301
          { s with
            machine := { m with pc := m.pc + 1, stack := rest },
            storage := writeSlot s.storage key value,
            warm := warmKey s.warm key,
            refund := s.refund + refundDelta (env.original key) (s.storage key) value }
    | _ => .fault
  | 0x56 => match m.stack with
    | dest :: rest =>
      if dest.toNat ∈ jumpDestinations code then
        .next 8 0 { s with machine := { m with pc := dest.toNat, stack := rest } }
      else .fault
    | _ => .fault
  | 0x57 => match m.stack with
    | dest :: condition :: rest =>
      if condition = 0#256 then .next 10 0 { s with machine := { m with pc := m.pc + 1, stack := rest } }
      else if dest.toNat ∈ jumpDestinations code then
        .next 10 0 { s with machine := { m with pc := dest.toNat, stack := rest } }
      else .fault
    | _ => .fault
  | 0x58 => push s 2 1 (BitVec.ofNat 256 m.pc)
  | 0x59 => push s 2 1 (BitVec.ofNat 256 (32 * m.memoryWords))
  | 0x5b => .next 1 0 { s with machine := { m with pc := m.pc + 1 } }
  | 0x5f => push s 2 1 0#256
  | 0x80 => match m.stack with
    | top :: _ => push s 3 1 top
    | _ => .fault
  | 0xf3 | 0xfd => match m.stack with
    | offset :: size :: _ =>
      let bytes := m.memory.read offset.toNat size.toNat
      let s' := { s with machine := { m with memoryWords := expandedWords m.memoryWords offset.toNat size.toNat } }
      .halt (expansionCost m.memoryWords offset.toNat size.toNat)
        ⟨(if opcode = 0xf3 then Halt.returned else Halt.reverted) bytes, s'⟩
    | _ => .fault
  | 0xfe => .fault
  | _ =>
    if 0x60 ≤ opcode.toNat ∧ opcode.toNat ≤ 0x7f then
      let w := pushWidth opcode
      push s 3 (1 + w) (bytesWord (padded code (m.pc + 1) w))
    else if 0x81 ≤ opcode.toNat ∧ opcode.toNat ≤ 0x8f then
      match m.stack[opcode.toNat - 0x80]? with
      | some value => push s 3 1 value
      | none => .fault
    else if 0x90 ≤ opcode.toNat ∧ opcode.toNat ≤ 0x9f then
      match m.stack with
      | top :: rest => match rest[opcode.toNat - 0x90]? with
        | some value =>
          .next 3 0 { s with machine := { m with pc := m.pc + 1, stack := value :: rest.set (opcode.toNat - 0x90) top } }
        | none => .fault
      | _ => .fault
    else .unsupported opcode

def run (code : List UInt8) (input : Input) (env : Environment) :=
  Guarded.run (step code input env)

def runMetered (code : List UInt8) (input : Input) (env : Environment) :=
  Guarded.runMetered (step code input env)

theorem writeSlot_other (storage : Slots) (key other value : Word) (hne : other ≠ key) :
    writeSlot storage key value other = storage other := by
  simp [writeSlot, hne]

theorem writeSlot_same (storage : Slots) (key value : Word) :
    writeSlot storage key value key = value := by
  simp [writeSlot]

#audit_contract_proof store_cost_bounds
#audit_contract_proof writeSlot_other
#audit_contract_proof writeSlot_same

end Contract.Evm
