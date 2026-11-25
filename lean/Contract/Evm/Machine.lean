/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Yul.Expression
import Contract.Evm.Guarded

/-! Unified Cancun EVM bytecode semantics covering all pure arithmetic/bitwise/
shift/signed/modular opcodes, environmental context opcodes, byte-addressed
memory with quadratic expansion gas, JUMPDEST scanning, and EIP-2200/2929/3529
storage with gas sentries and clearing refunds.

Pure/environmental straight-line stack operations (`WordOp` / `decodeWordOp` /
`decodeWordOpAt`) are specified once here and executed by `step`, avoiding any
duplicate opcode table in translation validators. Unimplemented opcodes return
`unsupported`, never silent success. -/
namespace Contract.Evm

open Contract.Yul

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

/-- Canonical pure/environmental EVM stack operation shared between `Machine.step`
and straight-line word-block translation validation. -/
inductive WordOp where
  | push (width : Nat) (value : Word)
  | dup (index : Nat)
  | swap (index : Nat)
  | pop
  | nullary (op : Nullary)
  | unary (op : Unary)
  | binary (op : Binary)
  | ternary (op : Ternary)
  deriving DecidableEq, Repr

def binaryGasCost (op : Binary) (stack : List Word) : Nat :=
  match op with
  | .mul | .div | .sdiv | .mod | .smod | .signextend => 5
  | .exp =>
    match stack with
    | _ :: b :: _ => 10 + 50 * expByteLen b
    | _ => 10
  | _ => 3

def WordOp.gasCost (op : WordOp) (stack : List Word) : Nat :=
  match op with
  | .push 0 _ => 2
  | .push (_ + 1) _ => 3
  | .dup _ => 3
  | .swap _ => 3
  | .pop => 2
  | .nullary _ => 2
  | .unary _ => 3
  | .binary bop => binaryGasCost bop stack
  | .ternary _ => 8

def WordOp.byteWidth : WordOp → Nat
  | .push w _ => 1 + w
  | _ => 1

/-- Decode a 1-byte pure/environmental opcode (`PUSH0`, `DUP1..DUP16`, `SWAP1..SWAP16`,
`POP`, arithmetic, bitwise, comparison, shift, modular, or `Context` nullary). -/
def decodeFixedWordOp (opcode : UInt8) : Option WordOp :=
  let n := opcode.toNat
  if n = 0x5f then
    some (.push 0 0#256)
  else if 0x80 ≤ n ∧ n ≤ 0x8f then
    some (.dup (n - 0x80))
  else if 0x90 ≤ n ∧ n ≤ 0x9f then
    some (.swap (n - 0x90))
  else match n with
    | 0x50 => some .pop
    | 0x01 => some (.binary .add)
    | 0x02 => some (.binary .mul)
    | 0x03 => some (.binary .sub)
    | 0x04 => some (.binary .div)
    | 0x05 => some (.binary .sdiv)
    | 0x06 => some (.binary .mod)
    | 0x07 => some (.binary .smod)
    | 0x08 => some (.ternary .addmod)
    | 0x09 => some (.ternary .mulmod)
    | 0x0a => some (.binary .exp)
    | 0x0b => some (.binary .signextend)
    | 0x10 => some (.binary .lt)
    | 0x11 => some (.binary .gt)
    | 0x12 => some (.binary .slt)
    | 0x13 => some (.binary .sgt)
    | 0x14 => some (.binary .eq)
    | 0x15 => some (.unary .iszero)
    | 0x16 => some (.binary .and)
    | 0x17 => some (.binary .or)
    | 0x18 => some (.binary .xor)
    | 0x19 => some (.unary .bitnot)
    | 0x1a => some (.binary .byte)
    | 0x1b => some (.binary .shl)
    | 0x1c => some (.binary .shr)
    | 0x1d => some (.binary .sar)
    | 0x30 => some (.nullary .address)
    | 0x32 => some (.nullary .origin)
    | 0x33 => some (.nullary .caller)
    | 0x41 => some (.nullary .coinbase)
    | _ => none

/-- Decode a `WordOp` for general EVM execution at `pc` (allowing zero-padded
trailing `PUSH1..PUSH32` immediates per Yellow Paper §9.4.1). -/
def decodeWordOp (code : List UInt8) (pc : Nat) (opcode : UInt8) : Option WordOp :=
  if 0x60 ≤ opcode.toNat ∧ opcode.toNat ≤ 0x7f then
    let w := pushWidth opcode
    some (.push w (bytesWord (padded code (pc + 1) w)))
  else
    decodeFixedWordOp opcode

/-- Decode a straight-line `WordOp` inside `code`, rejecting out-of-bounds `pc`
and truncated `PUSH1..PUSH32` immediates (`pc + 1 + w ≤ code.length`). -/
def decodeWordOpAt (code : List UInt8) (pc : Nat) : Option (WordOp × Nat) :=
  match code[pc]? with
  | none => none
  | some byte =>
    if 0x60 ≤ byte.toNat ∧ byte.toNat ≤ 0x7f then
      let w := pushWidth byte
      if pc + 1 + w ≤ code.length then
        some (.push w (bytesWord (padded code (pc + 1) w)), 1 + w)
      else none
    else
      (decodeFixedWordOp byte).map fun op => (op, 1)

def WordOp.evalStack (ctx : Context) (stack : List Word) : WordOp → Option (List Word)
  | .push _ v =>
    if stack.length < 1024 then some (v :: stack) else none
  | .dup i =>
    if stack.length < 1024 then do return (← stack[i]?) :: stack else none
  | .swap i => match stack with
    | top :: rest => do return (← rest[i]?) :: rest.set i top
    | _ => none
  | .pop => match stack with
    | _ :: rest => some rest
    | _ => none
  | .nullary op =>
    if stack.length < 1024 then some (op.eval ctx :: stack) else none
  | .unary op => match stack with
    | a :: rest => some (op.eval a :: rest)
    | _ => none
  | .binary op => match stack with
    | a :: b :: rest => some (op.eval a b :: rest)
    | _ => none
  | .ternary op => match stack with
    | a :: b :: c :: rest => some (op.eval a b c :: rest)
    | _ => none

def push (s : State) (cost width : Nat) (value : Word) : Guarded.Step State Result :=
  if s.machine.stack.length < 1024 then
    .next cost 0 { s with machine := { s.machine with pc := s.machine.pc + width, stack := value :: s.machine.stack } }
  else .fault

def execWordOp (ctx : Context) (s : State) (op : WordOp) : Guarded.Step State Result :=
  match op.evalStack ctx s.machine.stack with
  | some stack' =>
    .next (op.gasCost s.machine.stack) 0
      { s with machine := { s.machine with pc := s.machine.pc + op.byteWidth, stack := stack' } }
  | none => .fault

def step (code : List UInt8) (input : Input) (env : Environment) (s : State) : Guarded.Step State Result :=
  let m := s.machine
  let opcode := code[m.pc]?.getD 0
  match decodeWordOp code m.pc opcode with
  | some op => execWordOp env.ctx s op
  | none =>
    match opcode.toNat with
    | 0x00 => .halt 0 ⟨.returned [], s⟩
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
    | 0xf3 | 0xfd => match m.stack with
      | offset :: size :: _ =>
        let bytes := m.memory.read offset.toNat size.toNat
        let s' := { s with machine := { m with memoryWords := expandedWords m.memoryWords offset.toNat size.toNat } }
        .halt (expansionCost m.memoryWords offset.toNat size.toNat)
          ⟨(if opcode = 0xf3 then Halt.returned else Halt.reverted) bytes, s'⟩
      | _ => .fault
    | 0xfe => .fault
    | _ => .unsupported opcode

def run (code : List UInt8) (input : Input) (env : Environment) :=
  Guarded.run (step code input env)

def runMetered (code : List UInt8) (input : Input) (env : Environment) :=
  Guarded.runMetered (step code input env)

theorem padded_append_left (code tail : List UInt8) (offset w : Nat)
    (h : offset + w ≤ code.length) :
    padded (code ++ tail) offset w = padded code offset w := by
  simp only [padded, readBytesPadded]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have hlt : offset + i < code.length := by omega
  rw [List.getElem?_append_left hlt]

theorem decodeWordOpAt_step_append (code tail : List UInt8) (pc : Nat) (op : WordOp) (width : Nat)
    (input : Input) (env : Environment) (s : State) (wStack : List Word)
    (hsp : s.machine.pc = pc)
    (hd : decodeWordOpAt code pc = some (op, width))
    (hop : op.evalStack env.ctx s.machine.stack = some wStack) :
    step (code ++ tail) input env s =
      .next (op.gasCost s.machine.stack) 0
        { s with machine := { s.machine with pc := pc + width, stack := wStack } } := by
  unfold decodeWordOpAt at hd
  cases hbyte : code[pc]? with
  | none => simp [hbyte] at hd
  | some byte =>
    have hlt : pc < code.length := by
      cases Nat.lt_or_ge pc code.length with
      | inl h => exact h
      | inr hge => rw [List.getElem?_eq_none hge] at hbyte; cases hbyte
    have hcode_byte : ((code ++ tail)[pc]?).getD 0 = byte := by
      rw [List.getElem?_append_left hlt, hbyte]; rfl
    simp only [hbyte] at hd
    by_cases hpush : 0x60 ≤ byte.toNat ∧ byte.toNat ≤ 0x7f
    · simp only [hpush, and_self, ↓reduceIte] at hd
      split at hd
      · rename_i hfit
        simp only [Option.some.injEq, Prod.mk.injEq] at hd
        rcases hd with ⟨rfl, rfl⟩
        have hpad := padded_append_left code tail (pc + 1) (pushWidth byte) hfit
        unfold step decodeWordOp execWordOp
        simp [hsp, hcode_byte, hpush, hpad, hop, WordOp.byteWidth]
      · cases hd
    · simp only [hpush, ↓reduceIte, Option.map_eq_some_iff] at hd
      rcases hd with ⟨op', hfixed, heq⟩
      injection heq with hop_eq hw_eq
      subst hop_eq hw_eq
      have hbw : op'.byteWidth = 1 := by
        unfold decodeFixedWordOp at hfixed
        by_cases h5f : byte.toNat = 0x5f
        · simp [h5f] at hfixed; subst hfixed; rfl
        · simp only [h5f, ↓reduceIte] at hfixed
          by_cases hdup : 0x80 ≤ byte.toNat ∧ byte.toNat ≤ 0x8f
          · simp [hdup] at hfixed; subst hfixed; rfl
          · simp only [hdup, ↓reduceIte] at hfixed
            by_cases hswap : 0x90 ≤ byte.toNat ∧ byte.toNat ≤ 0x9f
            · simp [hswap] at hfixed; subst hfixed; rfl
            · simp only [hswap, ↓reduceIte] at hfixed
              split at hfixed <;> simp at hfixed <;> subst hfixed <;> rfl
      unfold step decodeWordOp execWordOp
      simp [hsp, hcode_byte, hpush, hfixed, hop, hbw]

theorem writeSlot_other (storage : Slots) (key other value : Word) (hne : other ≠ key) :
    writeSlot storage key value other = storage other := by
  simp [writeSlot, hne]

theorem writeSlot_same (storage : Slots) (key value : Word) :
    writeSlot storage key value key = value := by
  simp [writeSlot]

#audit_contract_proof store_cost_bounds
#audit_contract_proof decodeWordOpAt_step_append
#audit_contract_proof writeSlot_other
#audit_contract_proof writeSlot_same

end Contract.Evm
