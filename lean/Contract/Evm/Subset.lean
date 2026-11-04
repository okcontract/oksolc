/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Interaction.Eval

/-! Raw-byte, read-only Cancun execution for the first artifact proof. This is
a deliberately partial *specification*, not an EVM backend. Unimplemented
opcodes return `unsupported`, never success. Byte memory and word encodings are
shared with the interaction model; gas and instruction semantics are separate.
World effects are impossible for the admitted instructions. -/
namespace Contract.Evm
open Interaction (Word Memory bytesWord wordBytes)

structure Input where
  calldata : List UInt8 := []
  value : Word := 0

structure Machine where
  pc : Nat := 0
  stack : List Word := []
  memory : Memory := fun _ => 0
  memoryWords : Nat := 0

inductive Halt where
  | returned (bytes : List UInt8)
  | reverted (bytes : List UInt8)
  deriving DecidableEq, Repr

inductive Step where
  | next (cost : Nat) (state : Machine)
  | halt (cost : Nat) (result : Halt)
  | fault
  | unsupported (opcode : UInt8)

def padded (bytes : List UInt8) (offset size : Nat) : List UInt8 :=
  Memory.read (fun i => bytes[i]?.getD 0) offset size

def loadWord (bytes : List UInt8) (offset : Nat) : Word :=
  bytesWord (padded bytes offset 32)

def pushWidth (opcode : UInt8) : Nat :=
  if 0x60 ≤ opcode.toNat ∧ opcode.toNat ≤ 0x7f then opcode.toNat - 0x5f else 0

/-- Decode instruction boundaries, skipping PUSH data, including truncated
immediates. The structural fuel is code length, sufficient even for PUSH0. -/
def scanJumps (code : List UInt8) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, pc =>
    if pc < code.length then
      let opcode := code[pc]?.getD 0
      let rest := scanJumps code fuel (pc + 1 + pushWidth opcode)
      if opcode = 0x5b then pc :: rest else rest
    else []

def jumpDestinations (code : List UInt8) : List Nat := scanJumps code code.length 0

def memoryCost (words : Nat) : Nat := 3 * words + words * words / 512

def expandedWords (old offset size : Nat) : Nat :=
  if size = 0 then old else max old ((offset + size + 31) / 32)

def expansionCost (old offset size : Nat) : Nat :=
  memoryCost (expandedWords old offset size) - memoryCost old

def push (s : Machine) (cost width : Nat) (value : Word) : Step :=
  if s.stack.length < 1024 then
    .next cost { s with pc := s.pc + width, stack := value :: s.stack }
  else .fault

def binary (s : Machine) (f : Word → Word → Word) (cost : Nat := 3) : Step :=
  match s.stack with
  | a :: b :: rest => .next cost { s with pc := s.pc + 1, stack := f a b :: rest }
  | _ => .fault

def unary (s : Machine) (f : Word → Word) : Step :=
  match s.stack with
  | a :: rest => .next 3 { s with pc := s.pc + 1, stack := f a :: rest }
  | _ => .fault

/-- A missing byte decodes to STOP, as in the EVM. Admitted instructions are
word arithmetic/bitwise/comparison operations, PUSH/DUP/SWAP/POP, calldata and
call value, code size/copy, word memory, jumps and STOP/RETURN/REVERT/INVALID.
No storage, external calls, logs or gas introspection are admitted. -/
def step (code : List UInt8) (input : Input) (s : Machine) : Step :=
  let opcode := code[s.pc]?.getD 0
  match opcode.toNat with
  | 0x00 => .halt 0 (.returned [])
  | 0x01 => binary s (· + ·)
  | 0x02 => binary s (· * ·) 5
  | 0x03 => binary s (· - ·)
  | 0x04 => binary s (fun a b => if b = 0 then 0 else a / b) 5
  | 0x06 => binary s (fun a b => if b = 0 then 0 else a % b) 5
  | 0x10 => binary s (fun a b => if a.toNat < b.toNat then 1 else 0)
  | 0x11 => binary s (fun a b => if b.toNat < a.toNat then 1 else 0)
  | 0x12 => binary s (fun a b => if a.toInt < b.toInt then 1 else 0)
  | 0x14 => binary s (fun a b => if a = b then 1 else 0)
  | 0x15 => unary s (fun a => if a = 0 then 1 else 0)
  | 0x16 => binary s (· &&& ·)
  | 0x17 => binary s (· ||| ·)
  | 0x18 => binary s (· ^^^ ·)
  | 0x19 => unary s (~~~·)
  | 0x1b => binary s (fun a b => b <<< a.toNat)
  | 0x1c => binary s (fun a b => b >>> a.toNat)
  | 0x34 => push s 2 1 input.value
  | 0x35 => match s.stack with
    | offset :: rest => .next 3 { s with pc := s.pc + 1, stack := loadWord input.calldata offset.toNat :: rest }
    | _ => .fault
  | 0x36 => push s 2 1 (BitVec.ofNat 256 input.calldata.length)
  | 0x38 => push s 2 1 (BitVec.ofNat 256 code.length)
  | 0x39 => match s.stack with
    | dest :: source :: size :: rest =>
      .next (3 + 3 * ((size.toNat + 31) / 32) + expansionCost s.memoryWords dest.toNat size.toNat)
        { s with
          pc := s.pc + 1, stack := rest,
          memory := s.memory.write dest.toNat (padded code source.toNat size.toNat),
          memoryWords := expandedWords s.memoryWords dest.toNat size.toNat }
    | _ => .fault
  | 0x50 => match s.stack with
    | _ :: rest => .next 2 { s with pc := s.pc + 1, stack := rest }
    | _ => .fault
  | 0x51 => match s.stack with
    | offset :: rest =>
      .next (3 + expansionCost s.memoryWords offset.toNat 32)
        { s with
          pc := s.pc + 1, stack := bytesWord (s.memory.read offset.toNat 32) :: rest,
          memoryWords := expandedWords s.memoryWords offset.toNat 32 }
    | _ => .fault
  | 0x52 => match s.stack with
    | offset :: value :: rest =>
      .next (3 + expansionCost s.memoryWords offset.toNat 32)
        { s with
          pc := s.pc + 1, stack := rest,
          memory := s.memory.write offset.toNat (wordBytes value),
          memoryWords := expandedWords s.memoryWords offset.toNat 32 }
    | _ => .fault
  | 0x56 => match s.stack with
    | dest :: rest => if dest.toNat ∈ jumpDestinations code then
        .next 8 { s with pc := dest.toNat, stack := rest }
      else .fault
    | _ => .fault
  | 0x57 => match s.stack with
    | dest :: condition :: rest =>
      if condition = 0 then .next 10 { s with pc := s.pc + 1, stack := rest }
      else if dest.toNat ∈ jumpDestinations code then
        .next 10 { s with pc := dest.toNat, stack := rest }
      else .fault
    | _ => .fault
  | 0x5b => .next 1 { s with pc := s.pc + 1 }
  | 0x5f => push s 2 1 0
  | 0x80 => match s.stack with
    | top :: _ => push s 3 1 top
    | _ => .fault
  | 0xf3 | 0xfd => match s.stack with
    | offset :: size :: _ =>
      .halt (expansionCost s.memoryWords offset.toNat size.toNat)
        ((if opcode = 0xf3 then Halt.returned else Halt.reverted) (s.memory.read offset.toNat size.toNat))
    | _ => .fault
  | 0xfe => .fault
  | _ => if 0x60 ≤ opcode.toNat ∧ opcode.toNat ≤ 0x7f then
      push s 3 (1 + pushWidth opcode) (bytesWord (padded code (s.pc + 1) (pushWidth opcode)))
    else if 0x81 ≤ opcode.toNat ∧ opcode.toNat ≤ 0x8f then
      match s.stack[opcode.toNat - 0x80]? with
      | some value => push s 3 1 value
      | none => .fault
    else if 0x90 ≤ opcode.toNat ∧ opcode.toNat ≤ 0x9f then
      match s.stack with
      | top :: rest => match rest[opcode.toNat - 0x90]? with
        | some value => .next 3 { s with pc := s.pc + 1, stack := value :: rest.set (opcode.toNat - 0x90) top }
        | none => .fault
      | _ => .fault
    else .unsupported opcode

inductive Execution where
  | finished (cost : Nat) (result : Halt)
  | fault
  | unsupported (opcode : UInt8)
  | exhausted
  deriving DecidableEq, Repr

def Execution.charge (cost : Nat) : Execution → Execution
  | .finished rest result => .finished (cost + rest) result
  | other => other

/-- Costed execution is independent of supplied gas because this subset has no
GAS or calls. The metered interpreter below charges each instruction separately. -/
def run (code : List UInt8) (input : Input) : Nat → Machine → Execution
  | 0, _ => .exhausted
  | fuel + 1, s => match step code input s with
    | .next cost after => (run code input fuel after).charge cost
    | .halt cost result => .finished cost result
    | .fault => .fault
    | .unsupported op => .unsupported op

inductive Metered where
  | finished (remaining : Nat) (result : Halt)
  | exceptional
  | unsupported (opcode : UInt8)
  | exhausted
  deriving DecidableEq, Repr

def runMetered (code : List UInt8) (input : Input) : Nat → Nat → Machine → Metered
  | 0, _, _ => .exhausted
  | fuel + 1, gas, s => match step code input s with
    | .next cost after => if cost ≤ gas then runMetered code input fuel (gas - cost) after else .exceptional
    | .halt cost result => if cost ≤ gas then .finished (gas - cost) result else .exceptional
    | .fault => .exceptional
    | .unsupported op => .unsupported op

end Contract.Evm
