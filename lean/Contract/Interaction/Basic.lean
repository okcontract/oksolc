/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Language.Word

/-! Word-typed, structured interaction profile. Unlike the finite-storage core,
this profile exposes EVM byte memory and external effects. There is no raw Yul
escape. Scope/arity validation is mandatory before export. -/
namespace Contract.Interaction

abbrev Word := BitVec 256

inductive Fault where
  | invalidProgram | resourceLimit | exceptionalHalt
  deriving DecidableEq, Repr

inductive Op where
  | add | sub | word (op : WordOp) | eq | lt | gt | slt | sgt | iszero | not
  /-- EVM byte-indexed sign extension; indices at least 31 leave the word intact. -/
  | signextend
  /-- Big-endian byte selection; indices at least 32 yield zero. -/
  | byte
  /-- EVM modular exponentiation, including zero to the zero power = one. -/
  | exp
  /-- Full-precision EVM arithmetic before reduction; zero modulus yields zero.
  Solidity's distinct zero-modulus failure requires an explicit source guard. -/
  | addmod | mulmod
  | sload | tload | mload | calldataload | calldatasize | caller | origin | gasprice | basefee | address
  | callvalue | timestamp | number | chainid | gas | returndatasize | extcodesize | extcodehash | balance | keccak256
  | codesize
  /-- Linked size of this program's creation object, excluding appended inputs.
  Admitted only directly in the constructor, never in shared helpers/runtime. -/
  | creationSize
  /-- Compilation phase of this object: one in creation and zero at runtime.
  Export folds this intrinsic to a literal, including in shared helpers. -/
  | creationPhase
  /-- Dense immutable binding. Construction reads its reserved memory word;
  runtime reads the explicitly bound installed-code environment. -/
  | immutable (index : Nat)
  deriving DecidableEq, Repr

def Op.name : Op → String
  | .add => "add" | .sub => "sub" | .eq => "eq" | .lt => "lt" | .gt => "gt"
  | .slt => "slt" | .sgt => "sgt"
  | .signextend => "signextend"
  | .byte => "byte"
  | .exp => "exp"
  | .addmod => "addmod" | .mulmod => "mulmod"
  | .iszero => "iszero" | .not => "not" | .sload => "sload" | .mload => "mload"
  | .tload => "tload"
  | .calldataload => "calldataload" | .calldatasize => "calldatasize"
  | .caller => "caller" | .origin => "origin" | .gasprice => "gasprice" | .basefee => "basefee"
  | .address => "address" | .callvalue => "callvalue"
  | .timestamp => "timestamp" | .number => "number" | .chainid => "chainid" | .gas => "gas"
  | .returndatasize => "returndatasize" | .extcodesize => "extcodesize"
  | .extcodehash => "extcodehash"
  | .balance => "balance"
  | .keccak256 => "keccak256"
  | .codesize => "codesize" | .creationSize => "datasize"
  | .creationPhase => "creationPhase"
  | .immutable _ => "loadimmutable"
  | .word .mul => "mul" | .word .div => "div" | .word .mod => "mod"
  | .word .and => "and" | .word .or => "or" | .word .xor => "xor"
  | .word .shl => "shl" | .word .shr => "shr"

def Op.arity : Op → Nat
  | .addmod | .mulmod => 3
  | .calldatasize | .caller | .origin | .gasprice | .basefee | .address | .callvalue | .timestamp | .number | .chainid
  | .gas | .returndatasize | .codesize | .creationSize | .creationPhase | .immutable _ => 0
  | .iszero | .not | .sload | .tload | .mload | .calldataload | .extcodesize | .extcodehash | .balance => 1
  | _ => 2

inductive Expr where
  | lit (value : Word)
  | var (name : String)
  | app (op : Op) (args : List Expr)
  deriving Repr, Inhabited

inductive Effect where
  | sstore | tstore | mstore | mstore8 | calldatacopy | returndatacopy | codecopy | extcodecopy | mcopy
  | log (topics : Fin 5) | return_ | revert | stop | invalid
  deriving DecidableEq, Repr

def Effect.name : Effect → String
  | .sstore => "sstore" | .mstore => "mstore" | .mstore8 => "mstore8"
  | .tstore => "tstore"
  | .calldatacopy => "calldatacopy" | .returndatacopy => "returndatacopy"
  | .codecopy => "codecopy"
  | .extcodecopy => "extcodecopy"
  | .mcopy => "mcopy"
  | .log n => "log" ++ toString n.val | .return_ => "return" | .revert => "revert"
  | .stop => "stop" | .invalid => "invalid"

def Effect.arity : Effect → Nat
  | .extcodecopy => 4
  | .calldatacopy | .returndatacopy | .codecopy | .mcopy => 3
  | .log n => 2 + n.val
  | .stop | .invalid => 0
  | _ => 2

inductive CallKind where
  | call | staticcall | delegatecall
  deriving DecidableEq, Repr

def CallKind.name : CallKind → String
  | .call => "call" | .staticcall => "staticcall" | .delegatecall => "delegatecall"

inductive Stmt where
  | let_ (name : String) (value : Expr)
  | assign (name : String) (value : Expr)
  /-- A fresh remaining-gas observation, sequenced with the surrounding code.
  Unlike the legacy opaque expression snapshot, each execution consumes its
  own explicitly bound observation. This operation does not meter EVM gas. -/
  | observeGas (name : String)
  | effect (op : Effect) (args : List Expr)
  | call (names : List String) (function : String) (args : List Expr)
  /-- EVM order: gas, target, [value], input offset/size, output offset/size.
  An external call is a statement; it cannot hide inside a pure expression. -/
  | external (name : String) (kind : CallKind) (args : List Expr)
  /-- CALL/STATICCALL/DELEGATECALL with an explicit funding/depth prelude.
  Delegate entry preserves caller/value and does not transfer funds.
  Operand order and emitted instruction match external; the model checks the
  message boundary before invoking its foreign executor. -/
  | message (name : String) (kind : CallKind) (args : List Expr)
  /-- Value, memory offset/length, salt. Creation binds a fresh address local
  and can mutate accounts, storage, logs and the return buffer. -/
  | create2 (name : String) (args : List Expr)
  /-- Ordinary CREATE: value, memory offset/length; nonce-derived address. -/
  | create (name : String) (args : List Expr)
  | branch (condition : Expr) (yes no : List Stmt)
  | while_ (condition : Expr) (body : List Stmt)
  /-- Native structured loop. The body runs before each post; continue reaches
  post, break skips it. Condition effects and a false-condition break may lead
  the body, before the original source body. -/
  | for_ (body post : List Stmt)
  | break_ | continue_
  | scope (body : List Stmt)
  | leave
  deriving Repr, Inhabited

structure Function where
  name : String
  params : List String
  results : List String
  body : List Stmt
  deriving Repr, Inhabited

structure Entry where
  signature : String
  body : List Stmt
  payable : Bool := false
  deriving Repr, Inhabited

structure Fallback where
  body : List Stmt
  payable : Bool := false
  deriving Repr, Inhabited

structure Program where
  name : String
  helpers : List Function
  constructor : List Stmt
  entries : List Entry
  /-- Top-level constructor statements that precede the nonpayable check.
  Legacy Solidity field initializers run here. The default retains the DSL's
  established check-before-body behavior; validation bounds this position. -/
  constructorValueCheckAfter : Nat := 0
  /-- Immutable construction words occupy [128,128+32*count). The constructor
  must reserve these words before allocating other live memory. -/
  immutableCount : Nat := 0
  constructorPayable : Bool := false
  /-- Receive is always payable and handles only empty calldata. -/
  receiveBody : Option (List Stmt) := none
  fallback : Option Fallback := none
  deriving Repr, Inhabited

namespace Immutable

def maxCount : Nat := 128
def slot (index : Nat) : Nat := 128 + 32 * index
def key (index : Nat) : String := "immutable_" ++ toString index
def read (index : Nat) : Expr := .app (.immutable index) []
def write (index : Nat) (value : Expr) : Stmt :=
  .effect .mstore [.lit (BitVec.ofNat 256 (slot index)), value]
def reserve (count : Nat) : List Stmt :=
  [.effect .mstore [.lit 64, .lit (BitVec.ofNat 256 (slot count))]]

end Immutable

end Contract.Interaction
