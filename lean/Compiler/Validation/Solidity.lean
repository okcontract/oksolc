/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Primitives
import Contract.Export.Keccak
import Contract.Yul.Expression
import Contract.Evm.World

/-! In-kernel Solidity source syntax, deterministic lexer/parser, Keccak-256
method selector calculation, and executable source contract/deployment
reference semantics over `Contract.Evm.World`.

Unlike external Python source extractors, every character of the admitted
Solidity source is tokenized, parsed, and evaluated inside Lean. -/
namespace Compiler.Validation.Solidity

open Contract
open Contract.Evm

/-- Admitted ABI/state value types. -/
inductive Ty where
  | uint256
  | bool
  | address
  | bytes32
  deriving DecidableEq, Repr, Inhabited

def Ty.abiName : Ty → String
  | .uint256 => "uint256"
  | .bool => "bool"
  | .address => "address"
  | .bytes32 => "bytes32"

/-- ABI calldata word validity check: `uint256` and `bytes32` accept all 256-bit
words; `address` requires the upper 96 bits to be zero; `bool` requires `< 2`. -/
def Ty.validWord : Ty → Word → Bool
  | .uint256 => fun _ => true
  | .bytes32 => fun _ => true
  | .address => fun w => (w &&& BitVec.ofNat 256 ((1 <<< 160) - 1)) == w
  | .bool => fun w => decide (w.toNat < 2)

/-- Mask/normalize an expression word to its declared return type. -/
def Ty.normalizeWord : Ty → Word → Word
  | .uint256 => id
  | .bytes32 => id
  | .address => fun w => w &&& BitVec.ofNat 256 ((1 <<< 160) - 1)
  | .bool => fun w => boolWord (w != 0#256)

inductive Mutability where
  | pure
  | view
  | nonpayable
  | payable
  deriving DecidableEq, Repr, Inhabited

def Mutability.allowsValue : Mutability → Bool
  | .payable => true
  | _ => false

def Mutability.allowsRead : Mutability → Bool
  | .pure => false
  | _ => true

def Mutability.allowsWrite : Mutability → Bool
  | .nonpayable | .payable => true
  | _ => false

inductive UnaryOp where
  | bitNot
  | lnot
  deriving DecidableEq, Repr, Inhabited

inductive BinOp where
  | add | sub | mul | div | mod
  | bitAnd | bitOr | bitXor | shl | shr
  | eq | ne | lt | le | gt | ge
  | land | lor
  deriving DecidableEq, Repr, Inhabited

inductive Expr where
  | lit (val : Word)
  | boolLit (b : Bool)
  | var (name : String)
  | cast (ty : Ty) (arg : Expr)
  | msgSender
  | msgValue
  | addressThis
  | txOrigin
  | blockCoinbase
  | unary (op : UnaryOp) (arg : Expr)
  | binary (op : BinOp) (lhs rhs : Expr)
  deriving DecidableEq, Repr, Inhabited

inductive Stmt where
  | assign (slotName : String) (rhs : Expr)
  | returnVal (val : Expr)
  | returnVoid
  | uncheckedBlock (body : List Stmt)
  | ifElse (cond : Expr) (thenBody : List Stmt) (elseBody : List Stmt)
  deriving Repr, Inhabited

structure Param where
  ty : Ty
  name : String
  deriving DecidableEq, Repr, Inhabited

structure StateVar where
  ty : Ty
  name : String
  init : Option Expr := none
  deriving DecidableEq, Repr, Inhabited

structure FuncDecl where
  name : String
  params : List Param
  mutability : Mutability
  returnTy : Option Ty
  body : List Stmt
  deriving Repr, Inhabited

structure CtorDecl where
  payable : Bool := false
  body : List Stmt := []
  deriving Repr, Inhabited

structure ContractSpec where
  name : String
  stateVars : List StateVar := []
  ctor : Option CtorDecl := none
  hasReceive : Bool := false
  functions : List FuncDecl := []
  deriving Repr, Inhabited

def joinWithComma : List String → String
  | [] => ""
  | [x] => x
  | x :: xs => x ++ "," ++ joinWithComma xs

/-- Canonical ABI signature string, e.g. `"identity(uint256)"`. -/
def FuncDecl.signature (fn : FuncDecl) : String :=
  fn.name ++ "(" ++ joinWithComma (fn.params.map (fun p => p.ty.abiName)) ++ ")"

/-- Proved 4-byte Keccak-256 function selector via `Contract.Export.Keccak`. -/
def FuncDecl.selectorBytes (fn : FuncDecl) : List UInt8 :=
  (Contract.Export.Keccak.hashBytes (Contract.Export.Keccak.asciiBytes fn.signature)).take 4

/-- 32-bit selector word (`0x0000...0000_s0s1s2s3`) matching `SHR(0xe0, CALLDATALOAD(0))`. -/
def FuncDecl.selectorWord (fn : FuncDecl) : Word :=
  BitVec.ofNat 256
    (Contract.Export.Keccak.selectorBits (Contract.Export.Keccak.asciiBytes fn.signature)).toNat

/-- Standard Solidity `Panic(uint256)` revert payload:
`keccak256("Panic(uint256)")[0..4] = 0x4e487b71` followed by 32-byte code (`0x11` or `0x12`). -/
def panicPayload (code : Nat) : List UInt8 :=
  [0x4e, 0x48, 0x7b, 0x71] ++ wordBytes (BitVec.ofNat 256 code)

/-- Look up sequential storage slot index `0, 1, ...` by variable name. -/
def findSlotAux (name : String) (idx : Nat) : List StateVar → Option (Nat × Ty)
  | [] => none
  | v :: vs => if v.name == name then some (idx, v.ty) else findSlotAux name (idx + 1) vs

def ContractSpec.findSlot (spec : ContractSpec) (name : String) : Option (Nat × Ty) :=
  findSlotAux name 0 spec.stateVars

def findParamAux (name : String) (idx : Nat) : List Param → Option (Nat × Ty)
  | [] => none
  | p :: ps => if p.name == name then some (idx, p.ty) else findParamAux name (idx + 1) ps

inductive EvalOutcome (α : Type) where
  | ok (val : α)
  | revert (bytes : List UInt8)
  | invalidSource
  deriving DecidableEq, Repr

/-- Source expression evaluation under `checked` / `unchecked` Solidity 0.8 arithmetic. -/
def evalExpr (spec : ContractSpec) (params : List Param) (checked : Bool)
    (ctx : Context) (input : Input) (storage : Slots) : Expr → EvalOutcome Word
  | .lit w => .ok w
  | .boolLit b => .ok (boolWord b)
  | .var name =>
    match findParamAux name 0 params with
    | some (idx, ty) =>
      .ok (ty.normalizeWord (loadWord input.calldata (4 + 32 * idx)))
    | none =>
      match spec.findSlot name with
      | some (slot, ty) => .ok (ty.normalizeWord (storage (BitVec.ofNat 256 slot)))
      | none => .invalidSource
  | .cast ty arg =>
    match evalExpr spec params checked ctx input storage arg with
    | .ok w => .ok (ty.normalizeWord w)
    | other => other
  | .msgSender => .ok ctx.caller.toWord
  | .msgValue => .ok input.value
  | .addressThis => .ok ctx.self.toWord
  | .txOrigin => .ok ctx.origin.toWord
  | .blockCoinbase => .ok ctx.coinbase.toWord
  | .unary op arg =>
    match evalExpr spec params checked ctx input storage arg with
    | .ok w =>
      match op with
      | .bitNot => .ok (~~~w)
      | .lnot => .ok (boolWord (w == 0#256))
    | other => other
  | .binary .land lhs rhs =>
    match evalExpr spec params checked ctx input storage lhs with
    | .ok a =>
      if a == 0#256 then .ok 0#256
      else match evalExpr spec params checked ctx input storage rhs with
        | .ok b => .ok (boolWord (b != 0#256))
        | other => other
    | other => other
  | .binary .lor lhs rhs =>
    match evalExpr spec params checked ctx input storage lhs with
    | .ok a =>
      if a != 0#256 then .ok 1#256
      else match evalExpr spec params checked ctx input storage rhs with
        | .ok b => .ok (boolWord (b != 0#256))
        | other => other
    | other => other
  | .binary op lhs rhs =>
    match evalExpr spec params checked ctx input storage lhs with
    | .revert r => .revert r
    | .invalidSource => .invalidSource
    | .ok a =>
      match evalExpr spec params checked ctx input storage rhs with
      | .revert r => .revert r
      | .invalidSource => .invalidSource
      | .ok b =>
        match op with
        | .add =>
          if checked && decide (a.toNat + b.toNat ≥ 2 ^ 256) then
            .revert (panicPayload 0x11)
          else .ok (a + b)
        | .sub =>
          if checked && decide (a.toNat < b.toNat) then
            .revert (panicPayload 0x11)
          else .ok (a - b)
        | .mul =>
          if checked && decide (a.toNat * b.toNat ≥ 2 ^ 256) then
            .revert (panicPayload 0x11)
          else .ok (a * b)
        | .div =>
          if b == 0#256 then .revert (panicPayload 0x12)
          else .ok (evmDiv a b)
        | .mod =>
          if b == 0#256 then .revert (panicPayload 0x12)
          else .ok (evmMod a b)
        | .bitAnd => .ok (a &&& b)
        | .bitOr => .ok (a ||| b)
        | .bitXor => .ok (a ^^^ b)
        | .shl => .ok (evmShl b a)
        | .shr => .ok (evmShr b a)
        | .eq => .ok (boolWord (a == b))
        | .ne => .ok (boolWord (a != b))
        | .lt => .ok (boolWord (a.ult b))
        | .le => .ok (boolWord (!b.ult a))
        | .gt => .ok (boolWord (b.ult a))
        | .ge => .ok (boolWord (!a.ult b))
        | .land | .lor => .invalidSource

inductive StmtStep where
  | cont (storage : Slots)
  | returned (bytes : List UInt8) (storage : Slots)
  | reverted (bytes : List UInt8)
  | invalidSource

def evalStmtsWith (evalStmtFn : Bool → Slots → Stmt → StmtStep)
    (checked : Bool) (storage : Slots) : List Stmt → StmtStep
  | [] => .cont storage
  | s :: ss =>
    match evalStmtFn checked storage s with
    | .cont storage' => evalStmtsWith evalStmtFn checked storage' ss
    | term => term

def evalStmtAux (spec : ContractSpec) (params : List Param) (retTy : Option Ty)
    (ctx : Context) (input : Input) : Nat → Bool → Slots → Stmt → StmtStep
  | 0, _, _, _ => .invalidSource
  | _ + 1, checked, storage, .assign slotName rhs =>
    match spec.findSlot slotName with
    | none => .invalidSource
    | some (slotIdx, ty) =>
      match evalExpr spec params checked ctx input storage rhs with
      | .ok val =>
        .cont (writeSlot storage (BitVec.ofNat 256 slotIdx) (ty.normalizeWord val))
      | .revert r => .reverted r
      | .invalidSource => .invalidSource
  | _ + 1, _, storage, .returnVoid =>
    match retTy with
    | none => .returned [] storage
    | some _ => .invalidSource
  | _ + 1, checked, storage, .returnVal expr =>
    match retTy with
    | none => .invalidSource
    | some ty =>
      match evalExpr spec params checked ctx input storage expr with
      | .ok val => .returned (wordBytes (ty.normalizeWord val)) storage
      | .revert r => .reverted r
      | .invalidSource => .invalidSource
  | depth + 1, _, storage, .uncheckedBlock body =>
    evalStmtsWith (evalStmtAux spec params retTy ctx input depth) false storage body
  | depth + 1, checked, storage, .ifElse cond thenBody elseBody =>
    match evalExpr spec params checked ctx input storage cond with
    | .ok val =>
      if val != 0#256 then
        evalStmtsWith (evalStmtAux spec params retTy ctx input depth) checked storage thenBody
      else
        evalStmtsWith (evalStmtAux spec params retTy ctx input depth) checked storage elseBody
    | .revert r => .reverted r
    | .invalidSource => .invalidSource

def evalStmts (spec : ContractSpec) (params : List Param) (retTy : Option Ty)
    (checked : Bool) (ctx : Context) (input : Input) (storage : Slots) (stmts : List Stmt) : StmtStep :=
  evalStmtsWith (evalStmtAux spec params retTy ctx input 64) checked storage stmts

def checkAbiParams (calldata : List UInt8) : Nat → List Param → Bool
  | _, [] => true
  | idx, p :: ps =>
    p.ty.validWord (loadWord calldata (4 + 32 * idx)) && checkAbiParams calldata (idx + 1) ps

/-- Source-level ABI dispatch + execution for a Solidity contract at runtime. -/
def evalRuntime (spec : ContractSpec) (ctx : Context) (input : Input) (storage : Slots) :
    Option (Halt × Slots) :=
  if input.calldata.isEmpty && spec.hasReceive then
    some (.returned [], storage)
  else if input.calldata.length < 4 then
    some (.reverted [], storage)
  else
    let sel := loadWord input.calldata 0 >>> 224
    match spec.functions.find? (fun fn => fn.selectorWord == sel) with
    | none => some (.reverted [], storage)
    | some fn =>
      if (!fn.mutability.allowsValue && input.value != 0#256) ||
         decide (input.calldata.length < 4 + 32 * fn.params.length) ||
         !checkAbiParams input.calldata 0 fn.params then
        some (.reverted [], storage)
      else
        match evalStmts spec fn.params fn.returnTy true ctx input storage fn.body with
        | .returned bytes storage' => some (.returned bytes, storage')
        | .cont storage' =>
          match fn.returnTy with
          | none => some (.returned [], storage')
          | some ty => some (.returned (wordBytes (ty.normalizeWord 0#256)), storage')
        | .reverted bytes => some (.reverted bytes, storage)
        | .invalidSource => none

def evalStateInits (spec : ContractSpec) (ctx : Context) (input : Input)
    (idx : Nat) (storage : Slots) : List StateVar → StmtStep
  | [] => .cont storage
  | v :: vs =>
    match v.init with
    | none => evalStateInits spec ctx input (idx + 1) storage vs
    | some expr =>
      match evalExpr spec [] true ctx input storage expr with
      | .ok val =>
        let storage' := writeSlot storage (BitVec.ofNat 256 idx) (v.ty.normalizeWord val)
        evalStateInits spec ctx input (idx + 1) storage' vs
      | .revert bytes => .reverted bytes
      | .invalidSource => .invalidSource

/-- Source-level constructor + state-variable initialization semantics. -/
def evalDeployment (spec : ContractSpec) (runtimeBytes : List UInt8)
    (ctx : Context) (input : Input) (storage : Slots) : Option (Halt × Slots) :=
  let ctorPayable := match spec.ctor with | some c => c.payable | none => false
  if !ctorPayable && input.value != 0#256 then
    some (.reverted [], storage)
  else
    match evalStateInits spec ctx input 0 storage spec.stateVars with
    | .reverted bytes => some (.reverted bytes, storage)
    | .invalidSource | .returned _ _ => none
    | .cont storageAfterInit =>
      let ctorBody := match spec.ctor with | some c => c.body | none => []
      match evalStmts spec [] none true ctx input storageAfterInit ctorBody with
      | .cont storageFinal | .returned _ storageFinal =>
        some (.returned runtimeBytes, storageFinal)
      | .reverted bytes => some (.reverted bytes, storage)
      | .invalidSource => none

/-! ## Deterministic In-Kernel Lexer and Recursive-Descent Parser -/

inductive Token where
  | ident (s : String)
  | num (n : Nat)
  | lparen | rparen | lbrace | rbrace
  | semi | comma | dot
  | caret | tilde | bang
  | assign | eqeq | neq
  | lt | le | gt | ge | shl | shr
  | plus | minus | star | slash | percent
  | amp | ampamp | pipe | pipepipe
  deriving DecidableEq, Repr, Inhabited

private def isIdentStart (c : Char) : Bool :=
  c.isAlpha || c == '_' || c == '$'

private def isIdentCont (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '$'

private def hexDigitVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

private def parseDecChars : List Char → Nat → Option Nat
  | [], acc => some acc
  | '_' :: cs, acc => parseDecChars cs acc
  | c :: cs, acc =>
    if '0' ≤ c ∧ c ≤ '9' then parseDecChars cs (acc * 10 + (c.toNat - '0'.toNat))
    else none

private def parseHexChars : List Char → Nat → Option Nat
  | [], acc => some acc
  | '_' :: cs, acc => parseHexChars cs acc
  | c :: cs, acc =>
    match hexDigitVal c with
    | some d => parseHexChars cs (acc * 16 + d)
    | none => none

private def parseNumberToken (chars : List Char) : Option Nat :=
  match chars with
  | '0' :: 'x' :: rest | '0' :: 'X' :: rest =>
    if rest.isEmpty then none else parseHexChars rest 0
  | _ =>
    if chars.isEmpty then none else parseDecChars chars 0

private def skipLineComment : List Char → List Char
  | [] => []
  | '\n' :: cs => cs
  | _ :: cs => skipLineComment cs

private def skipBlockComment : List Char → Option (List Char)
  | [] => none
  | '*' :: '/' :: cs => some cs
  | _ :: cs => skipBlockComment cs

private def takeWhileAux (p : Char → Bool) : List Char → List Char → List Char × List Char
  | acc, [] => (acc.reverse, [])
  | acc, c :: cs =>
    if p c then takeWhileAux p (c :: acc) cs else (acc.reverse, c :: cs)

def tokenizeAux : Nat → List Char → List Token → Option (List Token)
  | 0, _, _ => none
  | _ + 1, [], acc => some acc.reverse
  | fuel + 1, c :: cs, acc =>
    if c.isWhitespace then
      tokenizeAux fuel cs acc
    else if c == '/' then
      match cs with
      | '/' :: rest => tokenizeAux fuel (skipLineComment rest) acc
      | '*' :: rest =>
        match skipBlockComment rest with
        | some rest' => tokenizeAux fuel rest' acc
        | none => none
      | _ => tokenizeAux fuel cs (.slash :: acc)
    else if isIdentStart c then
      let (word, rest) := takeWhileAux isIdentCont [c] cs
      tokenizeAux fuel rest (.ident (String.ofList word) :: acc)
    else if c.isDigit then
      let (numChars, rest) := takeWhileAux (fun ch => ch.isAlphanum || ch == '_') [c] cs
      match parseNumberToken numChars with
      | some n =>
        if n < 2 ^ 256 then tokenizeAux fuel rest (.num n :: acc) else none
      | none => none
    else
      match c, cs with
      | '(', rest => tokenizeAux fuel rest (.lparen :: acc)
      | ')', rest => tokenizeAux fuel rest (.rparen :: acc)
      | '{', rest => tokenizeAux fuel rest (.lbrace :: acc)
      | '}', rest => tokenizeAux fuel rest (.rbrace :: acc)
      | ';', rest => tokenizeAux fuel rest (.semi :: acc)
      | ',', rest => tokenizeAux fuel rest (.comma :: acc)
      | '.', rest => tokenizeAux fuel rest (.dot :: acc)
      | '^', rest => tokenizeAux fuel rest (.caret :: acc)
      | '~', rest => tokenizeAux fuel rest (.tilde :: acc)
      | '+', rest => tokenizeAux fuel rest (.plus :: acc)
      | '-', rest => tokenizeAux fuel rest (.minus :: acc)
      | '*', rest => tokenizeAux fuel rest (.star :: acc)
      | '%', rest => tokenizeAux fuel rest (.percent :: acc)
      | '=', '=' :: rest => tokenizeAux fuel rest (.eqeq :: acc)
      | '=', rest => tokenizeAux fuel rest (.assign :: acc)
      | '!', '=' :: rest => tokenizeAux fuel rest (.neq :: acc)
      | '!', rest => tokenizeAux fuel rest (.bang :: acc)
      | '<', '<' :: rest => tokenizeAux fuel rest (.shl :: acc)
      | '<', '=' :: rest => tokenizeAux fuel rest (.le :: acc)
      | '<', rest => tokenizeAux fuel rest (.lt :: acc)
      | '>', '>' :: rest => tokenizeAux fuel rest (.shr :: acc)
      | '>', '=' :: rest => tokenizeAux fuel rest (.ge :: acc)
      | '>', rest => tokenizeAux fuel rest (.gt :: acc)
      | '&', '&' :: rest => tokenizeAux fuel rest (.ampamp :: acc)
      | '&', rest => tokenizeAux fuel rest (.amp :: acc)
      | '|', '|' :: rest => tokenizeAux fuel rest (.pipepipe :: acc)
      | '|', rest => tokenizeAux fuel rest (.pipe :: acc)
      | _, _ => none

def tokenize (src : String) : Option (List Token) :=
  let chars := src.toList
  tokenizeAux (chars.length + 1) chars []

private def parseTyName : String → Option Ty
  | "uint256" | "uint" => some .uint256
  | "bool" => some .bool
  | "address" => some .address
  | "bytes32" => some .bytes32
  | _ => none

def parseBlock (parseLower : List Token → Option (Expr × List Token))
    (matchOp : Token → Option BinOp) :
    Nat → Expr → List Token → Option (Expr × List Token)
  | 0, _, _ => none
  | fuel + 1, lhs, tok :: rest =>
    match matchOp tok with
    | some op =>
      match parseLower rest with
      | some (rhs, rest') => parseBlock parseLower matchOp fuel (.binary op lhs rhs) rest'
      | none => none
    | none => some (lhs, tok :: rest)
  | _ + 1, lhs, [] => some (lhs, [])

def mkLeftAssoc (fuel : Nat) (parseLower : List Token → Option (Expr × List Token))
    (matchOp : Token → Option BinOp) (toks : List Token) : Option (Expr × List Token) :=
  match parseLower toks with
  | some (lhs, rest) => parseBlock parseLower matchOp fuel lhs rest
  | none => none

def parseUnaryAux (parseExprFn : List Token → Option (Expr × List Token)) :
    Nat → List Token → Option (Expr × List Token)
  | 0, _ => none
  | fuel + 1, .tilde :: rest =>
    match parseUnaryAux parseExprFn fuel rest with
    | some (e, rest') => some (.unary .bitNot e, rest')
    | none => none
  | fuel + 1, .bang :: rest =>
    match parseUnaryAux parseExprFn fuel rest with
    | some (e, rest') => some (.unary .lnot e, rest')
    | none => none
  | _ + 1, .num n :: rest => some (.lit (BitVec.ofNat 256 n), rest)
  | _ + 1, .ident "true" :: rest => some (.boolLit true, rest)
  | _ + 1, .ident "false" :: rest => some (.boolLit false, rest)
  | _ + 1, .ident "msg" :: .dot :: .ident "sender" :: rest => some (.msgSender, rest)
  | _ + 1, .ident "msg" :: .dot :: .ident "value" :: rest => some (.msgValue, rest)
  | _ + 1, .ident "tx" :: .dot :: .ident "origin" :: rest => some (.txOrigin, rest)
  | _ + 1, .ident "block" :: .dot :: .ident "coinbase" :: rest => some (.blockCoinbase, rest)
  | _ + 1, .ident "address" :: .lparen :: .ident "this" :: .rparen :: rest =>
    some (.addressThis, rest)
  | _ + 1, .ident name :: .lparen :: rest =>
    match parseTyName name with
    | some ty =>
      match parseExprFn rest with
      | some (arg, .rparen :: rest') => some (.cast ty arg, rest')
      | _ => none
    | none => none
  | _ + 1, .ident name :: rest => some (.var name, rest)
  | _ + 1, .lparen :: rest =>
    match parseExprFn rest with
    | some (e, .rparen :: rest') => some (e, rest')
    | _ => none
  | _, _ => none

def parseExpr : Nat → List Token → Option (Expr × List Token)
  | 0, _ => none
  | depth + 1, toks =>
    let opFuel := toks.length + 1
    let pUnary := parseUnaryAux (parseExpr depth) opFuel
    let pMul := mkLeftAssoc opFuel pUnary (fun
      | .star => some .mul | .slash => some .div | .percent => some .mod | _ => none)
    let pAdd := mkLeftAssoc opFuel pMul (fun
      | .plus => some .add | .minus => some .sub | _ => none)
    let pShift := mkLeftAssoc opFuel pAdd (fun
      | .shl => some .shl | .shr => some .shr | _ => none)
    let pRel := mkLeftAssoc opFuel pShift (fun
      | .lt => some .lt | .le => some .le | .gt => some .gt | .ge => some .ge | _ => none)
    let pEq := mkLeftAssoc opFuel pRel (fun
      | .eqeq => some .eq | .neq => some .ne | _ => none)
    let pBitAnd := mkLeftAssoc opFuel pEq (fun | .amp => some .bitAnd | _ => none)
    let pBitXor := mkLeftAssoc opFuel pBitAnd (fun | .caret => some .bitXor | _ => none)
    let pBitOr := mkLeftAssoc opFuel pBitXor (fun | .pipe => some .bitOr | _ => none)
    let pLand := mkLeftAssoc opFuel pBitOr (fun | .ampamp => some .land | _ => none)
    let pLor := mkLeftAssoc opFuel pLand (fun | .pipepipe => some .lor | _ => none)
    pLor toks

def parseBlockBodyAux (parseStmtFn : List Token → Option (Stmt × List Token)) :
    Nat → List Stmt → List Token → Option (List Stmt × List Token)
  | 0, _, _ => none
  | _ + 1, acc, .rbrace :: rest => some (acc.reverse, rest)
  | fuel + 1, acc, toks =>
    match parseStmtFn toks with
    | some (s, rest) => parseBlockBodyAux parseStmtFn fuel (s :: acc) rest
    | none => none

def parseStmt : Nat → List Token → Option (Stmt × List Token)
  | 0, _ => none
  | depth + 1, toks =>
    let exprDepth := toks.length + 2
    match toks with
    | .ident "return" :: .semi :: rest =>
      some (.returnVoid, rest)
    | .ident "return" :: rest =>
      match parseExpr exprDepth rest with
      | some (e, .semi :: rest') => some (.returnVal e, rest')
      | _ => none
    | .ident "unchecked" :: .lbrace :: rest =>
      match parseBlockBodyAux (parseStmt depth) (rest.length + 1) [] rest with
      | some (stmts, rest') => some (.uncheckedBlock stmts, rest')
      | none => none
    | .ident "if" :: .lparen :: rest =>
      match parseExpr exprDepth rest with
      | some (cond, .rparen :: .lbrace :: rest1) =>
        match parseBlockBodyAux (parseStmt depth) (rest1.length + 1) [] rest1 with
        | some (thenBody, .ident "else" :: .lbrace :: rest2) =>
          match parseBlockBodyAux (parseStmt depth) (rest2.length + 1) [] rest2 with
          | some (elseBody, rest3) => some (.ifElse cond thenBody elseBody, rest3)
          | none => none
        | some (thenBody, .ident "else" :: .ident "if" :: rest2) =>
          match parseStmt depth (.ident "if" :: rest2) with
          | some (elseStmt, rest3) => some (.ifElse cond thenBody [elseStmt], rest3)
          | none => none
        | some (thenBody, rest2) => some (.ifElse cond thenBody [], rest2)
        | none => none
      | _ => none
    | .ident slot :: .assign :: rest =>
      match parseExpr exprDepth rest with
      | some (rhs, .semi :: rest') => some (.assign slot rhs, rest')
      | _ => none
    | _ => none

def parseBlockBody (fuel : Nat) (acc : List Stmt) (toks : List Token) :
    Option (List Stmt × List Token) :=
  parseBlockBodyAux (parseStmt (toks.length + 2)) (fuel + 1) acc toks

private def parseParamsAux : Nat → List Param → List Token → Option (List Param × List Token)
  | 0, _, _ => none
  | _ + 1, acc, .rparen :: rest => some (acc.reverse, rest)
  | fuel + 1, acc, .ident tyStr :: .ident pName :: .comma :: rest =>
    match parseTyName tyStr with
    | some ty => parseParamsAux fuel (⟨ty, pName⟩ :: acc) rest
    | none => none
  | _ + 1, acc, .ident tyStr :: .ident pName :: .rparen :: rest =>
    match parseTyName tyStr with
    | some ty => some ((⟨ty, pName⟩ :: acc).reverse, rest)
    | none => none
  | _, _, _ => none

private def parseFuncQualifiers :
    Nat → Bool → Mutability → Option Ty → List Token →
    Option (Mutability × Option Ty × List Token)
  | 0, _, _, _, _ => none
  | _ + 1, true, m, retTy, .lbrace :: rest => some (m, retTy, rest)
  | _ + 1, false, _, _, .lbrace :: _ => none
  | fuel + 1, _, m, retTy, .ident "external" :: rest =>
    parseFuncQualifiers fuel true m retTy rest
  | fuel + 1, vis, _, retTy, .ident "pure" :: rest =>
    parseFuncQualifiers fuel vis .pure retTy rest
  | fuel + 1, vis, _, retTy, .ident "view" :: rest =>
    parseFuncQualifiers fuel vis .view retTy rest
  | fuel + 1, vis, _, retTy, .ident "payable" :: rest =>
    parseFuncQualifiers fuel vis .payable retTy rest
  | fuel + 1, vis, m, none,
    .ident "returns" :: .lparen :: .ident tyStr :: .rparen :: rest =>
    match parseTyName tyStr with
    | some ty => parseFuncQualifiers fuel vis m (some ty) rest
    | none => none
  | fuel + 1, vis, m, none,
    .ident "returns" :: .lparen :: .ident tyStr :: .ident _ :: .rparen :: rest =>
    match parseTyName tyStr with
    | some ty => parseFuncQualifiers fuel vis m (some ty) rest
    | none => none
  | _, _, _, _, _ => none

private def skipOptionalPrivate : List Token → List Token
  | .ident "private" :: rest => rest
  | .ident "internal" :: rest => rest
  | toks => toks

private def parseContractItems :
    Nat → ContractSpec → List Token → Option (ContractSpec × List Token)
  | 0, _, _ => none
  | _ + 1, spec, .rbrace :: rest => some (spec, rest)
  | fuel + 1, spec, .ident "function" :: .ident fnName :: .lparen :: rest =>
    match parseParamsAux fuel [] rest with
    | some (params, rest1) =>
      match parseFuncQualifiers fuel false .nonpayable none rest1 with
      | some (m, retTy, rest2) =>
        match parseBlockBody fuel [] rest2 with
        | some (body, rest3) =>
          let fn : FuncDecl := ⟨fnName, params, m, retTy, body⟩
          parseContractItems fuel { spec with functions := spec.functions ++ [fn] } rest3
        | none => none
      | none => none
    | none => none
  | fuel + 1, spec, .ident "constructor" :: .lparen :: .rparen :: rest =>
    if spec.ctor.isSome then none else
      let (payable, rest1) :=
        match rest with
        | .ident "payable" :: .lbrace :: r => (true, some r)
        | .lbrace :: r => (false, some r)
        | _ => (false, none)
      match rest1 with
      | some restBody =>
        match parseBlockBody fuel [] restBody with
        | some (body, rest2) =>
          parseContractItems fuel { spec with ctor := some ⟨payable, body⟩ } rest2
        | none => none
      | none => none
  | fuel + 1, spec,
    .ident "receive" :: .lparen :: .rparen :: .ident "external" :: .ident "payable" ::
      .lbrace :: .rbrace :: rest =>
    if spec.hasReceive then none
    else parseContractItems fuel { spec with hasReceive := true } rest
  | fuel + 1, spec, .ident tyStr :: rest =>
    match parseTyName tyStr with
    | none => none
    | some ty =>
      match skipOptionalPrivate rest with
      | .ident varName :: .semi :: rest' =>
        let sv : StateVar := ⟨ty, varName, none⟩
        parseContractItems fuel { spec with stateVars := spec.stateVars ++ [sv] } rest'
      | .ident varName :: .assign :: restInit =>
        match parseExpr fuel restInit with
        | some (initExpr, .semi :: rest') =>
          let sv : StateVar := ⟨ty, varName, some initExpr⟩
          parseContractItems fuel { spec with stateVars := spec.stateVars ++ [sv] } rest'
        | _ => none
      | _ => none
  | _, _, _ => none

private def skipUntilSemi : Nat → List Token → Option (List Token)
  | 0, _ => none
  | _ + 1, .semi :: rest => some rest
  | fuel + 1, _ :: rest => skipUntilSemi fuel rest
  | _, [] => none

private def parseTopContracts :
    Nat → List ContractSpec → List Token → Option (List ContractSpec)
  | 0, _, _ => none
  | _ + 1, acc, [] => some acc.reverse
  | fuel + 1, acc, .ident "pragma" :: rest =>
    match skipUntilSemi fuel rest with
    | some rest' => parseTopContracts fuel acc rest'
    | none => none
  | fuel + 1, acc, .ident "contract" :: .ident cName :: .lbrace :: rest =>
    match parseContractItems fuel { name := cName } rest with
    | some (spec, rest') => parseTopContracts fuel (spec :: acc) rest'
    | none => none
  | _, _, _ => none

/-- Parse a Solidity source file inside Lean and select the target contract
(or the unique contract when `target? = none`). -/
def parseSource (source : String) (target? : Option String := none) : Option ContractSpec := do
  let toks ← tokenize source
  let fuel := 4 * toks.length + 16
  let contracts ← parseTopContracts fuel [] toks
  match target? with
  | some name => contracts.find? (fun c => c.name == name)
  | none =>
    match contracts with
    | [c] => some c
    | _ => none

end Compiler.Validation.Solidity
