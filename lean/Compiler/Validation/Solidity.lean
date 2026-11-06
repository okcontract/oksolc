/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Primitives
import Contract.Export.Keccak
import Contract.Yul.Expression
import Contract.Evm.World

/-! In-kernel Solidity source syntax, deterministic lexer/parser, exact Solidity
binary operator precedence, tight 32-byte storage slot packing, static
well-formedness + mutability checking, Keccak-256 method selector calculation,
and executable source contract/deployment reference semantics over `Contract.Evm.World`.

Unlike external source extractors, every character of the admitted Solidity
source is tokenized, parsed, statically validated, and evaluated inside Lean. -/
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

/-- Storage width in bytes matching `src/libsolidity/ast/types.zig:storageBytes`. -/
def Ty.storageBytes : Ty → Nat
  | .bool => 1
  | .address => 20
  | .uint256 => 32
  | .bytes32 => 32

/-- ABI calldata word validity check: `uint256` and `bytes32` accept all 256-bit
words; `address` requires the upper 96 bits to be zero (`addressMask`); `bool` requires `< 2`. -/
def Ty.validWord : Ty → Word → Bool
  | .uint256 => fun _ => true
  | .bytes32 => fun _ => true
  | .address => fun w => (w &&& addressMask) == w
  | .bool => fun w => decide (w.toNat < 2)

/-- Mask/normalize an expression word to its declared value type. -/
def Ty.normalizeWord : Ty → Word → Word
  | .uint256 => id
  | .bytes32 => id
  | .address => fun w => w &&& addressMask
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

/-! ## Tight 32-Byte Storage Slot Packing -/

/-- Storage location of a value-type state variable: 256-bit `slot` index and
low-order `byteOffset` (`0 .. 31`) within that slot. -/
structure StorageEntry where
  name : String
  ty : Ty
  slot : Nat
  byteOffset : Nat
  deriving DecidableEq, Repr, Inhabited

private def computeStorageLayoutAux (slot byteOffset : Nat) :
    List StateVar → List StorageEntry × Nat
  | [] =>
    let totalSlots := if byteOffset > 0 then slot + 1 else slot
    ([], totalSlots)
  | v :: vs =>
    let bytes := v.ty.storageBytes
    let (curSlot, curOff) :=
      if byteOffset + bytes > 32 then (slot + 1, 0) else (slot, byteOffset)
    let entry : StorageEntry := ⟨v.name, v.ty, curSlot, curOff⟩
    let (nextSlot, nextOff) :=
      if curOff + bytes ≤ 32 then (curSlot, curOff + bytes) else (curSlot + 1, 0)
    let (rest, totalSlots) := computeStorageLayoutAux nextSlot nextOff vs
    (entry :: rest, totalSlots)

/-- Compute packed `(slot, byteOffset)` entries and total allocated storage slot
count matching `src/libsolidity/ast/types.zig:computeStorageOffsetsAlloc`. -/
def ContractSpec.storageLayoutWithSize (spec : ContractSpec) : List StorageEntry × Nat :=
  computeStorageLayoutAux 0 0 spec.stateVars

def ContractSpec.storageLayout (spec : ContractSpec) : List StorageEntry :=
  spec.storageLayoutWithSize.1

def ContractSpec.storageSlotCount (spec : ContractSpec) : Nat :=
  spec.storageLayoutWithSize.2

def ContractSpec.findStorageVar (spec : ContractSpec) (name : String) : Option StorageEntry :=
  spec.storageLayout.find? (fun e => e.name == name)

/-- Low-order mask covering `numBytes` bytes (`0..32`). -/
def storageByteMask (numBytes : Nat) : Word :=
  if numBytes ≥ 32 then maxWord
  else (1#256 <<< (8 * numBytes)) - 1#256

/-- Extract and clean a packed state variable from `storage`, matching
`extract_from_storage_value_offset_*` + `cleanup_from_storage_*` in
`yul_util_functions.zig` (first mask to `storageBytes`, then normalize for the value type). -/
def readPackedVar (storage : Slots) (entry : StorageEntry) : Word :=
  let raw := storage (BitVec.ofNat 256 entry.slot)
  let shifted := raw >>> (8 * entry.byteOffset)
  let masked := shifted &&& storageByteMask entry.ty.storageBytes
  entry.ty.normalizeWord masked

/-- Read-modify-write bitfield update of a packed state variable in `storage`, matching
`update_byte_slice_*` in `yul_util_functions.zig`. -/
def writePackedVar (storage : Slots) (entry : StorageEntry) (val : Word) : Slots :=
  let key := BitVec.ofNat 256 entry.slot
  let cleaned := entry.ty.normalizeWord val
  let shiftBits := 8 * entry.byteOffset
  let mask := storageByteMask entry.ty.storageBytes <<< shiftBits
  let oldSlot := storage key
  let newSlot := (oldSlot &&& ~~~mask) ||| ((cleaned <<< shiftBits) &&& mask)
  writeSlot storage key newSlot

def findParamAux (name : String) (idx : Nat) : List Param → Option (Nat × Ty)
  | [] => none
  | p :: ps => if p.name == name then some (idx, p.ty) else findParamAux name (idx + 1) ps

/-! ## Static Well-Formedness & Mutability Checker -/

/-- Check expression scope and state/environment read permissions (`allowsRead` is
`false` for `pure`, `true` for `view` / `nonpayable` / `payable`). -/
def checkExprWF (stateNames paramNames : List String) (allowsRead : Bool) : Expr → Bool
  | .lit _ | .boolLit _ => true
  | .var name =>
    if paramNames.contains name then true
    else if stateNames.contains name then allowsRead
    else false
  | .cast _ arg => checkExprWF stateNames paramNames allowsRead arg
  | .msgSender | .msgValue | .addressThis | .txOrigin | .blockCoinbase => allowsRead
  | .unary _ arg => checkExprWF stateNames paramNames allowsRead arg
  | .binary _ lhs rhs =>
    checkExprWF stateNames paramNames allowsRead lhs &&
    checkExprWF stateNames paramNames allowsRead rhs

def checkStmtWF (stateNames paramNames : List String) (mutability : Mutability)
    (retTy : Option Ty) : Nat → Stmt → Bool
  | 0, _ => false
  | _ + 1, .assign slotName rhs =>
    mutability.allowsWrite &&
    !paramNames.contains slotName &&
    stateNames.contains slotName &&
    checkExprWF stateNames paramNames mutability.allowsRead rhs
  | _ + 1, .returnVoid => retTy.isNone
  | _ + 1, .returnVal expr =>
    retTy.isSome && checkExprWF stateNames paramNames mutability.allowsRead expr
  | depth + 1, .uncheckedBlock body =>
    checkStmtsWFAux (checkStmtWF stateNames paramNames mutability retTy depth) body
  | depth + 1, .ifElse cond thenBody elseBody =>
    checkExprWF stateNames paramNames mutability.allowsRead cond &&
    checkStmtsWFAux (checkStmtWF stateNames paramNames mutability retTy depth) thenBody &&
    checkStmtsWFAux (checkStmtWF stateNames paramNames mutability retTy depth) elseBody
where
  checkStmtsWFAux (checkOne : Stmt → Bool) : List Stmt → Bool
    | [] => true
    | s :: ss => checkOne s && checkStmtsWFAux checkOne ss

def checkStmtsWF (stateNames paramNames : List String) (mutability : Mutability)
    (retTy : Option Ty) (depth : Nat) : List Stmt → Bool
  | [] => true
  | s :: ss =>
    checkStmtWF stateNames paramNames mutability retTy depth s &&
    checkStmtsWF stateNames paramNames mutability retTy depth ss

private def checkStateInitsWF (allStateNames : List String) :
    List String → List StateVar → Bool
  | _, [] => true
  | seenNames, v :: vs =>
    let initOk := match v.init with
      | none => true
      | some expr => checkExprWF seenNames [] true expr
    !allStateNames.isEmpty && initOk && checkStateInitsWF allStateNames (seenNames ++ [v.name]) vs

private def hasUniqueStrings : List String → Bool
  | [] => true
  | x :: xs => !xs.contains x && hasUniqueStrings xs

private def hasUniqueByteLists : List (List UInt8) → Bool
  | [] => true
  | x :: xs => !xs.contains x && hasUniqueByteLists xs

private def checkFuncWF (stateNames : List String) (fn : FuncDecl) : Bool :=
  let paramNames := fn.params.map Param.name
  hasUniqueStrings paramNames &&
  paramNames.all (fun n => !stateNames.contains n) &&
  checkStmtsWF stateNames paramNames fn.mutability fn.returnTy 64 fn.body

/-- Static contract well-formedness check enforced by both `parseSource` and
evaluation entrypoints:
1. State variable names are pairwise distinct.
2. State variable initializers reference only previously declared state variables.
3. Constructor body (if present) obeys nonpayable/payable write/read rules and returns void.
4. Function signatures and 4-byte selectors are pairwise distinct.
5. Each function has unique parameter names, no parameter/state-variable shadowing,
   mutability-sound reads/writes (`pure` forbids state & env reads and state writes;
   `view` forbids state writes), and return statements matching `returnTy`. -/
def ContractSpec.wellFormed (spec : ContractSpec) : Bool :=
  let stateNames := spec.stateVars.map StateVar.name
  let stateUnique := hasUniqueStrings stateNames
  let initsOk :=
    if spec.stateVars.isEmpty then true
    else checkStateInitsWF stateNames [] spec.stateVars
  let ctorOk := match spec.ctor with
    | none => true
    | some c =>
      let m : Mutability := if c.payable then .payable else .nonpayable
      checkStmtsWF stateNames [] m none 64 c.body
  let sigsUnique := hasUniqueStrings (spec.functions.map FuncDecl.signature)
  let selsUnique := hasUniqueByteLists (spec.functions.map FuncDecl.selectorBytes)
  let funcsOk := spec.functions.all (checkFuncWF stateNames)
  stateUnique && initsOk && ctorOk && sigsUnique && selsUnique && funcsOk

/-! ## Executable Source Reference Semantics -/

inductive EvalOutcome (α : Type) where
  | ok (val : α)
  | revert (bytes : List UInt8)
  | invalidSource
  deriving DecidableEq, Repr

/-- Source expression evaluation under `checked` / `unchecked` Solidity 0.8 arithmetic
and mutability `allowsRead` enforcement. -/
def evalExpr (spec : ContractSpec) (params : List Param) (allowsRead checked : Bool)
    (ctx : Context) (input : Input) (storage : Slots) : Expr → EvalOutcome Word
  | .lit w => .ok w
  | .boolLit b => .ok (boolWord b)
  | .var name =>
    match findParamAux name 0 params with
    | some (idx, ty) =>
      .ok (ty.normalizeWord (loadWord input.calldata (4 + 32 * idx)))
    | none =>
      if !allowsRead then .invalidSource
      else match spec.findStorageVar name with
        | some entry => .ok (readPackedVar storage entry)
        | none => .invalidSource
  | .cast ty arg =>
    match evalExpr spec params allowsRead checked ctx input storage arg with
    | .ok w => .ok (ty.normalizeWord w)
    | other => other
  | .msgSender => if allowsRead then .ok ctx.caller.toWord else .invalidSource
  | .msgValue => if allowsRead then .ok input.value else .invalidSource
  | .addressThis => if allowsRead then .ok ctx.self.toWord else .invalidSource
  | .txOrigin => if allowsRead then .ok ctx.origin.toWord else .invalidSource
  | .blockCoinbase => if allowsRead then .ok ctx.coinbase.toWord else .invalidSource
  | .unary op arg =>
    match evalExpr spec params allowsRead checked ctx input storage arg with
    | .ok w =>
      match op with
      | .bitNot => .ok (~~~w)
      | .lnot => .ok (boolWord (w == 0#256))
    | other => other
  | .binary .land lhs rhs =>
    match evalExpr spec params allowsRead checked ctx input storage lhs with
    | .ok a =>
      if a == 0#256 then .ok 0#256
      else match evalExpr spec params allowsRead checked ctx input storage rhs with
        | .ok b => .ok (boolWord (b != 0#256))
        | other => other
    | other => other
  | .binary .lor lhs rhs =>
    match evalExpr spec params allowsRead checked ctx input storage lhs with
    | .ok a =>
      if a != 0#256 then .ok 1#256
      else match evalExpr spec params allowsRead checked ctx input storage rhs with
        | .ok b => .ok (boolWord (b != 0#256))
        | other => other
    | other => other
  | .binary op lhs rhs =>
    match evalExpr spec params allowsRead checked ctx input storage lhs with
    | .revert r => .revert r
    | .invalidSource => .invalidSource
    | .ok a =>
      match evalExpr spec params allowsRead checked ctx input storage rhs with
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

def evalStmtAux (spec : ContractSpec) (params : List Param) (mutability : Mutability)
    (retTy : Option Ty) (ctx : Context) (input : Input) : Nat → Bool → Slots → Stmt → StmtStep
  | 0, _, _, _ => .invalidSource
  | _ + 1, checked, storage, .assign slotName rhs =>
    if !mutability.allowsWrite then .invalidSource
    else match spec.findStorageVar slotName with
      | none => .invalidSource
      | some entry =>
        match evalExpr spec params mutability.allowsRead checked ctx input storage rhs with
        | .ok val => .cont (writePackedVar storage entry val)
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
      match evalExpr spec params mutability.allowsRead checked ctx input storage expr with
      | .ok val => .returned (wordBytes (ty.normalizeWord val)) storage
      | .revert r => .reverted r
      | .invalidSource => .invalidSource
  | depth + 1, _, storage, .uncheckedBlock body =>
    evalStmtsWith (evalStmtAux spec params mutability retTy ctx input depth) false storage body
  | depth + 1, checked, storage, .ifElse cond thenBody elseBody =>
    match evalExpr spec params mutability.allowsRead checked ctx input storage cond with
    | .ok val =>
      if val != 0#256 then
        evalStmtsWith (evalStmtAux spec params mutability retTy ctx input depth) checked storage thenBody
      else
        evalStmtsWith (evalStmtAux spec params mutability retTy ctx input depth) checked storage elseBody
    | .revert r => .reverted r
    | .invalidSource => .invalidSource

def evalStmts (spec : ContractSpec) (params : List Param) (mutability : Mutability)
    (retTy : Option Ty) (checked : Bool) (ctx : Context) (input : Input)
    (storage : Slots) (stmts : List Stmt) : StmtStep :=
  evalStmtsWith (evalStmtAux spec params mutability retTy ctx input 64) checked storage stmts

def checkAbiParams (calldata : List UInt8) : Nat → List Param → Bool
  | _, [] => true
  | idx, p :: ps =>
    p.ty.validWord (loadWord calldata (4 + 32 * idx)) && checkAbiParams calldata (idx + 1) ps

/-- Source-level ABI dispatch + execution for a Solidity contract at runtime. -/
def evalRuntime (spec : ContractSpec) (ctx : Context) (input : Input) (storage : Slots) :
    Option (Halt × Slots) :=
  if !spec.wellFormed then
    none
  else if input.calldata.isEmpty && spec.hasReceive then
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
        match evalStmts spec fn.params fn.mutability fn.returnTy true ctx input storage fn.body with
        | .returned bytes storage' => some (.returned bytes, storage')
        | .cont storage' =>
          match fn.returnTy with
          | none => some (.returned [], storage')
          | some ty => some (.returned (wordBytes (ty.normalizeWord 0#256)), storage')
        | .reverted bytes => some (.reverted bytes, storage)
        | .invalidSource => none

def evalStateInits (spec : ContractSpec) (ctx : Context) (input : Input)
    (storage : Slots) : List StateVar → StmtStep
  | [] => .cont storage
  | v :: vs =>
    match v.init with
    | none => evalStateInits spec ctx input storage vs
    | some expr =>
      match spec.findStorageVar v.name with
      | none => .invalidSource
      | some entry =>
        match evalExpr spec [] true true ctx input storage expr with
        | .ok val =>
          let storage' := writePackedVar storage entry val
          evalStateInits spec ctx input storage' vs
        | .revert bytes => .reverted bytes
        | .invalidSource => .invalidSource

/-- Source-level constructor + packed state-variable initialization semantics. -/
def evalDeployment (spec : ContractSpec) (runtimeBytes : List UInt8)
    (ctx : Context) (input : Input) (storage : Slots) : Option (Halt × Slots) :=
  if !spec.wellFormed then
    none
  else
    let ctorPayable := match spec.ctor with | some c => c.payable | none => false
    if !ctorPayable && input.value != 0#256 then
      some (.reverted [], storage)
    else
      match evalStateInits spec ctx input storage spec.stateVars with
      | .reverted bytes => some (.reverted bytes, storage)
      | .invalidSource | .returned _ _ => none
      | .cont storageAfterInit =>
        let ctorMut : Mutability := if ctorPayable then .payable else .nonpayable
        let ctorBody := match spec.ctor with | some c => c.body | none => []
        match evalStmts spec [] ctorMut none true ctx input storageAfterInit ctorBody with
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

private def isAsciiAlpha (c : Char) : Bool :=
  (65 ≤ c.val && c.val ≤ 90) || (97 ≤ c.val && c.val ≤ 122)

private def isAsciiDigit (c : Char) : Bool :=
  48 ≤ c.val && c.val ≤ 57

private def isAsciiAlphanum (c : Char) : Bool :=
  isAsciiAlpha c || isAsciiDigit c

private def isAsciiSpace (c : Char) : Bool :=
  c == ' ' || c == '\n' || c == '\r' || c == '\t'

private def isIdentStart (c : Char) : Bool :=
  isAsciiAlpha c || c == '_' || c == '$'

private def isIdentCont (c : Char) : Bool :=
  isAsciiAlphanum c || c == '_' || c == '$'

private def hexDigitVal (c : Char) : Option Nat :=
  if 48 ≤ c.val && c.val ≤ 57 then some (c.toNat - 48)
  else if 97 ≤ c.val && c.val ≤ 102 then some (10 + c.toNat - 97)
  else if 65 ≤ c.val && c.val ≤ 70 then some (10 + c.toNat - 65)
  else none

private def parseDecChars : List Char → Nat → Option Nat
  | [], acc => some acc
  | '_' :: cs, acc => parseDecChars cs acc
  | c :: cs, acc =>
    if isAsciiDigit c then parseDecChars cs (acc * 10 + (c.toNat - 48))
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
    if isAsciiSpace c then
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
    else if isAsciiDigit c then
      let (numChars, rest) := takeWhileAux (fun ch => isAsciiAlphanum ch || ch == '_') [c] cs
      match parseNumberToken numChars with
      | some n =>
        if Nat.ble (Nat.shiftRight n 256) 0 then tokenizeAux fuel rest (.num n :: acc) else none
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

/-- Parse a Solidity expression using the exact binary precedence hierarchy from
`src/liblangutil/token.zig:precedence`:
`pUnary` → `* / %` (13) → `+ -` (12) → `<< >>` (11) → `&` (10) → `^` (9) →
`|` (8) → `< <= > >=` (7) → `== !=` (6) → `&&` (5) → `||` (4). -/
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
    let pBitAnd := mkLeftAssoc opFuel pShift (fun | .amp => some .bitAnd | _ => none)
    let pBitXor := mkLeftAssoc opFuel pBitAnd (fun | .caret => some .bitXor | _ => none)
    let pBitOr := mkLeftAssoc opFuel pBitXor (fun | .pipe => some .bitOr | _ => none)
    let pRel := mkLeftAssoc opFuel pBitOr (fun
      | .lt => some .lt | .le => some .le | .gt => some .gt | .ge => some .ge | _ => none)
    let pEq := mkLeftAssoc opFuel pRel (fun
      | .eqeq => some .eq | .neq => some .ne | _ => none)
    let pLand := mkLeftAssoc opFuel pEq (fun | .ampamp => some .land | _ => none)
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
    Nat → Bool → Option Mutability → Option Ty → List Token →
    Option (Mutability × Option Ty × List Token)
  | 0, _, _, _, _ => none
  | _ + 1, true, m?, retTy, .lbrace :: rest =>
    some (m?.getD .nonpayable, retTy, rest)
  | _ + 1, false, _, _, .lbrace :: _ => none
  | fuel + 1, false, m?, retTy, .ident "external" :: rest =>
    parseFuncQualifiers fuel true m? retTy rest
  | fuel + 1, vis, none, retTy, .ident "pure" :: rest =>
    parseFuncQualifiers fuel vis (some .pure) retTy rest
  | fuel + 1, vis, none, retTy, .ident "view" :: rest =>
    parseFuncQualifiers fuel vis (some .view) retTy rest
  | fuel + 1, vis, none, retTy, .ident "payable" :: rest =>
    parseFuncQualifiers fuel vis (some .payable) retTy rest
  | fuel + 1, vis, m?, none,
    .ident "returns" :: .lparen :: .ident tyStr :: .rparen :: rest =>
    match parseTyName tyStr with
    | some ty => parseFuncQualifiers fuel vis m? (some ty) rest
    | none => none
  | fuel + 1, vis, m?, none,
    .ident "returns" :: .lparen :: .ident tyStr :: .ident _ :: .rparen :: rest =>
    match parseTyName tyStr with
    | some ty => parseFuncQualifiers fuel vis m? (some ty) rest
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
      match parseFuncQualifiers fuel false none none rest1 with
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

/-- Parse a Solidity source file inside Lean, enforce pairwise unique contract names
and static well-formedness (`ContractSpec.wellFormed`), and select the target contract
(or the unique contract when `target? = none`). -/
def parseSource (source : String) (target? : Option String := none) : Option ContractSpec :=
  match tokenize source with
  | none => none
  | some toks =>
    let fuel := 4 * toks.length + 16
    match parseTopContracts fuel [] toks with
    | none => none
    | some contracts =>
      if !hasUniqueStrings (contracts.map ContractSpec.name) then none
      else
        let selected? := match target? with
          | some name => contracts.find? (fun (c : ContractSpec) => c.name == name)
          | none =>
            match contracts with
            | [c] => some c
            | _ => none
        match selected? with
        | some selected => if selected.wellFormed then some selected else none
        | none => none

end Compiler.Validation.Solidity
