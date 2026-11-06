/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Hex
import Compiler.Validation.GraphFailure
import Compiler.Validation.WordBlock
import Compiler.Validation.Bytecode

/-! `oksolc-verify`: Self-contained Lean 4 CLI validator for `oksolc` artifacts.

Supports four verification modes:
- `graph <request.json> <response.json>`
- `graph-failure <request.json> <response.json>`
- `word <request.json> <response.json>`
- `standard-json <request.json> <response.json>`

Includes an in-Lean FIPS 180-4 SHA-256 implementation and RFC 8259 JSON parser so
cryptographic request/response binding, Solidity source parsing, Keccak-256 selector
derivation, DAG/cache equivalence, OOM-sweep certification, and Cancun EVM execution
checks all happen inside Lean with zero external Python/jq preprocessing. -/
namespace Compiler.Validation.Cli
open Contract Contract.Yul

/-! ## FIPS 180-4 SHA-256 -/

namespace Sha256

private def kTable : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

private def rotr (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

private def ch (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ ((~~~x) &&& z)

private def maj (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

private def bigSigma0 (x : UInt32) : UInt32 :=
  rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22

private def bigSigma1 (x : UInt32) : UInt32 :=
  rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25

private def smallSigma0 (x : UInt32) : UInt32 :=
  rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)

private def smallSigma1 (x : UInt32) : UInt32 :=
  rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

private def byteAt (bytes : ByteArray) (off : Nat) : UInt8 :=
  bytes[off]?.getD 0

private def readBe32 (bytes : ByteArray) (off : Nat) : UInt32 :=
  let b0 := (byteAt bytes off).toUInt32
  let b1 := (byteAt bytes (off + 1)).toUInt32
  let b2 := (byteAt bytes (off + 2)).toUInt32
  let b3 := (byteAt bytes (off + 3)).toUInt32
  (b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3

private def padMessage (msg : ByteArray) : ByteArray := Id.run do
  let bitLen : UInt64 := msg.size.toUInt64 * 8
  let mut out := msg.push 0x80
  while out.size % 64 != 56 do
    out := out.push 0x00
  for i in [0:8] do
    let shift : UInt64 := (7 - i).toUInt64 * 8
    out := out.push ((bitLen >>> shift) &&& 0xff).toUInt8
  return out

private def compressBlock (state : Array UInt32) (padded : ByteArray) (blockOff : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.mkEmpty 64
  for i in [0:16] do
    w := w.push (readBe32 padded (blockOff + i * 4))
  for i in [16:64] do
    let s0 := smallSigma0 (w.getD (i - 15) 0)
    let s1 := smallSigma1 (w.getD (i - 2) 0)
    let wi := (w.getD (i - 16) 0) + s0 + (w.getD (i - 7) 0) + s1
    w := w.push wi
  let mut a := state.getD 0 0
  let mut b := state.getD 1 0
  let mut c := state.getD 2 0
  let mut d := state.getD 3 0
  let mut e := state.getD 4 0
  let mut f := state.getD 5 0
  let mut g := state.getD 6 0
  let mut h := state.getD 7 0
  for i in [0:64] do
    let t1 := h + bigSigma1 e + ch e f g + kTable.getD i 0 + w.getD i 0
    let t2 := bigSigma0 a + maj a b c
    h := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  return #[
    state.getD 0 0 + a, state.getD 1 0 + b, state.getD 2 0 + c, state.getD 3 0 + d,
    state.getD 4 0 + e, state.getD 5 0 + f, state.getD 6 0 + g, state.getD 7 0 + h
  ]

private def hexDigit (n : UInt32) : Char :=
  let v := (n &&& 0xf).toNat
  if v < 10 then Char.ofNat ('0'.toNat + v)
  else Char.ofNat ('a'.toNat + (v - 10))

def hexDigest (msg : ByteArray) : String := Id.run do
  let padded := padMessage msg
  let blocks := padded.size / 64
  let mut state : Array UInt32 := #[
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
  ]
  for b in [0:blocks] do
    state := compressBlock state padded (b * 64)
  let mut chars : List Char := []
  for i in [0:8] do
    let word := state.getD i 0
    for nib in [0:8] do
      let shift : UInt32 := (7 - nib).toUInt32 * 4
      chars := hexDigit (word >>> shift) :: chars
  return String.ofList chars.reverse

end Sha256

/-! ## Minimal RFC 8259 JSON AST & Parser -/

inductive JsonVal where
  | null
  | bool (b : Bool)
  | num (n : Nat)
  | str (s : String)
  | arr (items : List JsonVal)
  | obj (fields : List (String × JsonVal))
  deriving Repr

namespace JsonVal

def field? (j : JsonVal) (key : String) : Option JsonVal :=
  match j with
  | .obj fields => (fields.find? (fun p => p.1 == key)).map Prod.snd
  | _ => none

def asStr? : JsonVal → Option String
  | .str s => some s
  | _ => none

def asNat? : JsonVal → Option Nat
  | .num n => some n
  | _ => none

def asBool? : JsonVal → Option Bool
  | .bool b => some b
  | _ => none

def asArr? : JsonVal → Option (List JsonVal)
  | .arr items => some items
  | _ => none

def asObj? : JsonVal → Option (List (String × JsonVal))
  | .obj fields => some fields
  | _ => none

end JsonVal

namespace JsonParser

private def isWs (c : Char) : Bool :=
  c == ' ' || c == '\n' || c == '\r' || c == '\t'

private def skipWs : List Char → List Char
  | [] => []
  | c :: cs => if isWs c then skipWs cs else c :: cs

private def parseHex4? : List Char → Option (Nat × List Char)
  | h1 :: h2 :: h3 :: h4 :: rest => do
    let d1 ← Contract.Hex.charNibble? h1
    let d2 ← Contract.Hex.charNibble? h2
    let d3 ← Contract.Hex.charNibble? h3
    let d4 ← Contract.Hex.charNibble? h4
    some (((d1 * 16 + d2) * 16 + d3) * 16 + d4, rest)
  | _ => none

/-- RFC 8259 §7 JSON string decoder: decodes UTF-16 surrogate pairs
(`0xD800..0xDBFF` followed immediately by `\u` + `0xDC00..0xDFFF`) into their
supplementary Unicode scalar value and rejects lone UTF-16 surrogates (`0xD800..0xDFFF`). -/
private def parseStringChars : Nat → List Char → List Char → Option (String × List Char)
  | 0, _, _ => none
  | _ + 1, _, [] => none
  | _ + 1, acc, '"' :: rest => some (String.ofList acc.reverse, rest)
  | fuel + 1, acc, '\\' :: esc :: rest =>
    match esc with
    | '"' => parseStringChars fuel ('"' :: acc) rest
    | '\\' => parseStringChars fuel ('\\' :: acc) rest
    | '/' => parseStringChars fuel ('/' :: acc) rest
    | 'b' => parseStringChars fuel (Char.ofNat 8 :: acc) rest
    | 'f' => parseStringChars fuel (Char.ofNat 12 :: acc) rest
    | 'n' => parseStringChars fuel ('\n' :: acc) rest
    | 'r' => parseStringChars fuel ('\r' :: acc) rest
    | 't' => parseStringChars fuel ('\t' :: acc) rest
    | 'u' => do
      let (code, rest') ← parseHex4? rest
      if 0xD800 ≤ code && code ≤ 0xDBFF then
        match rest' with
        | '\\' :: 'u' :: rest2 => do
          let (low, rest3) ← parseHex4? rest2
          if 0xDC00 ≤ low && low ≤ 0xDFFF then
            let scalar := 0x10000 + (code - 0xD800) * 1024 + (low - 0xDC00)
            parseStringChars fuel (Char.ofNat scalar :: acc) rest3
          else none
        | _ => none
      else if 0xDC00 ≤ code && code ≤ 0xDFFF then
        none
      else
        parseStringChars fuel (Char.ofNat code :: acc) rest'
    | _ => none
  | fuel + 1, acc, c :: rest =>
    if c.toNat < 0x20 then none
    else parseStringChars fuel (c :: acc) rest

private def parseNatLit : List Char → Option (Nat × List Char)
  | '0' :: c :: cs =>
    if '0' ≤ c && c ≤ '9' then none else some (0, c :: cs)
  | '0' :: [] => some (0, [])
  | c :: cs =>
    if '1' ≤ c && c ≤ '9' then
      let rec loop (acc : Nat) : List Char → (Nat × List Char)
        | d :: ds =>
          if '0' ≤ d && d ≤ '9' then loop (acc * 10 + (d.toNat - '0'.toNat)) ds
          else (acc, d :: ds)
        | [] => (acc, [])
      some (loop (c.toNat - '0'.toNat) cs)
    else none
  | [] => none

private def parseArrAux (parseElem : List Char → Option (JsonVal × List Char)) :
    Nat → List JsonVal → List Char → Option (List JsonVal × List Char)
  | 0, _, _ => none
  | fuel + 1, acc, cs =>
    match parseElem (skipWs cs) with
    | none => none
    | some (v, rest) =>
      match skipWs rest with
      | ']' :: rest' => some ((v :: acc).reverse, rest')
      | ',' :: rest' => parseArrAux parseElem fuel (v :: acc) rest'
      | _ => none

private def parseObjAux (parseElem : List Char → Option (JsonVal × List Char)) :
    Nat → List (String × JsonVal) → List Char → Option (List (String × JsonVal) × List Char)
  | 0, _, _ => none
  | fuel + 1, acc, cs =>
    match skipWs cs with
    | '"' :: restKey =>
      match parseStringChars (restKey.length + 1) [] restKey with
      | none => none
      | some (key, afterKey) =>
        match skipWs afterKey with
        | ':' :: restVal =>
          match parseElem (skipWs restVal) with
          | none => none
          | some (v, afterVal) =>
            if acc.any (fun p => p.1 == key) then none
            else
              match skipWs afterVal with
              | '}' :: rest' => some (((key, v) :: acc).reverse, rest')
              | ',' :: rest' => parseObjAux parseElem fuel ((key, v) :: acc) rest'
              | _ => none
        | _ => none
    | _ => none

def parseValue : Nat → List Char → Option (JsonVal × List Char)
  | 0, _ => none
  | depth + 1, cs =>
    match skipWs cs with
    | 'n' :: 'u' :: 'l' :: 'l' :: rest => some (.null, rest)
    | 't' :: 'r' :: 'u' :: 'e' :: rest => some (.bool true, rest)
    | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest => some (.bool false, rest)
    | '"' :: rest => do
      let (s, rest') ← parseStringChars (rest.length + 1) [] rest
      return (.str s, rest')
    | '[' :: rest =>
      match skipWs rest with
      | ']' :: rest' => some (.arr [], rest')
      | rest' => do
        let (items, afterArr) ← parseArrAux (parseValue depth) (rest'.length + 1) [] rest'
        return (.arr items, afterArr)
    | '{' :: rest =>
      match skipWs rest with
      | '}' :: rest' => some (.obj [], rest')
      | rest' => do
        let (fields, afterObj) ← parseObjAux (parseValue depth) (rest'.length + 1) [] rest'
        return (.obj fields, afterObj)
    | rest => do
      let (n, rest') ← parseNatLit rest
      return (.num n, rest')

def parse (text : String) : Option JsonVal := do
  let chars := text.toList
  let (val, rem) ← parseValue (chars.length + 2) chars
  if (skipWs rem).isEmpty then some val else none

def escapeJsonString (s : String) : String :=
  let step (acc : List Char) (c : Char) : List Char :=
    match c with
    | '"' => '"' :: '\\' :: acc
    | '\\' => '\\' :: '\\' :: acc
    | '\n' => 'n' :: '\\' :: acc
    | '\r' => 'r' :: '\\' :: acc
    | '\t' => 't' :: '\\' :: acc
    | _ =>
      if c.toNat == 0x08 then 'b' :: '\\' :: acc
      else if c.toNat == 0x0c then 'f' :: '\\' :: acc
      else if c.toNat < 0x20 then
        let b := UInt8.ofNat c.toNat
        let hi := Contract.Hex.nibbleChar (b >>> (4 : UInt8))
        let lo := Contract.Hex.nibbleChar (b &&& (0x0f : UInt8))
        lo :: hi :: '0' :: '0' :: 'u' :: '\\' :: acc
      else c :: acc
  String.ofList ((s.toList.foldl step []).reverse)

end JsonParser

/-! ## Decimal and Identifier Parsers -/

def parseDecimalWordLiteral? (s : String) : Option Nat := do
  let chars := s.toList
  match chars with
  | [] => none
  | ['0'] => some 0
  | '0' :: _ => none
  | c :: cs =>
    if !('1' ≤ c && c ≤ '9') then none
    else
      let mut acc : Nat := c.toNat - '0'.toNat
      for d in cs do
        if !('0' ≤ d && d ≤ '9') then Option.none
        acc := acc * 10 + (d.toNat - '0'.toNat)
      if acc < 2 ^ 256 then some acc else none

def validGraphName (s : String) : Bool :=
  let cs := s.toList
  !cs.isEmpty && cs.length ≤ 64 &&
    cs.all fun c =>
      ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || ('0' ≤ c && c ≤ '9') || c == '_' || c == '$'

/-! ## Graph & Word Node Decoders -/

def decodeNullary? : String → Option Nullary
  | "address" => some .address
  | "caller" => some .caller
  | "origin" => some .origin
  | "coinbase" => some .coinbase
  | _ => none

def decodeUnary? : String → Option Unary
  | "bitnot" => some .bitnot
  | "iszero" => some .iszero
  | _ => none

def decodeBinary? : String → Option Binary
  | "add" => some .add
  | "sub" => some .sub
  | "mul" => some .mul
  | "div" => some .div
  | "sdiv" => some .sdiv
  | "mod" => some .mod
  | "smod" => some .smod
  | "exp" => some .exp
  | "signextend" => some .signextend
  | "and" => some .and
  | "or" => some .or
  | "xor" => some .xor
  | "byte" => some .byte
  | "shl" => some .shl
  | "shr" => some .shr
  | "sar" => some .sar
  | "lt" => some .lt
  | "gt" => some .gt
  | "slt" => some .slt
  | "sgt" => some .sgt
  | "eq" => some .eq
  | _ => none

def decodeTernary? : String → Option Ternary
  | "addmod" => some .addmod
  | "mulmod" => some .mulmod
  | _ => none

def decodeNode? (j : JsonVal) : Option Node := do
  let fields ← j.asObj?
  match fields with
  | [("input", v)] =>
    let name ← v.asStr?
    if validGraphName name then some (.input name) else none
  | [("literal", v)] =>
    let litStr ← v.asStr?
    let n ← parseDecimalWordLiteral? litStr
    some (.literal n)
  | [("nullary", v)] =>
    let opStr ← v.asStr?
    let op ← decodeNullary? opStr
    some (.nullary op)
  | [("unary", v)] =>
    let op ← (← v.field? "op") >>= JsonVal.asStr? >>= decodeUnary?
    let arg ← (← v.field? "arg") >>= JsonVal.asNat?
    if (← v.asObj?).length == 2 then some (.unary op arg) else none
  | [("binary", v)] =>
    let op ← (← v.field? "op") >>= JsonVal.asStr? >>= decodeBinary?
    let left ← (← v.field? "left") >>= JsonVal.asNat?
    let right ← (← v.field? "right") >>= JsonVal.asNat?
    if (← v.asObj?).length == 3 then some (.binary op left right) else none
  | [("ternary", v)] =>
    let op ← (← v.field? "op") >>= JsonVal.asStr? >>= decodeTernary?
    let first ← (← v.field? "first") >>= JsonVal.asNat?
    let second ← (← v.field? "second") >>= JsonVal.asNat?
    let third ← (← v.field? "third") >>= JsonVal.asNat?
    if (← v.asObj?).length == 4 then some (.ternary op first second third) else none
  | _ => none

def decodeNodes? (j : JsonVal) : Option (List Node) := do
  let arr ← j.asArr?
  if arr.isEmpty || arr.length > 512 then none
  else arr.mapM decodeNode?

def decodeNatList? (j : JsonVal) : Option (List Nat) := do
  let arr ← j.asArr?
  arr.mapM JsonVal.asNat?

def decodeStrList? (j : JsonVal) : Option (List String) := do
  let arr ← j.asArr?
  arr.mapM JsonVal.asStr?

def decodeCacheEntry? (j : JsonVal) : Option Inventory.Entry := do
  let fields ← j.asObj?
  if fields.length != 2 then none
  else
    let key ← (← j.field? "key") |> decodeNode?
    let id ← (← j.field? "id") >>= JsonVal.asNat?
    some ⟨key, id⟩

def decodeCache? (j : JsonVal) : Option (List Inventory.Entry) := do
  let arr ← j.asArr?
  if arr.length > 2048 then none
  else arr.mapM decodeCacheEntry?

/-! ## Mode 1: `graph` Validator -/

def verifyGraph (reqBytes : ByteArray) (reqJson respJson : JsonVal) : Except String String := do
  let reqFields ← (reqJson.asObj?).elim (.error "request must be JSON object") .ok
  if reqFields.length != 3 then .error "unexpected fields in graph request"
  let reqSchema ← (reqJson.field? "schema" >>= JsonVal.asStr?).elim (.error "missing request schema") .ok
  if reqSchema != "oksolc.compiler-graph-request.v1" then
    .error s!"unsupported graph request schema: {reqSchema}"
  let before ← (reqJson.field? "nodes" >>= decodeNodes?).elim (.error "invalid source graph nodes") .ok
  let beforeRoot ← (reqJson.field? "root" >>= JsonVal.asNat?).elim (.error "invalid source root") .ok

  let respFields ← (respJson.asObj?).elim (.error "response must be JSON object") .ok
  if respFields.length != 6 then .error "unexpected fields in graph response"
  let respSchema ← (respJson.field? "schema" >>= JsonVal.asStr?).elim (.error "missing response schema") .ok
  if respSchema != "oksolc.compiler-graph-response.v1" then
    .error s!"unsupported graph response schema: {respSchema}"
  let respSha ← (respJson.field? "requestSha256" >>= JsonVal.asStr?).elim (.error "missing requestSha256") .ok
  let expectedSha := Sha256.hexDigest reqBytes
  if respSha != expectedSha then
    .error s!"requestSha256 mismatch: expected {expectedSha}, got {respSha}"

  let after ← (respJson.field? "nodes" >>= decodeNodes?).elim (.error "invalid optimized graph nodes") .ok
  let afterRoot ← (respJson.field? "root" >>= JsonVal.asNat?).elim (.error "invalid optimized root") .ok
  let resultIds ← (respJson.field? "resultIds" >>= decodeNatList?).elim (.error "invalid resultIds") .ok
  let cache ← (respJson.field? "cache" >>= decodeCache?).elim (.error "invalid cache entries") .ok

  if resultIds.length != before.length then
    .error "resultIds length does not match source nodes length"
  else if hSel : resultIds[beforeRoot]? = some afterRoot then
    let fuel := before.length + after.length + 64
    if hRoot : validate fuel before after beforeRoot afterRoot = true then
      if hInv : Inventory.validate fuel before after resultIds cache = true then
        let _cert :
            (∀ ctx locals,
              Inventory.Preserves before after resultIds cache ctx locals ∧
              ∃ value,
                evaluate before beforeRoot ctx locals = some value ∧
                evaluate after afterRoot ctx locals = some value) :=
          fun ctx locals =>
            Inventory.certify fuel before after resultIds cache beforeRoot afterRoot hInv hSel ctx locals
        let _rootCert := fun ctx locals =>
          validate_sound fuel before after beforeRoot afterRoot hRoot ctx locals
        return s!"\{\"accepted\":true,\"mode\":\"graph\",\"requestSha256\":\"{expectedSha}\",\"sourceNodes\":{before.length},\"optimizedNodes\":{after.length},\"cacheEntries\":{cache.length}}"
      else
        .error "inventory and CSE cache equivalence check failed"
    else
      .error "root DAG normalization equivalence check failed"
  else
    .error "selected root does not match resultIds[beforeRoot]"

/-! ## Mode 2: `graph-failure` Validator -/

def decodeOutcome? : String → Option Failure.Outcome
  | "complete" => some .complete
  | "outOfMemory" => some .outOfMemory
  | _ => none

def decodeAttempt? (j : JsonVal) : Option Failure.Attempt := do
  let fields ← j.asObj?
  if fields.length != 4 then none
  let outcome ← (← j.field? "outcome") >>= JsonVal.asStr? >>= decodeOutcome?
  let nodesJson ← j.field? "nodes"
  let nodesArr ← nodesJson.asArr?
  if nodesArr.length > 512 then none
  let after ← nodesArr.mapM decodeNode?
  let ids ← (← j.field? "resultIds") >>= decodeNatList?
  let cache ← (← j.field? "cache") >>= decodeCache?
  some ⟨outcome, after, ids, cache⟩

def decodeObservation? (j : JsonVal) : Option Failure.Observation := do
  let fields ← j.asObj?
  if fields.length != 4 then none
  let failVal ← j.field? "failureAt"
  let failureAt ← match failVal with
    | .null => some none
    | .num n => some (some n)
    | _ => none
  let succAllocs ← (← j.field? "successfulAllocations") >>= JsonVal.asNat?
  let induced ← (← j.field? "inducedFailure") >>= JsonVal.asBool?
  let attempt ← (← j.field? "attempt") >>= decodeAttempt?
  some ⟨failureAt, succAllocs, induced, attempt⟩

def verifyGraphFailure (reqBytes : ByteArray) (reqJson respJson : JsonVal) : Except String String := do
  let reqFields ← (reqJson.asObj?).elim (.error "request must be JSON object") .ok
  if reqFields.length != 3 then .error "unexpected fields in graph-failure request"
  let reqSchema ← (reqJson.field? "schema" >>= JsonVal.asStr?).elim (.error "missing request schema") .ok
  if reqSchema != "oksolc.compiler-graph-failure-request.v1" then
    .error s!"unsupported graph-failure request schema: {reqSchema}"
  let before ← (reqJson.field? "nodes" >>= decodeNodes?).elim (.error "invalid source graph nodes") .ok
  let beforeRoot ← (reqJson.field? "root" >>= JsonVal.asNat?).elim (.error "invalid source root") .ok

  let respFields ← (respJson.asObj?).elim (.error "response must be JSON object") .ok
  if respFields.length != 4 then .error "unexpected fields in graph-failure response"
  let respSchema ← (respJson.field? "schema" >>= JsonVal.asStr?).elim (.error "missing response schema") .ok
  if respSchema != "oksolc.compiler-graph-failure-response.v1" then
    .error s!"unsupported graph-failure response schema: {respSchema}"
  let respSha ← (respJson.field? "requestSha256" >>= JsonVal.asStr?).elim (.error "missing requestSha256") .ok
  let expectedSha := Sha256.hexDigest reqBytes
  if respSha != expectedSha then
    .error s!"requestSha256 mismatch: expected {expectedSha}, got {respSha}"
  let policy ← (respJson.field? "resizePolicy" >>= JsonVal.asStr?).elim (.error "missing resizePolicy") .ok
  if policy != "always-fail" then
    .error s!"unexpected resizePolicy: {policy}"
  let obsArr ← (respJson.field? "observations" >>= JsonVal.asArr?).elim (.error "missing observations") .ok
  let observations ← (obsArr.mapM decodeObservation?).elim (.error "invalid observation payload") .ok

  let fuel := before.length + 64
  if hSweep : Failure.validateSweep fuel before beforeRoot observations = true then
    let _cert := fun ctx locals =>
      Failure.certifySweep fuel before beforeRoot observations hSweep ctx locals
    return s!"\{\"accepted\":true,\"mode\":\"graph-failure\",\"requestSha256\":\"{expectedSha}\",\"observations\":{observations.length}}"
  else
    .error "allocation-cut sweep failed Failure.validateSweep"

/-! ## Mode 3: `word` Validator -/

def verifyWord (reqBytes : ByteArray) (reqJson respJson : JsonVal) : Except String String := do
  let reqFields ← (reqJson.asObj?).elim (.error "request must be JSON object") .ok
  if reqFields.length != 6 then .error "unexpected fields in word request"
  let reqSchema ← (reqJson.field? "schema" >>= JsonVal.asStr?).elim (.error "missing request schema") .ok
  if reqSchema != "oksolc.compiler-word-request.v1" then
    .error s!"unsupported word request schema: {reqSchema}"
  let arith ← (reqJson.field? "arithmetic" >>= JsonVal.asStr?).elim (.error "missing arithmetic") .ok
  if arith != "unchecked" then .error s!"unsupported arithmetic mode: {arith}"
  let evmVer ← (reqJson.field? "evmVersion" >>= JsonVal.asStr?).elim (.error "missing evmVersion") .ok
  if evmVer != "cancun" then .error s!"unsupported evmVersion: {evmVer}"
  let params ← (reqJson.field? "parameters" >>= decodeStrList?).elim (.error "invalid parameters") .ok
  if params.length > 16 || !params.all validGraphName || !params.Nodup then
    .error "invalid or duplicate word parameters"
  let rawNodes ← (reqJson.field? "nodes" >>= decodeNodes?).elim (.error "invalid word nodes") .ok
  let root ← (reqJson.field? "root" >>= JsonVal.asNat?).elim (.error "invalid word root") .ok
  match hLow : WordBlock.lowerSourceNodes params rawNodes with
  | none => .error "unsupported source word operation"
  | some loweredNodes =>
    match hExp : expand loweredNodes root with
    | none => .error "invalid node reference in word DAG"
    | some sourceExpr =>
      let respFields ← (respJson.asObj?).elim (.error "response must be JSON object") .ok
      if respFields.length != 3 then .error "unexpected fields in word response"
      let respSchema ← (respJson.field? "schema" >>= JsonVal.asStr?).elim (.error "missing response schema") .ok
      if respSchema != "oksolc.compiler-word-response.v1" then
        .error s!"unsupported word response schema: {respSchema}"
      let respSha ← (respJson.field? "requestSha256" >>= JsonVal.asStr?).elim (.error "missing requestSha256") .ok
      let expectedSha := Sha256.hexDigest reqBytes
      if respSha != expectedSha then
        .error s!"requestSha256 mismatch: expected {expectedSha}, got {respSha}"
      let hexCode ← (respJson.field? "bytecode" >>= JsonVal.asStr?).elim (.error "missing bytecode") .ok
      let codeBytes ← (Contract.Hex.decodeBytes? hexCode).elim (.error "invalid hex bytecode") .ok

      let fuel := loweredNodes.length + codeBytes.length + 64
      if hVal : WordBlock.validate fuel codeBytes params sourceExpr = true then
        let _cert := fun input env locals s hpc hstack =>
          WordBlock.validateSource_sound fuel codeBytes params rawNodes loweredNodes root sourceExpr
            hLow hExp hVal input env locals s hpc hstack
        return s!"\{\"accepted\":true,\"mode\":\"word\",\"requestSha256\":\"{expectedSha}\",\"bytecodeBytes\":{codeBytes.length},\"parameters\":{params.length}}"
      else
        .error "word bytecode failed WordBlock.validate against source semantics"

/-! ## Mode 4: `standard-json` Validator -/

private def checkStandardJsonSettings (settings : JsonVal) : Except String Unit := do
  let viaIr ← (settings.field? "viaIR" >>= JsonVal.asBool?).elim (.error "settings.viaIR must be true") .ok
  if !viaIr then .error "settings.viaIR must be true"
  let opt ← (settings.field? "optimizer").elim (.error "missing settings.optimizer") .ok
  let optEnabled ← (opt.field? "enabled" >>= JsonVal.asBool?).elim (.error "settings.optimizer.enabled required") .ok
  if !optEnabled then .error "settings.optimizer.enabled must be true"
  let evmVer ← (settings.field? "evmVersion" >>= JsonVal.asStr?).elim (.error "settings.evmVersion required") .ok
  if evmVer != "cancun" then .error s!"unsupported settings.evmVersion: {evmVer}"
  let metaObj ← (settings.field? "metadata").elim (.error "settings.metadata required") .ok
  let appendCbor ← (metaObj.field? "appendCBOR" >>= JsonVal.asBool?).elim (.error "settings.metadata.appendCBOR required") .ok
  if appendCbor then .error "settings.metadata.appendCBOR must be false"
  let bcHash ← (metaObj.field? "bytecodeHash" >>= JsonVal.asStr?).elim (.error "settings.metadata.bytecodeHash required") .ok
  if bcHash != "none" then .error "settings.metadata.bytecodeHash must be \"none\""
  let outSel ← (settings.field? "outputSelection" >>= fun o => o.field? "*" >>= fun s => s.field? "*" >>= decodeStrList?).elim
    (.error "missing settings.outputSelection.*.*") .ok
  if !outSel.contains "evm.bytecode.object" ||
     !outSel.contains "evm.deployedBytecode.object" ||
     !outSel.contains "evm.methodIdentifiers" then
    .error "outputSelection must include evm.bytecode.object, evm.deployedBytecode.object, and evm.methodIdentifiers"

private def checkNoCompilerErrors (respJson : JsonVal) : Except String Unit := do
  match respJson.field? "errors" with
  | none => return ()
  | some errVal =>
    let errs ← (errVal.asArr?).elim (.error "errors field must be an array") .ok
    for item in errs do
      match item.field? "severity" >>= JsonVal.asStr? with
      | some "error" =>
        let msg := (item.field? "message" >>= JsonVal.asStr?).getD "compiler error"
        throw s!"response contains compiler error: {msg}"
      | _ => pure ()

private def decodeMethodIds? (j : JsonVal) : Option (List (String × List UInt8)) := do
  let fields ← j.asObj?
  fields.mapM fun (sig, hexVal) => do
    let hexStr ← hexVal.asStr?
    let bytes ← Contract.Hex.decodeBytes? hexStr
    if bytes.length == 4 then some (sig, bytes) else none

def verifyStandardJson (reqBytes respBytes : ByteArray) (reqJson respJson : JsonVal) : Except String String := do
  let lang ← (reqJson.field? "language" >>= JsonVal.asStr?).elim (.error "missing language") .ok
  if lang != "Solidity" then .error s!"unsupported language: {lang}"
  let settings ← (reqJson.field? "settings").elim (.error "missing settings") .ok
  checkStandardJsonSettings settings
  checkNoCompilerErrors respJson

  let sources ← (reqJson.field? "sources" >>= JsonVal.asObj?).elim (.error "missing sources object") .ok
  if sources.length != 1 then .error "standard-json verification requires exactly one source unit"
  let (sourceName, sourceObj) ← sources.head?.elim (.error "empty sources") .ok
  let sourceContent ← (sourceObj.field? "content" >>= JsonVal.asStr?).elim (.error "missing source content") .ok

  let spec ← (Solidity.parseSource sourceContent).elim
    (.error s!"source {sourceName} is outside the admitted verified Solidity grammar") .ok

  let contractsRoot ← (respJson.field? "contracts").elim (.error "missing response contracts") .ok
  let fileContracts ← (contractsRoot.field? sourceName >>= JsonVal.asObj?).elim
    (.error s!"missing response contracts for {sourceName}") .ok
  if fileContracts.length != 1 then
    .error s!"expected exactly 1 compiled contract in {sourceName}, got {fileContracts.length}"
  let contractObj ← (contractsRoot.field? sourceName >>= fun f => f.field? spec.name).elim
    (.error s!"missing compiled contract {spec.name}") .ok
  let evmObj ← (contractObj.field? "evm").elim (.error "missing evm object") .ok

  let creationHex ← (evmObj.field? "bytecode" >>= fun b => b.field? "object" >>= JsonVal.asStr?).elim
    (.error "missing evm.bytecode.object") .ok
  let runtimeHex ← (evmObj.field? "deployedBytecode" >>= fun b => b.field? "object" >>= JsonVal.asStr?).elim
    (.error "missing evm.deployedBytecode.object") .ok
  let methodIdsJson ← (evmObj.field? "methodIdentifiers").elim (.error "missing evm.methodIdentifiers") .ok

  let creationBytes ← (Contract.Hex.decodeBytes? creationHex).elim (.error "invalid creation hex bytecode") .ok
  let runtimeBytes ← (Contract.Hex.decodeBytes? runtimeHex).elim (.error "invalid deployed hex bytecode") .ok
  let methodIds ← (decodeMethodIds? methodIdsJson).elim (.error "invalid methodIdentifiers map") .ok
  if creationBytes.isEmpty || runtimeBytes.isEmpty then
    .error "empty creation or deployed bytecode"

  if hArt : Bytecode.validateContractArtifact spec creationBytes runtimeBytes methodIds = true then
    let _cert := Bytecode.validateContractArtifact_sound spec creationBytes runtimeBytes methodIds hArt
    let isPublicPreview :=
      sourceContent == Bytecode.previewSource &&
      creationBytes == Bytecode.previewCreationBytes &&
      runtimeBytes == Bytecode.previewRuntimeBytes

    let reqSha := Sha256.hexDigest reqBytes
    let respSha := Sha256.hexDigest respBytes
    let escapedContract := JsonParser.escapeJsonString spec.name
    let escapedSource := JsonParser.escapeJsonString sourceName
    let previewFlag := if isPublicPreview then "true" else "false"
    return s!"\{\"accepted\":true,\"mode\":\"standard-json\",\"source\":\"{escapedSource}\",\"contract\":\"{escapedContract}\",\"requestSha256\":\"{reqSha}\",\"responseSha256\":\"{respSha}\",\"functions\":{spec.functions.length},\"stateVars\":{spec.stateVars.length},\"creationBytes\":{creationBytes.length},\"runtimeBytes\":{runtimeBytes.length},\"universalPreviewTheorem\":{previewFlag}}"
  else
    .error s!"contract {spec.name} failed semantic bytecode validation against source specification"

end Compiler.Validation.Cli

/-! ## Executable Entrypoint -/

open Compiler.Validation.Cli in
def main (args : List String) : IO UInt32 := do
  match args with
  | [mode, reqPath, respPath] =>
    let reqBytes ← IO.FS.readBinFile reqPath
    let respBytes ← IO.FS.readBinFile respPath
    let some reqText := String.fromUTF8? reqBytes
      | IO.eprintln "error: request file is not valid UTF-8"
        return 1
    let some respText := String.fromUTF8? respBytes
      | IO.eprintln "error: response file is not valid UTF-8"
        return 1
    let some reqJson := JsonParser.parse reqText
      | IO.eprintln "error: malformed request JSON"
        return 1
    let some respJson := JsonParser.parse respText
      | IO.eprintln "error: malformed response JSON"
        return 1
    let result :=
      match mode with
      | "graph" => verifyGraph reqBytes reqJson respJson
      | "graph-failure" => verifyGraphFailure reqBytes reqJson respJson
      | "word" => verifyWord reqBytes reqJson respJson
      | "standard-json" => verifyStandardJson reqBytes respBytes reqJson respJson
      | other => .error s!"unknown mode '{other}' (expected graph, graph-failure, word, or standard-json)"
    match result with
    | .ok report =>
      IO.println report
      return 0
    | .error err =>
      let escaped := JsonParser.escapeJsonString err
      IO.eprintln s!"\{\"accepted\":false,\"mode\":\"{JsonParser.escapeJsonString mode}\",\"error\":\"{escaped}\"}"
      return 1
  | _ =>
    IO.eprintln "usage: oksolc-verify <graph|graph-failure|word|standard-json> <request.json> <response.json>"
    return 2
