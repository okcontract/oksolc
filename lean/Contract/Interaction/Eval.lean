/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Interaction.Creation
import Contract.Interaction.Calls
import Contract.Interaction.Bytes
import Contract.Export.Keccak
import Contract.Interaction.CodeHash
import Contract.Interaction.WordPower

namespace Contract.Interaction

abbrev Memory := Nat → UInt8
abbrev Locals := List (String × Word)

def Locals.set (env : Locals) (name : String) (v : Word) : Locals :=
  (name, v) :: env.filter (fun x => x.1 != name)

def Memory.read (m : Memory) (offset size : Nat) : List UInt8 :=
  (List.range size).map fun i => m (offset + i)

def Memory.write (m : Memory) (offset : Nat) (bytes : List UInt8) : Memory :=
  fun i => if offset ≤ i && i < offset + bytes.length then bytes[i-offset]! else m i

structure Context where
  self : Word := 0
  caller : Word := 0
  /-- Transaction sender, independent of the current caller and execution owner.
  Missing bindings fail on ORIGIN; nested executors must preserve this value. -/
  origin : Option Address := none
  /-- Effective transaction price per gas, constant across nested frames. This
  binding does not model gas consumption, base fee or a transaction fee cap. -/
  gasPrice : Option Word := none
  /-- Current block's base fee. Missing bindings fail explicitly; neither
  transaction gas price nor remaining gas supplies this independent word. -/
  baseFee : Option Word := none
  value : Word := 0
  readOnly : Bool := false
  timestamp : Word := 0
  /-- Current block height, supplied by the same explicit environment as timestamp. -/
  blockNumber : Word := 0
  chainid : Word := 1
  calldata : List UInt8 := []
  /-- Gas is an opaque observation here. This interpreter is not gas semantics. -/
  gas : Word := 0
  /-- Existing explicit environment adapters remain available. The default
  observes installed code in the same world that calls and rollback update. -/
  codeSize : World → Word → Word := World.codeSize
  /-- Executing bytes: creation code plus appended inputs during deployment,
  deployed code at runtime. This is distinct from account EXTCODESIZE. -/
  code : List UInt8 := []
  /-- Link environment for the creation object's DATASIZE. An absent binding
  is an invalid program context, never a guessed zero or an execution proof. -/
  creationSize : Option Word := none
  /-- Installed-code bindings, supplied by a separately checked deployment link.
  Missing bindings are invalid context; they never default to zero at runtime. -/
  immutableValues : List Word := []
  /-- Set by the entry boundary, independently of the immutable count. Shared
  helpers use the same phase for constant modes and immutable reads. -/
  isCreation : Bool := false
  /-- Root frame is depth zero. Nested execution must supply its actual depth. -/
  depth : Nat := 0
  /-- Opcode availability for this frame; the executor binds the same fork as
  the compiled artifact and any creation environment. Gas remains opaque. -/
  fork : Creation.Fork := .istanbul
  /-- Absent creation policy/executor fails closed; no default successful child. -/
  creation : Option Creation.Environment := none

structure State where
  world : World := {}
  memory : Memory := fun _ => 0
  locals : Locals := []
  returndata : List UInt8 := []
  context : Context := {}
  /-- Remaining-gas observations for this frame in execution order. Internal
  helpers and lexical scopes share the stream. Foreign executors bind their own
  frame streams; a correspondence to the artifact's gas semantics is required.
  Exhaustion is invalid context, never a guessed value or an EVM out-of-gas. -/
  gasObservations : List Word := []

def Locals.values (env : Locals) (names : List String) : Except Fault (List Word) :=
  names.mapM fun n => match env.lookup n with
    | some v => pure v
    | none => throw .invalidProgram

/-- Bounded host materialization is an explicit inconclusive outcome, never a
contract revert or a claim of unreachability. Runtime code has no such cap. -/
def materialize (offset size : Word) : Except Fault (Nat × Nat) := do
  if size = 0 then return (0, 0)
  if offset.toNat + size.toNat > 1048576 then throw .resourceLimit
  return (offset.toNat, size.toNat)

def Immutable.eval (s : State) (index : Nat) : Except Fault Word := do
  if index ≥ Immutable.maxCount then throw .invalidProgram
  if s.context.isCreation then
    let (offset,size) ← materialize (BitVec.ofNat 256 (Immutable.slot index)) 32
    return bytesWord (s.memory.read offset size)
  else match s.context.immutableValues[index]? with
    | some value => return value
    | none => throw .invalidProgram

def Op.eval (s : State) (op : Op) (args : List Word) : Except Fault Word := do
  match op, args with
  | .add, [a,b] => return a+b
  | .sub, [a,b] => return a-b
  | .addmod, [a,b,m] => return if m = 0 then 0 else BitVec.ofNat 256 ((a.toNat+b.toNat) % m.toNat)
  | .mulmod, [a,b,m] => return if m = 0 then 0 else BitVec.ofNat 256 ((a.toNat*b.toNat) % m.toNat)
  | .exp, [base,exponent] => return WordPower.pow base exponent.toNat
  | .word .shl, [n,a] => return WordOp.shl.eval a n
  | .word .shr, [n,a] => return WordOp.shr.eval a n
  | .word op, [a,b] => return op.eval a b
  | .eq, [a,b] => return if a = b then 1 else 0
  | .lt, [a,b] => return if a < b then 1 else 0
  | .gt, [a,b] => return if b < a then 1 else 0
  | .slt, [a,b] => return if a.toInt < b.toInt then 1 else 0
  | .sgt, [a,b] => return if b.toInt < a.toInt then 1 else 0
  | .signextend, [index,value] =>
    return if index.toNat < 31 then
      (value.setWidth (8*(index.toNat+1))).signExtend 256 else value
  | .byte, [index,value] =>
    return if index.toNat < 32 then
      (value >>> (8*(31-index.toNat))) &&& 255 else 0
  | .iszero, [a] => return if a = 0 then 1 else 0
  | .not, [a] => return ~~~a
  | .sload, [a] => return s.world.storage s.context.self a
  | .tload, [a] =>
    if !s.context.fork.hasTransientStorage then throw .exceptionalHalt
    return s.world.tload s.context.self a
  | .mload, [a] =>
    let (offset, size) ← materialize a 32
    return bytesWord (s.memory.read offset size)
  | .calldataload, [a] =>
    -- Out-of-range calldata reads are zero, including huge offsets.
    return bytesWord ((List.range 32).map fun i => (s.context.calldata[a.toNat+i]?).getD 0)
  | .calldatasize, [] => return BitVec.ofNat 256 s.context.calldata.length
  | .codesize, [] => return BitVec.ofNat 256 s.context.code.length
  | .creationSize, [] => match s.context.creationSize with
    | some size => return size
    | none => throw .invalidProgram
  | .creationPhase, [] => return if s.context.isCreation then 1 else 0
  | .immutable index, [] => Immutable.eval s index
  | .caller, [] => return s.context.caller
  | .origin, [] => match s.context.origin with
    | some sender => return sender.setWidth 256
    | none => throw .invalidProgram
  | .gasprice, [] => match s.context.gasPrice with
    | some price => return price
    | none => throw .invalidProgram
  | .basefee, [] =>
    if !s.context.fork.hasBaseFee then throw .exceptionalHalt
    match s.context.baseFee with
    | some fee => return fee
    | none => throw .invalidProgram
  | .address, [] => return s.context.self
  | .callvalue, [] => return s.context.value
  | .timestamp, [] => return s.context.timestamp
  | .number, [] => return s.context.blockNumber
  | .chainid, [] => return s.context.chainid
  | .gas, [] => return s.context.gas
  | .returndatasize, [] => return BitVec.ofNat 256 s.returndata.length
  | .extcodesize, [a] => return s.context.codeSize s.world (a &&& BitVec.ofNat 256 (2^160-1))
  | .extcodehash, [a] => return s.world.codeHash a
  | .balance, [a] => return (s.world.account a).balance
  | .keccak256, [a,n] =>
    let (offset, size) ← materialize a n
    return bytesWord (Contract.Export.Keccak.hash ⟨(s.memory.read offset size).toArray⟩).data.toList
  | _, _ => throw .invalidProgram

def Expr.eval (s : State) : Expr → Except Fault Word
  | .lit n => .ok n
  | .var n => match s.locals.lookup n with | some v => .ok v | none => .error .invalidProgram
  | .app op args => do
    let values ← args.attach.mapM fun a => Expr.eval s a.val
    op.eval s values
termination_by e => sizeOf e
decreasing_by
  have := List.sizeOf_lt_of_mem a.property
  simp_all
  omega

inductive Control where
  | next | leave | breakLoop | continueLoop
  | returned (bytes : List UInt8) | reverted (bytes : List UInt8)
  deriving DecidableEq, Repr

abbrev Result := Except Fault (Control × State)

def Effect.eval (s : State) (op : Effect) (args : List Word) : Result := do
  match op, args with
  | .sstore, [slot,v] =>
    if s.context.readOnly then throw .exceptionalHalt
    return (.next, { s with world := s.world.store s.context.self slot v })
  | .tstore, [slot,v] =>
    if !s.context.fork.hasTransientStorage || s.context.readOnly then throw .exceptionalHalt
    return (.next, { s with world := s.world.tstore s.context.self slot v })
  | .mstore, [offset,v] =>
    let (offset, _) ← materialize offset 32
    return (.next, { s with memory := s.memory.write offset (wordBytes v) })
  | .mstore8, [offset,v] =>
    let (offset, _) ← materialize offset 1
    return (.next, { s with memory := s.memory.write offset [v.toNat.toUInt8] })
  | .calldatacopy, [dest,src,size] =>
    let (dest, size) ← materialize dest size
    let bytes := readBytesPadded s.context.calldata src.toNat size
    return (.next, { s with memory := s.memory.write dest bytes })
  | .codecopy, [dest,src,size] =>
    let (dest, size) ← materialize dest size
    let bytes := readBytesPadded s.context.code src.toNat size
    return (.next, { s with memory := s.memory.write dest bytes })
  | .extcodecopy, [target,dest,src,size] =>
    let (dest, size) ← materialize dest size
    -- Installed account bytes, not executing-frame code or a delegated code
    -- target. The typed account lookup consumes only the low 160 target bits.
    let bytes := readBytesPadded (s.world.account target).code src.toNat size
    return (.next, { s with memory := s.memory.write dest bytes })
  | .mcopy, [dest,src,size] =>
    if !s.context.fork.hasMemoryCopy then throw .exceptionalHalt
    let (dest, count) ← materialize dest size
    let (src, _) ← materialize src size
    -- Snapshot the old memory, including overlapping ranges. Both spans count
    -- toward host materialization; zero length ignores either offset. Memory
    -- expansion/gas and MSIZE are not observations of this byte-memory model.
    return (.next, { s with memory := s.memory.write dest (s.memory.read src count) })
  | .returndatacopy, [dest,src,size] =>
    if src.toNat + size.toNat > s.returndata.length then throw .exceptionalHalt
    let (dest, size) ← materialize dest size
    return (.next, { s with memory := s.memory.write dest (s.returndata.drop src.toNat |>.take size) })
  | .log n, offset :: size :: topics =>
    if s.context.readOnly then throw .exceptionalHalt
    unless topics.length = n.val do throw .invalidProgram
    let (offset, size) ← materialize offset size
    let log : Event := ⟨s.context.self, topics, s.memory.read offset size⟩
    return (.next, { s with world := { s.world with logs := s.world.logs ++ [log] } })
  | .return_, [offset,size] =>
    let (offset, size) ← materialize offset size
    return (.returned (s.memory.read offset size), s)
  | .revert, [offset,size] =>
    let (offset, size) ← materialize offset size
    return (.reverted (s.memory.read offset size), s)
  | .stop, [] => return (.returned [], s)
  | .invalid, [] => throw .exceptionalHalt
  | _, _ => throw .invalidProgram

/-- One request constructor for execution and proof rules. Delegation separates
code identity from ADDRESS/storage ownership and inherits caller/value/staticness. -/
def State.callRequest (s : State) (kind : CallKind) (gas target value : Word)
    (start count : Nat) : CallRequest := {
  kind, caller := if kind == .delegatecall then s.context.caller else s.context.self,
  target := target &&& BitVec.ofNat 256 (2^160-1),
  value := if kind == .delegatecall then s.context.value else value,
  gas, input := s.memory.read start count,
  executionAddress := if kind == .delegatecall then s.context.self else target &&& BitVec.ofNat 256 (2^160-1),
  readOnly := kind == .staticcall || s.context.readOnly, origin := s.context.origin,
  gasPrice := s.context.gasPrice, baseFee := s.context.baseFee }

/-- Ordinary read-only calls use STATICCALL kind. Delegated read-only calls keep
their opcode identity, so their independent frame flag controls world commit. -/
def State.callResponse (s : State) (kind : CallKind) (response : CallResponse)
    (start count : Nat) : State :=
  { s with world := if response.success && (kind == .call || (kind == .delegatecall && !s.context.readOnly))
                     then response.world else s.world
           memory := s.memory.write start (response.output.take count)
           returndata := response.output }

def external (oracle : Oracle) (s : State) (kind : CallKind) (args : List Word)
    (funded : Bool := false) :
    Except Fault (Word × State) := do
  let args := if kind == .call then args else args.take 2 ++ [0] ++ args.drop 2
  match args with
  | [gas,target,value,offset,size,outOffset,outSize] =>
    let (offset, size) ← materialize offset size
    let (outOffset, outSize) ← materialize outOffset outSize
    if s.context.readOnly && value != 0 then throw .exceptionalHalt
    let kind := if s.context.readOnly && kind == .call then CallKind.staticcall else kind
    let request := s.callRequest kind gas target value offset size
    let response ← if funded then Calls.funded oracle s.context.depth request s.world
      else pure (oracle request s.world)
    return (if response.success then 1 else 0,
      s.callResponse kind response outOffset outSize)
  | _ => throw .invalidProgram

/-- Both creation statements read the current memory and preserve the parent
frame, replacing only the world and return buffer before binding its result. -/
def createWith (kind : Creation.Kind) (s : State) (args : List Word) : Except Fault (Word × State) := do
  match args with
  | [value,offset,size,salt] =>
    let some environment := s.context.creation | throw .invalidProgram
    if let some fault := Creation.preflight environment.fork s.context.readOnly environment.entryGasAvailable size.toNat then
      throw fault
    let (offset, size) ← materialize offset size
    let result ← Creation.createWith kind environment.fork environment.execute
      ⟨s.context.self,value,salt,s.memory.read offset size,s.context.depth,s.context.readOnly,environment.entryGasAvailable,s.context.origin,s.context.gasPrice,s.context.baseFee⟩ s.world
    pure (result.address,{s with world := result.world,returndata := result.returndata})
  | _ => throw .invalidProgram

def create2 := createWith .salted

/-- Normalize only the operand shape. The ordinary address rule does not use
the placeholder salt; invalid arities remain invalid, including four operands. -/
def create (s : State) : List Word → Except Fault (Word × State)
  | [value,offset,size] => createWith .nonce s [value,offset,size,0]
  | _ => .error .invalidProgram

/-- Restore the lexical local domain while retaining assignments to outer
locals. Shared by branches, explicit scopes and each loop iteration. -/
def State.closeScope (before after : State) : State :=
  { after with locals := before.locals.map fun (n,v) => (n, (after.locals.lookup n).getD v) }

/-- One instruction, using the supplied recursive evaluator for nested work.
Both execution and proof rules use this definition; there is no second semantics. -/
def step (oracle : Oracle) (helpers : List Function)
    (recur : State → List Stmt → Result) (s : State) (instruction : Stmt) : Result := do
  match instruction with
  | .assign n e => do
    unless s.locals.any (fun p => p.1 == n) do throw .invalidProgram
    let v ← e.eval s
    pure (.next, { s with locals := s.locals.set n v })
  | .let_ n e => do
    let v ← e.eval s
    pure (.next, { s with locals := s.locals.set n v })
  | .observeGas n => match s.gasObservations with
    | [] => throw .invalidProgram
    | value :: rest => pure (.next, {s with locals := s.locals.set n value, gasObservations := rest})
  | .effect op es => Effect.eval s op (← es.mapM (Expr.eval s))
  | .external name kind es => do
    let (v, s) ← external oracle s kind (← es.mapM (Expr.eval s))
    pure (.next, { s with locals := s.locals.set name v })
  | .message name kind es => do
    let (v, s) ← external oracle s kind (← es.mapM (Expr.eval s)) true
    pure (.next, { s with locals := s.locals.set name v })
  | .create2 name es => do
    let (v, s) ← create2 s (← es.mapM (Expr.eval s))
    pure (.next, { s with locals := s.locals.set name v })
  | .create name es => do
    let (v, s) ← create s (← es.mapM (Expr.eval s))
    pure (.next, { s with locals := s.locals.set name v })
  | .branch c yes no => do
    let code := if (← c.eval s) = 0 then no else yes
    let (ctrl, after) ← recur s code
    pure (ctrl, s.closeScope after)
  | .scope code => do
    let (ctrl, after) ← recur s code
    pure (ctrl, s.closeScope after)
  | .while_ c code => do
    if (← c.eval s) = 0 then pure (.next, s) else
      let (ctrl, after) ← recur s code
      let after := s.closeScope after
      if ctrl == .breakLoop then pure (.next, after)
      else if ctrl == .next || ctrl == .continueLoop then recur after [.while_ c code]
      else pure (ctrl, after)
  | .for_ code post => do
    let (ctrl, after) ← recur s code
    let after := s.closeScope after
    if ctrl == .breakLoop then pure (.next, after)
    else if ctrl == .next || ctrl == .continueLoop then
      let (ctrl, last) ← recur after post
      let last := after.closeScope last
      if ctrl == .next then recur last [.for_ code post]
      else if ctrl == .breakLoop || ctrl == .continueLoop then throw .invalidProgram
      else pure (ctrl, last)
    else pure (ctrl, after)
  | .call names fn args => do
    let some f := helpers.find? (·.name == fn) | throw .invalidProgram
    unless f.params.length == args.length && f.results.length == names.length do throw .invalidProgram
    let values ← args.mapM (Expr.eval s)
    let locals := f.params.zip values ++ f.results.map (·, 0)
    let (ctrl, after) ← recur { s with locals } f.body
    if ctrl == .next || ctrl == .leave then
      let values ← after.locals.values f.results
      let locals := (names.zip values).foldl (fun env (n,v) => env.set n v) s.locals
      pure (.next, { after with locals })
    else if ctrl == .breakLoop || ctrl == .continueLoop then throw .invalidProgram
    else pure (ctrl, after)
  | .leave => pure (.leave, s)
  | .break_ => pure (.breakLoop, s)
  | .continue_ => pure (.continueLoop, s)

/-- Fuel bounds recursion depth for source experiments, not EVM gas. Every
finite successful execution has sufficient fuel; exhaustion is inconclusive.
Nested work can exceed fuel: callers must additionally bound host resources. -/
def run (oracle : Oracle) (helpers : List Function) : Nat → State → List Stmt → Result
  | 0, _, _ => .error .resourceLimit
  | _+1, s, [] => .ok (.next, s)
  | fuel+1, s, instruction :: rest => do
    let (control, s) ← step oracle helpers (run oracle helpers fuel) s instruction
    if control == .next then run oracle helpers fuel s rest else pure (control, s)

/-- Frame commit/rollback boundary. Failed and inconclusive outcomes never
publish writes/logs, including effects of successful earlier nested calls.
Successful frames retain transaction-local storage for subsequent calls. -/
def committedWorld (before : World) : Result → World
  | .ok (.next, s) | .ok (.returned _, s) => s.world
  | _ => before

/-- Root transaction settlement, not nested-frame return. Clear transient state
on every outcome after applying the common rollback/commit rule. -/
def committedTransaction (before : World) (result : Result) : World :=
  (committedWorld before result).clearTransient

theorem revert_rolls_back (before : World) (s : State) (bytes : List UInt8) :
    committedWorld before (.ok (.reverted bytes, s)) = before := rfl

theorem failure_rolls_back (before : World) (fault : Fault) :
    committedWorld before (.error fault) = before := rfl

end Contract.Interaction
