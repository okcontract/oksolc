/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyItemConstructorLocal
import Compiler.Extraction.InternerCallerNativeRouting

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem
open Compiler.Algebraic Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open AssemblyItem.Fields

/-- The item pointer supplied to the complete caller is the actual initialized
local. Only ordinary results unwind this outer item frame; rejected observations
retain the reached callee locals and native memory. -/
def invoke (external : External σ) (budget allocator : Nat)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives σ)
    (q : Caller.Queries) (source : View) (request : Interner.Request) (debug : Values)
    (before : World σ) : Except Fault NodeId × State σ :=
  match prepare request.item debug before with
  | (.error fault, reached) => (.error fault, ⟨reached, { lookup := none }⟩)
  | (.ok address, prepared) =>
    let ran := ConstructorFrame.find external budget allocator (p address (input request.item debug)) q source request prepared
    if ordinary ran.1 then
      (ran.1, { ran.2 with world := { ran.2.world with memory := { ran.2.world.memory with
        memory := Compiler.ZigAir.Memory.cleanup before.memory.memory.nextId ran.2.world.memory.memory } } })
    else ran

def operation (external : External σ) (budget allocator : Nat)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives σ)
    (q : Caller.Queries) (source : View) (opcode : Opcode) (values : List NodeId) (debug : Values) :=
  invoke external budget allocator p q source (Interner.constructorCode.operationRequest opcode values) debug

def constant (external : External σ) (budget allocator : Nat)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives σ)
    (q : Caller.Queries) (value : Contract.Yul.Word) (debug : Values) :=
  invoke external budget allocator p q ⟨0, 0, 0⟩ (Interner.constructorCode.constantRequest value) debug

def materialize (external : External σ) (budget allocator : Nat)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives σ)
    (q : Caller.Queries) (_id : NodeId) (value : Contract.Yul.Word) (debug : Values) :=
  constant external budget allocator p q value debug

theorem invoke_prepared (external : External σ) (budget allocator : Nat)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives σ)
    (q : Caller.Queries) (source : View) (request : Interner.Request) (debug : Values)
    (before prepared : World σ) (address : Compiler.ZigAir.Memory.Address)
    (made : prepare request.item debug before = (.ok address, prepared)) :
    invoke external budget allocator p q source request debug before =
      (let ran := ConstructorFrame.find external budget allocator (p address (input request.item debug)) q source request prepared
       if ordinary ran.1 then
         (ran.1, { ran.2 with world := { ran.2.world with memory := { ran.2.world.memory with
           memory := Compiler.ZigAir.Memory.cleanup before.memory.memory.nextId ran.2.world.memory.memory } } })
       else ran) := by
  unfold invoke
  rw [made]

theorem invoke_rejected (external : External σ) (budget allocator : Nat)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives σ)
    (q : Caller.Queries) (source : View) (request : Interner.Request) (debug : Values)
    (before reached : World σ) (fault : Fault)
    (failed : prepare request.item debug before = (.error fault, reached)) :
    invoke external budget allocator p q source request debug before =
      (.error fault, ⟨reached, { lookup := none }⟩) := by
  unfold invoke
  rw [failed]

/-- Transfer item/scratch capacity witnesses through actual item stores.
Only address bounds come from the witnesses; reached memory, debug fields and
allocation identities are derived from the same preparation. -/
theorem prepare_with_scratch (item : Item) (debug : Values) (before : World σ)
    (witness middle last : Compiler.ZigAir.Memory.State)
    (firstPointer secondPointer : Compiler.ZigAir.Memory.Value)
    (valid : Valid before.memory) (witnessValid : witness.valid = true)
    (address : before.memory.memory.nextAddress = witness.nextAddress)
    (domain : (item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (typed : AssemblyItem.Initializers.DebugTyped debug)
    (first : Compiler.ZigAir.Memory.allocate witness AssemblyItem.viewType = .ok (firstPointer, middle))
    (second : Compiler.ZigAir.Memory.allocate middle (.array 2 word) = .ok (secondPointer, last)) :
    ∃ constructed scratch,
      prepare item debug before = (.ok ⟨before.memory.memory.nextId, 0⟩, constructed) ∧
      Prepared item debug before constructed ∧
      Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) =
        .ok (.pointer (.pointer true false (.array 2 word)) ⟨constructed.memory.memory.nextId, 0⟩, scratch) ∧
      scratch.nextAddress = last.nextAddress := by
  obtain ⟨pointer, allocated, ran, counter⟩ := Compiler.ZigAir.Memory.allocate_at_same_address _ _ _
    valid.memory witnessValid address _ _ first
  obtain ⟨constructed, made, post⟩ := prepare_verified item debug before pointer allocated valid domain typed ran
  obtain ⟨p, reached, allocation, assignedCounter⟩ := post.allocation
  have sameMemory : reached = allocated := congrArg Prod.snd (Except.ok.inj (allocation.symm.trans ran))
  have reachedCounter : constructed.memory.memory.nextAddress = middle.nextAddress :=
    assignedCounter.trans ((congrArg Compiler.ZigAir.Memory.State.nextAddress sameMemory).trans counter)
  have middleValid := Compiler.ZigAir.Memory.allocate_preserves_valid _ _ _ _ first
  obtain ⟨scratchPointer, scratch, scratchRan, scratchCounter⟩ := Compiler.ZigAir.Memory.allocate_at_same_address _ _ _
    post.valid.memory middleValid reachedCounter _ _ second
  have shape := Compiler.ZigAir.Memory.allocate_pointer _ _ _ _ scratchRan
  rw [shape.1] at scratchRan
  exact ⟨constructed, scratch, made, post, scratchRan, scratchCounter⟩

/-- Complete constructor-local initialization discharges native item reads and
preserves the actual argument view before scratch allocation and normalization.
The caller's reached ownership is derived from the same init/take observations;
no normalized owner or represented item is supplied as an input premise. -/
theorem caller_input (host : External σ) (budget allocator : Nat) (source : View)
    (request : Interner.Request) (debug : Values) (before constructed : World (Publication.Effects σ))
    (address : Compiler.ZigAir.Memory.Address) (memory : Compiler.ZigAir.Memory.State)
    (pointer : Compiler.ZigAir.Memory.Value) (values : List NodeId)
    (prepared taken : State (Publication.Effects σ)) (key : Key)
    (good : Good source request.arguments before)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (typed : AssemblyItem.Initializers.DebugTyped debug) (admitted : Admitted host)
    (made : prepare request.item debug before = (.ok address, constructed))
    (allocated : Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) = .ok (pointer, memory))
    (initialized : Caller.initLookup (Publication.external host) budget allocator source
      ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))
    (transferred : take (Publication.external host) allocator prepared = (.ok (), taken))
    (keyed : Interner.makeKey request values = .ok key)
    (live : OwnedKeys.Live allocator ⟨before.memory.effects.keys, before.memory.heap⟩)
    (unique : OwnedKeys.Unique before.memory.effects.keys)
    (sourceApart : ∀ old, before.memory.effects.keys key = some old → key.arguments ≠ [] →
      source.length ≠ 0 → source.allocation ≠ old.address) :
    ∃ normalized remaining,
      Insertion.Native.CallerInput allocator source address request values (input request.item debug) key
        constructed taken normalized remaining := by
  obtain ⟨addressed, post⟩ := prepare_success request.item debug before constructed address good.1 domain typed made
  have represented := post.represented
  rw [← addressed] at represented
  apply Insertion.Native.caller_input host budget allocator source address request (input request.item debug)
    constructed memory pointer values prepared taken key (good_frame before constructed source request.arguments good post.valid post.memory)
    admitted represented rfl allocated initialized transferred keyed
  · rw [post.effects, post.heap]; exact live
  · rw [post.effects]; exact unique
  · rw [post.effects]; exact sourceApart

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem
