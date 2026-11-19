/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeMissWords
import Compiler.Extraction.InternerNativeLeafFrame

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray NativeRecursion Recursive

/-- Observations of one actual item-entry prefix, not a new executor. The
existing preparation, initialization and take equations determine every field. -/
structure TakenSite (σ : Type) where
  constructed : World (Publication.Effects σ)
  address : Compiler.ZigAir.Memory.Address
  pointer : Compiler.ZigAir.Memory.Value
  memory : Compiler.ZigAir.Memory.State
  values : List NodeId
  prepared : State (Publication.Effects σ)
  taken : State (Publication.Effects σ)
  key : Key
  normalized : ArgumentSlice
  lookup : Handle
  deterministic : Bool

/-- These are precisely the source observations already requested by
JointEntry.taken. No replay model, child law or final result is included. -/
structure TakenSite.Reached (base : PairInput.Context (Publication.Effects σ))
    (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before : World (Publication.Effects σ)) (site : TakenSite σ) : Prop where
  made : prepare request.item debug before = (.ok site.address, site.constructed)
  room : base.queries.atCapacity site.constructed.graph = false
  allocated : Compiler.ZigAir.Memory.allocate site.constructed.memory.memory (.array 2 word) = .ok (site.pointer, site.memory)
  initialized : Caller.initLookup base.external base.budget base.allocator source ⟨site.constructed.memory.memory.nextId, 0, 2⟩ request
    ⟨{ site.constructed with memory := { site.constructed.memory with memory := site.memory } }, { lookup := none }⟩ =
      (.ok site.values, site.prepared)
  classified : base.queries.deterministic request.item = .ok site.deterministic
  keyed : Interner.makeKey request site.values = .ok site.key
  missed : site.deterministic = true → site.constructed.graph.table site.key = none
  transferred : OwnedCall.take base.external base.allocator site.prepared = (.ok (), site.taken)
  input : Insertion.Native.CallerInput base.allocator source site.address request site.values (input request.item debug) site.key
    site.constructed site.taken site.normalized site.lookup

/-- Determinacy of the executed prefix and the reached ownership scope gives a
single replay-selection site. Neither successful entry nor a unique site is an
assumption of the enclosing constructor theorem. -/
theorem TakenSite.Reached.unique {base : PairInput.Context (Publication.Effects σ)}
    {source : View} {request : Interner.Request} {debug : AssemblyItem.Fields.Values}
    {before : World (Publication.Effects σ)} {left right : TakenSite σ}
    (one : left.Reached base source request debug before) (two : right.Reached base source request debug before) :
    left = right := by
  rcases left with ⟨constructed, address, pointer, memory, values, prepared, taken, key, normalized, lookup, deterministic⟩
  rcases right with ⟨constructed', address', pointer', memory', values', prepared', taken', key', normalized', lookup', deterministic'⟩
  have made := one.made.symm.trans two.made
  injection made with addresses worlds
  cases worlds
  injection addresses with addresses
  cases addresses
  have allocated := one.allocated.symm.trans two.allocated
  injection allocated with allocated
  injection allocated with pointers memories
  cases pointers
  cases memories
  have initialized := one.initialized.symm.trans two.initialized
  injection initialized with valuesEqual states
  cases states
  injection valuesEqual with valuesEqual
  cases valuesEqual
  have classified := one.classified.symm.trans two.classified
  injection classified with classified
  cases classified
  have keyed := one.keyed.symm.trans two.keyed
  injection keyed with keyed
  cases keyed
  have transferred := one.transferred.symm.trans two.transferred
  injection transferred with _ states
  cases states
  have scopes := one.input.origin.scope.symm.trans two.input.origin.scope
  have handles := Option.some.inj (congrArg Local.lookup scopes)
  have slices := Option.some.inj (congrArg Local.slice scopes)
  cases handles
  cases slices
  rfl

/-- Derive the native inputs at the actual taken site from the original entry.
Both entry clients reuse the same preparation, retention and caller-frame proof. -/
theorem TakenSite.Reached.native_inputs {base : PairInput.Context (Publication.Effects σ)}
    {source : View} {request : Interner.Request} {debug : AssemblyItem.Fields.Values}
    {before : World (Publication.Effects σ)} {site : TakenSite σ}
    (reached : site.Reached base source request debug before)
    {safety : Bool} {owner capacity : Nat} {data : Compiler.ZigAir.Memory.Address} {rows : List Storage.Cell}
    {parent : World (Publication.Effects σ) → Prop}
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (privateSource : Caller.SourcePrivate source before.memory.effects.keys)
    (array : ArraySource source before.memory.memory)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (typed : AssemblyItem.Initializers.DebugTyped debug)
    (retained : ∀ after, Valid after.memory → after.graph = before.graph → Retains before after → parent after) :
    Prepared request.item debug before site.constructed ∧
      NativeGraph.Facts safety base.allocator owner data capacity site.constructed rows ∧ parent site.constructed ∧
      CallFrame safety base.allocator owner rows source request.arguments site.normalized site.address
        (ConstructorItem.input request.item debug) parent site.taken.world ∧
      NativeGraph.Facts safety base.allocator owner data capacity site.taken.world rows := by
  have item := (prepare_success request.item debug before site.constructed site.address facts.valid domain typed reached.made).2
  have constructedFacts := facts.frame item.valid (by rw [item.graph]; exact facts.projected)
    (congrArg Interner.Heap.table item.graph) (congrArg Publication.Effects.keys item.effects)
    (fun id cell found _ => item.memory id cell found) (fun _ _ found => item.heap ▸ found)
  have constructedParent := retained site.constructed item.valid item.graph
    ⟨congrArg Publication.Effects.keys item.effects, item.memory, fun _ _ found => item.heap ▸ found⟩
  have parentTaken := retained site.taken.world reached.input.origin.held.1.1 (reached.input.origin.graph.trans item.graph)
    ⟨reached.input.keys.trans (congrArg Publication.Effects.keys item.effects),
      fun id cell found => reached.input.origin.memory id cell (item.memory id cell found),
      fun id block found => reached.input.origin.registry id block (item.heap ▸ found)⟩
  have takenFacts := constructedFacts.frame reached.input.origin.held.1.1
    (by rw [reached.input.origin.graph]; exact constructedFacts.projected)
    (congrArg Interner.Heap.table reached.input.origin.graph) reached.input.keys
    (fun id cell found _ => reached.input.origin.memory id cell found) reached.input.origin.registry
  exact ⟨item, constructedFacts, constructedParent,
    CallFrame.caller reached.input constructedFacts (by rw [item.effects]; exact privateSource)
      (array.frame (fun _ cell found => item.memory _ cell found)) parent parentTaken, takenFacts⟩

/-- Actual normalization and key construction transport the requested value to
the reached key. This uses the same graph before any recursive child executes. -/
theorem TakenSite.Reached.key_value {base : PairInput.Context (Publication.Effects σ)}
    {source : View} {request : Interner.Request} {debug : AssemblyItem.Fields.Values}
    {before : World (Publication.Effects σ)} {site : TakenSite σ}
    (reached : site.Reached base source request debug before)
    (item : Prepared request.item debug before site.constructed)
    (env : AddressMask.Environment) (other : Meaning) (expected : Word)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read
      request.arguments request.sequence = some expected) :
    Interner.Invariant (Dispatch.wordDispatchMeaning env other) site.taken.world.graph ∧
      site.key.eval (Dispatch.wordDispatchMeaning env other) site.taken.world.graph.read = some expected := by
  have graphSame := reached.input.origin.graph.trans item.graph
  refine ⟨graphSame.symm ▸ valid, ?_⟩
  rw [graphSame]
  exact Interner.makeKey_sound _ _ _ _ _ _
    ((Compiler.Extraction.InsertionSort.normalize_word (Dispatch.wordBaseMeaning env other) request.item request.arguments
      site.values before.graph.read request.sequence reached.input.origin.normalized).trans evaluated) reached.keyed

/-- Return one actual owned miss through the existing item and scratch cleanup.
The native and observed-model clients share this composition. It assumes only
the local miss result; every prefix observation is bound to this reached site. -/
theorem TakenSite.Reached.return_verified {base : PairInput.Context (Publication.Effects σ)}
    {source : View} {request : Interner.Request} {debug : AssemblyItem.Fields.Values}
    {before : World (Publication.Effects σ)} {site : TakenSite σ}
    (reached : site.Reached base source request debug before)
    (children : Constructors (Publication.Effects σ)) (owner usizeBits : Nat)
    (meaning : Meaning) (expected : Word) (frame : World (Publication.Effects σ) → Prop)
    (graphSame : site.taken.world.graph = before.graph)
    (locals : ∀ world, frame world → frame
      (returnWorld before.memory.memory.nextId site.constructed.memory.memory.nextId world))
    (checked :
      let p := (context base owner usizeBits children debug).primitives source site.address (ConstructorItem.input request.item debug)
      let ran := Interner.findCode.controlMiss (OwnedCall.execution base.external base.allocator p)
        request site.key site.deterministic ⟨site.taken.world, ⟨some site.lookup, some site.normalized, false⟩⟩
      let actual := OwnedCall.finish base.external base.allocator ran.1 ran.2
      FramePost frame actual ∧ Semantic.Ensures meaning site.taken.world.graph actual.1 actual.2.world.graph
        (fun id after => after.read id = some expected)) :
    let actual := invoke base.external base.budget base.allocator
      ((context base owner usizeBits children debug).primitives source) base.queries source request debug before
    FramePost frame actual ∧ Semantic.Ensures meaning before.graph actual.1 actual.2.world.graph
      (fun id after => after.read id = some expected) := by
  obtain ⟨framed, words⟩ := checked
  have returned := FramePost.locals frame _ before.memory.memory.nextId site.constructed.memory.memory.nextId framed locals
  rw [graphSame] at words
  rw [invoke_after_take base.external base.budget base.allocator
    ((context base owner usizeBits children debug).primitives source) base.queries source request debug before
    site.constructed site.address site.pointer site.memory site.values site.prepared site.taken site.key site.deterministic
    reached.made reached.room reached.allocated reached.initialized reached.classified reached.keyed reached.missed reached.transferred]
  have sameState : site.taken = ⟨site.taken.world, ⟨some site.lookup, some site.normalized, false⟩⟩ := by
    have heldScope := reached.input.origin.scope
    cases stateEq : site.taken
    simp only [stateEq, State.mk.injEq, true_and] at heldScope ⊢
    exact heldScope
  rw [sameState]
  exact ⟨returned, by dsimp only at words ⊢; split <;> exact words⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
