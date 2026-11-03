/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeStep
import Compiler.Extraction.InternerNativeEntry
import Compiler.Extraction.InternerCallerRecursionEffects
import Compiler.Extraction.InternerEnclosingNativeMiss

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Recursive

variable (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits : Nat) (base : PairInput.Context (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning)
    (debug : AssemblyItem.Fields.Values) (rows : List Storage.Cell)
    (parent : World (Publication.Effects σ) → Prop)

local notation "nativeBase" => callerContext ops allocate safety owner meaning base growth

/-- Close native suffix and original-return frames at an actual taken site.
Only the proper children's source-guarded native frame law remains. Item
preparation, insertion/publication and enclosing cleanup use their existing
proofs; no child model, final frame or word theorem is an input. -/
theorem Enclosing.taken_invocation_frame (children : Constructors (Publication.Effects σ))
    (source : View) (request : Interner.Request) (before : World (Publication.Effects σ))
    (site : ProtocolTrace.TakenSite σ) (reached : site.Reached nativeBase source request debug before)
    (stack : Enclosing safety base.allocator owner parent) (initial : parent before)
    (data : Compiler.ZigAir.Memory.Address) (capacity : Nat)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (privateSource : Caller.SourcePrivate source before.memory.effects.keys)
    (array : ArraySource source before.memory.memory)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (admitted : Admitted ops.arguments) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (proper : (site.deterministic && (request.item.kind == 1)) = true →
      (keeping (CallFrame safety base.allocator owner rows source request.arguments site.normalized site.address
        (input request.item debug) parent)).SourceConstructorsAt (Nested.storageReads rows) debug children children) :
    FramePost (GraphFrame safety base.allocator owner rows parent)
      (invoke (nativeBase).external base.budget base.allocator
        ((context nativeBase owner usizeBits children debug).primitives source) base.queries source request debug before) := by
  obtain ⟨item, constructedFacts, parentConstructed, inputFrame, _⟩ :=
    reached.native_inputs facts privateSource array domain typed (fun _ valid graph kept => stack.retained initial valid graph kept)
  have frames := stack.native_miss_frames parentConstructed reached.input.origin rows site.address (input request.item debug)
    ops allocate growth meaning
    ((context nativeBase owner usizeBits children debug).primitives source site.address (input request.item debug))
    rfl rfl site.key site.deterministic (site.deterministic && (request.item.kind == 1)) admitted reached.input.publication.aligned domain
  obtain ⟨ownerCell, ownerFound, _, _⟩ := facts.ownerLive
  have ownerOlder := (Compiler.ZigAir.Memory.valid_lookup _ _ _ facts.valid.memory ownerFound).1
  have ordered : before.memory.memory.nextId ≤ site.constructed.memory.memory.nextId := by rw [item.nextId]; omega
  have locals := GraphFrame.locals safety base.allocator owner rows parent before.memory.memory.nextId
    site.constructed.memory.memory.nextId ownerOlder ordered
    (stack.locals initial _ _ (Nat.le_refl _) ordered)
  exact invoke_step_frame safety owner usizeBits nativeBase children source request debug before site.constructed site.address
    site.pointer site.memory site.values site.prepared site.taken site.key site.normalized site.lookup rows constructedFacts reached.input
    (by rw [item.effects]; exact privateSource) (array.frame (fun _ cell found => item.memory _ cell found))
    parent (GraphFrame safety base.allocator owner rows parent) inputFrame.parent locals reached.made reached.room
    reached.allocated reached.initialized reached.keyed reached.transferred site.deterministic proper frames reached.classified reached.missed

/-- The actual successor borrowed constructor consumes the native frame step
with proper children at the lower depth. Every opcode is allowed. A reached
taken site is still required; this does not assert all-entry admission or the
induction hypothesis for the lower constructors. -/
theorem Enclosing.taken_borrowed_frame (depth : Nat) (opcode : Opcode) (borrowed : ArgumentSlice)
    (before : World (Publication.Effects σ)) (site : ProtocolTrace.TakenSite σ)
    (reached : site.Reached nativeBase (view borrowed) (Interner.constructorCode.operationRequest opcode borrowed.items) debug before)
    (stack : Enclosing safety base.allocator owner parent) (initial : parent before)
    (data : Compiler.ZigAir.Memory.Address) (capacity : Nat)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (privateSource : Caller.SourcePrivate (view borrowed) before.memory.effects.keys)
    (array : ArraySource (view borrowed) before.memory.memory)
    (admitted : Admitted ops.arguments) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (proper : site.deterministic = true →
      (keeping (CallFrame safety base.allocator owner rows (view borrowed) borrowed.items site.normalized site.address
        (input (Interner.constructorCode.operationRequest opcode borrowed.items).item debug) parent)).SourceConstructorsAt
          (Nested.storageReads rows) debug (unfold nativeBase owner usizeBits depth) (unfold nativeBase owner usizeBits depth)) :
    let actual := (unfold nativeBase owner usizeBits (depth + 1)).borrowedOperation borrowed.address opcode borrowed.items debug before
    ordinary actual.1 = true → GraphFrame safety base.allocator owner rows parent actual.2 := by
  have checked := stack.taken_invocation_frame ops allocate safety owner usizeBits base growth meaning debug rows parent
    (unfold nativeBase owner usizeBits depth) (view borrowed) (Interner.constructorCode.operationRequest opcode borrowed.items)
    before site reached initial data capacity facts privateSource array
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) admitted typed
    (by simpa only [Interner.ConstructorCode.operationRequest, Interner.constructorCode, Scalar.run,
      beq_self_eq_true, Bool.and_true] using proper)
  dsimp only
  intro completed
  exact (checked completed).2

/-- Close every native entry route under the proper-child frame hypothesis.
The shared entry decomposition derives either a retained leaf or an actual
taken site. Neither successful entry nor semantic child correctness is assumed. -/
theorem Enclosing.invocation_frame (children : Constructors (Publication.Effects σ))
    (source : View) (request : Interner.Request) (before : World (Publication.Effects σ))
    (stack : Enclosing safety base.allocator owner parent) (initial : parent before)
    (data : Compiler.ZigAir.Memory.Address) (capacity : Nat)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (represented : Represents before.memory.memory source request.arguments)
    (privateSource : Caller.SourcePrivate source before.memory.effects.keys)
    (array : ArraySource source before.memory.memory)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (admitted : Admitted ops.arguments) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (proper : ∀ site : ProtocolTrace.TakenSite σ, site.Reached nativeBase source request debug before →
      (site.deterministic && (request.item.kind == 1)) = true →
      (keeping (CallFrame safety base.allocator owner rows source request.arguments site.normalized site.address
        (input request.item debug) parent)).SourceConstructorsAt (Nested.storageReads rows) debug children children) :
    FramePost (GraphFrame safety base.allocator owner rows parent)
      (invoke (nativeBase).external base.budget base.allocator
        ((context nativeBase owner usizeBits children debug).primitives source) base.queries source request debug before) := by
  intro completed
  rcases invocation_entry safety owner usizeBits capacity nativeBase ops.arguments children source request debug before data rows
      rfl facts represented privateSource admitted domain typed completed with leaf | ⟨site, reached⟩
  · exact ⟨leaf.closed, leaf.parent (fun _ valid graph kept => stack.retained initial valid graph kept)⟩
  · exact stack.taken_invocation_frame ops allocate safety owner usizeBits base growth meaning debug rows parent
      children source request before site reached initial data capacity facts privateSource array domain admitted typed
      (proper site reached) completed

/-- The successor borrowed constructor consumes the all-entry frame proof
with the actual lower-depth children. Admission, representation and the
proper-child frame hypothesis remain explicit; word/resource induction is separate. -/
theorem Enclosing.borrowed_frame (depth : Nat) (opcode : Opcode) (borrowed : ArgumentSlice)
    (before : World (Publication.Effects σ))
    (stack : Enclosing safety base.allocator owner parent) (initial : parent before)
    (data : Compiler.ZigAir.Memory.Address) (capacity : Nat)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (represented : Represents before.memory.memory (view borrowed) borrowed.items)
    (privateSource : Caller.SourcePrivate (view borrowed) before.memory.effects.keys)
    (array : ArraySource (view borrowed) before.memory.memory)
    (admitted : Admitted ops.arguments) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (proper : ∀ site : ProtocolTrace.TakenSite σ,
      site.Reached nativeBase (view borrowed) (Interner.constructorCode.operationRequest opcode borrowed.items) debug before →
      site.deterministic = true →
      (keeping (CallFrame safety base.allocator owner rows (view borrowed) borrowed.items site.normalized site.address
        (input (Interner.constructorCode.operationRequest opcode borrowed.items).item debug) parent)).SourceConstructorsAt
          (Nested.storageReads rows) debug (unfold nativeBase owner usizeBits depth) (unfold nativeBase owner usizeBits depth)) :
    let actual := (unfold nativeBase owner usizeBits (depth + 1)).borrowedOperation borrowed.address opcode borrowed.items debug before
    ordinary actual.1 = true → GraphFrame safety base.allocator owner rows parent actual.2 := by
  have checked := stack.invocation_frame ops allocate safety owner usizeBits base growth meaning debug rows parent
    (unfold nativeBase owner usizeBits depth) (view borrowed) (Interner.constructorCode.operationRequest opcode borrowed.items)
    before initial data capacity facts represented privateSource array
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) admitted typed
    (by simpa only [Interner.ConstructorCode.operationRequest, Interner.constructorCode, Scalar.run,
      beq_self_eq_true, Bool.and_true] using proper)
  dsimp only
  intro completed
  exact (checked completed).2

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
