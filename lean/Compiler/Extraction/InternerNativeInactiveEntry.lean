/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeConstructorWords
import Compiler.Extraction.InternerEnclosingNativeMiss

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- An inactive simplification guard needs no recursive child correspondence.
The original parent and native insertion reducer derive every entry frame.
The existing logical constructor witness is unused behind the false guard. -/
theorem Enclosing.inactive_entry_frames (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits : Nat) (base : PairInput.Context (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (children : Constructors (Publication.Effects σ))
    (env : AddressMask.Environment) (other : Meaning) (debug : AssemblyItem.Fields.Values)
    (source : View) (request : Interner.Request) (before : World (Publication.Effects σ)) (rows : List Storage.Cell)
    (parent : World (Publication.Effects σ) → Prop)
    (stack : Enclosing safety base.allocator owner parent) (initial : parent before)
    (valid : Valid before.memory) (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (admitted : Admitted ops.arguments) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (inactive : ∀ site : ProtocolTrace.TakenSite σ,
      site.Reached (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth) source request debug before →
      (site.deterministic && (request.item.kind == 1)) = false) :
    EntryFrames safety owner usizeBits
      (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth)
      children source request debug before rows parent env other where
  retained := fun _ good graph kept => stack.retained initial good graph kept
  localParent := by
    intro constructed address made
    have prepared := (prepare_success request.item debug before constructed address valid domain typed made).2
    exact stack.locals initial _ _ (Nat.le_refl _) (by rw [prepared.nextId]; omega)
  taken := by
    intro constructed address pointer memory values prepared taken key normalized lookup deterministic
      made room allocated initialized classified keyed missed transferred entry
    let site : ProtocolTrace.TakenSite σ :=
      ⟨constructed, address, pointer, memory, values, prepared, taken, key, normalized, lookup, deterministic⟩
    have reached : site.Reached
        (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth) source request debug before :=
      ⟨made, room, allocated, initialized, classified, keyed, missed, transferred, entry⟩
    have item := (prepare_success request.item debug before constructed address valid domain typed made).2
    have parentConstructed := stack.retained initial item.valid item.graph
      ⟨congrArg Publication.Effects.keys item.effects, item.memory, fun _ _ found => item.heap ▸ found⟩
    have frames := stack.native_miss_frames parentConstructed entry.origin rows address (input request.item debug)
      ops allocate growth (Dispatch.wordDispatchMeaning env other)
      ((context (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth)
        owner usizeBits children debug).primitives source address (input request.item debug))
      rfl rfl key deterministic (deterministic && (request.item.kind == 1)) admitted entry.publication.aligned domain
    have notSelected : (deterministic && (request.item.kind == 1)) ≠ true := by
      rw [inactive site reached]
      decide
    refine ⟨fun _ => 0, Compiler.Extraction.Recursive.constructors (fun _ => Interner.fail .unsupported), ?_⟩
    exact ⟨fun selected => (notSelected selected).elim, frames,
      fun selected => (notSelected selected).elim, fun selected => (notSelected selected).elim,
      fun selected => (notSelected selected).elim⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
