/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeDispatchEffects
import Compiler.Extraction.InternerInvocationTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ChildTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- A protocol history accompanies the existing allocator effects. The native
world is retained verbatim; erasure removes only this proof instrumentation.
Protocol events cannot be reconstructed by counting physical host calls. -/
abbrev Recorded (σ ε : Type) := σ × List ε
abbrev TracedWorld (σ ε : Type) := World (Publication.Effects (Recorded σ ε))

def history (world : TracedWorld σ ε) : List ε := world.memory.effects.allocator.2
def erase (world : TracedWorld σ ε) : World (Publication.Effects σ) :=
  world.mapEffects (Publication.Effects.mapAllocator Prod.fst)
def restore (events : List ε) (world : World (Publication.Effects σ)) : TracedWorld σ ε :=
  world.mapEffects (Publication.Effects.mapAllocator (fun effects => (effects, events)))
def prepend (leading : List ε) (effects : Recorded σ ε) : Recorded σ ε :=
  (effects.1, leading ++ effects.2)

@[simp] theorem erase_restore (events : List ε) (world : World (Publication.Effects σ)) :
    erase (restore events world) = world := by
  simp only [erase, restore, World.mapEffects, Session.mapEffects, Publication.Effects.mapAllocator]

@[simp] theorem restore_history (world : TracedWorld σ ε) : restore (history world) (erase world) = world := by
  simp only [history, erase, restore, World.mapEffects, Session.mapEffects, Publication.Effects.mapAllocator]

/-- Record the proper child's supplied observation at its actual native input.
This wrapper proves erasure and event order, not the observation's correctness:
each child body must still derive that observation from its protocol execution. -/
def record (action : GraphAction (Publication.Effects σ) α)
    (observe : World (Publication.Effects σ) → List ε) : GraphAction (Publication.Effects (Recorded σ ε)) α := fun before =>
  let actual := action (erase before)
  (actual.1, restore (history before ++ observe (erase before)) actual.2)

theorem record_erases (action : GraphAction (Publication.Effects σ) α)
    (observe : World (Publication.Effects σ) → List ε) :
    Effect.Transport (World.mapEffects (Publication.Effects.mapAllocator Prod.fst)) (record action observe) action := by
  intro before
  rfl

theorem record_prefix (action : GraphAction (Publication.Effects σ) α)
    (observe : World (Publication.Effects σ) → List ε) (leading : List ε) :
    Effect.Transport (World.mapEffects (Publication.Effects.mapAllocator (prepend leading)))
      (record action observe) (record action observe) := by
  intro before
  simp only [record, erase, history, restore, prepend, World.mapEffects, Session.mapEffects,
    Publication.Effects.mapAllocator, List.append_assoc]

/-- Reuse the existing five-field constructor interface for observations. No
callback request, source address, named-local choice or debug value is erased. -/
abbrev Observations (σ ε : Type) :=
  Associative.Constructors AssemblyItem.Fields.Values (fun _ => World (Publication.Effects σ) → List ε)

def constructors (children : Constructors (Publication.Effects σ)) (observations : Observations σ ε) :
    Constructors (Publication.Effects (Recorded σ ε)) where
  operation := fun opcode values debug => record (children.operation opcode values debug) (observations.operation opcode values debug)
  constant := fun value debug => record (children.constant value debug) (observations.constant value debug)
  materialize := fun id value debug => record (children.materialize id value debug) (observations.materialize id value debug)
  borrowedOperation := fun address opcode values debug =>
    record (children.borrowedOperation address opcode values debug) (observations.borrowedOperation address opcode values debug)
  localOperation := fun opcode source selected repeated first debug =>
    record (children.localOperation opcode source selected repeated first debug) (observations.localOperation opcode source selected repeated first debug)

theorem constructors_erase (children : Constructors (Publication.Effects σ)) (observations : Observations σ ε) :
    (Recursive.erasing (Publication.Effects.mapAllocator Prod.fst)).Constructors (constructors children observations) children :=
  ⟨fun _ _ _ => record_erases _ _, fun _ _ => record_erases _ _, fun _ _ _ => record_erases _ _,
   fun _ _ _ _ => record_erases _ _, fun _ _ _ _ _ _ => record_erases _ _⟩

theorem constructors_prefix (children : Constructors (Publication.Effects σ)) (observations : Observations σ ε) (leading : List ε) :
    (Recursive.erasing (Publication.Effects.mapAllocator (prepend leading))).Constructors
      (constructors children observations) (constructors children observations) :=
  ⟨fun _ _ _ => record_prefix _ _ _, fun _ _ => record_prefix _ _ _, fun _ _ _ => record_prefix _ _ _,
   fun _ _ _ _ => record_prefix _ _ _, fun _ _ _ _ _ _ => record_prefix _ _ _⟩

/-- A history-independent action determines its suffix from the same native
input with no earlier history. This covers the source guard as well as dispatch. -/
theorem action_segment (action : GraphAction (Publication.Effects (Recorded σ ε)) α)
    (independent : ∀ leading, Effect.Transport
      (World.mapEffects (Publication.Effects.mapAllocator (prepend leading))) action action)
    (before : TracedWorld σ ε) :
    let captured := action (restore [] (erase before))
    action before = (captured.1, captured.2.mapEffects (Publication.Effects.mapAllocator (prepend (history before)))) ∧
      history (action before).2 = history before ++ history captured.2 := by
  intro captured
  have prefixed := independent (history before) (restore [] (erase before))
  have restored : (restore [] (erase before)).mapEffects (Publication.Effects.mapAllocator (prepend (history before))) = before := by
    change restore (history before ++ []) (erase before) = before
    simpa only [List.append_nil] using restore_history before
  rw [restored] at prefixed
  exact ⟨prefixed, congrArg (fun pair => history pair.2) prefixed⟩

/-- The full native dispatcher composes child observations in source order.
Running it without history determines the segment; arbitrary previous history
cannot change native reads, child requests, results or reached state. Failure
retains exactly the events emitted before the failing return. -/
theorem dispatcher_segment (leftBase : PairInput.Context (Publication.Effects (Recorded σ ε)))
    (rightBase : PairInput.Context (Publication.Effects σ)) (owner usizeBits : Nat)
    (children : Constructors (Publication.Effects σ)) (observations : Observations σ ε)
    (debug : AssemblyItem.Fields.Values) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (native : AssemblyClone.NativeFields.ItemValue) (key : Key) (owned : ArgumentSlice) (before : TracedWorld σ ε) :
    let left := ((context leftBase owner usizeBits (constructors children observations) debug).primitives source address native).simplify key owned
    let right := ((context rightBase owner usizeBits children debug).primitives source address native).simplify key owned
    let captured := left (restore [] (erase before))
    right (erase before) = (captured.1, erase captured.2) ∧
      left before = (captured.1, captured.2.mapEffects (Publication.Effects.mapAllocator (prepend (history before)))) ∧
      history (left before).2 = history before ++ history captured.2 := by
  intro left right captured
  have erased := dispatcher_erases (Publication.Effects.mapAllocator Prod.fst) leftBase rightBase owner usizeBits
    (constructors_erase children observations) debug source address native key owned (restore [] (erase before))
  have segment := action_segment left (fun leading =>
    dispatcher_erases (Publication.Effects.mapAllocator (prepend leading)) leftBase leftBase owner usizeBits
      (constructors_prefix children observations leading) debug source address native key owned) before
  exact ⟨by simpa only [erase_restore] using erased, segment⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ChildTrace
