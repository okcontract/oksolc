/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchFrames
import Compiler.Extraction.Recursive

namespace Compiler.Extraction.Recursive
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul

def FindFrames (find : Find) : Prop := ∀ request, Frames (find request)

structure PrimitiveFrames (p : Primitives) : Prop where
  insert : ∀ key deterministic, Frames (p.insert key deterministic)
  publish : ∀ key id, Frames (p.publish key id)

theorem constructors_frames (find : Find) (framed : FindFrames find) :
    Dispatch.ConstructorFrames (constructors find : Constructors Debug) :=
  ⟨fun _ _ _ => framed _, fun _ _ => framed _, fun _ _ _ => framed _, fun _ _ _ _ => framed _, fun _ _ _ _ _ _ => framed _⟩

theorem miss_frames (code : FindCode) (p : Primitives) (primitive : PrimitiveFrames p)
    (simplify : ∀ key, Frames (p.simplify key)) (request : Request) (key : Key) (deterministic : Bool) :
    Frames (code.miss p request key deterministic) := by
  unfold FindCode.miss
  split
  · apply Frames.bind _ _ (simplify key)
    intro result
    cases result with
    | none => exact primitive.insert key deterministic
    | some id => exact Frames.bind _ _ (primitive.publish _ _) (fun _ => Frames.pure _)
  · exact primitive.insert key deterministic

theorem owned_frames (code : FindCode) (p : Primitives) (primitive : PrimitiveFrames p)
    (simplify : ∀ key, Frames (p.simplify key)) (request : Request) (args : List NodeId) (deterministic : Bool) :
    Frames (code.owned p request args deterministic) := by
  unfold FindCode.owned
  apply Frames.bind _ _ (Frames.local _)
  intro ignored
  exact Frames.bind _ _ (Frames.lift _) (fun key => miss_frames code p primitive simplify request key deterministic)

theorem find_frames (code : FindCode) (p : Primitives) (primitive : PrimitiveFrames p)
    (simplify : ∀ key, Frames (p.simplify key)) (request : Request) : Frames (code.run p request) := by
  unfold FindCode.run
  apply Frames.bind _ _ Frames.get
  intro before
  split
  · exact Frames.fail _
  · apply Frames.bind _ _ (Frames.local _)
    intro args
    apply Frames.bind _ _ (Frames.lift _)
    intro deterministic
    cases deterministic with
    | false => exact owned_frames code p primitive simplify request args false
    | true =>
      apply Frames.bind _ _ (Frames.lift _)
      intro key
      split
      · exact Frames.pure _
      · exact owned_frames code p primitive simplify request args true

theorem simplifier_frames (reads : Heap → Reads) (find : Find) (framed : FindFrames find)
    (usizeBits : Nat) (key : Key) : Frames (simplifier reads find usizeBits key) := by
  intro before
  unfold simplifier operationOnly
  split
  · exact Dispatch.simplify_frames (reads before) (constructors find) (constructors_frames find framed)
      usizeBits key.instruction key.arguments () before
  · exact Extends.refl before

theorem step_frames (p : Primitives) (primitive : PrimitiveFrames p) (reads : Heap → Reads)
    (usizeBits : Nat) (find : Find) (framed : FindFrames find) : FindFrames (step p reads usizeBits find) := by
  intro request
  exact find_frames findCode { p with simplify := simplifier reads find usizeBits }
    ⟨primitive.insert, primitive.publish⟩ (simplifier_frames reads find framed usizeBits) request

/-- No invariant, denotation, arity, coherent-read or recursive-preservation
premise is needed. Insertion and publication frame their input graph; the actual
dispatcher and recursive constructors carry that fact through every outcome. -/
theorem unfold_frames (p : Primitives) (primitive : PrimitiveFrames p) (reads : Heap → Reads)
    (usizeBits depth : Nat) : FindFrames (unfold p reads usizeBits depth) := by
  induction depth with
  | zero => intro request; exact Frames.fail _
  | succ depth ih => exact step_frames p primitive reads usizeBits _ ih

theorem executes_frames (p : Primitives) (primitive : PrimitiveFrames p) (reads : Heap → Reads)
    (usizeBits : Nat) (request : Request) (before after : Heap) (result : Except Error NodeId)
    (execution : Executes p reads usizeBits request before result after) : Extends before after := by
  obtain ⟨depth, ran, _⟩ := execution
  have retained := unfold_frames p primitive reads usizeBits depth request before
  simpa only [ran] using retained

end Compiler.Extraction.Recursive
