/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.ScopedRecursive
import Compiler.Extraction.InternerScopeFrames

namespace Compiler.Extraction.ScopedRecursive
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested

theorem step_frames (r : Scoped.Resources) (p : Primitives) (primitive : Recursive.PrimitiveFrames p)
    (reads : Heap → Reads) (usizeBits : Nat) (find : Recursive.Find) (framed : Recursive.FindFrames find) :
    Recursive.FindFrames (step r p reads usizeBits find) := by
  intro request
  apply Scoped.find_frames r (callbacks p reads usizeBits find) ⟨primitive.insert, primitive.publish⟩
    (fun key before => ?_) request
  exact Dispatch.simplify_frames (reads before) (Recursive.constructors find)
    (Recursive.constructors_frames find framed) usizeBits key.instruction key.arguments () before

/-- Every finite recursive depth, including all failure outcomes and cleanup
effects. No semantic value, arity, or coherent-read premise is needed. -/
theorem unfold_frames (r : Scoped.Resources) (p : Primitives) (primitive : Recursive.PrimitiveFrames p)
    (reads : Heap → Reads) (usizeBits depth : Nat) :
    Recursive.FindFrames (unfold r p reads usizeBits depth) := by
  induction depth with
  | zero => intro request; exact Frames.fail _
  | succ depth ih => exact step_frames r p primitive reads usizeBits _ ih

theorem detailed_frames (r : Scoped.Resources) (p : Primitives) (primitive : Recursive.PrimitiveFrames p)
    (reads : Heap → Reads) (usizeBits depth : Nat) (request : Request) (before : Heap) :
    Extends before (detailed r p reads usizeBits depth request before).2.heap := by
  have framed := unfold_frames r p primitive reads usizeBits depth request before
  simpa only [detailed_projection] using framed

/-- The same execution has both a retained graph prefix and a closed local
scope. This does not identify native addresses or prove word denotations. -/
theorem detailed_preserves (r : Scoped.Resources) (p : Primitives) (primitive : Recursive.PrimitiveFrames p)
    (reads : Heap → Reads) (usizeBits depth : Nat) (request : Request) (before : Heap) :
    Extends before (detailed r p reads usizeBits depth request before).2.heap ∧
      Scoped.Closed (detailed r p reads usizeBits depth request before).2.scope :=
  ⟨detailed_frames r p primitive reads usizeBits depth request before,
    all_scopes_closed r p reads usizeBits depth request before⟩

end Compiler.Extraction.ScopedRecursive
