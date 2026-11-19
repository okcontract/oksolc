/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.RepresentativeFrame
import Compiler.Extraction.DispatchDefaultProofs
import Compiler.Extraction.DispatchEffects

namespace Compiler.Extraction.Dispatch
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

structure ConstructorFrames (constructors : Constructors Debug) : Prop where
  operation : ∀ opcode ids debug, Frames (constructors.operation opcode ids debug)
  constant : ∀ value debug, Frames (constructors.constant value debug)
  materialize : ∀ id value debug, Frames (constructors.materialize id value debug)
  borrowedOperation : ∀ address opcode ids debug, Frames (constructors.borrowedOperation address opcode ids debug)
  localOperation : ∀ opcode source selected repeated first debug,
    Frames (constructors.localOperation opcode source selected repeated first debug)

-- Structural proof search emits ordinary kernel-checked terms. Only the effect
-- combinators and constructor frame hypotheses can discharge an action leaf.
syntax "frame_leaf " term : tactic
macro_rules
  | `(tactic| frame_leaf $h) => `(tactic|
    with_reducible first
    | assumption
    | exact ($h).operation _ _ _
    | exact ($h).constant _ _
    | exact ($h).materialize _ _ _
    | exact ($h).borrowedOperation _ _ _ _
    | exact ($h).localOperation _ _ _ _ _ _
    | exact Frames.pure _
    | exact Frames.read _
    | exact Frames.arithmetic _)
syntax "frame_steps " term : tactic
macro_rules
  | `(tactic| frame_steps $h) => `(tactic|
    first
    | frame_leaf $h
    | (apply Frames.bind
       · frame_steps $h
       · intro; frame_steps $h)
    | (split <;> frame_steps $h))

theorem add_word_frames (left right : Word) : Frames (addWord left right) := by
  unfold addWord
  exact Frames.bind _ _ (Frames.arithmetic _) (fun _ => Frames.pure _)

theorem sub_word_frames (left right : Word) : Frames (subWord left right) := by
  unfold subWord
  exact Frames.bind _ _ (Frames.arithmetic _) (fun _ => Frames.pure _)

theorem or_next_frames (stage next : Action (Option NodeId)) (first : Frames stage) (second : Frames next) :
    Frames (orNext stage next) := by
  apply Frames.bind _ _ first
  intro result
  cases result with
  | none => exact second
  | some id => exact Frames.pure _

theorem apply_frames (constructors : Constructors Debug) (framed : ConstructorFrames constructors)
    (replacement : Replacement) (left right : NodeId) (debug : Debug) :
    Frames (zigApply replacement (algebraicBuilder constructors) left right debug) := by
  cases replacement <;> simp only [zigApply, algebraicBuilder, beq_self_eq_true, ↓reduceIte] <;> frame_steps framed

theorem double_iszero_frames (constructors : Constructors Debug) (framed : ConstructorFrames constructors)
    (value : NodeId) (debug : Debug) : Frames (doubleIsZero constructors.operation value debug) := by
  unfold doubleIsZero
  frame_steps framed

theorem drop_repeated_frames (reads : Reads) (constructors : Constructors Debug) (framed : ConstructorFrames constructors)
    (instruction : Opcode) (nestedId repeated : NodeId) (repeatedIsFirst : Bool) (debug : Debug) :
    Frames (dropRepeatedLocal reads constructors.localOperation instruction nestedId repeated repeatedIsFirst debug) := by
  unfold dropRepeatedLocal
  frame_steps framed

theorem reassociate_frames (reads : Reads) (constructors : Constructors Debug) (framed : ConstructorFrames constructors)
    (instruction : Opcode) (nestedId other : NodeId) (nestedIsRight : Bool) (debug : Debug) :
    Frames (reassociate reads constructors instruction nestedId other nestedIsRight debug) := by
  unfold reassociate
  frame_steps framed

theorem remove_shift_mask_frames (reads : Reads) (constructors : Constructors Debug) (framed : ConstructorFrames constructors)
    (maskId shiftedId : NodeId) (debug : Debug) :
    Frames (ShiftMasks.removeCoveredShiftMask reads constructors maskId shiftedId debug) := by
  unfold ShiftMasks.removeCoveredShiftMask
  frame_steps framed

theorem shift_product_frames (reads : Reads) (constructors : Constructors Debug) (framed : ConstructorFrames constructors)
    (value shiftId : NodeId) (debug : Debug) :
    Frames (ShiftMasks.powerOfTwoShiftProduct reads constructors.operation value shiftId debug) := by
  unfold ShiftMasks.powerOfTwoShiftProduct ShiftMasks.powerOfTwoShiftProductWithInputs
  frame_steps framed

theorem signextend_mask_frames (reads : Reads) (constructors : Constructors Debug) (framed : ConstructorFrames constructors)
    (constantId signExtendId : NodeId) (debug : Debug) :
    Frames (SignExtendMask.stripRedundantSignExtendMask reads constructors constantId signExtendId debug) := by
  unfold SignExtendMask.stripRedundantSignExtendMask SignExtendMask.stripRedundantSignExtendMaskWithInputs
  frame_steps framed

theorem net_shift_frames (constructors : Constructors Debug) (framed : ConstructorFrames constructors)
    (opcode : Opcode) (outer inner : Word) (value : NodeId) (debug : Debug) :
    Frames (OppositeShifts.buildNet constructors opcode outer inner value debug) := by
  unfold OppositeShifts.buildNet
  frame_steps framed

theorem opposite_shifts_frames (constructors : Constructors Debug) (framed : ConstructorFrames constructors)
    (opcode : Opcode) (outer inner : Word) (value : NodeId) (debug : Debug) :
    Frames (OppositeShifts.combineOppositeShifts constructors opcode outer inner value debug) := by
  unfold OppositeShifts.combineOppositeShifts
  apply Frames.bind _ _ (Frames.read _)
  intro mask
  apply Frames.bind _ _ (net_shift_frames constructors framed _ _ _ _ _)
  intro shifted
  frame_steps framed

theorem alternating_build_frames (constructors : Constructors Debug) (framed : ConstructorFrames constructors)
    (capture : AlternatingMask.Capture) (debug : Debug) :
    Frames (AlternatingMask.buildCandidate constructors capture debug) := by
  unfold AlternatingMask.buildCandidate AlternatingMask.buildCandidateWithInputs
  frame_steps framed

theorem alternating_search_frames (reads : Reads) (constructors : Constructors Debug) (framed : ConstructorFrames constructors)
    (left right : NodeId) (debug : Debug) (choices : List AlternatingMask.Choice) :
    Frames (AlternatingMask.search reads constructors left right debug choices) := by
  induction choices with
  | nil => exact Frames.pure _
  | cons choice rest ih =>
    simp only [AlternatingMask.search]
    apply Frames.bind _ _ (Frames.read _)
    intro capture
    cases capture with
    | none => exact ih
    | some capture =>
      exact Frames.bind _ _ (alternating_build_frames constructors framed capture debug) (fun _ => Frames.pure _)

theorem alternating_frames (reads : Reads) (constructors : Constructors Debug) (framed : ConstructorFrames constructors)
    (left right : NodeId) (debug : Debug) :
    Frames (AlternatingMask.distributeAlternatingMask reads constructors left right debug) :=
  alternating_search_frames reads constructors framed left right debug _

syntax "dispatch_frame_steps " term : tactic
macro_rules
  | `(tactic| dispatch_frame_steps $h) => `(tactic|
    with_reducible first
    | frame_leaf $h
    | exact apply_frames _ $h _ _ _ _
    | exact double_iszero_frames _ $h _ _
    | exact drop_repeated_frames _ _ $h _ _ _ _ _
    | exact reassociate_frames _ _ $h _ _ _ _ _
    | exact remove_shift_mask_frames _ _ $h _ _ _
    | exact shift_product_frames _ _ $h _ _ _
    | exact signextend_mask_frames _ _ $h _ _ _
    | exact opposite_shifts_frames _ $h _ _ _ _ _
    | exact alternating_frames _ _ $h _ _ _
    | exact add_word_frames _ _
    | exact sub_word_frames _ _
    | (apply Frames.ite <;> dispatch_frame_steps $h)
    | (apply Frames.option
       · dispatch_frame_steps $h
       · intro; dispatch_frame_steps $h)
    | (apply Frames.bind
       · dispatch_frame_steps $h
       · intro; dispatch_frame_steps $h)
    | (split <;> dispatch_frame_steps $h))

theorem constant_stage_frames (reads : Reads) (constructors : Constructors Debug) (framed : ConstructorFrames constructors)
    (instruction : Opcode) (arguments : List NodeId) (debug : Debug) :
    Frames (constantStage reads constructors instruction arguments debug) := by
  unfold constantStage
  frame_steps framed

theorem unary_stage_frames (reads : Reads) (constructors : Constructors Debug) (framed : ConstructorFrames constructors)
    (instruction : Opcode) (value : NodeId) (debug : Debug) :
    Frames (unaryStage reads constructors instruction value debug) := by
  unfold unaryStage unaryStageWithInputs
  frame_steps framed

theorem evm_stage_frames (reads : Reads) (constructors : Constructors Debug) (framed : ConstructorFrames constructors)
    (usizeBits : Nat) (instruction : Opcode) (arguments : List NodeId) (debug : Debug) (version : Version) :
    Frames (evmStage reads constructors usizeBits instruction arguments debug version) := by
  unfold evmStage evmStageWithInputs
  frame_steps framed

/-- Frame preservation is an effect interpretation of the same dispatcher.
Reuse its checked structural composition instead of expanding every opcode. -/
private def frameEffects : Effects Action Action where
  related := fun left _ => Frames left
  pure := Frames.pure
  bind := fun first next => Frames.bind _ _ first next
  lift := Frames.lift

private theorem frameConstructors (constructors : Constructors Debug) (framed : ConstructorFrames constructors) :
    frameEffects.Constructors constructors constructors :=
  ⟨framed.operation, framed.constant, framed.materialize, framed.borrowedOperation, framed.localOperation⟩

theorem binary_stage_frames (reads : Reads) (constructors : Constructors Debug) (framed : ConstructorFrames constructors)
    (usizeBits : Nat) (instruction : Opcode) (left right : NodeId) (debug : Debug) (options : Options) :
    Frames (binaryStage reads constructors usizeBits instruction left right debug options) :=
  frameEffects.binary_stage (frameConstructors constructors framed) reads usizeBits instruction left right debug options

theorem simplify_options_frames (reads : Reads) (constructors : Constructors Debug) (framed : ConstructorFrames constructors)
    (usizeBits : Nat) (instruction : Opcode) (arguments : List NodeId) (debug : Debug) (options : Options) :
    Frames (simplifyWithOptions reads constructors usizeBits instruction arguments debug options) := by
  unfold simplifyWithOptions simplifyOptionsWithInputs
  apply or_next_frames _ _ (constant_stage_frames reads constructors framed instruction arguments debug)
  apply or_next_frames
  · split
    · exact binary_stage_frames reads constructors framed _ _ _ _ _ _
    · exact Frames.pure _
  apply or_next_frames
  · split
    · exact unary_stage_frames reads constructors framed _ _ _
    · exact Frames.pure _
  split
  · exact evm_stage_frames reads constructors framed _ _ _ _ _
  · exact Frames.pure _

theorem simplify_frames (reads : Reads) (constructors : Constructors Debug) (framed : ConstructorFrames constructors)
    (usizeBits : Nat) (instruction : Opcode) (arguments : List NodeId) (debug : Debug) :
    Frames (simplify reads constructors usizeBits instruction arguments debug) :=
  simplify_options_frames reads constructors framed usizeBits instruction arguments debug defaultOptions

end Compiler.Extraction.Dispatch
