/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationTransferOrigin
import Compiler.Extraction.InternerCallerInit

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- Actual initialization retains every prior allocation and establishes that
any optional normalization owner is fresh before scratch allocation. This is
the frame needed to close an owned cache-hit lookup without transferring it. -/
theorem initialize_origin_frame (external : External σ) (budget allocator : Nat) (source : View)
    (request : Interner.Request) (before : World σ) (memory : Compiler.ZigAir.Memory.State)
    (pointer : Compiler.ZigAir.Memory.Value) (values : List NodeId) (prepared : State σ)
    (good : Good source request.arguments before) (admitted : Admitted external)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (initialized : initLookup external budget allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared)) :
    Initialized allocator source request (.ok values, prepared) ∧ prepared.world.graph = before.graph ∧
      (∀ handle, prepared.scope = { lookup := some handle } →
        InitialFrame before.memory ⟨before.memory.memory.nextId, 0, 2⟩ handle prepared.world.memory) := by
  obtain ⟨valid, represented, scratch, kept⟩ := caller_buffer before.memory memory pointer source request.arguments good.1 good.2 allocated
  have ready := initialize_verified external budget allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request
    { before with memory := { before.memory with memory } } ⟨valid, represented⟩ scratch admitted
  have graph := initialize_graph external budget allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request
    ⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩
  rw [initialized] at ready graph
  refine ⟨ready, graph, ?_⟩
  unfold initLookup at initialized
  cases decoded : Interner.Scoped.commutative request.item with
  | error fault => simp only [decoded, Prod.mk.injEq] at initialized; cases initialized.1
  | ok commutative =>
    simp only [decoded] at initialized
    cases ran : init normalizationOwnershipCode external budget allocator commutative source
        ⟨before.memory.memory.nextId, 0, 2⟩ request.arguments { before.memory with memory } with
    | mk result session =>
      rw [ran] at initialized
      cases result with
      | error failure => cases initialized
      | ok handle =>
        have same := Prod.mk.inj initialized
        rcases same with ⟨sameValues, sameState⟩
        cases sameValues
        subst prepared
        have frame := init_frame external budget allocator commutative source ⟨before.memory.memory.nextId, 0, 2⟩
          request.arguments { before.memory with memory } session handle valid represented (scratch commutative) admitted ran
        intro selected scope
        have sameHandle : handle = selected := Option.some.inj (congrArg Local.lookup scope)
        subst selected
        refine ⟨?_, frame.registry, ?_⟩
        · intro id cell found _
          have older := (Compiler.ZigAir.Memory.valid_lookup _ _ _ good.1.memory found).1
          exact frame.memory id cell (kept id cell found) (by dsimp only; omega)
        · intro owned ownership
          cases present : before.memory.memory.heap.lookup owned.address with
          | none => rfl
          | some cell =>
            have absent := frame.freshOwned owned ownership
            rw [kept owned.address cell present] at absent
            cases absent

/-- The actual scratch allocation and initializer establish the lookup state
and retain every allocation that preceded that scratch frame. -/
theorem initialize_origin (external : External σ) (budget allocator : Nat) (source : View)
    (request : Interner.Request) (before : World σ) (memory : Compiler.ZigAir.Memory.State)
    (pointer : Compiler.ZigAir.Memory.Value) (values : List NodeId) (prepared : State σ)
    (good : Good source request.arguments before) (admitted : Admitted external)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (initialized : initLookup external budget allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared)) :
    Initialized allocator source request (.ok values, prepared) ∧ prepared.world.graph = before.graph ∧
      (∀ id cell, before.memory.memory.heap.lookup id = some cell → prepared.world.memory.memory.heap.lookup id = some cell) ∧
      (∀ id block, before.memory.heap id = some block → prepared.world.memory.heap id = some block) := by
  obtain ⟨ready, graph, origin⟩ := initialize_origin_frame external budget allocator source request before memory pointer
    values prepared good admitted allocated initialized
  refine ⟨ready, graph, ?_⟩
  obtain ⟨handle, scope, _, _, _⟩ := ready
  have frame := origin handle scope
  refine ⟨?_, frame.registry⟩
  intro id cell found
  have older := (Compiler.ZigAir.Memory.valid_lookup _ _ _ good.1.memory found).1
  exact frame.memory id cell found (by dsimp only; omega)

/-- Ownership at the actual caller's take boundary, relative to its state
before stack-buffer allocation. Later recursive calls still have to preserve
these facts; no recursive preservation is built into this predicate. -/
structure Origin (allocator : Nat) (source : View) (request : Interner.Request)
    (values : List NodeId) (before : World σ) (after : State σ)
    (slice : ArgumentSlice) (remaining : Handle) : Prop where
  scope : after.scope = ⟨some remaining, some slice, false⟩
  detached : remaining.owned = none
  held : Held allocator source request.arguments slice after.world
  contents : Represents after.world.memory.memory (view slice) values
  aligned : slice.items = values
  normalized : normalizeCode.run InsertionSort.sortIds request.item request.arguments = some values
  graph : after.world.graph = before.graph
  memory : ∀ id cell, before.memory.memory.heap.lookup id = some cell →
    after.world.memory.memory.heap.lookup id = some cell
  registry : ∀ id block, before.memory.heap id = some block → after.world.memory.heap id = some block
  fresh : ∀ id block, before.memory.heap id = some block → slice.address ≠ id
  freshNative : ∀ id cell, before.memory.memory.heap.lookup id = some cell → slice.address ≠ id

/-- Derive the native scratch permissions, normalized ownership and frame of
all prior allocations from the caller's actual stack allocation, initializer
and take. The production commutativity decision is inspected, not assumed. -/
theorem take_origin (external : External σ) (budget allocator : Nat) (source : View)
    (request : Interner.Request) (before : World σ) (memory : Compiler.ZigAir.Memory.State)
    (pointer : Compiler.ZigAir.Memory.Value) (values : List NodeId) (prepared after : State σ)
    (good : Good source request.arguments before) (admitted : Admitted external)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (initialized : initLookup external budget allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))
    (taken : take external allocator prepared = (.ok (), after)) :
    ∃ slice remaining, Origin allocator source request values before after slice remaining := by
  obtain ⟨valid, represented, scratch, kept⟩ := caller_buffer before.memory memory pointer source request.arguments good.1 good.2 allocated
  unfold initLookup at initialized
  cases decoded : Interner.Scoped.commutative request.item with
  | error fault => simp only [decoded] at initialized; cases initialized
  | ok commutative =>
    simp only [decoded] at initialized
    cases ran : init normalizationOwnershipCode external budget allocator commutative source
        ⟨before.memory.memory.nextId, 0, 2⟩ request.arguments { before.memory with memory } with
    | mk result session =>
      rw [ran] at initialized
      cases result with
      | error failure => cases initialized
      | ok handle =>
        have same := Prod.mk.inj initialized
        rcases same with ⟨sameValues, sameState⟩
        cases sameValues
        subst prepared
        simp only [take] at taken
        cases transferred : takeOwned normalizationOwnershipCode external allocator handle session with
        | mk result reached =>
          rw [transferred] at taken
          cases result with
          | error fault => cases taken
          | ok pair =>
            rcases pair with ⟨slice, remaining⟩
            have sameState := (Prod.mk.inj taken).2
            subst after
            obtain ⟨post, normalizedValues, frame, fresh, freshNative⟩ := initialized_take_origin external budget allocator commutative source
              ⟨before.memory.memory.nextId, 0, 2⟩ request.arguments { before.memory with memory } session reached handle remaining slice
              valid represented (scratch commutative) admitted ran transferred
            refine ⟨slice, remaining, rfl, post.detached, ⟨⟨post.ready.valid, post.ready.source⟩, post.live, post.separate⟩,
              post.contents, post.values, ?_, rfl, ?_, frame.registry, fresh, ?_⟩
            · rw [← post.values, normalizedValues]
              exact normalized_projection request.item commutative source request.arguments good.2.1 decoded
            · intro id cell found
              have older := (Compiler.ZigAir.Memory.valid_lookup before.memory.memory id cell good.1.memory found).1
              exact frame.memory id cell (kept id cell found) (by dsimp only; omega)
            · intro id cell found
              have older := (Compiler.ZigAir.Memory.valid_lookup before.memory.memory id cell good.1.memory found).1
              exact freshNative id cell (kept id cell found) (by dsimp only; omega)

/-- Once the actual caller has detached the handle, outer lookup destruction
needs no ownership premise about the normalized slice. This also applies after
an insertion has consumed that slice and changed the world. -/
theorem Origin.deinit (external : External σ) (allocator : Nat) (source : View) (request : Interner.Request)
    (values : List NodeId) (before : World σ) (after : State σ) (slice : ArgumentSlice) (remaining : Handle)
    (origin : Origin allocator source request values before after slice remaining)
    (reached : World σ) (handedOff : Bool) :
    deinit external allocator ⟨reached, { after.scope with handedOff }⟩ =
      (.ok (), ⟨reached, { after.scope with lookup := none, handedOff }⟩) := by
  exact deinit_detached external allocator _ remaining
    (by rw [origin.scope]) origin.detached

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller
