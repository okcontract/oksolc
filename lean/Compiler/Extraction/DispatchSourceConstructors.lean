/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.DispatchEffects

namespace Compiler.Extraction.Dispatch.Effects
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul

variable {m n : Type → Type} [Monad m] [Monad n]
  [MonadLift (Except Interner.Error) m] [MonadLift (Except Interner.Error) n]

/-- Child correspondence for source-backed calls. Borrowed arguments must be
the actual slice returned by a graph query. Named locals additionally retain
the source's binary shape and an in-bounds overwrite index. -/
structure SourceConstructors (r : Effects m n) (reads : Reads)
    (left : Associative.Constructors Debug m) (right : Associative.Constructors Debug n) : Prop where
  operation : ∀ opcode ids debug, r.related (left.operation opcode ids debug) (right.operation opcode ids debug)
  constant : ∀ value debug, r.related (left.constant value debug) (right.constant value debug)
  materialize : ∀ id value debug, r.related (left.materialize id value debug) (right.materialize id value debug)
  borrowedOperation : ∀ id queried source, reads.operation id queried = .ok (some source) →
    ∀ opcode debug, r.related (left.borrowedOperation source.address opcode source.items debug)
      (right.borrowedOperation source.address opcode source.items debug)
  localOperation : ∀ id opcode source, reads.operation id opcode = .ok (some source) →
    source.items.length = 2 → ∀ selected, selected < 2 → ∀ repeated first debug,
    r.related (left.localOperation opcode source selected repeated first debug)
      (right.localOperation opcode source selected repeated first debug)

variable {r : Effects m n} {reads : Reads}
  {left : Associative.Constructors Debug m} {right : Associative.Constructors Debug n}

/-- Existing all-input proofs specialize without changing either program. -/
theorem Constructors.source (c : Constructors r left right) : SourceConstructors r reads left right :=
  ⟨c.operation, c.constant, c.materialize, fun _ _ _ _ _ _ => c.borrowedOperation _ _ _ _,
    fun _ _ _ _ _ _ _ _ _ _ => c.localOperation _ _ _ _ _ _⟩

instance : Coe (Constructors r left right) (SourceConstructors r reads left right) := ⟨Constructors.source⟩

/-- Scalar-only helpers use the existing effect lemmas. Their unused storage
entries are the already-defined logical adapters of the operation builder. -/
def scalarConstructors (c : Associative.Constructors Debug m) : Associative.Constructors Debug m :=
  { operation := c.operation, constant := c.constant, materialize := c.materialize }

theorem SourceConstructors.scalars (c : SourceConstructors r reads left right) :
    Constructors r (scalarConstructors left) (scalarConstructors right) :=
  ⟨c.operation, c.constant, c.materialize, fun _ => c.operation,
    fun opcode source selected repeated first debug => c.operation opcode (localArguments source selected repeated first) debug⟩

/-- The dispatcher forwards its current debug value to every constructor.
This adapter makes that one value explicit without changing any call argument. -/
def atDebug (c : Associative.Constructors Debug m) (debug : Debug) : Associative.Constructors Unit m where
  operation := fun opcode ids _ => c.operation opcode ids debug
  constant := fun value _ => c.constant value debug
  materialize := fun id value _ => c.materialize id value debug
  borrowedOperation := fun address opcode ids _ => c.borrowedOperation address opcode ids debug
  localOperation := fun opcode source selected repeated first _ => c.localOperation opcode source selected repeated first debug

/-- Proper children need correspondence only at the current caller's debug
value. In a native induction its admissibility comes from the caller's typed
input; no contract for unrelated or malformed debug values is required. -/
def SourceConstructorsAt (r : Effects m n) (reads : Reads) (debug : Debug)
    (left : Associative.Constructors Debug m) (right : Associative.Constructors Debug n) : Prop :=
  SourceConstructors r reads (atDebug left debug) (atDebug right debug)

theorem SourceConstructors.at (c : SourceConstructors r reads left right) (debug : Debug) :
    SourceConstructorsAt r reads debug left right :=
  ⟨fun opcode ids _ => c.operation opcode ids debug, fun value _ => c.constant value debug,
    fun id value _ => c.materialize id value debug,
    fun id queried source found opcode _ => c.borrowedOperation id queried source found opcode debug,
    fun id opcode source found shape selected bound repeated first _ =>
      c.localOperation id opcode source found shape selected bound repeated first debug⟩

instance {debug : Debug} : Coe (SourceConstructors r reads left right) (SourceConstructorsAt r reads debug left right) :=
  ⟨fun c => c.at debug⟩

end Compiler.Extraction.Dispatch.Effects
