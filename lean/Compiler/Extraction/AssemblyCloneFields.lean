/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyItemInitializers
import Compiler.Extraction.AssemblyClonePhysical

namespace Compiler.Extraction.AssemblyClone.NativeFields
open Compiler.ZigAir.Memory
open AssemblyItem AssemblyItem.Fields

/-- Reuse the complete evaluated member register as clone metadata. Kind,
instruction and data come from the existing key item, and verbatim comes from
the cloned payload. Those four metadata selectors are deliberately ignored;
every other member, including borrowed debug descriptors, is copied exactly. -/
abbrev ItemValue := AssemblyClone.Value Values

def payloadValue (payload : Verbatim) : ObjectValue := .fields [
  (verbatim_argumentsOffset, .leaf (.scalar (.int false 64 payload.arguments))),
  (verbatim_return_variablesOffset, .leaf (.scalar (.int false 64 payload.returns))),
  (verbatim_dataOffset, .leaf (.slice (.slice true (.scalar (.int false 8)))
    ⟨payload.data.address, payload.data.offset⟩ payload.data.contents.length))]

def verbatimValue (payload : Option Verbatim) : Compiler.ZigAir.Memory.Value :=
  .optionalObject verbatimType ⟨40, 8⟩ (payload.map payloadValue)

def values (input : ItemValue) : Values
  | .kind => AssemblyItem.Initializers.construct input.item input.metadata .kind
  | .instruction => AssemblyItem.Initializers.construct input.item input.metadata .instruction
  | .data => AssemblyItem.Initializers.construct input.item input.metadata .data
  | .verbatim => verbatimValue input.verbatim
  | selected => input.metadata selected

theorem key_fields (input : ItemValue) :
    values input .kind = .scalar (.int true 32 input.item.kind.toNat) ∧
    values input .instruction = OptionalScalar.byteValue input.item.instruction ∧
    values input .data = .scalar (.int false 256 input.item.data.toNat) := ⟨rfl, rfl, rfl⟩

/-- Initial native field correspondence, including the complete optional payload
descriptor. Pointee reads remain the existing clone copy operation's checks. -/
def Represents (state : State) (source : Address) (input : ItemValue) : Prop :=
  ∀ selected, member state source selected = .ok (values input selected)

theorem Represents.typed (represented : Represents state source input) : (values input).Typed := by
  intro selected
  exact readTyped_typed state source selected.offset selected.type _ (represented selected)

theorem Represents.backed (represented : Represents state source input) :
    ∃ cell, state.heap.lookup source.allocation = some cell ∧ acceptsView cell.type source.offset viewType = true := by
  have viewed := (readTyped_parts state source Member.kind.offset Member.kind.type _ (represented .kind)).1
  obtain ⟨_, layout, cell, _, _, accessed, shape⟩ := recordView_parent state viewType false false _ _ source _ viewed
  exact ⟨cell, (access_success_region state source layout false cell accessed).1, shape⟩

theorem Represents.live (represented : Represents state source input) :
    ∃ cell, state.heap.lookup source.allocation = some cell := by
  obtain ⟨cell, found, _⟩ := represented.backed
  exact ⟨cell, found⟩

/-- A successfully read item cannot occupy a normalized argument word array,
including at an interior offset. Separation follows from the typed view. -/
theorem Represents.apart_words (represented : Represents state source input)
    (id length : Nat) (cell : Allocation) (found : state.heap.lookup id = some cell)
    (typed : cell.type = .array length WordArray.word) : source.allocation ≠ id := by
  intro same
  obtain ⟨actual, located, viewed⟩ := represented.backed
  rw [same, found] at located
  cases Option.some.inj located
  simp [typed, WordArray.word, acceptsView, Ty.project, viewType] at viewed

theorem Represents.frame (represented : Represents before source input)
    (same : after.heap.lookup source.allocation = before.heap.lookup source.allocation) :
    Represents after source input := by
  intro selected
  exact (readTyped_frame before after source selected.offset selected.type same).trans (represented selected)

/-- The actual represented members supply the operation-query relation before
or after publication. Native validity, allocation identity and type stay explicit; no
installation origin or final query agreement is required. -/
theorem Represents.query (represented : Represents state ⟨object, 0⟩ copied) (logical : Storage.Cell)
    (cell : Allocation) (valid : state.valid = true)
    (found : state.heap.lookup object = some cell) (typed : cell.type = AssemblyItem.viewType)
    (address : logical.itemAddress = object) (item : logical.item = copied.item)
    (domain : (copied.item.kind.toNat : Int) ∈ itemTagValues) :
    RepresentativeArray.Operation.Item state logical := by
  apply Query.of_members state logical cell valid (address.symm ▸ found) typed (item.symm ▸ domain)
  · simpa only [address, item, (key_fields copied).1] using represented .kind
  · simpa only [address, item, (key_fields copied).2.1] using represented .instruction

theorem payload_typed_same (original copied : Verbatim)
    (arguments : copied.arguments = original.arguments) (returns : copied.returns = original.returns)
    (contents : copied.data.contents = original.data.contents) :
    (payloadValue copied).hasType verbatimType = (payloadValue original).hasType verbatimType := by
  simp only [payloadValue, ObjectValue.hasType, objectFieldsTyped, verbatimType, Field.type,
    Value.type, Value.valid, arguments, returns, contents]

theorem values_typed_same (original copied : ItemValue) (same : SameValue original copied)
    (typed : (values original).Typed) : (values copied).Typed := by
  intro selected
  have fieldTyped := typed selected
  have item := same.1
  have metadata := same.2.1
  cases selected with
  | verbatim =>
    have fields := same.2.2
    have originalTyped := fieldTyped
    cases old : original.verbatim <;> cases new : copied.verbatim
    · simpa only [values, new, old] using originalTyped
    · simp [old, new] at fields
    · simp [old, new] at fields
    · rename_i originalPayload copiedPayload
      simp only [old, new, Option.map_some, Option.some.injEq, Prod.mk.injEq] at fields
      rcases fields with ⟨arguments, returns, contents⟩
      simpa only [values, verbatimValue, old, new, Option.map_some, Value.hasType, Value.type,
        Value.valid, payload_typed_same originalPayload copiedPayload arguments returns contents] using originalTyped
  | _ => simpa only [values, item, metadata] using fieldTyped

theorem payload_owned_frame (allocator object : Nat) (slice : AssemblyItemDeinit.Bytes)
    (before : Compiler.Extraction.Memory.Arguments.Normalization.Session σ) (after : State)
    (written : Written fields object members before.memory after)
    (itemOwned : AssemblyItem.Owned allocator object before)
    (payloadOwned : AssemblyItemDeinit.Owned allocator slice before) :
    AssemblyItemDeinit.Owned allocator slice { before with memory := after } := by
  by_cases empty : slice.length = 0
  · exact Or.inl empty
  · have apart := AssemblyItem.payload_ne allocator object slice before itemOwned payloadOwned empty
    obtain ⟨stored, cell, found, typed, writable, stack, offset⟩ := payloadOwned.resolve_left empty
    exact Or.inr ⟨stored, cell, (written.frame slice.address apart).trans found, typed, writable, stack, offset⟩

theorem payload_reads_frame (allocator object : Nat) (bytes : Bytes)
    (before : Compiler.Extraction.Memory.Arguments.Normalization.Session σ) (after : State)
    (written : Written fields object members before.memory after)
    (itemOwned : AssemblyItem.Owned allocator object before)
    (payloadOwned : AssemblyItemDeinit.Owned allocator (Physical.descriptor bytes) before)
    (reads : Physical.Reads before.memory bytes) : Physical.Reads after bytes := by
  by_cases empty : bytes.contents = []
  · intro value index present; simp [empty] at present
  · have nonempty : (Physical.descriptor bytes).length ≠ 0 := by
      intro zero
      exact empty (List.eq_nil_of_length_eq_zero zero)
    have apart := AssemblyItem.payload_ne allocator object (Physical.descriptor bytes) before itemOwned payloadOwned nonempty
    exact reads.frame before.memory after bytes (written.frame bytes.address apart)

def install (copied : ItemValue) (object : Nat)
    (before : Compiler.Extraction.Memory.Arguments.Normalization.Session σ) :
    Except Compiler.ZigAir.Memory.Fault (Compiler.Extraction.Memory.Arguments.Normalization.Session σ) :=
  (assign (values copied) object before.memory).map (fun memory => { before with memory })

theorem install_assigned (copied : ItemValue) (object : Nat)
    (before : Compiler.Extraction.Memory.Arguments.Normalization.Session σ) (after : State)
    (assigned : assign (values copied) object before.memory = .ok after) :
    install copied object before = .ok { before with memory := after } := by
  unfold install
  generalize values copied = fields at assigned ⊢
  exact congrArg (fun result => result.map (fun memory => { before with memory })) assigned

theorem install_unchanged (copied : ItemValue) (object : Nat)
    (before : Compiler.Extraction.Memory.Arguments.Normalization.Session σ)
    (assigned : assign (values copied) object before.memory = .ok before.memory) :
    install copied object before = .ok before :=
  (install_assigned copied object before before.memory assigned).trans rfl

structure Installed (allocator object : Nat) (copied : ItemValue)
    (before after : Compiler.Extraction.Memory.Arguments.Normalization.Session σ) : Prop where
  written : Written (values copied) object members before.memory after.memory
  heap : after.heap = before.heap
  effects : after.effects = before.effects
  valid : Compiler.Extraction.Memory.Arguments.Normalization.Valid after
  owned : AssemblyItem.Owned allocator object after
  reads : ∀ selected, member after.memory ⟨object, 0⟩ selected = .ok (values copied selected)
  payload : ∀ slice, Physical.payload copied = some slice → AssemblyItemDeinit.Owned allocator slice after
  contents : ∀ payload, copied.verbatim = some payload → Physical.Reads after.memory payload.data

/-- The same installed clone supplies the query item relation. The logical
cell retains its evaluated descriptor fields and must name this clone's item. -/
theorem Installed.query (installed : Installed allocator object copied before after) (logical : Storage.Cell)
    (address : logical.itemAddress = object) (item : logical.item = copied.item)
    (domain : (copied.item.kind.toNat : Int) ∈ itemTagValues) :
    RepresentativeArray.Operation.Item after.memory logical := by
  obtain ⟨cell, found, typed, _⟩ := installed.owned.2
  exact Represents.query installed.reads logical cell installed.valid.memory found typed address item domain

/-- Complete assignment follows from initial object ownership and a typed
evaluated clone. Payload ownership and byte reads are framed using registry
separation, rather than a caller-provided blanket disjointness assumption. -/
theorem install_total (allocator object : Nat) (copied : ItemValue)
    (before : Compiler.Extraction.Memory.Arguments.Normalization.Session σ)
    (typed : (values copied).Typed) (valid : Compiler.Extraction.Memory.Arguments.Normalization.Valid before)
    (owned : AssemblyItem.Owned allocator object before)
    (payloadOwned : ∀ slice, Physical.payload copied = some slice → AssemblyItemDeinit.Owned allocator slice before)
    (payloadReads : ∀ payload, copied.verbatim = some payload → Physical.Reads before.memory payload.data) :
    ∃ after, install copied object before = .ok after ∧ Installed allocator object copied before after := by
  obtain ⟨cell, found, cellTyped, writable, _⟩ := owned.2
  obtain ⟨memory, assigned, written, readback⟩ := assign_total (values copied) object before.memory cell
    typed valid.memory found cellTyped writable
  have session := written.session (values copied) allocator object members before memory valid owned
  refine ⟨{ before with memory }, ?_, written, rfl, rfl, session.1, session.2, readback, ?_, ?_⟩
  · exact install_assigned copied object before memory assigned
  · intro slice selected
    exact payload_owned_frame allocator object slice before memory written owned (payloadOwned slice selected)
  · intro payload selected
    have descriptor : Physical.payload copied = some (Physical.descriptor payload.data) := by simp [Physical.payload, selected]
    exact payload_reads_frame allocator object payload.data before memory written owned
      (payloadOwned _ descriptor) (payloadReads payload selected)

inductive SourceFault where
  | memory (selected : Member) (reason : Compiler.ZigAir.Memory.Fault)
  | mismatch (selected : Member)
  deriving DecidableEq, Repr

/-- Admit the initial native `self.*` through every existing typed member read.
This does not read payload bytes: allocation still precedes those reads in the
existing clone operation. The check is a model admission, not a native branch. -/
def checkMembers (state : State) (source : Address) (input : ItemValue) : List Member → Except SourceFault Unit
  | [] => .ok ()
  | selected :: rest => match member state source selected with
    | .error reason => .error (.memory selected reason)
    | .ok value => if value = values input selected then checkMembers state source input rest
        else .error (.mismatch selected)

def checkSource (state : State) (source : Address) (input : ItemValue) : Except SourceFault Unit :=
  checkMembers state source input members

theorem checkMembers_iff (state : State) (source : Address) (input : ItemValue) (selected : List Member) :
    checkMembers state source input selected = .ok () ↔
      ∀ field, field ∈ selected → member state source field = .ok (values input field) := by
  induction selected with
  | nil => simp [checkMembers]
  | cons field rest ih =>
    cases read : member state source field with
    | error reason => simp [checkMembers, read]
    | ok value =>
      by_cases same : value = values input field
      · simp [checkMembers, read, same, ih]
      · simp [checkMembers, read, same]

theorem checkSource_iff (state : State) (source : Address) (input : ItemValue) :
    checkSource state source input = .ok () ↔ Represents state source input := by
  rw [checkSource, checkMembers_iff]
  exact ⟨fun checked field => checked field (members_complete field), fun represented field _ => represented field⟩

/-- Actual clone execution supplies the copied payload and its ownership. The
initial native fields supply typing; complete assignment and every final read
are conclusions, not premises. -/
theorem clone_install (request : Physical.Allocate σ) (allocator object : Nat) (source : Address)
    (input copied : ItemValue) (before middle : Compiler.Extraction.Memory.Arguments.Normalization.Session σ)
    (initial : Compiler.Extraction.Memory.Arguments.Normalization.Valid before)
    (represented : Represents before.memory source input) (owned : AssemblyItem.Owned allocator object before)
    (cloned : Physical.run request allocator input before = (.ok copied, middle)) :
    ∃ after, install copied object middle = .ok after ∧ Installed allocator object copied middle after := by
  have post := Physical.run_valid request allocator input copied before middle initial cloned
  exact install_total allocator object copied middle (values_typed_same input copied post.same represented.typed)
    post.valid (post.item initial object owned) post.owned post.reads

end Compiler.Extraction.AssemblyClone.NativeFields
