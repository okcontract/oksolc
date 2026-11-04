#!/usr/bin/env python3
"""Audit caller-derived nondeterministic transfer through nonempty relocation.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NATIVE = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.'
CHAIN = NATIVE + 'CallerGrowingChainTests.'
TESTS = CHAIN + 'TransferredGrowthTests.'
STORAGE = 'Compiler.Extraction.Storage.'
MODULE = 'Compiler.Extraction.InternerCallerInsertionTransferredGrowthTests'
CLAIMS = [NATIVE + 'prepare_item', STORAGE + 'insert_transferred_success',
          NATIVE + 'CallerInput.prepare_transferred', NATIVE + 'CallerInput.transferred_growing_success']
CLAIMS += [TESTS + name for name in ('transferred_observed', 'shared_completion', 'preparation_results', 'ready_contract', 'backing_fits', 'completed',
                                   'derived_contract', 'parent_borrow_after_growth', 'key_unchanged',
                                   'effects_observed', 'transferred_query')]


def audit(claims):
    required = {
        NATIVE + 'prepare_item': {'Compiler.Extraction.AssemblyItem.Creation.create_verified',
            'Compiler.Extraction.AssemblyClone.Physical.run_valid',
            'Compiler.Extraction.AssemblyItem.Creation.NativeFields.clone_callback_installed'},
        STORAGE + 'insert_transferred_success': {STORAGE + 'insertProgram', STORAGE + 'Program.execute'},
        NATIVE + 'CallerInput.prepare_transferred': {NATIVE + 'prepare_transferred_reached'},
        NATIVE + 'CallerInput.transferred_growing_success': {NATIVE + 'transferred_growing_success_reached'},
        TESTS + 'transferred_observed': {CHAIN + 'initialized_prefix', TESTS + 'preparation_results', TESTS + 'backing_fits'},
        TESTS + 'shared_completion': {TESTS + 'transferred_observed', NATIVE + 'NativeGrowingTests.reached_frame',
            'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.Enclosing.insertion_rollback_derived'},
        TESTS + 'completed': {CHAIN + 'initialized_prefix', NATIVE + 'CallerInput.handoff_insert'},
        TESTS + 'derived_contract': {NATIVE + 'CallerInput.transferred_growing_success', TESTS + 'completed',
            CHAIN + 'initialized_prefix'},
        TESTS + 'parent_borrow_after_growth': {TESTS + 'derived_contract', CHAIN + 'GraphFacts.first_borrow'},
        TESTS + 'transferred_query': {TESTS + 'derived_contract'},
        TESTS + 'key_unchanged': {TESTS + 'derived_contract'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('transferred growth lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    if TESTS + 'effects_observed' in claims[TESTS + 'derived_contract']:
        raise ValueError('transferred ownership was replaced by a fixture observation')
    return {'checkedDependencies': sorted(required), 'scope': 'successful nondeterministic sixth insertion after five initialized rows',
            'sharedNativePreparation': True, 'normalizedOwnerTransferredWithoutDuplicate': True,
            'nonemptyRelocationConnected': True, 'keysUnchangedWithoutPublication': True,
            'graphNativeQueriesAndParentBorrowDerived': True, 'outerCallerCleanupConnected': True,
            'bothOwnerLayoutsAndEmptyNonemptyArgumentsChecked': True,
            'nondeterministicFailureCompositionVerified': False, 'nativeAllocatorVtableBindingVerified': False,
            'nativeMapImplementationVerified': False, 'fullCallerCacheRoutingVerified': False,
            'completePublicationRollbackVerified': False, 'recursiveChildPreservationVerified': False,
            'composedProductionTheoremVerified': False}


def audit_statements(rows):
    import check_native_invocation as gate
    import constructor_joint_checks as joint
    import constructor_replay_choice_checks as choice
    statements = {row['theorem']: row['statement'] for row in rows}
    value = statements[TESTS + 'shared_completion']
    fields, root, context = gate.domains(value)
    if list(fields) != ['safety', 'empty']:
        raise ValueError('transferred success fixture assumes its final frame')
    args = joint.app(value, root, gate.NS + 'FramePost')
    choice.one_call(value, args[-1], context, gate.OWNED + 'finish')
    call, local = choice.one_call(value, value['root'], [], NATIVE + 'insert')
    if len(call) != 14 or gate.named(value, call[12], local) != 'Bool.false':
        raise ValueError('transferred success fixture selects a different ownership mode')
    value = statements[TESTS + 'transferred_observed']
    fields, root, context = gate.domains(value)
    if list(fields) != ['safety', 'empty']:
        raise ValueError('transferred success observations assume a fixture result')
    joint.app(value, root, NATIVE + 'RelocatedTransferred')
    return {'existingExecutionUsesSharedReducer': True, 'noFinalFixtureFramesAssumed': True,
            'actualTransferredSourceObservation': True}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / name).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\nset_option pp.notation false\n' + without_imports(raw)
    fixtures = '''import Compiler.Extraction.InternerCallerInsertionTransferredGrowthTests
namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.TransferredGrowthTests.Controls
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open RepresentativeArray
open CallerInputTests (request key)
example (safety empty : Bool) :
    Operation.run (world safety empty).memory.memory (Owner.headerAddress ⟨6, 0⟩) 0 254 =
      .ok (.ok (some (Operation.returned (CallerInputTests.operands empty)))) ∧
    Good (parent empty) (request empty).arguments (world safety empty) := parent_borrow_after_growth safety empty
example (safety empty : Bool) :
    (world safety empty).memory.effects.keys (key empty) = some ⟨if empty then 22 else 30, 4⟩ := key_unchanged safety empty
example (safety empty : Bool) :
    (world safety empty).memory.effects.allocator = ((ready safety empty).effects.allocator * 10 + 7) * 10 + 9 := by
  have observed := effects_observed safety empty
  generalize ((ready safety empty).effects.allocator * 10 + 7) * 10 + 9 = expected at observed ⊢
  exact observed
example (safety empty : Bool) :
    Operation.run (world safety empty).memory.memory (Owner.headerAddress ⟨6, 0⟩) 5 254 =
      .ok (.ok (some (Operation.returned (normalized safety empty 4)))) := transferred_query safety empty
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.TransferredGrowthTests.Controls
'''
    return (
        ('program', source('StorageTransferredInsertion.lean'), (
            ('retain-normalized-defer', '.setFlag .normalized true).setFlag .normalized false', '.setFlag .normalized true).setFlag .normalized true', 1),
            ('deterministic-route', 'insertProgram.execute ⟨false, true, fun _ => false⟩', 'insertProgram.execute ⟨true, true, fun _ => false⟩', 5),
            ('fail-success', '((.ok (some .success), transferredOwnership), after)', '((.ok (some .allocationFailure), transferredOwnership), after)', 2),
        )),
        ('preparation', source('InternerCallerInsertionTransferredPreparation.lean'), (
            ('lose-normalized-owner', 'Memory.SliceValid allocator installed.heap normalized ∧', '¬ Memory.SliceValid allocator installed.heap normalized ∧', 2),
            ('erase-old-native', '→ installed.memory.heap.lookup id = some cell)', '→ installed.memory.heap.lookup id = none)', 2),
            ('erase-old-registry', '→ installed.heap id = some block)', '→ installed.heap id = none)', 2),
        )),
        ('growth', source('InternerCallerInsertionTransferredGrowth.lean'), (
            ('publish-key', '(memory after).effects.keys = before.memory.effects.keys ∧',
             '(memory after).effects.keys = OwnedKeys.store before.memory.effects.keys key ⟨normalized.address, BitVec.ofNat 32 cells.length⟩ ∧', 1),
            ('duplicate-allocation', '(memory after).memory.nextId = middle.memory.nextId + 1 ∧', '(memory after).memory.nextId = middle.memory.nextId + 2 ∧', 1),
            ('retain-old-backing', '(memory after).heap oldLifetime = none ∧', '(memory after).heap oldLifetime ≠ none ∧', 1),
            ('erase-parent', '(memory after).memory.heap.lookup id = some native) ∧', '(memory after).memory.heap.lookup id = none) ∧', 1),
            ('release-transferred-buffer', 'Memory.SliceValid allocator (memory after).heap normalized ∧',
             '¬ Memory.SliceValid allocator (memory after).heap normalized ∧', 1),
        )),
        ('fixtures', fixtures, (
            ('wrong-parent-values', 'Good (parent empty) (request empty).arguments', 'Good (parent empty) [1]', 1),
            ('replace-old-key', 'some ⟨if empty then 22 else 30, 4⟩', 'some ⟨if empty then 25 else 35, 5⟩', 1),
            ('unexpected-probe', '= ((ready safety empty).effects.allocator * 10 + 7) * 10 + 9 := by',
             '= (((ready safety empty).effects.allocator * 10 + 7) * 10 + 9) * 10 + 8 := by', 1),
            ('wrong-transferred-descriptor', 'Operation.returned (normalized safety empty 4)', 'Operation.returned (CallerGrowingChainTests.operands safety empty 4)', 1),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    cases = mutation_cases()
    for group, text, changes in cases:
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous transferred growth mutation: ' + group + '-' + name)
    records = []
    for group, text, changes in cases:
        records += checked_controls(output, [mutation_check(output, 'transferred-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'transferred-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
