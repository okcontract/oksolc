#!/usr/bin/env python3
"""Audit nondeterministic allocation failure and single-owner native cleanup.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NATIVE = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.'
CHAIN = NATIVE + 'CallerGrowingChainTests.'
TESTS = CHAIN + 'TransferredAllocationFailureTests.'
STORAGE = 'Compiler.Extraction.Storage.'
MODULE = 'Compiler.Extraction.InternerCallerInsertionTransferredAllocationFailureTests'
CLAIMS = [NATIVE + 'argument_free_frame', NATIVE + 'local_cleanup', STORAGE + 'insert_transferred_append_oom',
          NATIVE + 'CallerInput.transferred_cleanup_apart', NATIVE + 'CallerInput.transferred_growing_allocation_oom']
CLAIMS += [TESTS + name for name in ('completed', 'derived_contract', 'parent_borrow_after_oom', 'key_unchanged', 'effects_observed', 'backing_observed', 'shared_completion')]


def audit(claims):
    required = {
        NATIVE + 'local_cleanup': {'Compiler.Extraction.AssemblyItemDeinit.Native.run_verified',
            'Compiler.Extraction.AssemblyItem.destroy_verified',
            'Compiler.Extraction.Memory.Arguments.Normalization.free_valid', NATIVE + 'free_keeps_dead',
            NATIVE + 'release_keeps_arguments', NATIVE + 'argument_free_frame', NATIVE + 'cleanup_sequence_keys'},
        STORAGE + 'insert_transferred_append_oom': {STORAGE + 'insertProgram', STORAGE + 'Program.execute'},
        NATIVE + 'CallerInput.transferred_cleanup_apart': {'Compiler.Extraction.AssemblyItem.Creation.create_verified',
            'Compiler.Extraction.AssemblyClone.Physical.run_valid'},
        NATIVE + 'CallerInput.transferred_growing_allocation_oom': {NATIVE + 'growing_allocation_oom_reached_at', NATIVE + 'TransferredFailure.caller',
            NATIVE + 'item_cleanup_apart', NATIVE + 'local_cleanup', NATIVE + 'append_growth_callback',
            'Compiler.Extraction.RepresentativeArray.Append.Registered.growing_oom', STORAGE + 'insert_transferred_append_oom'},
        TESTS + 'backing_observed': {CHAIN + 'initialized_prefix', CHAIN + 'TransferredGrowthTests.preparation_results'},
        TESTS + 'shared_completion': {TESTS + 'backing_observed', NATIVE + 'NativeGrowingTests.reached_frame',
            'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.Enclosing.insertion_frame',
            'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.CallFrame.backing_oom_execution_at'},
        TESTS + 'completed': {CHAIN + 'initialized_prefix', NATIVE + 'CallerInput.handoff_insert'},
        TESTS + 'derived_contract': {NATIVE + 'CallerInput.transferred_growing_allocation_oom', TESTS + 'completed',
            CHAIN + 'initialized_prefix', 'Compiler.Extraction.RepresentativeArray.Operation.query',
            'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.BorrowedQuery.Native.of_resident'},
        TESTS + 'parent_borrow_after_oom': {TESTS + 'derived_contract', CHAIN + 'GraphFacts.first_borrow'},
        TESTS + 'key_unchanged': {TESTS + 'derived_contract'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('transferred failure lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    if TESTS + 'effects_observed' in claims[TESTS + 'derived_contract']:
        raise ValueError('transferred failure used fixture observations as ownership premises')
    return {'checkedDependencies': sorted(required), 'scope': 'ordinary backing-allocation OOM after nondeterministic transfer',
            'sharedLocalCleanupDerived': True, 'sharedReachedBackingFrame': True, 'existingFixtureConsumesEnclosingReducer': True, 'singleArgumentOwnerReleasedOnce': True,
            'cleanupFreshnessDerivedFromCaller': True, 'oldGraphNativeKeysAndParentBorrowPreserved': True,
            'outerDetachedLookupCleanupConnected': True, 'bothOwnerLayoutsAndEmptyNonemptyArgumentsChecked': True,
            'nondeterministicPreparationFailuresConnected': False, 'generalGrowingFailureCompositionVerified': False,
            'nativeAllocatorVtableBindingVerified': False, 'nativeMapImplementationVerified': False,
            'completePublicationRollbackVerified': False, 'fullCallerCacheRoutingVerified': False,
            'recursiveChildPreservationVerified': False, 'composedProductionTheoremVerified': False}


def audit_statements(rows):
    import check_native_invocation as gate
    import constructor_joint_checks as joint
    import constructor_replay_choice_checks as choice
    statements = {row['theorem']: row['statement'] for row in rows}
    value = statements[TESTS + 'shared_completion']
    fields, root, context = gate.domains(value)
    if list(fields) != ['safety', 'empty']:
        raise ValueError('transferred backing fixture assumes its final frame')
    args = joint.app(value, root, gate.NS + 'FramePost')
    choice.one_call(value, args[-1], context, gate.OWNED + 'finish')
    value = statements[TESTS + 'backing_observed']
    fields, root, context = gate.domains(value)
    if list(fields) != ['safety', 'empty']:
        raise ValueError('transferred backing observations assume a fixture result')
    args = joint.app(value, root, NATIVE + 'BackingAllocationOOMAt')
    if gate.named(value, args[-3], context) != 'Bool.false':
        raise ValueError('transferred backing fixture selects the wrong ownership mode')
    return {'existingExecutionUsesSharedReducer': True, 'noFinalFixtureFramesAssumed': True,
            'actualTransferredSourceObservation': True}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / name).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\nset_option pp.notation false\n' + without_imports(raw)
    fixtures = '''import Compiler.Extraction.InternerCallerInsertionTransferredAllocationFailureTests
namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.TransferredAllocationFailureTests.Controls
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open CallerInputTests (request key)
example (safety empty : Bool) : outcome safety empty = (.error (.language .outOfMemory),
    ⟨world safety empty, ⟨none, some (normalized safety empty 4), true⟩⟩) := (derived_contract safety empty).1
example (safety empty : Bool) : Good (parent empty) (request empty).arguments (world safety empty) :=
  (parent_borrow_after_oom safety empty).2
example (safety empty : Bool) :
    (world safety empty).memory.effects.keys (key empty) = some ⟨if empty then 22 else 30, 4⟩ := key_unchanged safety empty
example (safety empty : Bool) : (world safety empty).memory.effects.allocator = expectedEffects safety empty := by
  have observed := effects_observed safety empty
  generalize expectedEffects safety empty = expected at observed ⊢
  exact observed
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.TransferredAllocationFailureTests.Controls
'''
    return (
        ('program', source('StorageTransferredInsertion.lean'), (
            ('success-after-oom', '((.ok (some .allocationFailure), (Cleanup.sequence', '((.ok (some .success), (Cleanup.sequence', 3),
            ('double-normalized-release', '[.value, .allocation, .arguments]', '[.value, .allocation, .arguments, .normalized]', 1),
        )),
        ('local-cleanup', source('InternerInsertionUnappendedCleanup.lean'), (
            ('wrong-argument-owner', '(argumentsPresent : arguments normalized ownership before = some operands)',
             '(argumentsPresent : arguments normalized ownership before = some normalized)', 1),
            ('double-argument-release', '[.value, .allocation, .arguments]', '[.value, .allocation, .arguments, .arguments]', 6),
            ('destroy-separate-owner', 'Memory.SliceValid keptAllocator (memory after).heap kept)',
             '¬ Memory.SliceValid keptAllocator (memory after).heap kept)', 1),
        )),
        ('caller', source('InternerCallerInsertionTransferredAllocationFailure.lean'), (
            ('allocate-on-oom', '(memory after).memory.nextId = middle.memory.nextId ∧',
             '(memory after).memory.nextId = middle.memory.nextId + 1 ∧', 1),
            ('erase-parent', '→ (memory after).memory.heap.lookup id = some native) ∧',
             '→ (memory after).memory.heap.lookup id = none) ∧', 1),
            ('retain-transferred-buffer', '(normalized.items ≠ [] ∧ id = normalized.address) →\n        (memory after).heap id = none',
             '(normalized.items ≠ [] ∧ id = normalized.address) →\n        (memory after).heap id ≠ none', 1),
            ('row-invalidation-marker', 'after.item.clone.execution.invalidated = false ∧',
             'after.item.clone.execution.invalidated = true ∧', 1),
        )),
        ('fixtures', fixtures, (
            ('detach-lookup', '⟨none, some (normalized safety empty 4), true⟩',
             '⟨some (lookup empty), some (normalized safety empty 4), true⟩', 1),
            ('lose-parent-values', 'Good (parent empty) (request empty).arguments', 'Good (parent empty) [1]', 1),
            ('replace-old-key', 'some ⟨if empty then 22 else 30, 4⟩', 'some ⟨if empty then 25 else 35, 5⟩', 1),
            ('charge-second-free', '= expectedEffects safety empty := by',
             '= expectedEffects safety empty + (if empty then 0 else 101) := by', 1),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    cases = mutation_cases()
    for group, text, changes in cases:
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous transferred failure mutation: ' + group + '-' + name)
    records = []
    for group, text, changes in cases:
        records += checked_controls(output, [mutation_check(output, 'transferred-failure-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'transferred-failure-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
