#!/usr/bin/env python3
"""Audit caller-derived graph and key preservation through growing publication OOM.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NATIVE = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.'
CHAIN = NATIVE + 'CallerGrowingChainTests.'
TESTS = CHAIN + 'RollbackTests.'
CLAIMS = [NATIVE + name for name in (
    'free_keys', 'destroy_keys', 'payload_free_keys', 'payload_stage_keys', 'payload_execute_keys',
    'item_deinit_keys', 'expression_stage_keys', 'expression_execute_keys', 'releaseValue_keys',
    'releaseLast_keys', 'pop_keys', 'cleanup_action_keys', 'cleanup_sequence_keys',
    'CallerInput.cleanup_apart', 'growing_publication_oom_cleanup', 'CallerInput.growing_oom')]
CLAIMS += [TESTS + name for name in ('completed', 'owner_observed', 'owner', 'cleanup_observed',
    'derived_contract', 'parent_borrow_after_rollback', 'key_unchanged', 'partial_failure_keys')]


def audit(claims):
    required = {
        NATIVE + 'item_deinit_keys': {NATIVE + 'payload_execute_keys', 'Compiler.Extraction.AssemblyItemDeinit.Native.finish_retains'},
        NATIVE + 'expression_execute_keys': {NATIVE + 'expression_stage_keys'},
        NATIVE + 'cleanup_action_keys': {NATIVE + name for name in ('free_keys', 'destroy_keys', 'releaseValue_keys', 'releaseLast_keys', 'pop_keys')},
        NATIVE + 'cleanup_sequence_keys': {NATIVE + 'cleanup_action_keys'},
        NATIVE + 'CallerInput.cleanup_apart': {NATIVE + 'duplicate_taken', 'Compiler.Extraction.AssemblyItem.Creation.create_verified',
            'Compiler.Extraction.AssemblyClone.Physical.run_valid'},
        NATIVE + 'growing_publication_oom_cleanup': {NATIVE + 'cleanup_sequence_keys', NATIVE + 'rollback_normalized_verified',
            NATIVE + 'growing_append_owned'},
        NATIVE + 'CallerInput.growing_oom': {NATIVE + 'growing_publication_oom_reached',
            'Compiler.Extraction.RepresentativeArray.Operation.query', 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.BorrowedQuery.Native.of_resident'},
        TESTS + 'completed': {CHAIN + 'initialized_prefix', NATIVE + 'CallerInput.handoff_insert'},
        TESTS + 'derived_contract': {NATIVE + 'CallerInput.growing_oom', TESTS + 'completed',
            CHAIN + 'initialized_prefix', CHAIN + 'backing_fits'},
        TESTS + 'parent_borrow_after_rollback': {TESTS + 'derived_contract', CHAIN + 'GraphFacts.first_borrow'},
        TESTS + 'key_unchanged': {TESTS + 'derived_contract'},
        TESTS + 'partial_failure_keys': {NATIVE + 'releaseValue_keys', NATIVE + 'CleanupTests.rejection_keeps_reached'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('caller growing rollback lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    observed = {TESTS + name for name in ('owner', 'owner_observed', 'cleanup_observed')}
    if observed & claims[TESTS + 'derived_contract']:
        raise ValueError('caller growing rollback used fixture observations as its ownership proof')
    return {'checkedDependencies': sorted(required),
            'scope': 'publication OOM after successful nonempty relocation from five initialized insertion continuations',
            'cleanupKeysPreservedForAllOutcomes': True, 'cleanupSeparationDerivedFromActualCallerPreparation': True,
            'oldGraphAndNativeQueriesDerived': True, 'globalKeyOwnershipAndOldKeyRetentionDerived': True,
            'liveParentBorrowAcrossRollbackDerived': True, 'outerNormalizedAndDetachedLookupCleanupConnected': True,
            'exactCleanupDeathsAndAllocatorEffectsChecked': True, 'fixtureOwnerGeometryChecked': True,
            'genericInitialValidityOwnershipAndCorrespondenceExplicit': True, 'genericFinalOwnerGeometryDerived': True,
            'genericCleanupDeathsDerived': True, 'fixtureObservationsExcludedFromDerivedContract': True,
            'nativeAllocatorVtableBindingVerified': False, 'nativeMapImplementationVerified': False,
            'fullCallerCacheRoutingVerified': False, 'generalGrowingFailureCompositionVerified': False,
            'completePublicationRollbackVerified': False, 'recursiveChildPreservationVerified': False,
            'composedProductionTheoremVerified': False}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / name).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\nset_option pp.notation false\n' + without_imports(raw)
    return (
        ('effects', source('InternerInsertionCleanupEffects.lean'), (
            ('erase-payload-keys', '(AssemblyItemDeinit.free (release bytes) allocator slice before).2.effects.keys = before.effects.keys',
             '(AssemblyItemDeinit.free (release bytes) allocator slice before).2.effects.keys = (fun _ => none)', 1),
            ('erase-partial-item-keys', '(AssemblyItemDeinit.Native.run (release bytes) allocator object before).2.memory.effects.keys = before.effects.keys',
             '(AssemblyItemDeinit.Native.run (release bytes) allocator object before).2.memory.effects.keys = (fun _ => none)', 1),
            ('erase-last-row-keys', '(memory (releaseLast ops allocator container before).2).effects.keys = (memory before).effects.keys',
             '(memory (releaseLast ops allocator container before).2).effects.keys = (fun _ => none)', 1),
            ('erase-unwind-keys', 'actions owner before).2).effects.keys = (memory before).effects.keys',
             'actions owner before).2).effects.keys = (fun _ => none)', 1),
        )),
        ('preparation', source('InternerCallerInsertionPreparation.lean'), (
            ('alias-old-item', 'id ≠ object ∧ ¬AssemblyItemDeinit.Touches', 'id = object ∧ ¬AssemblyItemDeinit.Touches', 1),
            ('confuse-source-payload', 'id ≠ object ∧ ¬AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload copied) id ∧',
             'id ≠ object ∧ ¬AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload input) id ∧', 1),
            ('alias-old-arguments', 'id ≠ operands.address ∧ id ≠ normalized.address := by', 'id = operands.address ∧ id ≠ normalized.address := by', 1),
            ('alias-old-normalized', 'id ≠ operands.address ∧ id ≠ normalized.address := by', 'id ≠ operands.address ∧ id = normalized.address := by', 1),
        )),
        ('proof', source('InternerCallerInsertionGrowingRollback.lean'), (
            ('publish-failed-key', '(memory after).effects.keys = before.memory.effects.keys ∧',
             '(memory after).effects.keys = OwnedKeys.store before.memory.effects.keys key ⟨normalized.address, BitVec.ofNat 32 cells.length⟩ ∧', 1),
            ('omit-pop', '⟨middle.memory.nextId, 0⟩ cells.length, .scalar (.int false 64 capacity)',
             '⟨middle.memory.nextId, 0⟩ (cells.length + 1), .scalar (.int false 64 capacity)', 1),
            ('rewind-history', '(memory after).memory.nextId = middle.memory.nextId + 1', '(memory after).memory.nextId = middle.memory.nextId', 1),
            ('revive-backing', '(memory after).heap oldLifetime = none ∧', '(memory after).heap oldLifetime = before.memory.heap oldLifetime ∧', 1),
            ('erase-parent', '(memory after).memory.heap.lookup id = some native) ∧', '(memory after).memory.heap.lookup id = none) ∧', 1),
            ('erase-old-registry', '(memory after).heap id = some block) ∧', '(memory after).heap id = none) ∧', 1),
            ('succeed-after-oom', '((.ok (some .allocationFailure), (Storage.Cleanup.sequence', '((.ok (some .success), (Storage.Cleanup.sequence', 1),
            ('move-owner', 'ownerCell.SameShape finalOwner', 'ownerCell.SameShape { finalOwner with base := finalOwner.base + 1 }', 1),
            ('revive-cleanup-native', '        (memory after).heap id = none ∧ (memory after).memory.heap.lookup id = none) := by',
             '        (memory after).heap id = none ∧ (memory after).memory.heap.lookup id ≠ none) := by', 1),
        )),
        ('observations', source('InternerCallerInsertionGrowingRollbackSetupTests.lean'), (
            ('writable-owner-lost', 'some (Owner.viewType safety, true) := by', 'some (Owner.viewType safety, false) := by', 1),
            ('item-still-live', '= (true, true, true, expectedEffects safety empty) := by', '= (false, true, true, expectedEffects safety empty) := by', 1),
            ('payload-still-live', '= (true, true, true, expectedEffects safety empty) := by', '= (true, false, true, expectedEffects safety empty) := by', 1),
            ('omit-normalized-release', '(if empty then 0 else 202)', '(if empty then 0 else 101)', 1),
            ('omit-old-backing-release', '* 10 + 9) * 10 + 8)', '* 10 + 0) * 10 + 8)', 1),
        )),
        ('fixtures', source('InternerCallerInsertionGrowingRollbackTests.lean'), (
            ('lose-detached-cleanup', '⟨none, some (normalized safety empty 4), true⟩', '⟨some (lookup empty), some (normalized safety empty 4), true⟩', 1),
            ('lose-parent-values', 'Good (parent empty) (request empty).arguments (world safety empty)', 'Good (parent empty) [1] (world safety empty)', 1),
            ('replace-old-key', 'some ⟨if empty then 22 else 30, 4⟩ := by', 'some ⟨if empty then 25 else 35, 5⟩ := by', 2),
            ('rewind-address', '(world safety empty).memory.memory.nextAddress = 8608', '(world safety empty).memory.memory.nextAddress = 4256', 1),
            ('discard-partial-effects', '(memory CleanupTests.readonly.2).effects.allocator = 12', '(memory CleanupTests.readonly.2).effects.allocator = 1', 1),
            ('move-derived-owner', 'original.SameShape current', 'original.SameShape { current with base := current.base + 1 }', 1),
            ('revive-cleanup-registry', '(world safety empty).memory.heap id = none ∧ (world safety empty).memory.memory.heap.lookup id = none) := by',
             '(world safety empty).memory.heap id ≠ none ∧ (world safety empty).memory.memory.heap.lookup id = none) := by', 1),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    cases = mutation_cases()
    for group, text, changes in cases:
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous growing-rollback mutation: ' + group + '-' + name)
    records = []
    for group, text, changes in cases:
        records += checked_controls(output, [mutation_check(output, 'caller-growing-rollback-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'caller-growing-rollback-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
