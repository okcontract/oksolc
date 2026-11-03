#!/usr/bin/env python3
"""Audit caller-connected nonempty backing-allocation OOM and local cleanup.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NATIVE = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.'
CHAIN = NATIVE + 'CallerGrowingChainTests.'
TESTS = CHAIN + 'AllocationFailureTests.'
ARRAY = 'Compiler.Extraction.RepresentativeArray.'
STORAGE = 'Compiler.Extraction.Storage.'
CLAIMS = [ARRAY + 'Append.Registered.growing_oom', STORAGE + 'insert_append_oom',
          NATIVE + 'unappended_cleanup', NATIVE + 'CallerInput.growing_allocation_oom']
CLAIMS += [TESTS + name for name in ('completed', 'derived_contract', 'parent_borrow_after_oom',
                                   'key_unchanged', 'effects_observed')]


def audit(claims):
    required = {
        ARRAY + 'Append.Registered.growing_oom': {ARRAY + 'Growth.Registered.fallback_execution',
            ARRAY + 'Backing.Fallback.oom_verified', ARRAY + 'Capacity.Registered.growing'},
        STORAGE + 'insert_append_oom': {STORAGE + 'insertProgram', STORAGE + 'Program.execute'},
        NATIVE + 'unappended_cleanup': {'Compiler.Extraction.AssemblyItemDeinit.Native.run_verified',
            'Compiler.Extraction.AssemblyItem.destroy_verified',
            'Compiler.Extraction.Memory.Arguments.Normalization.free_valid', NATIVE + 'free_keeps_dead',
            NATIVE + 'release_keeps_arguments', NATIVE + 'cleanup_sequence_keys'},
        NATIVE + 'CallerInput.growing_allocation_oom': {NATIVE + 'growing_allocation_oom_reached',
            NATIVE + 'append_oom_reached', NATIVE + 'preparation_cleanup_apart',
            NATIVE + 'unappended_cleanup', ARRAY + 'Append.Registered.growing_oom'},
        TESTS + 'completed': {CHAIN + 'initialized_prefix', NATIVE + 'CallerInput.handoff_insert'},
        TESTS + 'derived_contract': {NATIVE + 'CallerInput.growing_allocation_oom', TESTS + 'completed',
            CHAIN + 'initialized_prefix', ARRAY + 'Operation.query',
            'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.BorrowedQuery.Native.of_resident'},
        TESTS + 'parent_borrow_after_oom': {TESTS + 'derived_contract', CHAIN + 'GraphFacts.first_borrow'},
        TESTS + 'key_unchanged': {TESTS + 'derived_contract'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('growth allocation failure lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    if TESTS + 'effects_observed' in claims[TESTS + 'derived_contract']:
        raise ValueError('allocation OOM used fixture observations as its ownership proof')
    return {'checkedDependencies': sorted(required),
            'scope': 'ordinary backing-allocation OOM on the sixth initialized insertion',
            'capacityAndRemapConnectionDerived': True, 'preparedCleanupOwnersDerivedFromCaller': True,
            'allOldNativeAndRegistryAllocationsPreserved': True, 'localOwnersReleasedInSourceOrder': True,
            'oldGraphNativeQueriesKeysAndParentBorrowDerived': True, 'outerCallerCleanupConnected': True,
            'exactReachedEffectsChecked': True, 'bothOwnerLayoutsAndEmptyNonemptyArgumentsChecked': True,
            'nativeAllocatorVtableBindingVerified': False, 'nativeMapImplementationVerified': False,
            'generalGrowingFailureCompositionVerified': False, 'completePublicationRollbackVerified': False,
            'fullCallerCacheRoutingVerified': False, 'recursiveChildPreservationVerified': False,
            'composedProductionTheoremVerified': False}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / name).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\nset_option pp.notation false\n' + without_imports(raw)
    return (
        ('append', source('RepresentativeRegisteredGrowthAppendProofs.lean'), (
            ('succeed-after-oom', '(.ok false, {before with effects}) := by', '(.ok true, {before with effects}) := by', 1),
            ('discard-allocator-effects', '(.ok false, {before with effects}) := by', '(.ok false, before) := by', 1),
        )),
        ('cleanup', source('InternerInsertionUnappendedCleanup.lean'), (
            ('erase-old-native', '(memory after).memory.heap.lookup id = (memory before).memory.heap.lookup id',
             '(memory after).memory.heap.lookup id = none', 1),
            ('erase-old-registry', '(memory after).heap id = (memory before).heap id', '(memory after).heap id = none', 1),
            ('revive-released-native', '(memory after).heap id = none ∧ (memory after).memory.heap.lookup id = none',
             '(memory after).heap id = none ∧ (memory after).memory.heap.lookup id ≠ none', 1),
            ('release-empty-sentinel', '(operands.items ≠ [] ∧ id = operands.address)', '(True ∧ id = operands.address)', 1),
            ('erase-keys', '(memory after).effects.keys = (memory before).effects.keys',
             '(memory after).effects.keys = (fun _ => none)', 1),
        )),
        ('caller', source('InternerCallerInsertionGrowthAllocationFailure.lean'), (
            ('succeed-after-oom', '((.ok (some .allocationFailure), (Storage.Cleanup.sequence',
             '((.ok (some .success), (Storage.Cleanup.sequence', 1),
            ('allocate-on-oom', '(memory after).memory.nextId = middle.memory.nextId ∧',
             '(memory after).memory.nextId = middle.memory.nextId + 1 ∧', 1),
            ('erase-parent', '→ (memory after).memory.heap.lookup id = some native) ∧',
             '→ (memory after).memory.heap.lookup id = none) ∧', 1),
            ('revive-normalized', '(normalized.items ≠ [] ∧ id = normalized.address) →\n        (memory after).heap id = none',
             '(normalized.items ≠ [] ∧ id = normalized.address) →\n        (memory after).heap id ≠ none', 1),
            ('row-invalidation-marker', 'after.item.clone.execution.invalidated = false ∧',
             'after.item.clone.execution.invalidated = true ∧', 1),
        )),
        ('fixtures', source('InternerCallerInsertionGrowthAllocationFailureTests.lean'), (
            ('lose-detached-cleanup', '⟨none, some (normalized safety empty 4), true⟩',
             '⟨some (lookup empty), some (normalized safety empty 4), true⟩', 1),
            ('lose-parent-values', 'Good (parent empty) (request empty).arguments (world safety empty)',
             'Good (parent empty) [1] (world safety empty)', 1),
            ('replace-old-key', 'some ⟨if empty then 22 else 30, 4⟩ := by', 'some ⟨if empty then 25 else 35, 5⟩ := by', 2),
            ('omit-normalized-free', '(if empty then 0 else 202)', '(if empty then 0 else 101)', 1),
            ('add-old-backing-free', '.effects.allocator * 10 + 7) * 10 + 2)',
             '.effects.allocator * 100 + 79) * 10 + 2)', 1),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    cases = mutation_cases()
    for group, text, changes in cases:
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous allocation failure mutation: ' + group + '-' + name)
    records = []
    for group, text, changes in cases:
        records += checked_controls(output, [mutation_check(output, 'growth-allocation-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'growth-allocation-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
