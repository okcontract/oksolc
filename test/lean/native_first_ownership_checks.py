#!/usr/bin/env python3
"""Audit first native allocation through publication OOM and outer cleanup.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NATIVE = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.'
PUBLICATION = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication.'
CLAIMS = [PUBLICATION + 'Input.frame']
CLAIMS += [NATIVE + name for name in ('append_pointees', 'first_append_owned', 'first_publication_oom_cleanup', 'deterministic_first_oom')]
CLAIMS += [NATIVE + 'FirstTests.' + name for name in (
    'initial_frame', 'initial_valid', 'preparation_results', 'backing_response', 'probe_result',
    'derived_contract', 'reached_observations', 'retained_allocations', 'backing_oom', 'invalid_backing_response')]


def audit(claims):
    required = {
        NATIVE + 'append_pointees': {'Compiler.Extraction.AssemblyClone.NativeFields.Represents.frame',
            'Compiler.ZigAir.Memory.Heap.lookup_ne_of_type_ne'},
        NATIVE + 'spare_append_owned': {NATIVE + 'append_pointees'},
        NATIVE + 'first_append_owned': {NATIVE + 'append_pointees',
            'Compiler.Extraction.RepresentativeArray.DescriptorRelation.first_registered',
            'Compiler.Extraction.RepresentativeArray.Append.Execution.first_verified',
            'Compiler.Extraction.RepresentativeArray.Append.Registered.completed',
            'Compiler.Extraction.RepresentativeArray.Append.Registered.admit_first'},
        NATIVE + 'first_publication_oom_cleanup': {NATIVE + 'first_append_owned', PUBLICATION + 'Input.frame',
            PUBLICATION + 'publish_oom', NATIVE + 'rollback_normalized_verified'},
        NATIVE + 'deterministic_first_oom': {NATIVE + 'prepare_owned', NATIVE + 'first_publication_oom_cleanup',
            PUBLICATION + 'Input.frame', 'Compiler.Extraction.Storage.insert_prepared_oom'},
        NATIVE + 'FirstTests.derived_contract': {NATIVE + 'deterministic_first_oom', NATIVE + 'FirstTests.preparation_results',
            NATIVE + 'FirstTests.backing_response', NATIVE + 'FirstTests.probe_result'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('first ownership lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'firstAppendDerivesCleanupOwners': True,
            'completeDeterministicFirstPublicationOom': True, 'outerNormalizedCleanupConnected': True,
            'newBackingAndLifetimeHistoryRetained': True, 'initialGraphAndInputPremisesExplicit': True,
            'nonemptyGrowthIntegrated': False, 'nativeHashMapRefinementVerified': False,
            'completePublicationRollbackVerified': False, 'recursiveConstructorsVerified': False}


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    directory = ROOT / 'lean/Compiler/Extraction'
    owners = 'import Compiler.Extraction.InternerInsertionPointeeFrame\n' + '\n'.join(
        without_imports((directory / name).read_text()) for name in (
            'InternerInsertionAppendPointees.lean', 'InternerInsertionFirstOwnership.lean'))
    complete = ('import Compiler.Extraction.InternerInsertionPreparedRollback\n'
                'import Compiler.Extraction.InternerInsertionFirstOwnership\n' +
                without_imports((directory / 'InternerInsertionFirstPrepared.lean').read_text()))
    cases = (
        ('owners', owners, (
            ('erase-pointee', 'after.memory.heap.lookup id = before.memory.heap.lookup id',
             'after.memory.heap.lookup id = none', 1),
            ('wrong-row-object', '= .ok ⟨object, 0⟩ ∧', '= .ok ⟨object + 1, 0⟩ ∧', 1),
            ('alias-row-to-normalized', '.ok (.slice Expression.argumentsType ⟨operands.address, 0⟩ operands.items.length) ∧',
             '.ok (.slice Expression.argumentsType ⟨normalized.address, 0⟩ operands.items.length) ∧', 1),
            ('wrong-request', 'allocate allocator 160 8 (memory before).effects.allocator',
             'allocate allocator 128 8 (memory before).effects.allocator', 2),
            ('rewind-lifetime', '(memory after).memory.nextId = lifetime + 1', '(memory after).memory.nextId = lifetime', 1),
            ('discard-allocation-effects', '(memory after).effects = { (memory before).effects with allocator := reached }',
             '(memory after).effects = (memory before).effects', 1),
            ('free-new-backing', 'Memory.Vector allocator (memory after).heap (memory before).memory.nextId []',
             '(memory after).heap (memory before).memory.nextId = none', 1),
            ('discard-probe-effects', 'memory failed = { memory appended with effects := { (memory appended).effects with allocator := probeEffects } }',
             'memory failed = memory before', 1),
            ('alias-argument-owners', '(separate : operands.items ≠ [] → normalized.items ≠ [] → normalized.address ≠ operands.address)',
             '(separate : True)', 1),
            ('omit-normalized-release', '[.lastValue, .pop, .normalized]', '[.lastValue, .pop]', 2),
        )),
        ('complete', complete, (
            ('wrong-outcome', '((.ok (some .allocationFailure), (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).run handed), after)',
             '((.ok (some .success), (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).run handed), after)', 1),
            ('omit-outer-cleanup', '((.ok (some .allocationFailure), (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).run handed), after)',
             '((.ok (some .allocationFailure), (Storage.Cleanup.sequence [.lastValue, .pop]).run handed), after)', 1),
            ('rewind-history', '(memory after).memory.nextId = middle.memory.nextId + 1',
             '(memory after).memory.nextId = middle.memory.nextId', 1),
            ('retain-published-length', '⟨middle.memory.nextId, 0⟩ 0, .scalar (.int false 64 5)',
             '⟨middle.memory.nextId, 0⟩ 1, .scalar (.int false 64 5)', 1),
            ('wrong-created-object', 'allocator input.item duplicated = (.ok object, allocated)',
             'allocator input.item duplicated = (.ok (object + 1), allocated)', 1),
            ('wrong-cloned-value', 'allocator input allocated = (.ok copied, middle)',
             'allocator input allocated = (.ok input, middle)', 1),
        )),
    )
    for group, source, changes in cases:
        for name, before, _, count in changes:
            if source.count(before) != count:
                raise ValueError('ambiguous first ownership mutation: ' + group + '-' + name)
    records = []
    for group, source, changes in cases:
        records += checked_controls(output, [mutation_check(output, 'first-' + group + '-unchanged', source, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'first-' + group + '-' + name,
                                                               source.replace(before, after), False, env, lean)])
    return records
