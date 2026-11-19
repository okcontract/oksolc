#!/usr/bin/env python3
"""Check pre-lookup entry failures and actual scratch allocation.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
from assembly_item_creation_checks import checked_controls
import native_cache_checks as cache
import native_step_checks as step

ITEM, CALLER, NORMAL = cache.ITEM, cache.CALLER, cache.NORMAL
TESTS = ITEM + 'EntryFailureTests.'
MODULE = 'Compiler.Extraction.InternerConstructorEntryFailureTests'
CLAIMS = [CALLER + name for name in ('initialize_failed', 'find_init_failed')]
CLAIMS += [ITEM + name for name in ('prepare_scratch', 'invoke_init_failed', 'invoke_capacity_failed',
                                  'invoke_init_rejected', 'invoke_entry_failed_native')]
CLAIMS += [step.NS + 'step_entry_failed_verified']
CLAIMS += [TESTS + name for name in ('failed_prefix', 'initialization_oom_contract', 'incomplete_route',
                                   'capacity_contract', 'capacity_observed', 'boundary_observed', 'scratch_contract')]


def audit(claims):
    required = {
        CALLER + 'initialize_failed': {NORMAL + 'init_refines'},
        CALLER + 'find_init_failed': {CALLER + 'find', CALLER + 'findBody'},
        ITEM + 'prepare_scratch': {ITEM + 'prepare_success', 'Compiler.ZigAir.Memory.allocate'},
        ITEM + 'invoke_init_failed': {CALLER + 'initialize_failed', CALLER + 'find_init_failed',
            NORMAL + 'caller_buffer', ITEM + 'invoke_after_scratch', ITEM + 'returnWorld_frame', ITEM + 'returnWorld_valid'},
        ITEM + 'invoke_capacity_failed': {ITEM + 'prepare_success', ITEM + 'invoke_prepared', ITEM + 'good_frame'},
        ITEM + 'invoke_init_rejected': {ITEM + 'invoke_after_scratch', CALLER + 'find_init_failed',
                                       NORMAL + 'OwnedCall.finish_semantic'},
        ITEM + 'invoke_entry_failed_native': {ITEM + 'prepare_scratch', ITEM + 'invoke_init_failed', ITEM + 'invoke_capacity_failed',
            cache.PUBLICATION + 'caller_init_keys', NORMAL + 'OwnedCall.NativeGraph.Facts.frame'},
        step.NS + 'step_entry_failed_verified': {ITEM + 'invoke_entry_failed_native', step.NS + 'step_return_verified'},
        TESTS + 'initialization_oom_contract': {ITEM + 'invoke_init_failed', TESTS + 'failed_prefix', cache.TESTS + 'prefix_observed'},
        TESTS + 'incomplete_route': {ITEM + 'invoke_init_rejected', cache.TESTS + 'prefix_observed'},
        TESTS + 'capacity_contract': {ITEM + 'invoke_capacity_failed', cache.TESTS + 'prefix_observed'},
        TESTS + 'scratch_contract': {ITEM + 'prepare_scratch', cache.TESTS + 'prefix_observed'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('entry failure lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'actualScratchAllocationDerived': True,
        'capacityAndOrdinaryInitializationFailureDerived': True, 'exactRejectedInitializationRetained': True,
        'oldNativeAndRegistryFramesDerived': True, 'arbitraryProperChildrenNotReached': True,
        'nativeCapacityQueryRefinementVerified': False, 'allEntryPrefixesVerified': False,
        'completeNativeGraphInvariantVerified': False, 'recursiveInductionVerified': False,
        'composedProductionTheoremVerified': False}


def audit_statements(rows):
    return cache.audit_statements(rows, {
        ITEM + 'prepare_scratch': {'item', 'debug', 'before', 'constructed', 'valid', 'domain', 'typed', 'made'},
        CALLER + 'initialize_failed': {'external', 'budget', 'allocator', 'source', 'buffer', 'request', 'before',
                                      'fault', 'after', 'good', 'scratch', 'admitted', 'failed', 'completed'},
        ITEM + 'invoke_init_failed': {'external', 'budget', 'allocator', 'p', 'q', 'source', 'request', 'debug',
            'good', 'admitted', 'domain', 'typed', 'made', 'room', 'allocated', 'failed', 'completed'},
        ITEM + 'invoke_entry_failed_native': {'host', 'budget', 'allocator', 'owner', 'capacity', 'safety', 'data', 'rows', 'p',
            'facts', 'represented', 'admitted', 'domain', 'typed', 'made', 'completed', 'stopped'},
        step.NS + 'step_entry_failed_verified': {'base', 'host', 'children', 'source', 'request', 'debug', 'facts', 'represented',
            'admitted', 'external', 'domain', 'typed', 'made', 'completed', 'stopped', 'valid'},
    })


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / name).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)

    return (
        ('initialization', source('InternerCallerInitFailure.lean'), (
            ('close-nonordinary', 'ordinary (.error fault : Except Fault NodeId) = true',
             'ordinary (.error fault : Except Fault NodeId) = false', 1),
            ('erase-registry', 'after.world.memory.heap = before.memory.heap', 'after.world.memory.heap = (fun _ => none)', 1),
        )),
        ('scratch', source('InternerConstructorScratch.lean'), (
            ('oversized-scratch', 'nextAddress + 8 <', 'nextAddress + 16 <', 1),
            ('wrong-scratch-identity', '⟨constructed.memory.memory.nextId, 0⟩', '⟨constructed.memory.memory.nextId + 1, 0⟩', 1),
        )),
        ('return', source('InternerConstructorEntryFailure.lean'), (
            ('turn-oom-into-success', 'actual.1 = .error fault ∧', 'actual.1 = .ok 0 ∧', 1),
            ('erase-original-cell', 'actual.2.world.memory.memory.heap.lookup id = some cell',
             'actual.2.world.memory.memory.heap.lookup id = none', 2),
            ('wrong-capacity-observation', 'full : q.atCapacity constructed.graph = true',
             'full : q.atCapacity constructed.graph = false', 1),
            ('unwind-rejected', 'before = (.error fault, reached) := by',
             'before = (.error fault, { reached with world := returnWorld before.memory.memory.nextId constructed.memory.memory.nextId reached.world }) := by', 1),
        )),
        ('native', source('InternerNativeEntryFailure.lean'), (
            ('wrong-native-rows', 'capacity actual.2.world rows ∧', 'capacity actual.2.world [] ∧', 1),
            ('wrong-borrowed-result', '(.error fault, actual.2.world)) := by', '(.ok 0, actual.2.world)) := by', 1),
            ('erase-key-table', 'actual.2.world.memory.effects.keys = before.memory.effects.keys',
             'actual.2.world.memory.effects.keys = (fun _ => none)', 1),
        )),
        ('observations', source('InternerConstructorEntryFailureTests.lean'), (
            ('capacity-runs-initializer', 'world.memory.effects.allocator = 5', 'world.memory.effects.allocator = 17', 1),
            ('capacity-allocates-scratch', 'world.memory.memory.nextId = 4', 'world.memory.memory.nextId = 5', 1),
            ('accept-oversized-boundary', '(.array 4 word) = .error .outOfMemory', '(.array 3 word) = .error .outOfMemory', 1),
        )),
    )


def controls(output, env, lean):
    records = []
    for group, text, changes in mutation_cases():
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous entry failure mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'entry-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'entry-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
