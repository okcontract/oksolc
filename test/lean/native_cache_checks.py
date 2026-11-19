#!/usr/bin/env python3
"""Audit the general native cache-hit entry and its proper-child leaf.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
from assembly_item_creation_checks import checked_controls
import constructor_argument_checks as arguments
import native_step_checks as step

NORMAL = 'Compiler.Extraction.Memory.Arguments.Normalization.'
CALLER = arguments.OWNED + 'Caller.'
PUBLICATION = arguments.OWNED + 'Publication.'
ITEM = arguments.ITEM
TESTS = ITEM + 'CacheTests.'
CLAIMS = [CALLER + name for name in ('initialize_origin_frame', 'initialize_origin', 'finish_initialized')]
CLAIMS += [ITEM + name for name in ('invoke_after_scratch', 'invoke_after_take', 'invoke_cached',
    'invoke_cached_verified', 'invoke_cached_native', 'cached_word')]
CLAIMS += [PUBLICATION + name for name in ('deinitialize_keys', 'caller_deinit_keys', 'caller_cleanup_keys', 'caller_finish_keys')]
CLAIMS += [step.NS + 'step_cached_verified']
CLAIMS += [TESTS + name for name in ('prefix_observed', 'completed', 'cleanup_observed', 'owned_temporary',
    'initialization_oom', 'incomplete_retained')]


def audit(claims):
    required = {
        CALLER + 'initialize_origin_frame': {NORMAL + 'caller_buffer', NORMAL + 'init_frame',
            CALLER + 'initialize_verified', CALLER + 'initialize_graph'},
        CALLER + 'initialize_origin': {CALLER + 'initialize_origin_frame'},
        CALLER + 'finish_initialized': {CALLER + 'initialize_origin_frame', NORMAL + 'deinit_refines', NORMAL + 'closed_frame'},
        ITEM + 'invoke_after_scratch': {ITEM + 'invoke_prepared'},
        ITEM + 'invoke_after_take': {ITEM + 'invoke_after_scratch', CALLER + 'find_after_take'},
        ITEM + 'invoke_cached': {ITEM + 'invoke_after_scratch', CALLER + 'find_cached'},
        ITEM + 'invoke_cached_verified': {ITEM + 'invoke_initialized_verified', CALLER + 'find_cached'},
        PUBLICATION + 'deinitialize_keys': {arguments.OWNED + 'Insertion.Native.free_keys'},
        PUBLICATION + 'caller_finish_keys': {PUBLICATION + 'caller_cleanup_keys', PUBLICATION + 'caller_deinit_keys'},
        ITEM + 'invoke_cached_native': {ITEM + 'invoke_initialized_native', CALLER + 'find_cached'},
        ITEM + 'cached_word': {'Compiler.Extraction.InsertionSort.normalize_word', 'Compiler.Extraction.Interner.makeKey_sound'},
        step.NS + 'step_cached_verified': {step.NS + 'step_initialized_verified', ITEM + 'cached_word', CALLER + 'find_cached'},
        TESTS + 'completed': {ITEM + 'invoke_cached_verified', TESTS + 'prefix_observed', PUBLICATION + 'OriginTests.initial_good'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('cache entry lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'actualCacheHitEntryDerived': True,
        'ownedAndBorrowedNormalizationCleanupDerived': True, 'oldNativeAndRegistryFramesDerived': True,
        'arbitraryProperChildrenNotReached': True, 'successfulInitializationRequired': True,
        'allEntryPrefixesVerified': False, 'completeNativeGraphInvariantVerified': False,
        'recursiveInductionVerified': False, 'composedProductionTheoremVerified': False}


def audit_statements(rows, required=None):
    if required is None:
        required = {
            ITEM + 'invoke_cached_verified': {'external', 'budget', 'allocator', 'p', 'q', 'source', 'request', 'debug',
                'good', 'admitted', 'domain', 'typed', 'made', 'room', 'allocated', 'initialized', 'classified', 'keyed', 'found'},
            ITEM + 'invoke_cached_native': {'host', 'budget', 'allocator', 'owner', 'capacity', 'safety', 'data', 'rows', 'p',
                'facts', 'represented', 'admitted', 'domain', 'typed', 'made', 'room', 'allocated', 'initialized', 'classified', 'keyed', 'found'},
            step.NS + 'step_cached_verified': {'base', 'host', 'children', 'source', 'request', 'debug', 'facts', 'represented',
                'admitted', 'external', 'allocated', 'initialized', 'keyed', 'found', 'valid', 'evaluated'},
        }
    forbidden = {step.NS + name for name in ('Returns', 'GraphFrame', 'MissSteps', 'MissCompletions')}
    forbidden |= {arguments.OWNED + 'Semantic.Contracts', 'Compiler.Extraction.Recursive.Projects',
                  'Compiler.Extraction.Associative.ConstructorSound'}
    for name, expected in required.items():
        statement = next(row['statement'] for row in rows if row['theorem'] == name)
        if statement.get('encoding') != 'kernelExprDag-v1':
            raise ValueError('unsupported constructor entry statement encoding')
        nodes, index, binders = statement['nodes'], statement['root'], set()
        while nodes[index][0] in ('forall', 'let'):
            node = nodes[index]
            if node[0] == 'let':
                index = node[4]
                continue
            binders.add(node[1])
            constants = step.constants_below(statement, node[3])
            if forbidden & constants or any('.Tests.' in value or 'Tests.' in value for value in constants):
                raise ValueError('constructor entry assumes completion, child simulation or a fixture: ' + name + ':' + node[1])
            index = node[4]
        if not expected <= binders:
            raise ValueError('constructor entry lost arbitrary input/prefix binders: ' + name)
    return {'checkedGeneralInterfaces': sorted(required), 'finalFrameAndChildContractsNotAssumed': True}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / name).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)

    return (
        ('initialized-cleanup', source('InternerCallerInitializedCleanup.lean'), (
            ('erase-original-cell', 'after.world.memory.memory.heap.lookup id = some cell',
             'after.world.memory.memory.heap.lookup id = none', 1),
            ('keep-lookup-open', 'Good source request.arguments after.world ∧ OwnedCall.Closed after.scope',
             'Good source request.arguments after.world ∧ OwnedCall.Closed { after.scope with lookup := prepared.scope.lookup }', 1),
            ('wrong-normalized-values', 'request.item request.arguments = some values := by',
             'request.item request.arguments = some [] := by', 1),
        )),
        ('entry', source('InternerConstructorCacheHit.lean'), (
            ('wrong-cached-id', 'actual.1 = .ok id ∧', 'actual.1 = .ok (id + 1) ∧', 1),
            ('erase-registry', 'actual.2.world.memory.heap id = some block', 'actual.2.world.memory.heap id = none', 1),
            ('wrong-cache-observation', 'constructed.graph.table key = some id', 'constructed.graph.table key = none', 1),
        )),
        ('keys', source('InternerCallerPublicationCleanup.lean'), (
            ('drop-keys-on-deinit', 'allocator handle before).2.effects.keys = before.effects.keys',
             'allocator handle before).2.effects.keys = (fun _ => none)', 1),
            ('drop-keys-on-finish', 'allocator result before).2.world.memory.effects.keys = before.world.memory.effects.keys',
             'allocator result before).2.world.memory.effects.keys = (fun _ => none)', 1),
        )),
        ('native', source('InternerNativeCacheHit.lean'), (
            ('wrong-word', 'before.read id = some expected := by', 'before.read id = some (expected + 1) := by', 1),
            ('wrong-native-rows', 'capacity actual.2.world rows ∧', 'capacity actual.2.world [] ∧', 1),
            ('wrong-borrowed-result', '(.ok id, actual.2.world)) := by', '(.ok (id + 1), actual.2.world)) := by', 1),
        )),
        ('observations', source('InternerNativeCacheHitTests.lean'), (
            ('omit-temporary-release', 'if case = .temporary then 120 else 5', 'if case = .temporary then 17 else 5', 1),
            ('omit-oom-effects', 'oom.2.world.memory.effects.allocator = 17', 'oom.2.world.memory.effects.allocator = 5', 1),
            ('unwind-incomplete', '(suspended.2.world.memory.memory.heap.lookup 3).isSome = true',
             '(suspended.2.world.memory.memory.heap.lookup 3).isSome = false', 1),
            ('wrong-temporary-owner', 'some ⟨5, [1, 2, 3]⟩', 'some ⟨4, [1, 2, 3]⟩', 1),
        )),
    )


def controls(output, env, lean):
    records = []
    for group, text, changes in mutation_cases():
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous cache mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'cache-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'cache-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
