#!/usr/bin/env python3
"""Audit initialized lookup routing and shared constructor/step return.
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
TESTS = ITEM + 'ClassificationTests.'
MODULE = 'Compiler.Extraction.InternerConstructorClassificationTests'
CLAIMS = [CALLER + name for name in ('initialized_key', 'find_initialized', 'find_classification_failed', 'find_cached', 'find_after_take')]
CLAIMS += [ITEM + name for name in ('invoke_initialized_verified', 'invoke_initialized_native',
                                  'invoke_classification_failed', 'invoke_classification_rejected')]
CLAIMS += [step.NS + name for name in ('step_initialized_verified', 'step_classification_failed_verified')]
CLAIMS += [TESTS + name for name in ('initialized', 'ordinary_contract', 'rejected_contract',
                                   'ordinary_observed', 'rejected_temporary', 'native_observed')]


def audit(claims):
    required = {
        CALLER + 'initialized_key': {CALLER + 'initLookup', 'Compiler.Extraction.Interner.Scoped.commutative',
                                     'Compiler.Extraction.Interner.makeKey'},
        CALLER + 'find_initialized': {CALLER + 'initialized_key', CALLER + 'find', 'Compiler.Extraction.Interner.FindCode.controlOwned'},
        CALLER + 'find_classification_failed': {CALLER + 'find_initialized'},
        CALLER + 'find_cached': {CALLER + 'find_initialized'},
        CALLER + 'find_after_take': {CALLER + 'find_initialized'},
        ITEM + 'invoke_initialized_verified': {CALLER + 'finish_initialized', ITEM + 'prepare_success',
            ITEM + 'invoke_return_verified'},
        ITEM + 'invoke_initialized_native': {ITEM + 'invoke_initialized_verified', cache.PUBLICATION + 'caller_finish_keys',
            cache.PUBLICATION + 'caller_init_keys', ITEM + 'invoke_after_scratch_effects', NORMAL + 'OwnedCall.NativeGraph.Facts.frame'},
        ITEM + 'invoke_classification_failed': {ITEM + 'invoke_initialized_verified', CALLER + 'find_classification_failed'},
        ITEM + 'invoke_classification_rejected': {ITEM + 'invoke_after_scratch', CALLER + 'find_classification_failed',
                                                 NORMAL + 'OwnedCall.finish_semantic'},
        step.NS + 'step_initialized_verified': {ITEM + 'invoke_initialized_native', step.NS + 'step_return_verified'},
        step.NS + 'step_classification_failed_verified': {step.NS + 'step_initialized_verified', CALLER + 'find_classification_failed'},
        TESTS + 'ordinary_contract': {ITEM + 'invoke_classification_failed', TESTS + 'initialized', cache.TESTS + 'prefix_observed'},
        TESTS + 'rejected_contract': {ITEM + 'invoke_classification_rejected', TESTS + 'initialized'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('initialized lookup lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'initializedKeyExistenceDerived': True,
        'cacheAndMissRoutingShareInitializedDecomposition': True, 'cacheAndErrorShareNativeReturn': True,
        'cacheAndErrorShareProperChildLeaf': True, 'classificationErrorFramesDerived': True,
        'exactRejectedInitializedStateRetained': True, 'successfulInitializationRequired': True,
        'takenAllocationFailureVerified': False, 'allEntryPrefixesVerified': False,
        'completeNativeGraphInvariantVerified': False, 'recursiveInductionVerified': False,
        'composedProductionTheoremVerified': False}


def audit_statements(rows):
    return cache.audit_statements(rows, {
        CALLER + 'initialized_key': {'external', 'budget', 'allocator', 'source', 'buffer', 'request', 'before', 'prepared', 'values', 'initialized'},
        CALLER + 'find_initialized': {'external', 'budget', 'allocator', 'p', 'q', 'source', 'buffer', 'request', 'before', 'room', 'initialized'},
        ITEM + 'invoke_initialized_verified': {'external', 'budget', 'allocator', 'p', 'q', 'source', 'request', 'debug',
            'good', 'admitted', 'domain', 'typed', 'made', 'room', 'allocated', 'initialized', 'result', 'completed', 'routed'},
        ITEM + 'invoke_initialized_native': {'host', 'budget', 'allocator', 'owner', 'capacity', 'safety', 'data', 'rows', 'p',
            'facts', 'represented', 'admitted', 'domain', 'typed', 'made', 'room', 'allocated', 'initialized', 'outcome', 'completed', 'routed'},
        step.NS + 'step_initialized_verified': {'base', 'host', 'children', 'source', 'request', 'debug', 'facts', 'represented',
            'admitted', 'external', 'allocated', 'initialized', 'completed', 'routed', 'valid', 'word'},
        step.NS + 'step_classification_failed_verified': {'base', 'host', 'children', 'source', 'request', 'debug', 'facts', 'represented',
            'admitted', 'external', 'allocated', 'initialized', 'classified', 'completed', 'valid'},
    })


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / name).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)

    return (
        ('routing', source('InternerCallerLookupRouting.lean'), (
            ('failed-init-has-key', 'request before = (.ok values, prepared)',
             'request before = (.error (.language .invalidOptional), prepared)', 1),
            ('ignore-classification-error', '| .error error => finish external allocator (.error (.language error) : Except Fault NodeId) prepared',
             '| .error _ => finish external allocator (.ok 0 : Except Fault NodeId) prepared', 1),
            ('ignore-nondeterminism', 'if deterministic then before.graph.table key else none', 'before.graph.table key', 1),
        )),
        ('return', source('InternerConstructorLookupReturn.lean'), (
            ('close-rejected', 'completed : ordinary result = true', 'completed : ordinary result = false', 1),
            ('erase-original-cell', 'actual.2.world.memory.memory.heap.lookup id = some cell',
             'actual.2.world.memory.memory.heap.lookup id = none', 1),
        )),
        ('native', source('InternerNativeLookupReturn.lean'), (
            ('erase-key-table', 'actual.2.world.memory.effects.keys = before.memory.effects.keys',
             'actual.2.world.memory.effects.keys = (fun _ => none)', 1),
            ('wrong-borrowed-result', '(outcome, actual.2.world)) := by', '(.ok 0, actual.2.world)) := by', 1),
            ('wrong-word', 'before.graph.read id = some expected)', 'before.graph.read id = some (expected + 1))', 1),
        )),
        ('classification', source('InternerConstructorClassificationFailure.lean'), (
            ('turn-error-into-success', 'actual.1 = .error (.language error) ∧', 'actual.1 = .ok 0 ∧', 1),
            ('unwind-rejected', 'before = (.error (.language error), prepared) := by',
             'before = (.error (.language error), { prepared with world := returnWorld before.memory.memory.nextId constructed.memory.memory.nextId prepared.world }) := by', 1),
        )),
        ('step', source('InternerNativeClassificationFailure.lean'), (
            ('wrong-classification', 'base.queries.deterministic request.item = .error error',
             'base.queries.deterministic request.item = .ok true', 1),
        )),
        ('observations', source('InternerConstructorClassificationTests.lean'), (
            ('omit-temporary-release', 'if case = .temporary then 120 else 5', 'if case = .temporary then 17 else 5', 1),
            ('release-rejected-owner', 'some ⟨5, [1, 2, 3]⟩', 'none', 1),
            ('rewind-rejected-effects', 'world.memory.effects.allocator = 17', 'world.memory.effects.allocator = 5', 1),
            ('ordinary-safety-fault', '(native 2 (some 1)).2.scope.lookup = some ⟨source .temporary, [3, 1, 2], none⟩',
             '(native 2 (some 1)).2.scope.lookup = none', 1),
        )),
    )


def controls(output, env, lean):
    records = []
    for group, text, changes in mutation_cases():
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous initialized lookup mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'lookup-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'lookup-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
