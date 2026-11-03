#!/usr/bin/env python3
"""Audit actual take OOM and the shared constructor/native return composition.
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
TESTS = ITEM + 'TakeFailureTests.'
MODULE = 'Compiler.Extraction.InternerConstructorTakeFailureTests'
CLAIMS = [CALLER + name for name in ('take_failed', 'finish_take_failed', 'find_take_failed')]
CLAIMS += [ITEM + name for name in ('invoke_return_verified', 'invoke_after_scratch_effects',
                                  'invoke_take_failed', 'invoke_take_failed_native')]
CLAIMS += [step.NS + name for name in ('step_return_verified', 'step_take_failed_verified')]
CLAIMS += [TESTS + name for name in ('prefix_observed', 'missed', 'failed_observed',
                                   'failed_contract', 'cleanup_observed', 'allocation_boundaries')]


def audit(claims):
    required = {
        CALLER + 'take_failed': {NORMAL + 'take_refines'},
        CALLER + 'finish_take_failed': {CALLER + 'initialize_origin', CALLER + 'take_failed', NORMAL + 'OwnedCall.finish_ready'},
        CALLER + 'find_take_failed': {CALLER + 'find_initialized'},
        ITEM + 'invoke_return_verified': {ITEM + 'invoke_after_scratch', ITEM + 'returnWorld_frame', ITEM + 'returnWorld_valid'},
        ITEM + 'invoke_after_scratch_effects': {ITEM + 'invoke_after_scratch'},
        ITEM + 'invoke_take_failed': {ITEM + 'prepare_success', ITEM + 'invoke_return_verified',
            CALLER + 'finish_take_failed', CALLER + 'find_take_failed'},
        ITEM + 'invoke_take_failed_native': {ITEM + 'invoke_take_failed', cache.PUBLICATION + 'caller_init_keys',
            cache.PUBLICATION + 'caller_take_keys', NORMAL + 'OwnedCall.NativeGraph.Facts.frame'},
        step.NS + 'step_return_verified': {step.NS + 'step', NORMAL + 'OwnedCall.Semantic.Ensures.error',
            NORMAL + 'OwnedCall.Semantic.Ensures.pure'},
        step.NS + 'step_take_failed_verified': {ITEM + 'invoke_take_failed_native', step.NS + 'step_return_verified'},
        TESTS + 'failed_contract': {ITEM + 'invoke_take_failed', TESTS + 'prefix_observed', TESTS + 'failed_observed', TESTS + 'missed'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('take failure lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'takeFailureDerivedAsOOM': True,
        'exactReachedWorldRetainedThroughDetachedCleanup': True, 'oldNativeAndRegistryFramesDerived': True,
        'exactKeyTablePreserved': True, 'arbitraryProperChildrenNotReached': True,
        'sharedReturnRequiresDerivedLocalPostconditions': True, 'allEntryPrefixesVerified': False,
        'completeNativeGraphInvariantVerified': False, 'recursiveInductionVerified': False,
        'composedProductionTheoremVerified': False}


def audit_statements(rows):
    prefix = {'source', 'request', 'prepared', 'reached', 'fault', 'initialized', 'failed'}
    entry = {'debug', 'constructed', 'made', 'room', 'allocated', 'classified', 'keyed', 'missed', 'domain', 'typed'}
    required = {
        CALLER + 'take_failed': prefix | {'external', 'allocator', 'admitted'},
        CALLER + 'finish_take_failed': prefix | {'external', 'budget', 'allocator', 'good', 'admitted', 'allocated'},
        CALLER + 'find_take_failed': prefix | {'external', 'budget', 'allocator', 'p', 'q', 'classified', 'keyed', 'missed', 'room'},
        ITEM + 'invoke_take_failed': prefix | entry | {'external', 'budget', 'allocator', 'p', 'q', 'good', 'admitted'},
        ITEM + 'invoke_take_failed_native': prefix | entry | {'host', 'budget', 'allocator', 'owner', 'capacity', 'safety',
            'data', 'rows', 'p', 'q', 'facts', 'represented', 'admitted'},
        step.NS + 'step_take_failed_verified': prefix | entry | {'base', 'host', 'children', 'facts', 'represented',
            'admitted', 'external', 'valid'},
    }
    result = cache.audit_statements(rows, required)
    for row in rows:
        if row['theorem'] not in required:
            continue
        statement = row['statement']
        nodes, index = statement['nodes'], statement['root']
        while nodes[index][0] in ('forall', 'let'):
            node = nodes[index]
            if node[0] == 'forall' and node[1] in {'completed', 'routed', 'word', 'closed', 'closedGood', 'finalFrame'}:
                raise ValueError('take entry assumes its result or return frame: ' + row['theorem'])
            index = node[4]
    # This common helper intentionally takes derived local postconditions. Bind
    # them to the actual invocation, not a caller-selected execution variable.
    statement = next(row['statement'] for row in rows if row['theorem'] == step.NS + 'step_return_verified')
    nodes, index, found = statement['nodes'], statement['root'], False
    while nodes[index][0] in ('forall', 'let'):
        node = nodes[index]
        if node[1] == 'actual':
            if node[0] != 'let' or not {ITEM + 'invoke', step.NS + 'context'} <= step.constants_below(statement, node[3]):
                raise ValueError('shared native return is not bound to actual invocation')
            found = True
        index = node[4]
    if not found:
        raise ValueError('shared native return lost its actual invocation binding')
    result.update(sharedReturnActualInvocationBound=True, sharedReturnRequiresDerivedLocalPostconditions=True)
    return result


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / name).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)

    return (
        ('caller', source('InternerCallerTakeFailure.lean'), (
            ('wrong-fault', 'fault = .language .outOfMemory ∧ reached.world.graph',
             'fault = .language .invalidOptional ∧ reached.world.graph', 1),
            ('erase-registry', 'reached.world.memory.heap = prepared.world.memory.heap',
             'reached.world.memory.heap = (fun _ => none)', 1),
            ('rewind-world', 'after.world = reached.world ∧', 'after.world = before ∧', 1),
            ('ignore-classification', 'q.deterministic request.item = .ok deterministic',
             'q.deterministic request.item = .ok true', 1),
        )),
        ('return', source('InternerConstructorReturnedFrame.lean'), (
            ('wrong-result', 'actual.1 = result ∧', 'actual.1 = .ok 0 ∧', 1),
            ('erase-original-cell', 'actual.2.world.memory.memory.heap.lookup id = some cell',
             'actual.2.world.memory.memory.heap.lookup id = none', 1),
            ('rewind-effects', '(Caller.find external budget allocator (p address (input request.item debug)) q source\n        ⟨constructed.memory.memory.nextId, 0, 2⟩ request\n        { constructed with memory := { constructed.memory with memory } }).2.world.memory.effects := by',
             'before.memory.effects := by', 1),
        )),
        ('constructor', source('InternerConstructorTakeFailure.lean'), (
            ('wrong-result', 'actual.1 = .error fault ∧', 'actual.1 = .ok 0 ∧', 1),
            ('rewind-world', 'constructed.memory.memory.nextId reached.world ∧', 'constructed.memory.memory.nextId before ∧', 1),
        )),
        ('native-return', source('InternerNativeReturn.lean'), (
            ('wrong-borrowed-result', '(outcome, actual.2.world)) := by', '(.ok 0, actual.2.world)) := by', 1),
            ('wrong-word', 'before.graph.read id = some expected)', 'before.graph.read id = some (expected + 1))', 1),
        )),
        ('native', source('InternerNativeTakeFailure.lean'), (
            ('erase-key-table', 'actual.2.world.memory.effects.keys = before.memory.effects.keys',
             'actual.2.world.memory.effects.keys = (fun _ => none)', 1),
            ('wrong-native-rows', 'capacity actual.2.world rows ∧', 'capacity actual.2.world [] ∧', 1),
            ('wrong-borrowed-result', '(.error fault, actual.2.world)) := by', '(.ok 0, actual.2.world)) := by', 1),
        )),
        ('observations', source('InternerConstructorTakeFailureTests.lean'), (
            ('rewind-allocation-effects', 'effects.allocator = 5 + (sorted case).length * 4', 'effects.allocator = 5', 2),
            ('rewind-scratch-counter', 'nextId = (if case = .scratch then 6 else 5)', 'nextId = 5', 2),
            ('duplicate-owned', '(taken .temporary deterministic).1 = .ok ()',
             '(taken .temporary deterministic).1 = .error (.language .outOfMemory)', 1),
            ('allocate-empty', '(taken .empty deterministic).1 = .ok ()',
             '(taken .empty deterministic).1 = .error (.language .outOfMemory)', 1),
            ('consult-cache-despite-classification', 'deterministic := fun _ => .ok false', 'deterministic := fun _ => .ok true', 1),
        )),
    )


def controls(output, env, lean):
    records = []
    for group, text, changes in mutation_cases():
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous take failure mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'take-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'take-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
