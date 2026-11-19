#!/usr/bin/env python3
"""Audit reached backing OOM through shared preparation, cleanup and completion.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
from assembly_item_creation_checks import checked_controls
import native_step_checks as step
import caller_growth_allocation_failure_checks as caller

NATIVE, ARRAY = caller.NATIVE, caller.ARRAY
TESTS = NATIVE + 'BackingFailureTests.'
MODULE = 'Compiler.Extraction.InternerNativeBackingProofTests'
CLAIMS = [NATIVE + name for name in ('preparation_cleanup_apart', 'CallerInput.cleanup_apart',
    'append_oom_reached', 'first_allocation_oom_reached', 'growing_allocation_oom_reached',
    'CallerInput.growing_allocation_oom')]
CLAIMS += [ARRAY + 'Append.Registered.first_refused']
CLAIMS += [step.NS + 'CallFrame.' + name for name in ('insert_unpublished', 'insertion_unpublished', 'backing_oom_execution', 'backing_oom')]
CLAIMS += [TESTS + name for name in
    ('first_observed', 'first_completed', 'first_unsupported_callback_skipped', 'growing_observed', 'growing_completed')]


def audit(claims):
    required = {
        NATIVE + 'CallerInput.cleanup_apart': {NATIVE + 'preparation_cleanup_apart'},
        NATIVE + 'append_oom_reached': {NATIVE + name for name in
            ('prepare_owned', 'preparation_cleanup_apart', 'unappended_cleanup')} | {caller.STORAGE + 'insert_append_oom'},
        ARRAY + 'Append.Registered.first_refused': {ARRAY + name for name in
            ('DescriptorRelation.first_registry_oom', 'Remap.empty_old', 'Backing.Fallback.oom_verified')},
        NATIVE + 'first_allocation_oom_reached': {NATIVE + 'append_oom_reached', ARRAY + 'Append.Registered.first_refused'},
        NATIVE + 'growing_allocation_oom_reached': {NATIVE + 'append_oom_reached', ARRAY + 'Append.Registered.growing_oom'},
        NATIVE + 'CallerInput.growing_allocation_oom': {NATIVE + 'growing_allocation_oom_reached'},
        step.NS + 'CallFrame.insert_unpublished': {NATIVE + 'insert_unpublished', step.recursion.FACTS + 'frame_private'},
        step.NS + 'CallFrame.insertion_unpublished': {step.NS + 'CallFrame.insert_unpublished', step.arguments.OWNED + 'finish_handoff'},
        step.NS + 'CallFrame.backing_oom': {step.NS + 'CallFrame.insert_unpublished',
            step.NS + 'CallFrame.backing_oom_execution'},
        step.NS + 'CallFrame.backing_oom_execution': {
            NATIVE + 'first_allocation_oom_reached_at', NATIVE + 'growing_allocation_oom_reached_at'},
        TESTS + 'first_observed': {NATIVE + 'NativeFirstTests.published_observed'},
        TESTS + 'growing_observed': {NATIVE + 'NativeGrowingTests.published_observed'},
        TESTS + 'first_completed': {TESTS + 'first_observed', NATIVE + 'NativeFirstTests.reached_frame', step.NS + 'CallFrame.backing_oom'},
        TESTS + 'growing_completed': {TESTS + 'growing_observed', NATIVE + 'NativeGrowingTests.reached_frame', step.NS + 'CallFrame.backing_oom'},
        TESTS + 'first_unsupported_callback_skipped': {TESTS + 'first_completed'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('backing OOM lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
        if not name.startswith(TESTS) and any(any(part.endswith('Tests') for part in dep.split('.')) for dep in claims[name]):
            raise ValueError('general backing OOM depends on fixtures: ' + name)
    return {'checkedDependencies': sorted(required), 'sharedReachedPreparationAndCleanup': True,
        'oldCallerSpecializesReachedProof': True, 'sharedUnpublishedCompletion': True,
        'firstAndNoRemapBackingOomNativeFramesDerived': True,
        'emptySentinelAndOptionalCallbacksArbitrary': True, 'enclosingParentLawRemainsExplicit': True,
        'completeNativeInsertionVerified': False, 'recursiveInductionVerified': False,
        'composedProductionTheoremVerified': False}


def audit_statements(rows):
    required = {
        NATIVE + 'preparation_cleanup_apart': {'initial', 'live', 'admitted', 'duplicateCall', 'createCall', 'cloneCall'},
        NATIVE + 'append_oom_reached': {'world', 'represented', 'live', 'admitted', 'room', 'refused', 'growth'},
        ARRAY + 'Append.Registered.first_refused': {'before', 'sentinel', 'calls', 'cell', 'response', 'unlocked'},
        NATIVE + 'first_allocation_oom_reached': {'world', 'sentinel', 'growth', 'response', 'unlocked'},
        NATIVE + 'growing_allocation_oom_reached': {'world', 'backingOwned', 'oldNonempty', 'full', 'selected', 'size', 'room', 'response'},
        step.NS + 'CallFrame.insert_unpublished': {'frame', 'reads', 'executed', 'retained', 'consumed', 'parentFrame'},
        step.NS + 'CallFrame.backing_oom': {'frame', 'reads', 'room', 'admitted', 'failed', 'parentFrame', 'growth'},
        step.NS + 'CallFrame.backing_oom_execution': {'frame', 'room', 'admitted', 'failed', 'growth'},
    }
    forbidden = {NATIVE + 'CallerInput', step.arguments.OWNED + 'Caller.Origin',
        step.NS + 'GraphFrame', step.NS + 'Returns', 'Compiler.Extraction.Interner.Represented'}
    for name, expected in required.items():
        statement = next(row['statement'] for row in rows if row['theorem'] == name)
        if statement.get('encoding') != 'kernelExprDag-v1':
            raise ValueError('unsupported backing OOM statement encoding')
        nodes, index, binders = statement['nodes'], statement['root'], set()
        while nodes[index][0] in ('forall', 'let'):
            node = nodes[index]
            if node[0] == 'forall':
                binders.add(node[1])
                constants = step.constants_below(statement, node[3])
                if forbidden & constants or any(any(part.endswith('Tests') for part in value.split('.')) for value in constants):
                    raise ValueError('backing OOM assumes origin, completion, semantic coherence or fixture: ' + name + ':' + node[1])
            index = node[4]
        if not expected <= binders:
            raise ValueError('backing OOM lost arbitrary inputs/observations: ' + name + ': ' + ', '.join(sorted(expected - binders)))
    return {'checkedGeneralInterfaces': sorted(required), 'rebasedOriginAndFinalFrameNotAssumed': True,
        'readCorrespondenceSufficesWithoutSemanticCoherence': True,
        'arbitraryReachedNormalizedOwner': True, 'sourceAllocationResponsesAndParentLawExplicit': True}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / (name + '.lean')).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)
    return (
        ('adapter', source('RepresentativeFirstAllocationFailure'), (
            ('nonzero-capacity', '.ok (.scalar (.int false 64 0)))', '.ok (.scalar (.int false 64 1)))', 1),
            ('allocation-succeeded', '(none, effects))', '(some 0, effects))', 1),
            ('lose-effects', '(.ok false, { before with effects })', '(.ok false, before)', 2),
        )),
        ('cleanup', source('InternerInsertionAppendFailure'), (
            ('rewind-history', '(memory after).memory.nextId = middle.memory.nextId',
             '(memory after).memory.nextId = world.memory.memory.nextId', 1),
            ('normalized-owner-retained', 'Consumed normalized (memory after) ∧', 'Consumed normalized world.memory ∧', 1),
            ('change-result', '.ok (some .allocationFailure)', '.ok (some .success)', 1),
            ('release-order', '[.value, .allocation, .arguments, .normalized]', '[.allocation, .value, .arguments, .normalized]', 1),
        )),
        ('first', source('InternerInsertionReachedFirstAllocationFailure'), (
            ('wrong-request-size', 'allocate allocator 160 8 installed.effects.allocator',
             'allocate allocator 128 8 installed.effects.allocator', 2),
            ('lose-unlocked', '= .ok ())', '= .error .unsupported)', 2),
        )),
        ('growing', source('InternerInsertionReachedGrowthAllocationFailure'), (
            ('wrong-request-size', 'allocate allocator (capacity * 32) 8 installed.effects.allocator',
             'allocate allocator (oldCapacity * 32) 8 installed.effects.allocator', 2),
            ('discard-full', '(full : oldCapacity < Append.nextLength cells.length)', '(full : True)', 2),
        )),
        ('native', source('InternerNativeBackingFailure'), (
            ('nonzero-first-capacity', '.ok (.scalar (.int false 64 0)) ∧', '.ok (.scalar (.int false 64 1)) ∧', 1),
            ('unbind-growth', 'growth = some ⟨.noRemap context returnAddress, freeBacking⟩ ∧', 'True ∧', 1),
            ('success-after-refusal', 'actual.1 = .error (.language .outOfMemory)', 'actual.1 = .ok 0', 1),
            ('consumed-before-execution', 'Consumed normalized (Insertion.memory after)', 'Consumed normalized world.memory', 2),
        )),
        ('completion', source('InternerNativeInsertionFailure'), (
            ('drop-read-correspondence',
             '(reads : world.graph.read = Storage.readValue (world.graph.representatives.getD []))', '(reads : True)', 1),
            ('discard-parent', 'parentFrame _ valid retained', 'frame.2.2', 1),
        )),
        ('fixtures', source('InternerNativeBackingFailureTests'), (
            ('wrong-first-result', '(first safety empty growth).1 = .error (.language .outOfMemory)',
             '(first safety empty growth).1 = .ok 0', 1),
            ('wrong-growing-result', '(growing safety empty).1 = .error (.language .outOfMemory)',
             '(growing safety empty).1 = .ok 5', 1),
        )),
    )


def controls(output, env, lean):
    records = []
    for group, text, changes in mutation_cases():
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous backing OOM mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'backing-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'backing-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
