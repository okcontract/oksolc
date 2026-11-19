#!/usr/bin/env python3
"""Audit capacity and preparation exits through shared reached caller completion.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
import native_step_checks as step
import caller_native_insertion_checks as caller

OWNED = caller.NORMAL + 'OwnedCall.'
NATIVE = caller.NATIVE
FACTS = OWNED + 'NativeGraph.Facts.'
CLAIMS = [FACTS + 'frame_private', FACTS + 'release', NATIVE + 'free_private_frame',
          NATIVE + 'preparation_oom_execution', NATIVE + 'insert_allocation_failure',
          NATIVE + 'body_unpublished', NATIVE + 'insert_unpublished', NATIVE + 'capacity_execution',
          OWNED + 'finish_handoff', step.NS + 'CallFrame.insertion_unpublished',
          step.NS + 'CallFrame.preparation_oom', step.NS + 'CallFrame.capacity_failure']


def audit_statements(rows):
    for name in CLAIMS:
        statement = next(row['statement'] for row in rows if row['theorem'] == name)
        if statement.get('encoding') != 'kernelExprDag-v1':
            raise ValueError('unsupported preparation completion statement encoding')
        constants = {node[1] for node in statement['nodes'] if node[0] == 'const'}
        if {NATIVE + 'CallerInput', OWNED + 'Caller.Origin'} & constants:
            raise ValueError('preparation completion assumes an entry origin: ' + name)
        if name == step.NS + 'CallFrame.preparation_oom':
            binders = {node[1] for node in statement['nodes'] if node[0] == 'forall'}
            if not {'detached', 'logical', 'room', 'admitted', 'failed', 'parentFrame', 'growth'} <= binders:
                raise ValueError('preparation completion lost an explicit local boundary')
            if not {NATIVE + 'PreparationOOM', caller.NORMAL + 'Consumed', step.NS + 'Returns'} <= constants:
                raise ValueError('preparation completion lost actual failure, consumption or return correspondence')
        if name == step.NS + 'CallFrame.capacity_failure':
            binders = {node[1] for node in statement['nodes'] if node[0] == 'forall'}
            if not {'detached', 'logical', 'saturated', 'deterministic', 'parentFrame', 'growth'} <= binders:
                raise ValueError('capacity completion lost an explicit reached boundary')
            if not {caller.NORMAL + 'Consumed', step.NS + 'Returns', 'Option.getD'} <= constants:
                raise ValueError('capacity completion lost reached rows, consumption or return correspondence')
    return {'reachedFailureWithoutRebasedOrigin': True, 'parentFrameLawRemainsPremise': True,
            'logicalAllocationCouplingVerified': False, 'completeNativeInsertionVerified': False}


def audit(claims):
    required = {
        FACTS + 'frame_private': {FACTS + 'resident', FACTS + 'header', FACTS + 'live', FACTS + 'data'},
        FACTS + 'release': {FACTS + 'frame_private'},
        NATIVE + 'free_private_frame': {NATIVE + 'free_keys', caller.NORMAL + 'free_empty',
                                      'Compiler.Extraction.Memory.Arguments.ReleasePost.frame'},
        NATIVE + 'preparation_oom_execution': {NATIVE + stage + '_oom_execution' for stage in ('duplicate', 'create', 'clone')},
        NATIVE + 'body_unpublished': {NATIVE + 'projected_unchanged', NATIVE + 'body'},
        NATIVE + 'insert_unpublished': {NATIVE + 'checkedExecution_read', NATIVE + 'body_unpublished'},
        NATIVE + 'insert_allocation_failure': {NATIVE + 'insert_unpublished'},
        NATIVE + 'capacity_execution': {'Compiler.Extraction.Storage.insert_capacity_failure', NATIVE + 'callbacks'},
        OWNED + 'finish_handoff': {OWNED + 'deinit_detached', OWNED + 'handoff', OWNED + 'graph'},
        step.NS + 'CallFrame.insertion_unpublished': {step.NS + 'CallFrame.insert_unpublished', FACTS + 'frame_private', NATIVE + 'insert_unpublished',
            OWNED + 'finish_handoff', OWNED + 'Caller.GraphCustody.operands'},
        step.NS + 'CallFrame.preparation_oom': {NATIVE + 'preparation_oom_execution', step.NS + 'CallFrame.insertion_unpublished'},
        step.NS + 'CallFrame.capacity_failure': {NATIVE + 'capacity_execution', step.NS + 'CallFrame.insertion_unpublished',
            caller.NORMAL + 'free_valid', NATIVE + 'free_private_frame', caller.NORMAL + 'released_consumed'},
    }
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError('preparation completion lost dependencies: ' + name + ': ' + ', '.join(sorted(missing)))
        if any(any(part.endswith('Tests') for part in dependency.split('.')) for dependency in claims[name]):
            raise ValueError('preparation completion depends on fixtures: ' + name)
    return {'checkedDependencies': sorted(required), 'threeReachedPreparationFailuresComposed': True,
            'privateOwnerConsumptionAndNativeGraphDerived': True, 'detachedOuterCleanupShared': True,
            'reachedCapacityUsesSharedCompletion': True,
            'completeNativeInsertionVerified': False, 'composedProductionTheoremVerified': False}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / (name + '.lean')).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)

    return (
        ('frame', source('InternerNativeGraphFrame'), (
            ('shift-key-owner', '(fun address => owned.items ≠ [] ∧ address = owned.address)',
             '(fun address => owned.items ≠ [] ∧ address = owned.address + 1)', 2),
            ('shift-operand-owner', 'row.arguments ≠ [] → owned.address ≠ row.argumentsAddress',
             'row.arguments ≠ [] → owned.address + 1 ≠ row.argumentsAddress', 2),
            ('exclude-empty-sentinel', '(owned.items ≠ [] → id ≠ owned.address) →', 'id ≠ owned.address →', 1),
            ('discard-keys', '(keys : after.effects.keys = before.memory.effects.keys)', '(keys : True)', 2),
        )),
        ('outcome', source('InternerInsertionPreparationOutcome'), (
            ('accept-duplicate-success', '⟨view normalized, normalized.items, none⟩ before = (.error .outOfMemory, failed)',
             '⟨view normalized, normalized.items, none⟩ before = (.ok (normalized, ⟨view normalized, normalized.items, none⟩), failed)', 1),
            ('rewind-clone-state', 'allocator input allocated = (.error .outOfMemory, failed)',
             'allocator input before = (.error .outOfMemory, failed)', 2),
            ('invent-publication', 'closed.published = false', 'closed.published = true', 2),
        )),
        ('projection', source('InternerInsertionNativeBody'), (
            ('lose-native-count', 'itemsType backing rows.length))', 'itemsType backing (rows.length + 1)))', 3),
            ('forget-append', '(unappended : closed.appended = false)', '(unappended : True)', 4),
            ('forget-publish', '(unpublished : closed.published = false)', '(unpublished : True)', 4),
        )),
        ('finish', source('InternerOwnedCleanup'), (
            ('missing-detachment', '(detached : lookup.owned = none)', '(detached : True)', 1),
            ('unwind-rejection', 'else (result, ⟨reached, ⟨some lookup, some normalized, true⟩⟩)',
             'else (result, ⟨reached, ⟨none, some normalized, true⟩⟩)', 1),
        )),
        ('shared-return', source('InternerNativeInsertionFailure'), (
            ('missing-detachment', '(detached : lookup.owned = none)', '(detached : True)', 1),
            ('drop-parent', 'parentFrame _ valid retained', 'frame.2.2', 1),
            ('rewind-graph-memory', 'facts.frame_private normalized (Insertion.memory after)', 'facts.frame_private normalized world.memory', 1),
            ('forget-consumption', '(consumed : Consumed normalized (Insertion.memory after))', '(consumed : True)', 2),
            ('wrong-result', '(projectedResult : (Interner.insertionOutcome (world.graph.representatives.getD []) outcome).mapError Fault.language = result)',
             '(projectedResult : (Interner.insertionOutcome (world.graph.representatives.getD []) outcome).mapError Fault.language = .ok 0)', 2),
            ('unwind-nonordinary', '(recoverable : ordinary result = true)', '(recoverable : True)', 1),
        )),
        ('completion', source('InternerNativePreparationFailure'), (
            ('missing-detachment', '(detached : lookup.owned = none)', '(detached : True)', 1),
            ('missing-admission', '(admitted : Admitted ops.arguments)', '(admitted : True)', 1),
            ('invent-capacity-error', 'actual (.error (.language .outOfMemory)) world.graph', 'actual (.error (.language .capacity)) world.graph', 1),
            ('consume-original-world', 'Consumed normalized actual.2.world.memory', 'Consumed normalized world.memory', 1),
        )),
        ('capacity-execution', source('InternerInsertionCapacity'), (
            ('early-capacity', '(saturated : 2 ^ 32 - 1 ≤ rows.length)', '(saturated : 2 ^ 32 - 2 ≤ rows.length)', 1),
            ('retained-owner', 'Storage.Release.normalized.run Storage.normalizedOwnership', 'Storage.normalizedOwnership', 1),
            ('capacity-is-oom', '((.ok (some .capacityFailure),', '((.ok (some .allocationFailure),', 1),
            ('wrong-owner', 'allocator normalized world.memory = (.ok (), released)',
             'allocator { normalized with address := normalized.address + 1 } world.memory = (.ok (), released)', 1),
        )),
        ('capacity-return', source('InternerNativeCapacityFailure'), (
            ('early-capacity', '(saturated : 2 ^ 32 - 1 ≤ (world.graph.representatives.getD []).length)',
             '(saturated : 2 ^ 32 - 2 ≤ (world.graph.representatives.getD []).length)', 1),
            ('missing-detachment', '(detached : lookup.owned = none)', '(detached : True)', 1),
            ('capacity-is-oom', 'actual (.error (.language .capacity)) world.graph', 'actual (.error (.language .outOfMemory)) world.graph', 1),
            ('consume-original-world', 'Consumed normalized actual.2.world.memory', 'Consumed normalized world.memory', 1),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    records = []
    for group, text, changes in mutation_cases():
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous preparation completion mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'preparation-completion-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'preparation-completion-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
