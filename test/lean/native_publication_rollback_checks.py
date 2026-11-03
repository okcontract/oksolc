#!/usr/bin/env python3
"""Audit reached publication rollback and its general-step consumers.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
from assembly_item_creation_checks import checked_controls
import native_step_checks as step

NATIVE = step.arguments.OWNED + 'Insertion.Native.'
GRAPH = step.arguments.OWNED + 'NativeGraph.Facts.'
TESTS = NATIVE + 'NativeRollbackTests.'
MODULE = 'Compiler.Extraction.InternerNativeRollbackProofTests'
CLAIMS = [NATIVE + name for name in ('publication_oom_rollback', 'spare_publication_oom_cleanup',
    'first_publication_oom_cleanup', 'growing_publication_oom_cleanup',
    'growing_publication_oom_reached', 'CallerInput.growing_oom', 'prepare_publication_oom',
    'unrelocated_append_owned', 'unrelocated_publication_oom_reached')]
CLAIMS += [GRAPH + 'frame_storage', GRAPH + 'frame_private', step.NS + 'CallFrame.growing_rollback',
    step.NS + 'CallFrame.unrelocated_rollback', step.NS + 'CallFrame.publication_rollback']
CLAIMS += [TESTS + name for name in ('refused_observed', 'completed')]
SMALL = NATIVE + 'UnrelocatedRollbackTests.'
CLAIMS += [SMALL + branch + '.' + name for branch in ('First', 'Spare') for name in ('observed', 'completed')]


def audit(claims):
    union = step.refusal_union()
    required = {
        NATIVE + 'publication_oom_rollback': {NATIVE + 'rollback_normalized_verified', NATIVE + 'cleanup_sequence_keys',
            step.arguments.OWNED + 'Publication.publish_oom'},
        NATIVE + 'growing_publication_oom_reached': {NATIVE + name for name in
            ('prepare_publication_oom', 'preparation_cleanup_apart', 'growing_publication_oom_cleanup')} |
            {'Compiler.Extraction.Storage.insert_prepared_oom'},
        NATIVE + 'CallerInput.growing_oom': {NATIVE + 'growing_publication_oom_reached'},
        GRAPH + 'frame_storage': {'Compiler.Extraction.AssemblyItem.Query.frame',
            'Compiler.Extraction.RepresentativeArray.Constant.Data.frame'},
        GRAPH + 'frame_private': {GRAPH + 'frame_storage'},
        step.NS + 'CallFrame.growing_rollback': {NATIVE + 'growing_publication_oom_reached',
            GRAPH + 'frame_storage', NATIVE + 'insert_unpublished_projected'},
        TESTS + 'refused_observed': {NATIVE + 'NativeGrowingTests.published_observed'},
        TESTS + 'completed': {TESTS + 'refused_observed', NATIVE + 'NativeGrowingTests.reached_frame',
            step.NS + 'CallFrame.publication_rollback'},
        NATIVE + 'prepare_publication_oom': {NATIVE + 'prepare_owned', 'Compiler.Extraction.Storage.insert_prepared_oom'},
        NATIVE + 'unrelocated_append_owned': {NATIVE + 'first_append_owned', NATIVE + 'spare_append_owned',
            'Compiler.Extraction.RepresentativeArray.Append.Registered.first_same',
            'Compiler.Extraction.RepresentativeArray.Append.Registered.spare_same'},
        NATIVE + 'unrelocated_publication_oom_reached': {NATIVE + name for name in
            ('prepare_publication_oom', 'unrelocated_append_owned', 'publication_oom_rollback', 'preparation_cleanup_apart')},
        step.NS + 'CallFrame.unrelocated_rollback': {NATIVE + 'unrelocated_publication_oom_reached',
            GRAPH + 'frame_storage', NATIVE + 'insert_unpublished_projected'},
        step.NS + 'CallFrame.publication_rollback': {step.NS + 'CallFrame.unrelocated_rollback_frame', step.NS + 'CallFrame.growing_rollback_frame', step.NS + 'RollbackReturn.graph'},
    }
    for branch in ('First', 'Spare'):
        required[SMALL + branch + '.observed'] = {NATIVE + 'Native' + branch + 'Tests.published_observed'}
        required[SMALL + branch + '.completed'] = {SMALL + branch + '.observed',
            NATIVE + 'Native' + branch + 'Tests.reached_frame', step.NS + 'CallFrame.publication_rollback'}
    for branch in ('spare', 'first', 'growing'):
        required[NATIVE + branch + '_publication_oom_cleanup'] = {
            NATIVE + branch + '_append_owned', NATIVE + 'publication_oom_rollback'}
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('publication rollback lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
        if not name.startswith((TESTS, SMALL)) and any(any(part.endswith('Tests') for part in dep.split('.')) for dep in claims[name]):
            raise ValueError('general publication rollback depends on fixtures: ' + name)
    if NATIVE + 'CallerGrowingChainTests.RollbackTests.derived_contract' in claims[TESTS + 'completed']:
        raise ValueError('new native completion assumes the legacy fixture final graph')
    return {'refusalUnion': union, 'checkedDependencies': sorted(required), 'sharedPublicationRefusalAndRollback': True,
        'legacyCallerSpecializesReachedProof': True, 'privateAndChangedStorageShareGraphFrame': True,
        'reachedRelocationPublicationOomNativeFrameDerived': True,
        'existingPrefixAndBothSafetyAndOperandModesReused': True,
        'firstAndSparePublicationOomCompletionVerified': True,
        'firstSpareAndNoRemapRollbackSharePreparationComposition': True,
        'completeNativeGraphInvariantVerified': False, 'completeNativeInsertionVerified': False,
        'recursiveInductionVerified': False, 'composedProductionTheoremVerified': False}


def audit_statements(rows):
    required = {
        NATIVE + 'publication_oom_rollback': {'appended', 'initial', 'publication', 'response', 'growth', 'rowOwned'},
        NATIVE + 'growing_publication_oom_reached': {'world', 'initial', 'represented', 'live', 'publication',
            'duplicateCall', 'createCall', 'cloneCall', 'backing', 'response', 'unlocked'},
        GRAPH + 'frame_storage': {'facts', 'owned', 'after', 'newData', 'newCapacity', 'retained', 'keys',
            'ownerAfter', 'headerAfter', 'boundedAfter', 'storageAfter'},
        step.NS + 'CallFrame.growing_rollback': {'frame', 'reads', 'admitted', 'aligned', 'room', 'refused', 'growth'},
    }
    required.update({
        NATIVE + 'prepare_publication_oom': {'world', 'initial', 'live', 'represented', 'publication', 'finish', 'post'},
        NATIVE + 'unrelocated_append_owned': {'installedPost', 'storage', 'selected', 'first', 'growth'},
        NATIVE + 'unrelocated_publication_oom_reached': {'world', 'initial', 'represented', 'live', 'publication', 'storage',
            'selected', 'first', 'duplicateCall', 'createCall', 'cloneCall', 'response', 'growth'},
        step.NS + 'CallFrame.unrelocated_rollback': {'frame', 'reads', 'admitted', 'aligned', 'selected', 'first', 'response', 'growth'},
        step.NS + 'CallFrame.publication_rollback': {'frame', 'reads', 'admitted', 'aligned', 'room', 'refused', 'growth'},
    })
    forbidden = {NATIVE + 'CallerInput', step.arguments.OWNED + 'Caller.Origin',
        step.NS + 'GraphFrame', step.NS + 'Returns', 'Compiler.Extraction.Interner.Represented'}
    for name, expected in required.items():
        statement = next(row['statement'] for row in rows if row['theorem'] == name)
        if statement.get('encoding') != 'kernelExprDag-v1':
            raise ValueError('unsupported publication rollback statement encoding')
        nodes, index, binders = statement['nodes'], statement['root'], set()
        while nodes[index][0] in ('forall', 'let'):
            node = nodes[index]
            if node[0] == 'forall':
                binders.add(node[1])
                if name != NATIVE + 'prepare_publication_oom' and node[1] in {'post', 'finish'}:
                    raise ValueError('internal continuation escaped into native completion: ' + name)
                constants = step.constants_below(statement, node[3])
                if forbidden & constants or any(any(part.endswith('Tests') for part in value.split('.')) for value in constants):
                    raise ValueError('rollback assumes origin, final frame, coherence or fixture: ' + name + ':' + node[1])
                if step.arguments.OWNED + 'NativeGraph.Facts' in constants and node[1] != 'facts':
                    raise ValueError('rollback assumes extra native graph: ' + name + ':' + node[1])
            index = node[4]
        if not expected <= binders:
            raise ValueError('rollback lost actual inputs: ' + name + ': ' + ', '.join(sorted(expected - binders)))
    return {'checkedGeneralInterfaces': sorted(required), 'rebasedOriginAndFinalGraphNotAssumed': True,
        'readCorrespondenceWithoutSemanticCoherence': True, 'reachedNormalizedOwnerArbitrary': True,
        'storageFrameUsesDerivedPhysicalPostconditions': True, 'graphOnlyInterfacePreserved': True}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / (name + '.lean')).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)
    return (
        ('suffix', source('InternerInsertionPublicationFailure'), (
            ('wrong-probe', '= (false, probeEffects))', '= (true, probeEffects))', 1),
            ('cleanup-order', '(Storage.Cleanup.sequence [.lastValue, .pop, .normalized])',
             '(Storage.Cleanup.sequence [.pop, .lastValue, .normalized])', 2),
            ('erase-keys', '(memory after).effects.keys = (memory appended).effects.keys',
             '(memory after).effects.keys = (fun _ => none)', 1),
            ('retain-value', 'after.item.clone.value = none', 'after.item.clone.value = some stored', 1),
        )),
        ('reached', source('InternerInsertionReachedGrowingRollback'), (
            ('wrong-result', '.ok (some .allocationFailure)', '.ok (some .success)', 1),
            ('rewind-history', '(memory after).memory.nextId = middle.memory.nextId + 1',
             '(memory after).memory.nextId = world.memory.memory.nextId', 1),
            ('revive-backing', '(memory after).heap oldLifetime = none',
             '(memory after).heap oldLifetime = world.memory.heap oldLifetime', 1),
            ('omit-pop', '⟨middle.memory.nextId, 0⟩ cells.length,', '⟨middle.memory.nextId, 0⟩ (cells.length + 1),', 1),
            ('wrong-fits', 'Fits installed.memory ⟨capacity * 32, 8⟩ base', 'Fits installed.memory ⟨oldCapacity * 32, 8⟩ base', 1),
        )),
        ('frame', source('InternerNativeGraphStorageFrame'), (
            ('exclude-empty-sentinel', '(capacity ≠ 0 → id ≠ data.allocation)', '(id ≠ data.allocation)', 1),
            ('exclude-empty-normalized', '(owned.items ≠ [] → id ≠ owned.address)', '(id ≠ owned.address)', 1),
            ('lose-rows', 'itemsType newData rows.length', 'itemsType newData (rows.length + 1)', 1),
            ('lose-keys', '(keys : after.effects.keys = before.memory.effects.keys)', '(keys : True)', 1),
        )),
        ('completion', source('InternerNativeGrowingRollback'), (
            ('wrong-probe', 'normalized growth false world)', 'normalized growth true world)', 2),
            ('rewind-graph', 'capacity actual.2 (rows ++ added)', 'capacity world (rows ++ added)', 1),
            ('retain-normalized', 'Consumed normalized actual.2.memory', 'Consumed normalized world.memory', 1),
            ('lost-read-binding', '(reads : world.graph.read = Storage.readValue (world.graph.representatives.getD []))', '(reads : True)', 1),
        )),
        ('composition', source('InternerInsertionReachedRollback'), (
            ('wrong-result', '.ok (some .allocationFailure)', '.ok (some .success)', 1),
            ('lose-normalized-owner', '(live : Memory.SliceValid allocator world.memory.heap normalized)', '(live : True)', 1),
            ('omit-normalized-release', '[.lastValue, .pop, .normalized]', '[.lastValue, .pop]', 3),
        )),
        ('unrelocated-append', source('InternerInsertionUnrelocatedAppend'), (
            ('allow-full-capacity', '(selected : oldCapacity = 0 ∨ cells.length < oldCapacity)',
             '(selected : oldCapacity = 0 ∨ cells.length ≤ oldCapacity)', 1),
            ('wrong-first-fits', 'Fits installed.memory ⟨160, 8⟩ base', 'Fits installed.memory ⟨128, 8⟩ base', 1),
            ('wrong-first-size', 'allocate allocator 160 8 installed.effects.allocator', 'allocate allocator 128 8 installed.effects.allocator', 1),
        )),
        ('unrelocated-reached', source('InternerInsertionReachedUnrelocatedRollback'), (
            ('wrong-probe', '(false, probeEffects)', '(true, probeEffects)', 3),
            ('wrong-result', '.ok (some .allocationFailure)', '.ok (some .success)', 1),
            ('retain-normalized', '(memory after).heap normalized.address = none',
             '(memory after).heap normalized.address = world.memory.heap normalized.address', 1),
            ('erase-keys', '(memory after).effects.keys = world.memory.effects.keys',
             '(memory after).effects.keys = (fun _ => none)', 1),
        )),
        ('unrelocated-native', source('InternerNativeUnrelocatedRollback'), (
            ('lost-read-binding', '(reads : world.graph.read = Storage.readValue (world.graph.representatives.getD []))', '(reads : True)', 1),
            ('rewind-native-world', 'capacity actual.2 (rows ++ added)', 'capacity world (rows ++ added)', 1),
            ('retain-normalized', 'Consumed normalized actual.2.memory', 'Consumed normalized world.memory', 1),
        )),
        ('union', source('InternerNativePublicationRollback'), (
            ('accept-first', 'FirstPublication ops allocate safety allocator owner meaning input key normalized false world',
             'FirstPublication ops allocate safety allocator owner meaning input key normalized true world', 1),
            ('accept-spare', 'SparePublication ops allocate safety allocator owner meaning input key normalized false world',
             'SparePublication ops allocate safety allocator owner meaning input key normalized true world', 1),
            ('accept-relocated', 'normalized growth false world', 'normalized growth true world', 1),
            ('unbind-growth', 'normalized growth false world', 'normalized none false world', 1),
        )),
        ('unrelocated-fixtures', source('InternerNativeUnrelocatedRollbackTests'), (
            ('wrong-result', '(actual safety empty growth).1 = .error (.language .outOfMemory)',
             '(actual safety empty growth).1 = .ok 0', 2),
            ('retain-first-input', 'Consumed (CallerInputTests.normalized empty) (actual safety empty growth).2.memory',
             'Consumed (CallerInputTests.normalized empty) (taken safety empty).2.world.memory', 1),
            ('retain-spare-input', 'Consumed (CallerSpareSuccessTests.normalized empty) (actual safety empty growth).2.memory',
             'Consumed (CallerSpareSuccessTests.normalized empty) (taken safety empty).2.world.memory', 1),
        )),
        ('fixtures', source('InternerNativeGrowingRollbackTests'), (
            ('wrong-result', '(actual safety empty).1 = .error (.language .outOfMemory)', '(actual safety empty).1 = .ok 5', 1),
            ('retain-normalized', 'Consumed (CallerGrowingChainTests.normalized safety empty 4) (actual safety empty).2.memory',
             'Consumed (CallerGrowingChainTests.normalized safety empty 4) (taken safety empty 4).2.world.memory', 1),
        )),
    )


def controls(output, env, lean):
    records = []
    for group, text, changes in mutation_cases():
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous rollback mutation: ' + group + '-' + name + ': ' + str(text.count(before)))
        records += checked_controls(output, [mutation_check(output, 'rollback-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'rollback-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
