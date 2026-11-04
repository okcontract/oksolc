#!/usr/bin/env python3
"""Audit reached first publication and the shared publication completion.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
from assembly_item_creation_checks import checked_controls
import native_step_checks as step
import native_spare_checks as spare

NATIVE, GRAPH = spare.NATIVE, spare.GRAPH
TESTS = NATIVE + 'NativeFirstTests.'
ARRAY = 'Compiler.Extraction.RepresentativeArray.'
CLONE = 'Compiler.Extraction.AssemblyClone.NativeFields.'
MODULE = 'Compiler.Extraction.InternerNativeFirstProofTests'
CLAIMS = [CLONE + 'Represents.query', CLONE + 'Installed.query',
    ARRAY + 'Capacity.Registered.first_pair', ARRAY + 'Append.Registered.first_same',
    NATIVE + 'first_success_reached', NATIVE + 'CallerInput.first_success',
    GRAPH + 'Facts.insert_published', GRAPH + 'Facts.first_success',
    step.NS + 'CallFrame.first_published', step.NS + 'CallFrame.published']
CLAIMS += [TESTS + name for name in
    ('initial_facts', 'reached_frame', 'published_observed', 'completed', 'unsupported_callback_skipped')]
CLAIMS += [ARRAY + 'Append.Registered.FirstAdapterTests.sentinel_aliases']


def audit(claims):
    required = {
        CLONE + 'Represents.query': {'Compiler.Extraction.AssemblyItem.Query.of_members', CLONE + 'key_fields'},
        CLONE + 'Installed.query': {CLONE + 'Represents.query'},
        ARRAY + 'Capacity.Registered.first_pair': {ARRAY + name for name in
            ('Remap.empty_old', 'Backing.Release.empty', 'Backing.reserve_verified', 'Publication.run_verified',
             'Growth.first_of_reservation_and_publication')},
        ARRAY + 'Append.Registered.first_same': {ARRAY + 'Capacity.Registered.first_pair', ARRAY + 'DescriptorRelation.first_registered'},
        NATIVE + 'first_success_reached': {NATIVE + name for name in
            ('prepare_reached', 'first_append_owned', 'extended_arguments_apart', 'publication_rows',
             'publication_payload', 'prepared_publication_cell')} | {ARRAY + 'Append.Registered.first_same', CLONE + 'Represents.query'},
        NATIVE + 'CallerInput.first_success': {NATIVE + 'first_success_reached', NATIVE + 'CallerInput.graph_custody'},
        GRAPH + 'Facts.first_success': {NATIVE + 'first_success_reached', GRAPH + 'Facts.insert_published'},
        step.NS + 'CallFrame.first_published': {GRAPH + 'Facts.first_success'},
        step.NS + 'CallFrame.published': {step.NS + 'CallFrame.' + name for name in
            ('first_published', 'spare_published', 'growing_published')},
        TESTS + 'initial_facts': {GRAPH + 'initialized', NATIVE + 'CallerInputTests.initializer'},
        TESTS + 'reached_frame': {TESTS + 'initial_facts', step.NS + 'CallFrame.caller'},
        TESTS + 'published_observed': {NATIVE + 'CallerInputTests.preparation', NATIVE + 'CallerInputTests.backing_response',
            NATIVE + 'CallerFirstSuccessTests.probe_result'},
        TESTS + 'completed': {step.NS + 'CallFrame.published', TESTS + 'reached_frame', TESTS + 'published_observed'},
        TESTS + 'unsupported_callback_skipped': {TESTS + 'completed'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('first publication lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
        if not name.startswith(TESTS) and any(any(part.endswith('Tests') for part in dependency.split('.'))
                for dependency in claims[name]):
            raise ValueError('general first publication depends on fixtures: ' + name)
    return {'checkedDependencies': sorted(required), 'publicationUnion': step.publication_union(),
        'reachedFirstNativeFrameDerived': True, 'oldCallerSpecializesReachedProof': True,
        'sharedPhysicalPreparationPublicationAndGraphLift': True, 'sharedRepresentedItemQuery': True,
        'emptySentinelHasNoRootOrFreshnessPremise': True,
        'optionalGrowthCallbacksArbitraryAtZeroCapacity': True, 'oldKeyRetirementExplicit': True,
        'enclosingParentFrameRemainsExplicit': True, 'completeNativeInsertionVerified': False,
        'completeNativeGraphInvariantVerified': False, 'recursiveInductionVerified': False,
        'advancingAllocationStreamCouplingVerified': False, 'composedProductionTheoremVerified': False}


def audit_statements(rows):
    required = {
        CLONE + 'Represents.query': {'represented', 'logical', 'cell', 'valid', 'found', 'typed', 'address', 'item', 'domain'},
        ARRAY + 'Capacity.Registered.first_pair': {'calls', 'allocate', 'allocator', 'owner', 'before', 'sentinel', 'count', 'response', 'fits', 'unlocked'},
        ARRAY + 'Append.Registered.first_same': {'calls', 'before', 'sentinel', 'cell', 'argumentsValid', 'response', 'fits'},
        NATIVE + 'first_success_reached': {'world', 'sentinel', 'custody', 'publication', 'live', 'unique', 'represented',
            'duplicateCall', 'createCall', 'cloneCall', 'backing', 'response', 'unlocked', 'growth'},
        GRAPH + 'Facts.insert_published': {'oldData', 'facts', 'world', 'rows', 'executed', 'candidate', 'data', 'frame'},
        GRAPH + 'Facts.first_success': {'sentinel', 'world', 'facts', 'custody', 'privateSource', 'domain', 'backing', 'response', 'growth'},
        step.NS + 'CallFrame.first_published': {'world', 'rows', 'frame', 'growth', 'success'},
        step.NS + 'CallFrame.published': {'world', 'rows', 'frame', 'growth', 'room', 'success'},
    }
    forbidden = {NATIVE + 'CallerInput', spare.arguments.OWNED + 'Caller.Origin',
        step.NS + 'GraphFrame', step.NS + 'Returns', spare.arguments.OWNED + 'Semantic.Contracts',
        'Compiler.Extraction.Recursive.Projects'}
    for name, expected in required.items():
        statement = next(row['statement'] for row in rows if row['theorem'] == name)
        if statement.get('encoding') != 'kernelExprDag-v1':
            raise ValueError('unsupported first publication statement encoding')
        nodes, index, binders = statement['nodes'], statement['root'], set()
        while nodes[index][0] in ('forall', 'let'):
            node = nodes[index]
            if node[0] == 'forall':
                binders.add(node[1])
                constants = step.constants_below(statement, node[3])
                if forbidden & constants or any(any(part.endswith('Tests') for part in value.split('.')) for value in constants):
                    raise ValueError('first publication assumes origin, completion or fixture: ' + name + ':' + node[1])
                if node[1] in {'emptyKeys', 'sentinelRoot', 'sentinelApart', 'finalFrame', 'afterFacts', 'completed'}:
                    raise ValueError('first publication gained a forbidden premise: ' + name + ':' + node[1])
            index = node[4]
        if not expected <= binders:
            raise ValueError('first publication lost arbitrary inputs/observations: ' + name + ': ' + ', '.join(sorted(expected - binders)))
    return {'checkedGeneralInterfaces': sorted(required), 'publicationUnion': step.publication_union(),
        'rebasedOriginAndFinalNativeFrameNotAssumed': True, 'arbitraryEmptyStorageAddress': True,
        'sharedGraphLiftRequiresDerivedPhysicalPostconditions': True, 'allocationAndProbeObservationsExplicit': True}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / (name + '.lean')).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)
    return (
        ('item-query', source('AssemblyCloneFields'), (
            ('wrong-kind-read', 'using represented .kind', 'using represented .data', 1),
            ('allow-invalid-tag', '(domain : (copied.item.kind.toNat : Int) ∈ itemTagValues)',
             '(domain : True)', 2),
        )),
        ('adapter', source('RepresentativeRegisteredFirstAppend'), (
            ('nonempty-old-storage', '.ok (.scalar (.int false 64 0)))', '.ok (.scalar (.int false 64 1)))', 2),
            ('allocator-refusal', '(some base, effects)', '(none, effects)', 2),
            ('unlocked-not-required', '= .ok ()) :', '= .error .unsupported) :', 2),
            ('lose-actual-allocation', 'RegionAllocation.Fits before.memory ⟨160, 8⟩ base', 'True', 2),
        )),
        ('reached', source('InternerInsertionReachedFirstSuccess'), (
            ('wrong-probe', '(true, probeEffects)', '(false, probeEffects)', 2),
            ('wrong-key-owner', 'OwnedKeys.store world.memory.effects.keys key ⟨normalized.address, 0⟩',
             'OwnedKeys.store world.memory.effects.keys key ⟨operands.address, 0⟩', 2),
            ('rewind-history', '(memory after).memory.nextId = middle.memory.nextId + 1',
             '(memory after).memory.nextId = middle.memory.nextId', 1),
            ('retain-retired-key', '(memory after).heap old.address = none ∧',
             '(memory after).heap old.address = world.memory.heap old.address ∧', 1),
            ('discard-retirement-exclusion',
             '(∀ old, world.memory.effects.keys key = some old → key.arguments ≠ [] → id ≠ old.address) →',
             'True →', 2),
        )),
        ('native', source('InternerNativeFirstInsertion'), (
            ('wrong-item-data', 'exact itemReads .data', 'exact itemReads .instruction', 1),
            ('wrong-key-owner', '⟨normalized.address, 0⟩', '⟨operands.address, 0⟩', 1),
            ('wrong-capacity', '5 actual.2 [row]', '4 actual.2 [row]', 1),
        )),
        ('observation', 'import Compiler.Extraction.InternerNativePublishedFrame\n' + spare.publication_observation_source('InternerNativeFirstInsertion') + '\n' +
            without_imports((ROOT / 'lean/Compiler/Extraction/InternerNativeFirstCompletion.lean').read_text()), (
            ('nonzero-capacity', '.ok (.scalar (.int false 64 0)) ∧', '.ok (.scalar (.int false 64 1)) ∧', 1),
            ('wrong-probe', 'normalized true world', 'normalized false world', 1),
            ('drop-fits', 'Compiler.ZigAir.Memory.RegionAllocation.Fits installed.memory ⟨160, 8⟩ base)', 'True)', 2),
            ('allow-invalid-tag', '(input.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues ∧', 'True ∧', 1),
        )),
        ('union', source('InternerNativePublishedCompletion'), (
            ('substitute-first', '  FirstPublished ops', '  SparePublished ops', 1),
            ('substitute-spare', '  SparePublished ops', '  FirstPublished ops', 1),
            ('unbind-relocated-callback', 'RelocatedPublished ops allocate safety allocator owner meaning input key normalized growth world',
             'RelocatedPublished ops allocate safety allocator owner meaning input key normalized none world', 1),
            ('rewind-result', 'capacity actual.2 (rows ++ added)', 'capacity world (rows ++ added)', 1),
        )),
        ('fixtures', source('InternerNativeFirstInsertionTests'), (
            ('wrong-id', '(actual safety empty growth).1 = .ok 0', '(actual safety empty growth).1 = .ok 1', 1),
            ('callback-executed', '(actual safety sentinel).2.effects = [(160, 8)]',
             '(actual safety sentinel).2.effects = [(160, 8), (999, 999)]', 1),
            ('rewind-history', '(actual safety sentinel).2.memory.nextId = 5', '(actual safety sentinel).2.memory.nextId = 4', 1),
        )),
    )


def controls(output, env, lean):
    records = []
    for group, text, changes in mutation_cases():
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous first publication mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'first-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'first-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
