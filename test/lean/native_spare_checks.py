#!/usr/bin/env python3
"""Audit reached spare publication and its proper-child native-frame consumer.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
from assembly_item_creation_checks import checked_controls
import native_step_checks as step
import constructor_argument_checks as arguments

NATIVE = arguments.OWNED + 'Insertion.Native.'
GRAPH = arguments.OWNED + 'NativeGraph.'
TESTS = NATIVE + 'NativeSpareTests.'
CHAIN = NATIVE + 'CallerGrowingChainTests.GraphFacts.'
MODULE = 'Compiler.Extraction.InternerNativeSpareInsertionTests'
CLAIMS = [NATIVE + name for name in ('extended_arguments_apart', 'CallerInput.extended_arguments_apart',
    'spare_success_reached', 'CallerInput.spare_success', 'insert_published')]
CLAIMS += [GRAPH + 'data_frame', GRAPH + 'Facts.spare_success', CHAIN + 'data_after', step.NS + 'CallFrame.spare_published']
CLAIMS += [TESTS + name for name in ('initial_facts', 'reached_frame', 'published_observed', 'completed')]


def audit(claims):
    required = {
        NATIVE + 'extended_arguments_apart': {arguments.OWNED + 'Caller.GraphCustody.operands',
            'Compiler.ZigAir.Memory.valid_lookup'},
        NATIVE + 'CallerInput.extended_arguments_apart': {NATIVE + 'extended_arguments_apart', NATIVE + 'CallerInput.graph_custody'},
        NATIVE + 'spare_success_reached': {NATIVE + 'prepare_reached', NATIVE + 'extended_arguments_apart',
            NATIVE + 'spare_append_owned', NATIVE + 'publication_payload', NATIVE + 'publication_rows', 'Compiler.Extraction.Storage.insert_prepared_success',
            'Compiler.Extraction.AssemblyItem.Query.of_members',
            'Compiler.Extraction.OwnedKeys.Physical.Completed.graph_resident',
            arguments.OWNED + 'BorrowedQuery.Native.of_resident', 'Compiler.Extraction.RepresentativeArray.Operation.query'},
        NATIVE + 'CallerInput.spare_success': {NATIVE + 'spare_success_reached', NATIVE + 'CallerInput.graph_custody'},
        GRAPH + 'data_frame': {'Compiler.Extraction.RepresentativeArray.Constant.Data.frame',
            'Compiler.ZigAir.Memory.Heap.lookup_ne_of_type_ne'},
        CHAIN + 'data_after': {GRAPH + 'data_frame'},
        NATIVE + 'insert_published': {NATIVE + 'insert_success_at'},
        GRAPH + 'Facts.spare_success': {NATIVE + 'spare_success_reached', GRAPH + 'Facts.insert_published', GRAPH + 'data_frame',
            arguments.OWNED + 'Caller.GraphCustody.publication', 'Compiler.Extraction.OwnedKeys.view_store'},
        step.NS + 'CallFrame.spare_published': {GRAPH + 'Facts.spare_success'},
        TESTS + 'initial_facts': {NATIVE + 'CallerSpareSuccessTests.initial_representation', NATIVE + 'CallerSpareSuccessTests.initial_geometry'},
        TESTS + 'reached_frame': {step.NS + 'InputFrame.caller', TESTS + 'initial_facts'},
        TESTS + 'published_observed': {NATIVE + 'CallerSpareSuccessTests.preparation_results', NATIVE + 'CallerSpareSuccessTests.probe_result'},
        TESTS + 'completed': {step.NS + 'CallFrame.published', step.NS + 'CallFrame.spare_published', TESTS + 'published_observed', TESTS + 'reached_frame'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('spare composition lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
        if not name.startswith((TESTS, CHAIN)) and any(any(part.endswith('Tests') for part in dependency.split('.'))
                for dependency in claims[name]):
            raise ValueError('general spare composition depends on fixtures: ' + name)
    return {'checkedDependencies': sorted(required), 'reachedSpareNativeFrameDerived': True,
        'oldAndNewConstantDataDerived': True, 'callerAndGrowthDataSpecializeGeneralProof': True,
        'arbitraryOptionalGrowthCallbacksVerified': True, 'enclosingParentFrameRemainsExplicit': True,
        'completeNativeGraphInvariantVerified': False, 'advancingAllocationStreamCouplingVerified': False,
        'recursiveInductionVerified': False, 'composedProductionTheoremVerified': False}


def audit_statements(rows):
    required = {
        NATIVE + 'extended_arguments_apart': {'allocator', 'world', 'normalized', 'operands', 'cells', 'custody', 'fresh', 'separate'},
        NATIVE + 'spare_success_reached': {'ops', 'allocate', 'allocator', 'container', 'capacity', 'world', 'cells', 'custody',
            'duplicateCall', 'createCall', 'cloneCall', 'response', 'growth'},
        GRAPH + 'data_frame': {'allocator', 'owner', 'backing', 'rows', 'before', 'after', 'data', 'frame'},
        GRAPH + 'Facts.spare_success': {'ops', 'allocate', 'allocator', 'owner', 'capacity', 'world', 'rows', 'facts', 'custody',
            'aligned', 'privateSource', 'duplicateCall', 'createCall', 'cloneCall', 'response', 'growth'},
        step.NS + 'CallFrame.spare_published': {'allocator', 'owner', 'rows', 'world', 'frame', 'ops', 'allocate',
            'growth', 'aligned', 'room', 'success'},
    }
    forbidden = {NATIVE + 'CallerInput', arguments.OWNED + 'Caller.Origin', step.NS + 'GraphFrame', step.NS + 'Returns',
        arguments.OWNED + 'Semantic.Contracts', 'Compiler.Extraction.Recursive.Projects'}
    for name, expected in required.items():
        statement = next(row['statement'] for row in rows if row['theorem'] == name)
        if statement.get('encoding') != 'kernelExprDag-v1':
            raise ValueError('unsupported reached spare statement encoding')
        nodes, index, binders = statement['nodes'], statement['root'], set()
        while nodes[index][0] in ('forall', 'let'):
            node = nodes[index]
            if node[0] == 'forall':
                binders.add(node[1])
                constants = step.constants_below(statement, node[3])
                if forbidden & constants or any(any(part.endswith('Tests') for part in value.split('.')) for value in constants):
                    raise ValueError('reached spare assumes origin, completion or fixture: ' + name + ':' + node[1])
                if node[1] in {'finalFrame', 'preserved', 'nativeFrame', 'completed', 'afterFacts'}:
                    raise ValueError('reached spare assumes its final native result: ' + name)
            index = node[4]
        if not expected <= binders:
            raise ValueError('reached spare lost arbitrary inputs/observations: ' + name + ': ' + ', '.join(sorted(expected - binders)))
    return {'checkedGeneralInterfaces': sorted(required), 'rebasedOriginAndFinalNativeFrameNotAssumed': True,
        'actualPrefixObservationsExplicit': True, 'physicalDataFrameHelperExplicit': True}


def publication_observation_source(name):
    """Mutate shared source observations together with their actual consumer."""
    folder = ROOT / 'lean/Compiler/Extraction'
    raw = (folder / (name + '.lean')).read_text()
    shared = (folder / 'InternerUnrelocatedPublication.lean').read_text()
    imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import ') and
        line != 'import Compiler.Extraction.InternerUnrelocatedPublication')
    return (imports + '\n' + shared + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' +
        without_imports(raw))


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / (name + '.lean')).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)
    return (
        ('separation', source('InternerInsertionOperandSeparation'), (
            ('duplicate-not-fresh', 'operands.address = world.memory.memory.nextId', 'operands.address = normalized.address', 1),
            ('lose-old-separation', '(custody : Caller.GraphCustody allocator normalized cells world.memory)',
             '(custody : Caller.GraphCustody allocator normalized [] world.memory)', 1),
        )),
        ('reached', source('InternerInsertionSpareSuccess'), (
            ('allow-full-backing', '(spare : cells.length < capacity)', '(spare : cells.length ≤ capacity)', 1),
            ('accept-failed-probe', '(true, probeEffects)', '(false, probeEffects)', 2),
            ('wrong-key-owner', '⟨normalized.address, BitVec.ofNat 32 cells.length⟩', '⟨operands.address, BitVec.ofNat 32 cells.length⟩', 1),
            ('rewind-history', '(memory after).memory.nextId = middle.memory.nextId', '(memory after).memory.nextId = world.memory.memory.nextId', 1),
        )),
        ('graph', source('InternerNativeGraphInsertion'), (
            ('wrong-old-data', '(data : ∀ row ∈ rows, Constant.Data before.memory.memory row)',
             '(data : ∀ row ∈ rows, Constant.Data before.memory.memory { row with itemAddress := 0 })', 1),
            ('wrong-result', '(.ok (Storage.idFor rows), Insertion.projected', '(.ok (Storage.idFor rows + 1), Insertion.projected', 4),
            ('wrong-candidate', 'Storage.publishedOwnership after = row)', 'Storage.publishedOwnership after = { row with itemAddress := 0 })', 2),
        )),
        ('native', 'import Compiler.Extraction.InternerNativePublishedFrame\n' + publication_observation_source('InternerNativeSpareInsertion') + '\n' +
            without_imports((ROOT / 'lean/Compiler/Extraction/InternerNativeSpareCompletion.lean').read_text()), (
            ('unbound-capacity', 'capacityOffset = .ok (.scalar (.int false 64 capacity))', 'capacityOffset = .ok (.scalar (.int false 64 0))', 1),
            ('allow-full-observation', '(world.graph.representatives.getD []).length < capacity', '(world.graph.representatives.getD []).length ≤ capacity', 1),
            ('wrong-probe-observation', 'normalized true world', 'normalized false world', 1),
            ('wrong-new-data', 'exact itemReads .data', 'exact itemReads .instruction', 1),
            ('wrong-key-table', 'actual.2.memory.effects.keys = OwnedKeys.store', 'world.memory.effects.keys = OwnedKeys.store', 1),
        )),
        ('completion', source('InternerNativeSpareCompletion'), (
            ('rewind-native-world', 'rows key normalized world actual', 'rows key normalized world (actual.1, world)', 1),
            ('wrong-result', 'rows key normalized world actual', 'rows key normalized world (.ok 0, actual.2)', 1),
            ('omit-child-extension', 'result, added,', 'result, [],', 1),
        )),
        ('observations', source('InternerNativeSpareInsertionTests'), (
            ('wrong-id', '(actual safety empty growth).1 = .ok 1', '(actual safety empty growth).1 = .ok 0', 1),
            ('wrong-capacity', '⟨lifetime empty, 0⟩ 5 (before safety empty)', '⟨lifetime empty, 0⟩ 4 (before safety empty)', 1),
        )),
    )


def controls(output, env, lean):
    records = []
    for group, text, changes in mutation_cases():
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous reached spare mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'spare-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'spare-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
