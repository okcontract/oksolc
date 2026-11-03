#!/usr/bin/env python3
"""Audit reached nonempty relocation and its proper-child native-frame consumer.
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
TESTS = NATIVE + 'NativeGrowingTests.'
CHAIN = NATIVE + 'CallerGrowingChainTests.'
MODULE = 'Compiler.Extraction.InternerNativeGrowthProofTests'
CLAIMS = [NATIVE + 'publication_payload', NATIVE + 'growing_success_reached',
    NATIVE + 'CallerInput.growing_success', GRAPH + 'Facts.insert_published',
    GRAPH + 'Facts.spare_success', GRAPH + 'Facts.growing_success', step.NS + 'CallFrame.growing_published']
CLAIMS += [TESTS + name for name in ('reached_frame', 'published_observed', 'completed')]


def audit(claims):
    required = {
        NATIVE + 'publication_payload': {'Compiler.Extraction.AssemblyClone.Physical.Reads.frame'},
        NATIVE + 'growing_success_reached': {NATIVE + name for name in
            ('prepare_reached', 'extended_arguments_apart', 'growing_append_owned', 'publication_rows',
             'publication_payload', 'prepared_publication_cell')},
        NATIVE + 'CallerInput.growing_success': {NATIVE + 'growing_success_reached',
            NATIVE + 'CallerInput.graph_custody_after_growth', NATIVE + 'CallerInput.custody_after_growth'},
        GRAPH + 'Facts.insert_published': {GRAPH + 'Facts.insert_success_at'},
        GRAPH + 'Facts.spare_success': {NATIVE + 'spare_success_reached', GRAPH + 'Facts.insert_published'},
        GRAPH + 'Facts.growing_success': {NATIVE + 'growing_success_reached', GRAPH + 'Facts.insert_published'},
        step.NS + 'CallFrame.growing_published': {GRAPH + 'Facts.growing_success'},
        TESTS + 'reached_frame': {CHAIN + 'initialized_prefix', CHAIN + 'Prefix.source_private',
            CHAIN + 'GraphFacts.native', step.NS + 'CallFrame.caller'},
        TESTS + 'published_observed': {CHAIN + 'preparation_results', CHAIN + 'backing_fits',
            CHAIN + 'growth_entry_unlocked'},
        TESTS + 'completed': {step.NS + 'CallFrame.published', step.NS + 'CallFrame.growing_published', TESTS + 'reached_frame', TESTS + 'published_observed'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('relocation composition lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
        if not name.startswith(TESTS) and any(any(part.endswith('Tests') for part in dependency.split('.'))
                for dependency in claims[name]):
            raise ValueError('general relocation composition depends on fixtures: ' + name)
    return {'checkedDependencies': sorted(required), 'reachedRelocationNativeFrameDerived': True,
        'sharedSpareAndRelocatedGraphConstruction': True, 'sharedPayloadPreservation': True,
        'oldCallerSpecializesReachedProof': True, 'oldBackingRetirementAndAllocationCountersExact': True,
        'nonemptyRefusingRemapScope': True, 'allGrowthPathsVerified': False,
        'completeNativeGraphInvariantVerified': False, 'enclosingParentFrameRemainsExplicit': True,
        'advancingAllocationStreamCouplingVerified': False, 'recursiveInductionVerified': False,
        'composedProductionTheoremVerified': False}


def audit_statements(rows):
    required = {
        NATIVE + 'publication_payload': {'allocator', 'key', 'copied', 'before', 'after', 'live', 'owned', 'contents', 'preserved'},
        NATIVE + 'growing_success_reached': {'allocator', 'world', 'cells', 'custody', 'oldNonempty', 'full', 'selected',
            'size', 'duplicateCall', 'createCall', 'cloneCall', 'backing', 'response', 'unlocked'},
        GRAPH + 'Facts.insert_published': {'facts', 'world', 'rows', 'after', 'executed', 'candidate', 'data', 'frame'},
        GRAPH + 'Facts.growing_success': {'allocator', 'owner', 'world', 'rows', 'facts', 'custody', 'aligned', 'privateSource',
            'oldNonempty', 'full', 'selected', 'size', 'duplicateCall', 'createCall', 'cloneCall', 'backing', 'response', 'unlocked'},
        step.NS + 'CallFrame.growing_published': {'allocator', 'owner', 'rows', 'world', 'frame', 'ops', 'allocate',
            'growth', 'aligned', 'room', 'success'},
    }
    forbidden = {NATIVE + 'CallerInput', spare.arguments.OWNED + 'Caller.Origin',
        step.NS + 'GraphFrame', step.NS + 'Returns', spare.arguments.OWNED + 'Semantic.Contracts',
        'Compiler.Extraction.Recursive.Projects'}
    for name, expected in required.items():
        statement = next(row['statement'] for row in rows if row['theorem'] == name)
        if statement.get('encoding') != 'kernelExprDag-v1':
            raise ValueError('unsupported reached relocation statement encoding')
        nodes, index, binders = statement['nodes'], statement['root'], set()
        while nodes[index][0] in ('forall', 'let'):
            node = nodes[index]
            if node[0] == 'forall':
                binders.add(node[1])
                constants = step.constants_below(statement, node[3])
                if forbidden & constants or any(any(part.endswith('Tests') for part in value.split('.')) for value in constants):
                    raise ValueError('relocation assumes origin, completion or fixture: ' + name + ':' + node[1])
                if node[1] in {'finalFrame', 'nativeFrame', 'completed', 'afterFacts'}:
                    raise ValueError('relocation assumes its final native result: ' + name)
            index = node[4]
        if not expected <= binders:
            raise ValueError('relocation lost arbitrary inputs/observations: ' + name + ': ' + ', '.join(sorted(expected - binders)))
    return {'checkedGeneralInterfaces': sorted(required), 'rebasedOriginAndFinalNativeFrameNotAssumed': True,
        'actualGrowthObservationsExplicit': True, 'sharedGraphLiftRequiresDerivedPhysicalPostconditions': True,
        'payloadHelperRequiresActualPublicationFrame': True}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / (name + '.lean')).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)
    return (
        ('payload', source('InternerInsertionPublicationSuccess'), (
            ('shift-bytes', 'AssemblyClone.Physical.Reads after.memory payload.data)',
             'AssemblyClone.Physical.Reads after.memory { payload.data with offset := payload.data.offset + 1 })', 1),
            ('lose-live-key', 'Memory.SliceValid allocator before.heap (OwnedKeys.slice key old))',
             'Memory.SliceValid allocator before.heap (OwnedKeys.slice { key with arguments := [] } old))', 1),
        )),
        ('reached', source('InternerInsertionReachedGrowingSuccess'), (
            ('allow-spare', '(full : oldCapacity < Append.nextLength cells.length)',
             '(full : oldCapacity ≤ Append.nextLength cells.length)', 1),
            ('wrong-probe', '(true, probeEffects)', '(false, probeEffects)', 2),
            ('revive-backing', '(memory after).heap oldLifetime = none ∧',
             '(memory after).heap oldLifetime = world.memory.heap oldLifetime ∧', 1),
            ('rewind-history', '(memory after).memory.nextId = middle.memory.nextId + 1',
             '(memory after).memory.nextId = middle.memory.nextId', 1),
        )),
        ('graph', source('InternerNativeGrowingInsertion'), (
            ('wrong-new-data', 'exact itemReads .data', 'exact itemReads .instruction', 1),
            ('wrong-key-owner', '⟨normalized.address, Storage.idFor rows⟩', '⟨operands.address, Storage.idFor rows⟩', 1),
            ('revive-backing', 'actual.2.memory.heap lifetime = none',
             'actual.2.memory.heap lifetime = world.memory.heap lifetime', 1),
            ('wrong-counter', 'actual.2.memory.memory.nextId = middle.memory.nextId + 1',
             'actual.2.memory.memory.nextId = middle.memory.nextId', 1),
        )),
        ('observed', 'import Compiler.Extraction.InternerNativePublishedFrame\nimport Compiler.Extraction.InternerInsertionReachedGrowingSuccess\nimport Compiler.Extraction.InternerNativeGraphInsertion\n' + source('InternerRelocatedPublication') + '\n' +
            without_imports((ROOT / 'lean/Compiler/Extraction/InternerNativeGrowingInsertion.lean').read_text()) + '\n' +
            without_imports((ROOT / 'lean/Compiler/Extraction/InternerNativeGrowingCompletion.lean').read_text()), (
            ('unbound-remap', '∃ context returnAddress freeBacking, growth = some ⟨.noRemap context returnAddress, freeBacking⟩',
             '∃ context returnAddress freeBacking, growth = none', 1),
            ('allow-empty-backing', 'oldCapacity ≠ 0 ∧', 'True ∧', 1),
            ('wrong-selected-growth', 'capacity = Capacity.grow (Append.nextLength', 'capacity = oldCapacity + (Append.nextLength', 2),
            ('unbound-allocation', '(some base, allocationEffects)', '(none, allocationEffects)', 2),
            ('drop-fits', 'Compiler.ZigAir.Memory.RegionAllocation.Fits installed.memory ⟨capacity * 32, 8⟩ base)',
             'True)', 2),
            ('allow-spare-observation', 'oldCapacity < Append.nextLength (world.graph.representatives.getD []).length',
             'oldCapacity ≤ Append.nextLength (world.graph.representatives.getD []).length', 1),
            ('wrong-probe', 'normalized growth true world', 'normalized growth false world', 1),
        )),
        ('completion', source('InternerNativeGrowingCompletion'), (
            ('rewind-native-world', 'rows key normalized world actual', 'rows key normalized world (actual.1, world)', 1),
            ('wrong-result', 'rows key normalized world actual', 'rows key normalized world (.ok 0, actual.2)', 1),
            ('omit-child-extension', 'result, added,', 'result, [],', 1),
        )),
        ('fixtures', source('InternerNativeGrowingInsertionTests'), (
            ('wrong-id', '(actual safety empty).1 = .ok 5', '(actual safety empty).1 = .ok 4', 1),
            ('wrong-growth', '⟨by decide, 5, 13,', '⟨by decide, 5, 12,', 1),
        )),
    )


def controls(output, env, lean):
    records = []
    for group, text, changes in mutation_cases():
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous relocation mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'relocation-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'relocation-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
