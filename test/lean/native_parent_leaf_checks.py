#!/usr/bin/env python3
"""Audit shared live-parent framing for unchanged-graph step leaves.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
from assembly_item_creation_checks import checked_controls
import native_step_checks as step
import native_local_checks as local
import native_take_checks as take

NS = step.NS
CORE = [NS + name for name in ('GraphFrame.retained_parent', 'Returns.parent')]
LEAVES = [NS + name for name in ('step_return_verified', 'step_initialized_verified', 'step_cached_verified',
    'step_classification_failed_verified', 'step_entry_failed_verified', 'step_take_failed_verified')]
CLAIMS = CORE + LEAVES + [local.TESTS + 'local_parent', local.TESTS + 'parent_publication']
MODULE = take.MODULE


def audit(claims):
    required = {
        CORE[0]: {NS + 'CallFrame.frame', step.recursion.FACTS + 'valid', NS + 'Retains'},
        CORE[1]: {CORE[0], NS + 'Returns'},
        LEAVES[0]: {NS + 'Retains', NS + 'step'},
        LEAVES[1]: {LEAVES[0], step.arguments.ITEM + 'invoke_initialized_native'},
        LEAVES[2]: {LEAVES[1], step.arguments.ITEM + 'cached_word'},
        LEAVES[3]: {LEAVES[1]},
        LEAVES[4]: {LEAVES[0], step.arguments.ITEM + 'invoke_entry_failed_native'},
        LEAVES[5]: {LEAVES[0], step.arguments.ITEM + 'invoke_take_failed_native'},
        local.TESTS + 'local_parent': {CORE[0], NS + 'CallFrame.caller', local.TESTS + 'local_native'},
        local.TESTS + 'parent_publication': {local.TESTS + 'local_parent'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('parent leaf lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
        if name in CORE + LEAVES and any(any(part.endswith('Tests') for part in dep.split('.')) for dep in claims[name]):
            raise ValueError('general parent leaf depends on fixtures: ' + name)
    return {'checkedDependencies': sorted(required), 'unchangedGraphLeavesRetainKeysAndAllocations': True,
            'parentFrameDerivedFromInitialCallAndReachedRetention': True,
            'existingNamedLocalPublicationConsumesConcreteParent': True,
            'ordinaryGuardRetained': True, 'allEntryPrefixesVerified': False,
            'arbitraryOuterLawsAndInsertionParentLawsRemainOpen': True,
            'allEntryInductionVerified': False, 'composedProductionTheoremVerified': False}


def audit_statements(rows):
    expected = {
        CORE[0]: {'before', 'after', 'reached', 'graph', 'initial', 'outerKept'},
        CORE[1]: {'before', 'actual', 'result', 'returned', 'initial', 'outerKept'},
    }
    native = {NS + name for name in ('CallFrame', 'InputFrame', 'GraphFrame', 'Retains')}
    native.add(step.recursion.FACTS.rstrip('.'))
    for name in CORE + LEAVES:
        statement = next(row['statement'] for row in rows if row['theorem'] == name)
        if statement.get('encoding') != 'kernelExprDag-v1':
            raise ValueError('unsupported parent leaf statement encoding')
        nodes, index, binders = statement['nodes'], statement['root'], set()
        while nodes[index][0] in ('forall', 'let'):
            node = nodes[index]
            if node[0] == 'forall':
                binders.add(node[1])
                constants = step.constants_below(statement, node[3])
                if node[1] == 'outerKept' and constants & native:
                    raise ValueError('outer law hides a native parent frame')
                if name in LEAVES[1:] and constants & {NS + 'Retains', NS + 'Returns', NS + 'GraphFrame', NS + 'CallFrame'}:
                    raise ValueError('early-return branch assumes its native retention or completion')
            index = node[4]
        if not expected.get(name, set()) <= binders:
            raise ValueError('parent leaf lost original worlds or outer law: ' + name)
        if name in LEAVES and not {NS + 'Retains', NS + 'Returns', NS + 'GraphFrame'} <= step.constants_below(statement, index):
            raise ValueError('early-return leaf no longer exposes shared retained-frame conclusion')
    return {'checkedGeneralInterfaces': CORE + LEAVES, 'branchRetentionDerivedNotAssumed': True,
            'sharedConclusionAcceptedByParentAdapter': True, 'outerLawRemainsSeparate': True}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / (name + '.lean')).read_text()
        return '\n'.join(line for line in raw.splitlines() if line.startswith('import ')) + '\n' + (
            'set_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw))
    return (
        ('frame', source('InternerNativeLeafFrame'), (
            ('unrelated-keys', 'after.memory.effects.keys = before.memory.effects.keys',
             'after.memory.effects.keys = after.memory.effects.keys', 1),
            ('omit-native-retention', '→ after.memory.memory.heap.lookup id = some cell',
             '→ before.memory.memory.heap.lookup id = some cell', 1),
            ('omit-registry-retention', '→ after.memory.heap id = some block',
             '→ before.memory.heap id = some block', 1),
            ('unrelated-graph', '(graph : after.graph = before.graph)', '(graph : after.graph = after.graph)', 1),
            ('rewind-outer', '(outerKept : outer after)', '(outerKept : outer before)', 1),
            ('rewind-frame-world', 'normalized address native outer) after := by',
             'normalized address native outer) before := by', 1),
            ('rewind-returned-outer', 'ordinary actual.1 = true → outer actual.2.world',
             'ordinary actual.1 = true → outer before', 1),
            ('outer-only-on-rejection', 'ordinary actual.1 = true → outer actual.2.world',
             'ordinary actual.1 = false → outer actual.2.world', 1),
            ('return-wrong-result', ')) actual result before.graph := by', ')) actual (.error .outsideOwnedContinuation) before.graph := by', 1),
        )),
        ('return', source('InternerNativeReturn'), (
            ('omit-derived-keys', '(_keys : actual.2.world.memory.effects.keys = before.memory.effects.keys)',
             '(_keys : before.memory.effects.keys = before.memory.effects.keys)', 1),
            ('rewind-result-world', '(outcome, actual.2.world)) := by', '(outcome, before)) := by', 1),
        )),
        ('consumer', source('InternerNativeLocalReturnTests'), (
            ('rewind-parent', '(fun _ => True) (localReturned safety).2 := by',
             '(fun _ => True) (parent safety).before := by', 1),
            ('wrong-parent-values', 'rootSource [0, 4] (parent safety).normalized',
             'rootSource [4, 0] (parent safety).normalized', 1),
        )),
    )


def controls(output, env, lean):
    records = []
    for group, source, changes in mutation_cases():
        records += checked_controls(output, [mutation_check(output,
            'parent-leaf-' + group + '-unchanged', source, True, env, lean)])
        for name, before, after, count in changes:
            if source.count(before) != count:
                raise ValueError('ambiguous parent leaf control: ' + name)
            records += checked_controls(output, [mutation_check(output,
                'parent-leaf-' + group + '-' + name, source.replace(before, after), False, env, lean)])
    return records
