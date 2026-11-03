#!/usr/bin/env python3
"""Audit shared insertion and rollback framing for an enclosing recursive call.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
from assembly_item_creation_checks import checked_controls
import native_step_checks as step
import recursive_growth_checks as growth

NS = step.NS
OWNED = step.arguments.OWNED
CALLER = OWNED + 'Caller.'
NATIVE = OWNED + 'Insertion.Native.'
CORE = [NS + name for name in ('PublishedFrame.parent', 'PublishedReturn.graph',
    'CallFrame.published_frame', 'CallFrame.published_parent')]
BRANCHES = [NS + 'CallFrame.' + name for name in ('first_published', 'spare_published', 'growing_published')]
CLAIMS = CORE + BRANCHES + [NS + 'CallFrame.published', growth.TESTS + 'child_published', growth.TESTS + 'child_contract', growth.TESTS + 'child_refused', growth.TESTS + 'child_rollback_parent']
MODULE = 'Compiler.Extraction.InternerNativeParentInsertionProofTests'


def audit(claims):
    required = {
        CORE[0]: {CALLER + 'Origin.custody_after_publication', CALLER + 'Origin.source_private_after_publication',
            'Compiler.Extraction.AssemblyClone.NativeFields.Represents.apart_words', NS + 'PublishedFrame.fresh', OWNED + 'ArraySource.storage',
            'Compiler.Extraction.AssemblyClone.NativeFields.Represents.storage'},
        CORE[1]: {NS + 'PublishedFrame.native'},
        CORE[2]: set(BRANCHES),
        CORE[3]: {CORE[0], CORE[1], CORE[2]},
        NS + 'CallFrame.published': {CORE[1], CORE[2]},
        growth.TESTS + 'child_published': {OWNED + 'ConstructorItem.RecursiveNonemptyTests.preparation_results', growth.TESTS + 'backing_fits'},
        growth.TESTS + 'child_refused': {growth.TESTS + 'child_published'},
        growth.TESTS + 'child_rollback_parent': {NS + 'CallFrame.publication_rollback_frame', NS + 'Enclosing.rolled_back',
            growth.TESTS + 'child_entry', growth.TESTS + 'child_refused'},
        growth.TESTS + 'child_contract': {CORE[2], NS + 'Enclosing.published', OWNED + 'ArraySource.frame',
            OWNED + 'ConstructorItem.Arguments.Prepared.arraySource', growth.TESTS + 'child_published', growth.TESTS + 'child_entry',
            NS + 'CallFrame.locals', NS + 'CallFrame.cleanup'},
    }
    for name, operation in zip(BRANCHES, ('first_success', 'spare_success', 'growing_success')):
        required[name] = {step.recursion.FACTS + operation, NATIVE + 'duplicate_taken'}
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('parent insertion lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
        if not name.startswith(growth.TESTS) and any(any(part.endswith('Tests') for part in dep.split('.')) for dep in claims[name]):
            raise ValueError('general parent insertion depends on fixtures: ' + name)
    return {'checkedDependencies': sorted(required), 'threeStorageBranchesShareParentCompletion': True,
        'originalOriginAndReachedCustodyRetained': True, 'existingGrowthConsumesSharedParent': True,
        'sourceAndItemStorageSeparationDerived': True, 'outerLawExplicit': True, 'firstSpareNoRemapRollbackParentDerived': True,
        'allEntryInductionVerified': False, 'composedProductionTheoremVerified': False}


def audit_statements(rows):
    expected = {
        CORE[0]: {'original', 'before', 'after', 'origin', 'initial', 'reached', 'facts', 'post',
            'outerKept'},
        CORE[1]: {'before', 'actual', 'completed'},
        CORE[2]: {'world', 'frame', 'ops', 'allocate', 'growth', 'success'},
        CORE[3]: {'original', 'world', 'origin', 'initial', 'frame', 'ops', 'allocate', 'growth',
            'success'},
    }
    native = {NS + name for name in ('Returns', 'CallFrame', 'InputFrame', 'GraphFrame', 'PublishedReturn', 'PublishedFrame')}
    for name in CORE + BRANCHES:
        statement = next(row['statement'] for row in rows if row['theorem'] == name)
        if statement.get('encoding') != 'kernelExprDag-v1':
            raise ValueError('unsupported parent insertion statement encoding')
        nodes, index, binders = statement['nodes'], statement['root'], set()
        while nodes[index][0] in ('forall', 'let'):
            node = nodes[index]
            if node[0] == 'forall':
                binders.add(node[1])
                constants = step.constants_below(statement, node[3])
                if node[1] in ('outerKept',) and constants & native:
                    raise ValueError('input geometry or outer law hides a final native frame')
                if name in BRANCHES + [CORE[2], CORE[3]] and constants & {NS + 'PublishedReturn', NS + 'PublishedFrame', NS + 'Returns', NS + 'GraphFrame'}:
                    raise ValueError('source-selected completion assumes its result')
            index = node[4]
        if not expected.get(name, set()) <= binders:
            raise ValueError('parent insertion lost worlds or source observations: ' + name)
        if name in BRANCHES + [CORE[2]] and NS + 'PublishedReturn' not in step.constants_below(statement, index):
            raise ValueError('storage branch discards the shared retained completion')
    return {'checkedGeneralInterfaces': CORE + BRANCHES, 'sourceSelectedCompletionDerivedNotAssumed': True,
        'storageGeometryDerivedFromCallFrame': True, 'originalAndReachedWorldsSeparate': True}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / (name + '.lean')).read_text()
        return '\n'.join(line for line in raw.splitlines() if line.startswith('import ')) + '\n' + (
            'set_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw))
    return (
        ('frame', source('InternerNativePublishedFrame'), (
            ('unrelated-keys', 'OwnedKeys.store before.memory.effects.keys key', 'OwnedKeys.store after.memory.effects.keys key', 1),
            ('lose-fresh-operands', 'row.argumentsAddress = before.memory.memory.nextId', 'row.argumentsAddress = owned.address', 1),
            ('omit-native-retention', '→\n    after.memory.memory.heap.lookup id = some cell', '→\n    before.memory.memory.heap.lookup id = some cell', 1),
            ('omit-registry-retention', '→\n    after.memory.heap id = some block', '→\n    before.memory.heap id = some block', 1),
            ('exclude-empty-sentinel', '(oldCapacity ≠ 0 → id ≠ oldData.allocation)', '(id ≠ oldData.allocation)', 2),
            ('rebase-child-origin', 'childValues original taken owned lookup)', 'childValues before taken owned lookup)', 1),
            ('rewind-reached-parent', 'normalized address native outer before)', 'normalized address native outer original)', 1),
            ('rebase-source-geometry', 'reached.arraySource.storage facts', 'initial.arraySource.storage facts', 1),
            ('rebase-item-geometry', 'reached.2.1.storage facts', 'initial.2.1.storage facts', 1),
            ('rewind-outer', '(outerKept : outer after)', '(outerKept : outer before)', 1),
        )),
        ('completion', source('InternerNativePublishedCompletion'), (
            ('rewind-outer', 'outer actual.2 →', 'outer world →', 1),
            ('rebase-initial-parent', 'parentAddress parentNative outer original)', 'parentAddress parentNative outer world)', 1),
            ('wrong-parent-source', 'parentRows parentSource parentValues parentNormalized parentAddress parentNative outer) actual.2',
             'parentRows source parentValues parentNormalized parentAddress parentNative outer) actual.2', 1),
        )),
        ('consumer', source('InternerRecursiveGrowthReturnTests'), (
            ('rewind-rollback-parent', 'native (fun _ => True) actual.2 ∧',
             'native (fun _ => True) (child safety).taken.2.world ∧', 1),
            ('retain-rollback-child', 'Consumed (child safety).normalized actual.2.memory',
             'Consumed (child safety).normalized (child safety).taken.2.world.memory', 1),
            ('wrong-rollback-outcome', 'actual.1 = .error (.language .outOfMemory)', 'actual.1 = .ok 5', 1),
            ('rewind-parent-result', 'exact kept', 'exact (child_entry safety).1', 1),
            ('wrong-parent-custody',
             'Caller.GraphCustody 7 (parent safety).normalized (appendedRows safety) (appendedWorld safety after).memory',
             'Caller.GraphCustody 7 (child safety).normalized (appendedRows safety) (appendedWorld safety after).memory', 1),
        )),
    )


def controls(output, env, lean):
    records = []
    for group, source, changes in mutation_cases():
        records += checked_controls(output, [mutation_check(output,
            'parent-insertion-' + group + '-unchanged', source, True, env, lean)])
        for name, before, after, count in changes:
            if source.count(before) != count:
                raise ValueError('ambiguous parent insertion control: ' + name)
            records += checked_controls(output, [mutation_check(output,
                'parent-insertion-' + group + '-' + name, source.replace(before, after), False, env, lean)])
    return records
