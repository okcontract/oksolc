#!/usr/bin/env python3
"""Audit actual child entry and live-parent preparation.
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
ITEM = OWNED + 'ConstructorItem.'
CALLER = OWNED + 'Caller.'
NATIVE = OWNED + 'Insertion.Native.'
CORE = [NS + 'CallFrame.' + name for name in ('frame', 'prepared', 'arguments', 'caller_parent', 'enter_child')]
CLAIMS = CORE + [NS + 'CallFrame.caller', growth.TESTS + 'child_entry', growth.TESTS + 'child_contract',
                 NS + 'invoke_step', NS + 'step_taken_verified']
MODULE = 'Compiler.Extraction.InternerNativeParentEntryProofTests'


def audit(claims):
    required = {
        CORE[0]: {step.recursion.FACTS + 'frame', ITEM + 'good_frame',
                  'Compiler.Extraction.AssemblyClone.NativeFields.Represents.frame',
                  CALLER + 'Custody.apart', CALLER + 'GraphCustody.operands', step.arguments.OWNED + 'ArraySource.frame'},
        CORE[1]: {CORE[0], ITEM + 'Prepared.memory', ITEM + 'Prepared.graph'},
        CORE[2]: {CORE[0], ITEM + 'Arguments.Prepared.frame', ITEM + 'Arguments.Prepared.good'},
        CORE[3]: {CORE[0], NS + 'CallFrame.caller', CALLER + 'Origin.memory', CALLER + 'Origin.registry',
                  CALLER + 'Origin.graph', NATIVE + 'CallerInput.keys'},
        CORE[4]: {CORE[1], CORE[3], ITEM + 'prepare_success', ITEM + 'caller_input'},
        NS + 'CallFrame.caller': {NS + 'InputFrame.caller', NATIVE + 'CallerInput.item'},
        growth.TESTS + 'child_entry': {CORE[2], CORE[4], growth.TESTS + 'parent_input',
                                      ITEM + 'Arguments.Prepared.key_apart'},
        growth.TESTS + 'child_contract': {growth.TESTS + 'child_entry', NS + 'CallFrame.locals',
                                         NS + 'CallFrame.cleanup', growth.TESTS + 'child_native'},
        NS + 'invoke_step': {NS + 'CallFrame.caller', NS + 'dispatch_projects_framed_at'},
        NS + 'step_taken_verified': {NS + 'invoke_step'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('parent entry lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
        if name in CORE and any(any(part.endswith('Tests') for part in dep.split('.')) for dep in claims[name]):
            raise ValueError('general parent entry depends on fixtures: ' + name)
    return {'checkedDependencies': sorted(required), 'parentEntryDerivedFromActualPreparationAndTake': True,
            'literalItemAndNormalizerReuseOneAllocationFrame': True, 'originalChildOriginRetained': True,
            'existingGrowthContinuationConsumesSharedEntry': True, 'allEntryPrefixesVerified': False,
            'arbitraryOuterLawsAndInsertionParentLawsRemainOpen': True,
            'allEntryInductionVerified': False, 'composedProductionTheoremVerified': False}


def audit_statements(rows):
    expected = {
        CORE[0]: {'before', 'after', 'initial', 'valid', 'graph', 'keys', 'memory', 'registry', 'outer'},
        CORE[1]: {'before', 'after', 'initial', 'prepared', 'outer'},
        CORE[2]: {'before', 'after', 'initial', 'prepared', 'outer'},
        CORE[3]: {'constructed', 'taken', 'entry', 'initial', 'outerKept', 'array'},
        CORE[4]: {'budget', 'before', 'constructed', 'debug', 'values', 'prepared', 'taken', 'initial',
                  'good', 'privateSource', 'array', 'domain', 'typed', 'admitted', 'made', 'allocated',
                  'initialized', 'transferred', 'keyed', 'constructedOuter', 'outerKept'},
    }
    forbidden = {NS + 'Returns', 'Compiler.Extraction.Interner.Represented'}
    native = {NS + 'CallFrame', NS + 'InputFrame', NS + 'GraphFrame', step.recursion.FACTS.rstrip('.')}
    for name, wanted in expected.items():
        statement = next(row['statement'] for row in rows if row['theorem'] == name)
        if statement.get('encoding') != 'kernelExprDag-v1':
            raise ValueError('unsupported parent entry statement encoding')
        nodes, index, binders = statement['nodes'], statement['root'], set()
        while nodes[index][0] in ('forall', 'let'):
            node = nodes[index]
            if node[0] == 'forall':
                binders.add(node[1])
                constants = step.constants_below(statement, node[3])
                if constants & forbidden:
                    raise ValueError('parent entry assumes completed execution or semantic correspondence')
                if node[1] in ('outer', 'constructedOuter', 'outerKept') and constants & native:
                    raise ValueError('outer predicate hides a native parent frame')
                if name == CORE[4] and constants & {NATIVE + 'CallerInput', CALLER + 'Origin', ITEM + 'Prepared'}:
                    raise ValueError('actual child entry assumes its preparation or normalization postcondition')
            index = node[4]
        if not wanted <= binders:
            raise ValueError('parent entry lost original worlds or actual prefix observations: ' + name)
    return {'checkedGeneralInterfaces': sorted(expected), 'arbitraryBudgetDebugAllocatorAndSources': True,
            'actualChildEntryDoesNotAssumePreparedOrOrigin': True, 'outerLawRemainsSeparate': True}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / (name + '.lean')).read_text()
        return '\n'.join(line for line in raw.splitlines() if line.startswith('import ')) + '\n' + (
            'set_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw))
    return (
        ('prefix', source('InternerNativeParentEntry'), (
            ('omit-native-retention', '      after.memory.memory.heap.lookup id = some cell)',
             '      before.memory.memory.heap.lookup id = some cell)', 1),
            ('omit-registry-retention', '→ after.memory.heap id = some block)',
             '→ before.memory.heap id = some block)', 1),
            ('allow-unrelated-keys', '(keys : after.memory.effects.keys = before.memory.effects.keys)',
             '(keys : after.memory.effects.keys = after.memory.effects.keys)', 1),
            ('rewind-source', 'good_frame before after source values', 'good_frame before before source values', 1),
            ('reverse-source-values', 'source values initial.1.2.1 valid memory',
             'source values.reverse initial.1.2.1 valid memory', 1),
            ('rewind-item', 'initial.2.1.frame ((memory _ item found).trans found.symm)',
             'initial.2.1', 1),
            ('reverse-item-worlds', 'initial.frame prepared.valid prepared.graph',
             'initial.frame prepared.valid prepared.graph.symm', 1),
            ('omit-literal-frame', '    prepared.frame (fun _ _ found => prepared.heap ▸ found) outer',
             '    (fun _ _ found => found) (fun _ _ found => prepared.heap ▸ found) outer', 1),
            ('rewind-origin-validity', 'initial.frame entry.origin.held.1.1',
             'initial.frame initial.1.2.1.1', 1),
            ('rewind-outer-world', '(outerKept : outer taken.world)', '(outerKept : outer constructed)', 2),
            ('rebase-parent-entry', 'parentAddress parentNative outer before)',
             'parentAddress parentNative outer taken.world)', 1),
            ('substitute-normalized-values', 'address memory pointer values prepared taken key good domain typed',
             'address memory pointer request.arguments prepared taken key good domain typed', 1),
            ('rebase-item-preparation', 'prepare request.item debug before = (.ok address, constructed)',
             'prepare request.item debug constructed = (.ok address, constructed)', 1),
            ('rewind-constructed-outer', '(constructedOuter : outer constructed)',
             '(constructedOuter : outer before)', 1),
        )),
        ('consumer', source('InternerRecursiveGrowthReturnTests'), (
            ('replace-child-by-parent', 'exact ⟨parentConstructed, ready⟩',
             'exact ⟨parentConstructed, ready.parent⟩', 1),
            ('omit-literal-entry', 'have before := initial.arguments literal trivial',
             'have before := initial', 1),
        )),
    )


def controls(output, env, lean):
    records = []
    for group, source, changes in mutation_cases():
        records += checked_controls(output, [mutation_check(output,
            'parent-entry-' + group + '-unchanged', source, True, env, lean)])
        for name, before, after, count in changes:
            if source.count(before) != count:
                raise ValueError('ambiguous parent entry control: ' + name)
            records += checked_controls(output, [mutation_check(output,
                'parent-entry-' + group + '-' + name, source.replace(before, after), False, env, lean)])
    return records
