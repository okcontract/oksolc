#!/usr/bin/env python3
"""Audit actual ISZERO(XOR) borrowed recursion, growth failure and parent return.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
import constructor_argument_checks as arguments
import recursive_child_checks as recursive
import recursive_nonempty_checks as nonempty
import view_input_checks as views

TESTS = arguments.ITEM + 'RecursiveBorrowedTests.'
CALL = recursive.TESTS + 'Call.'
CLAIMS = [CALL + name for name in ('spare_native', 'spare_publication')]
CLAIMS += [TESTS + name for name in (
    'prefix_observed', 'literal_facts', 'xor_literal', 'xor_established', 'xor_simplified',
    'xor_inner_contract', 'xor_route', 'rows_count', 'xor_contract', 'literals_observed',
    'calls_observed', 'parent_literal', 'parent_established', 'xor_query_at', 'xor_input_at',
    'xor_query', 'child_input', 'child_established', 'graph_reads', 'constant_nonpush',
    'constants', 'parent_iszero', 'xor_native_reads', 'preparation_observed', 'preparation_results', 'child_allocation',
    'child_insert', 'eq_miss', 'child_simplified', 'child_result', 'child_contract', 'child_source',
    'borrowed_failure', 'parent_continuation', 'held_after_child', 'full_contract', 'prior_words',
    'complete_route', 'literal_stack', 'complete_contract', 'composition')]


def bindings():
    return {'dispatcher': nonempty.bindings(), 'views': views.bindings(),
            'selectedCall': 'RuleList.simplify ISZERO(XOR(x,y)) -> borrowed EQ(x,y)',
            'initialPrefixIsSelectedInsertionContinuations': False, 'initialPrefixUsesSameRecursiveContext': True}


def audit(claims):
    native = recursive.NATIVE
    graph = native + 'CallerGrowingChainTests.GraphFacts.'
    required = {
        CALL + 'spare_native': {native + 'CallerInput.spare_success', native + 'CallerInput.checked_execution'},
        CALL + 'spare_publication': {CALL + 'spare_native', CALL + 'establish',
            native + 'CallerInput.finish_native', graph + 'cleanup'},
        TESTS + 'xor_inner_contract': {CALL + 'spare_publication', CALL + 'route', arguments.ITEM + 'BinaryPreludeTests.simplified'},
        TESTS + 'xor_contract': {arguments.ITEM + 'BinaryPreludeTests.inner_contract',
            arguments.ITEM + 'BinaryPreludeTests.route', graph + 'cleanup'},
        TESTS + 'xor_input_at': {views.NS + 'queried_input', TESTS + 'xor_query_at'},
        TESTS + 'child_established': {TESTS + 'child_input', TESTS + 'parent_established', CALL + 'establish'},
        TESTS + 'constant_nonpush': {recursive.CONSTANT + 'nonpush'},
        TESTS + 'child_allocation': {native + 'CallerInput.growing_allocation_oom', TESTS + 'child_established'},
        TESTS + 'child_insert': {native + 'CallerInput.checked_execution', native + 'projected_unchanged'},
        TESTS + 'child_simplified': {TESTS + 'constants', TESTS + 'eq_miss'},
        TESTS + 'child_result': {CALL + 'route', native + 'CallerInput.finish_native',
            TESTS + 'child_insert', TESTS + 'child_simplified', views.NS + 'operation'},
        TESTS + 'child_contract': {TESTS + 'child_allocation', TESTS + 'child_result',
            CALL + 'returned_frame', CALL + 'returned_valid', TESTS + 'child_input'},
        TESTS + 'child_source': {views.NS + 'borrowed_forwards', TESTS + 'child_input'},
        TESTS + 'borrowed_failure': {'Compiler.Extraction.Dispatch.simplifyWithInputs', 'Compiler.Extraction.Dispatch.unaryStageWithInputs'},
        TESTS + 'parent_continuation': {TESTS + 'borrowed_failure', TESTS + 'xor_query',
            TESTS + 'parent_iszero', TESTS + 'constants', TESTS + 'child_source'},
        TESTS + 'full_contract': {TESTS + 'child_contract', TESTS + 'parent_continuation',
            TESTS + 'held_after_child', arguments.OWNED + 'finish_taken', CALL + 'route'},
        TESTS + 'literal_stack': {TESTS + 'parent_literal', arguments.ARGUMENTS + 'Prepared.storage'},
        TESTS + 'complete_contract': {TESTS + 'full_contract', TESTS + 'xor_contract',
            TESTS + 'complete_route', TESTS + 'xor_input_at', arguments.ARGUMENTS + 'Prepared.retire'},
        TESTS + 'composition': {TESTS + 'complete_contract', TESTS + 'xor_native_reads',
            TESTS + 'constants', TESTS + 'parent_iszero', TESTS + 'xor_query'},
    }
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError('borrowed recursion lost dependencies: ' + name + ': ' + ', '.join(sorted(missing)))
    return {'checkedDependencies': sorted(required), 'sourceBinding': bindings(),
            'fullXorPublicationBeforeParent': True, 'actualBorrowedDispatcherBranch': True,
            'nativeQueryDerivesChildContentsAndKeySeparation': True,
            'nonemptyChildGrowthOOMAndParentReturn': True, 'parentNormalizedArgumentsFreedOnce': True,
            'graphOperandSurvivesBothReturns': True, 'outerParentLiteralRetired': True,
            'initialPrefixIsSelectedInsertionContinuations': False, 'initialPrefixUsesSameRecursiveContext': True,
            'completeConstructorDependencyClosureVerified': False, 'successfulRecursiveGrowthVerified': False,
            'nativeMapAndAllocatorBindingVerified': False, 'completePublicationRollbackVerified': False,
            'recursiveInductionVerified': False, 'composedProductionTheoremVerified': False}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / name).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)

    dispatch = source('InternerRecursiveBorrowedDispatchTests.lean')
    # The complete execution remains in the acceptance roots. These controls
    # isolate the source-selected branch before the concrete parent continuation.
    dispatch = dispatch.split('theorem parent_continuation')[0] + '\nend ' + TESTS[:-1] + '\n'
    composed = source('InternerRecursiveBorrowedTests.lean').split('/-- One composed execution')[0] + '\nend ' + TESTS[:-1] + '\n'
    return (
        ('dispatch', dispatch, (
            ('wrong-borrowed-opcode', '(called : constructors.borrowedOperation xorOperands.address 20 xorOperands.items debug before',
             '(called : constructors.borrowedOperation xorOperands.address 21 xorOperands.items debug before', 1),
            ('wrong-borrowed-address', '(called : constructors.borrowedOperation xorOperands.address 20 xorOperands.items debug before',
             '(called : constructors.borrowedOperation (xorOperands.address + 1) 20 xorOperands.items debug before', 1),
        )),
        ('allocation', source('InternerRecursiveBorrowedAllocationTests.lean'), (
            ('alias-argument-owners', 'memory.nextId + 3, [0, 1]', 'memory.nextId + 2, [0, 1]', 1),
        )),
        ('return', source('InternerRecursiveBorrowedReturnTests.lean'), (
            ('erase-live-parent', '(child safety).returnedWorld (failedWorld safety after)',
             '(child safety).returnedWorld { (failedWorld safety after) with memory := { (failedWorld safety after).memory with memory := Compiler.ZigAir.Memory.cleanup 0 (failedWorld safety after).memory.memory } }', 1),
            ('wrong-borrowed-contents', 'Good childSource [0, 1] (childReturned safety after)',
             'Good childSource [1, 0] (childReturned safety after)', 1),
        )),
        ('composed', composed, (
            ('wrong-result', '(complete safety).1 = .error (.language .outOfMemory)',
             '(complete safety).1 = .error (.language .capacity)', 1),
            ('double-parent-free', '.memory.effects.allocator + 101', '.memory.effects.allocator + 202', 1),
            ('retain-parent-literal', '(complete safety).2.memory.memory.heap.lookup rootSource.allocation = none ∧',
             '(complete safety).2.memory.memory.heap.lookup rootSource.allocation ≠ none ∧', 1),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    records = []
    for group, text, changes in mutation_cases():
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous borrowed recursive mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'recursive-borrowed-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'recursive-borrowed-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
