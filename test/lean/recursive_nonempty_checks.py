#!/usr/bin/env python3
"""Audit a nonempty native child through growth OOM and both returns.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
import constructor_argument_checks as arguments
import recursive_child_checks as recursive
import extract_compiler
import extract_dispatch

TESTS = arguments.ITEM + 'RecursiveNonemptyTests.'
CLAIMS = [recursive.CONSTANT + 'push']
CLAIMS += [TESTS + name for name in (
    'zero_observed', 'zero_established', 'zero_contract', 'caller_source', 'rows_count', 'literals_observed',
    'calls_observed', 'literal_facts', 'parent_literal', 'parent_established', 'child_literal',
    'child_established', 'graph_reads', 'first_row', 'first_constant', 'first_operation', 'zero_constant', 'parent_zero',
    'preparation_observed', 'preparation_results', 'child_allocation', 'child_insert', 'iszero_miss',
    'child_simplified', 'child_result', 'child_literal_stack', 'child_contract', 'iszero_failure',
    'parent_continuation', 'held_after_child', 'full_contract', 'prior_words', 'complete_route',
    'literal_stack', 'complete_contract')]


def bindings():
    source = extract_compiler.SOURCE.read_bytes()
    if (extract_compiler.extract(source) != extract_compiler.OUTPUT.read_bytes() or
            extract_compiler.extract_construction(source) != extract_compiler.CONSTRUCTION.read_bytes()):
        raise ValueError('algebraic selector/construction profile is stale')
    if extract_dispatch.extract(extract_dispatch.nested.SOURCE.read_bytes(),
            extract_dispatch.nested.OPCODES.read_bytes(), extract_dispatch.nested.STORAGE.read_bytes(),
            extract_dispatch.VERSIONS.read_bytes()) != extract_dispatch.OUTPUT.read_bytes():
        raise ValueError('dispatcher profile is stale')
    return {'arguments': arguments.bindings(), 'constantReads': recursive.bindings(),
            'selectedLiteral': 'Algebraic.apply iszero_left: ISZERO(&.{left})',
            'scope': 'EQ(non-Push row, published Push-zero row), then ISZERO(non-Push row)'}


def audit(claims):
    native = recursive.NATIVE
    required = {
        recursive.CONSTANT + 'push': {'Compiler.Extraction.RepresentativeArray.representative_from_array',
            'Compiler.Extraction.AssemblyItem.Fields.readTyped_from_root'},
        TESTS + 'zero_contract': {native + 'CallerInput.spare_success', recursive.TESTS + 'Call.route',
            native + 'CallerInput.finish_native', native + 'CallerGrowingChainTests.GraphFacts.cleanup'},
        TESTS + 'caller_source': {TESTS + 'zero_contract', arguments.ITEM + 'ReachablePrefixTests.initialized_prefix',
            'Compiler.Extraction.Memory.Arguments.Normalization.represented_frame', arguments.OWNED + 'Good.backed',
            native + 'CallerInputTests.source_inputs'},
        TESTS + 'literal_facts': {arguments.ARGUMENTS + 'prepare_success', native + 'CallerGrowingChainTests.GraphFacts.frame'},
        TESTS + 'zero_constant': {arguments.OWNED + 'NativeGraph.Facts.constants',
            native + 'CallerGrowingChainTests.GraphFacts.native'},
        TESTS + 'parent_zero': {TESTS + 'zero_constant', arguments.OWNED + 'NativeGraph.Facts.constants',
            native + 'CallerGrowingChainTests.GraphFacts.native', TESTS + 'parent_established'},
        TESTS + 'child_allocation': {native + 'CallerInput.growing_allocation_oom', TESTS + 'child_established'},
        TESTS + 'child_insert': {native + 'CallerInput.checked_execution', native + 'projected_unchanged', TESTS + 'graph_reads'},
        TESTS + 'child_simplified': {TESTS + 'first_constant', TESTS + 'first_operation', TESTS + 'iszero_miss'},
        TESTS + 'child_result': {recursive.TESTS + 'Call.route', native + 'CallerInput.finish_native',
            TESTS + 'child_insert', TESTS + 'child_simplified', arguments.ARGUMENTS + 'operation_prepared'},
        TESTS + 'child_literal_stack': {TESTS + 'child_literal', arguments.ARGUMENTS + 'Prepared.storage'},
        TESTS + 'literal_stack': {TESTS + 'parent_literal', arguments.ARGUMENTS + 'Prepared.storage'},
        TESTS + 'child_contract': {TESTS + 'child_allocation', TESTS + 'child_result',
            recursive.TESTS + 'Call.returned_frame', TESTS + 'child_literal_stack', arguments.ARGUMENTS + 'Prepared.retire'},
        TESTS + 'iszero_failure': {'Compiler.Extraction.Dispatch.simplifyWithInputs', 'Compiler.Extraction.Dispatch.binaryStageWithInputs'},
        TESTS + 'parent_continuation': {TESTS + 'iszero_failure', TESTS + 'parent_zero', TESTS + 'child_source'},
        TESTS + 'full_contract': {TESTS + 'child_contract', TESTS + 'parent_continuation', TESTS + 'held_after_child',
            arguments.OWNED + 'finish_taken', recursive.TESTS + 'Call.route'},
        TESTS + 'complete_contract': {TESTS + 'full_contract', TESTS + 'complete_route', TESTS + 'zero_contract',
            TESTS + 'literal_stack', arguments.ARGUMENTS + 'Prepared.retire'},
    }
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError('nonempty recursive connection lost dependencies: ' + name + ': ' + ', '.join(sorted(missing)))
    return {'checkedDependencies': sorted(required), 'sourceBinding': bindings(),
            'fullConstantPublicationBeforeParent': True, 'nativePushDataReadDerived': True,
            'actualNonemptyChildGrowthOOMAndReturn': True,
            'childCloneAndBothNonemptyArgumentOwnersReleased': True,
            'childAndParentLiteralsRetired': True, 'liveParentBorrowAndCleanupDerived': True,
            'initialPrefixIsSelectedInsertionContinuations': False,
            'completeConstructorDependencyClosureVerified': False, 'successfulRecursiveGrowthVerified': False,
            'nativeMapAndAllocatorBindingVerified': False, 'completePublicationRollbackVerified': False,
            'recursiveInductionVerified': False, 'composedProductionTheoremVerified': False}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / name).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)

    dispatch = source('InternerRecursiveNonemptyDispatchTests.lean')
    ordered = dispatch.split('theorem parent_continuation')[0] + '\nend ' + TESTS[:-1] + '\n'
    return (
        ('push', source('RepresentativeConstant.lean'), (
            ('wrong-loaded-word', 'some (BitVec.ofInt 256 word)', 'some (BitVec.ofInt 256 word + 1)', 1),
        )),
        ('ordered', ordered, (
            ('wrong-child-operand', '(called : zigApply .iszero_left (Dispatch.algebraicBuilder constructors) 0 4 debug before =\n      (result, after))',
             '(called : zigApply .iszero_left (Dispatch.algebraicBuilder constructors) 4 0 debug before =\n      (result, after))', 1),
        )),
        ('allocation', source('InternerRecursiveNonemptyAllocationTests.lean'), (
            ('alias-argument-owners', 'memory.nextId + 3, [0]', 'memory.nextId + 2, [0]', 1),
        )),
        ('return', source('InternerRecursiveNonemptyReturnTests.lean'), (
            ('retain-child-literal', 'let memory := Compiler.ZigAir.Memory.cleanup (parent safety).taken.2.world.memory.memory.nextId world.memory.memory',
             'let memory := world.memory.memory', 1),
            ('erase-live-parent', 'let memory := Compiler.ZigAir.Memory.cleanup (parent safety).taken.2.world.memory.memory.nextId world.memory.memory',
             'let memory := Compiler.ZigAir.Memory.cleanup 0 world.memory.memory', 1),
        )),
        ('composed', source('InternerRecursiveNonemptyTests.lean'), (
            ('wrong-result', '(complete safety).1 = .error (.language .outOfMemory)',
             '(complete safety).1 = .error (.language .capacity)', 1),
            ('double-parent-free', '.memory.effects.allocator + 102', '.memory.effects.allocator + 204', 1),
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
                raise ValueError('ambiguous nonempty recursive mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'recursive-nonempty-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'recursive-nonempty-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
