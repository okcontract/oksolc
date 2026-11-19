#!/usr/bin/env python3
"""Audit SUB's actual negated constant child through growth OOM and return.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
import constructor_argument_checks as arguments
import constant_word_checks as words
import native_graph_checks as graph
import native_recursion_checks as recursive

TESTS = arguments.ITEM + 'ConstantNegationTests.'
NATIVE = recursive.NS + 'NegateConstantTests.'
CALL = words.CALL
TEMPORARY = arguments.OWNED + 'TemporaryArguments.'
PRELUDE = arguments.ITEM + 'BinaryPreludeTests.'
CLAIMS = [CALL + name for name in ('borrowed_taken', 'duplicate_empty', 'created')]
CLAIMS += [TEMPORARY + 'orderedStores_address', TEMPORARY + 'prepare_address',
           PRELUDE + 'literal_return_facts', words.PUBLICATION + 'other_missed', words.PUBLICATION + 'first_read']
CLAIMS += [TESTS + name for name in ('allocations', 'literal', 'prepared', 'taken', 'parent_missed',
    'observed', 'established', 'child_allocations', 'child_prepared', 'child_normalized', 'child_missed',
    'child_observed', 'child_established', 'child_duplicate', 'child_creation_fits', 'child_unlocked', 'child_reads',
    'child_contract', 'negate_failure')]
CLAIMS += [NATIVE + name for name in ('child_equivalent', 'parent_simplified', 'inner_contract', 'root_route',
    'root_contract', 'program_equivalent', 'program_contract', 'root_one', 'program_one',
    'exhaustion_retained', 'program_zero')]


def bindings():
    return {'recursiveFamily': words.bindings(),
            'scope': 'native initialization and four operation constructors; arbitrary-word publication; '
                     'SUB of nonconstant ID zero and the actual returned constant ID; '
                     'negated constant cache miss, nonempty growth OOM and all enclosing returns',
            'productionBranch': 'src/libevmasm/rule_list.zig:simplifyWithOptions:SUB/right_constant/makeConstant',
            'wordDomain': '0 - value != value in BitVec 256; zero and 2^255 remain outside this branch',
            'all256BitWords': False, 'bothSafetyLayouts': True, 'allDepthsAtLeastTwo': True,
            'observationExhaustionIsUnsupported': True,
            'completeConstructorDependencyClosureVerified': False, 'completeNativeGraphInvariantVerified': False,
            'generalAllocationOutcomesVerified': False, 'recursiveInductionVerified': False,
            'composedProductionTheoremVerified': False}


def audit(claims):
    required = {
        CALL + 'borrowed_taken': {'Compiler.Extraction.Memory.Arguments.Duplication.run_admitted',
            'Compiler.Extraction.Memory.Arguments.Duplication.run_address'},
        CALL + 'duplicate_empty': {CALL + 'normalized_empty'},
        CALL + 'created': {'Compiler.Extraction.AssemblyItem.Creation.create_from_response'},
        TEMPORARY + 'orderedStores_address': {TEMPORARY + 'orderedStores'},
        TEMPORARY + 'prepare_address': {TEMPORARY + 'orderedStores_address', words.MEMORY + 'store_keeps_counters'},
        PRELUDE + 'literal_return_facts': {arguments.ARGUMENTS + 'Prepared.retire', graph.FACTS + 'cleanup'},
        words.PUBLICATION + 'other_missed': {words.PUBLICATION + 'contract', words.INPUT + 'missed'},
        words.PUBLICATION + 'first_read': {graph.NS + 'Facts.constants', 'Compiler.Extraction.Storage.representative_correct'},
        TESTS + 'literal': {words.PUBLICATION + 'contract', TEMPORARY + 'prepare_verified', TEMPORARY + 'prepare_address'},
        TESTS + 'prepared': {CALL + 'prepared_allocations', TESTS + 'literal'},
        TESTS + 'taken': {CALL + 'borrowed_taken', TESTS + 'prepared'},
        TESTS + 'child_prepared': {CALL + 'prepared_allocations', TESTS + 'taken', TESTS + 'established'},
        TESTS + 'child_missed': {words.PUBLICATION + 'other_missed', TESTS + 'established'},
        TESTS + 'child_duplicate': {CALL + 'duplicate_empty', TESTS + 'child_prepared'},
        TESTS + 'child_contract': {CALL + 'constant_growth_contract', arguments.ITEM + 'constant_growing_empty_oom',
            TESTS + 'child_creation_fits', TESTS + 'child_unlocked', TESTS + 'child_observed'},
        TESTS + 'negate_failure': {'Compiler.Algebraic.zigSelectFrom_eq', 'Compiler.Algebraic.Effect.bind_failure'},
        NATIVE + 'child_equivalent': {recursive.TESTS + 'same_call', recursive.NS + 'constant_succ', TESTS + 'child_established'},
        NATIVE + 'parent_simplified': {recursive.NS + 'dispatcher_snapshot', graph.NS + 'Facts.reads',
            TESTS + 'negate_failure', NATIVE + 'child_equivalent', words.PUBLICATION + 'first_read', words.PUBLICATION + 'value_read'},
        NATIVE + 'inner_contract': {TESTS + 'child_contract', CALL + 'simplifier_oom', NATIVE + 'parent_simplified'},
        NATIVE + 'root_contract': {NATIVE + 'inner_contract', NATIVE + 'root_route', PRELUDE + 'literal_return_facts'},
        NATIVE + 'program_equivalent': {words.WORD + 'constant_equivalent', recursive.NS + 'ConstantTests.prefix_result'},
        NATIVE + 'program_contract': {NATIVE + 'program_equivalent', NATIVE + 'root_contract', words.PUBLICATION + 'value_read'},
        NATIVE + 'root_one': {TESTS + 'negate_failure', recursive.NS + 'exhausted', CALL + 'route'},
        NATIVE + 'exhaustion_retained': {NATIVE + 'program_one', TESTS + 'established'},
    }
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError('constant negation lost dependencies: ' + name + ': ' + ', '.join(sorted(missing)))
    return {'checkedDependencies': sorted(required), 'sourceBinding': bindings(),
            'actualNegatedConstantFailureAndParentReturnVerified': True,
            'laterAddNotExecutedAfterChildFailure': True, 'publishedWordRetainedAcrossChildFailure': True,
            'completeConstructorDependencyClosureVerified': False, 'completeNativeGraphInvariantVerified': False,
            'generalAllocationOutcomesVerified': False, 'recursiveInductionVerified': False,
            'composedProductionTheoremVerified': False}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / (name + '.lean')).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)

    module = source('InternerNativeConstantNegationTests')
    prefix = ('import Compiler.Extraction.InternerNativeConstantNegationTests\n'
        'set_option pp.maxSteps 8\nset_option pp.deepTerms false\n'
        'namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NegationControls\n'
        'open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul\n'
        'open Insertion Insertion.Native RecursiveTests ConstantNegationTests NativeRecursion NativeRecursion.NegateConstantTests\n'
        'open Compiler.Extraction.RepresentativeArray\n'
        'open ConstantTests (children prefix_result)\n')
    # This diagnostic variant abstracts the existing recursive family only while
    # rejecting changed sequencing. The complete module is audited and replayed.
    program = prefix + 'attribute [local irreducible] NativeRecursion.ConstantTests.children\n' + (
        module[module.index('def program ('):module.index('/-- Native initialization,')])
    post = prefix + (
        'example (safety : Bool) (depth : Nat) (value : Word) (apart : 0 - value ≠ value) :\n'
        '    (program safety (depth + 2) value).1 = .error (.language .outOfMemory) :=\n'
        '  (program_contract safety depth value apart).1\n'
        'example (safety : Bool) (depth : Nat) (value : Word) (apart : 0 - value ≠ value) :\n'
        '    Constant.value (program safety (depth + 2) value).2.memory.memory (Owner.headerAddress ⟨6, 0⟩) 4 =\n'
        '      .ok (.ok (some value)) := (program_contract safety depth value apart).2.2.1\n'
        'example (safety : Bool) (depth : Nat) (value : Word) (apart : 0 - value ≠ value) :\n'
        '    (program safety (depth + 2) value).2.memory.memory.heap.lookup (rootSource safety value).allocation = none :=\n'
        '  (program_contract safety depth value apart).2.2.2.2.1\n'
        'example (safety : Bool) (depth : Nat) : (program safety (depth + 2) 1).1 = .error (.language .outOfMemory) :=\n'
        '  (program_contract safety depth 1 (by decide)).1\n')
    shallow = prefix + (
        'example (safety : Bool) (value : Word) (apart : 0 - value ≠ value) : program safety 1 value =\n'
        '    (.error (.language .unsupported), (parent safety value).taken.2.world) := program_one safety value apart\n'
        'example (safety : Bool) (value : Word) : program safety 0 value =\n'
        '    (.error (.language .unsupported), CallerInputTests.world safety) := program_zero safety value\n'
        'example : (0 - (0 : Word)) = 0 := by decide\n'
        'example : (0 - (0x8000000000000000000000000000000000000000000000000000000000000000 : Word)) = 0x8000000000000000000000000000000000000000000000000000000000000000 := by decide\n')
    return (
        ('borrowed', source('InternerRecursiveCallTests'), (
            ('omit-take-effects', 'allocator := entered.memory.effects.allocator + call.request.arguments.length * 4',
             'allocator := entered.memory.effects.allocator', 1),
        )),
        ('input', source('InternerConstantNegationInputTests'), (
            ('stale-literal', '⟨(old safety value).memory.memory.nextId, 0, 2⟩',
             '⟨(old safety value).memory.memory.nextId + 1, 0, 2⟩', 1),
        )),
        ('child-input', source('InternerConstantNegationChildInputTests'), (
            ('wrong-negated-word', 'constantRequest (0 - value)', 'constantRequest value', 1),
            ('reuse-parent-lifetime', '⟨(child safety value).before.memory.memory.nextId + 1, 0⟩',
             '⟨(child safety value).before.memory.memory.nextId, 0⟩', 1),
        )),
        ('dispatch', source('InternerConstantNegationDispatchTests'), (
            ('wrong-child-argument', '(called : constructors.constant (0 - value) metadata before',
             '(called : constructors.constant value metadata before', 1),
            ('forget-earlier-zero-rule', '(nonzero : value ≠ 0)', '(nonzero : value = 0)', 1),
        )),
        ('program', program, (
            ('wrong-returned-operand', '(children safety depth).operation 3 [0, id] debug',
             '(children safety depth).operation 3 [0, id + 1] debug', 1),
        )),
        ('return', module, (
            ('double-parent-free', '.memory.effects.allocator + 102', '.memory.effects.allocator + 204', 1),
        )),
        ('post', post, (
            ('wrong-final-native-word', '.ok (.ok (some value))', '.ok (.ok (some (value + 1)))', 1),
            ('retain-literal', '.allocation = none', '.allocation ≠ none', 1),
            ('wrong-final-result', '.1 = .error (.language .outOfMemory)', '.1 = .ok 5', 2),
        )),
        ('shallow', shallow, (
            ('exhaustion-as-oom', '.error (.language .unsupported)', '.error (.language .outOfMemory)', 2),
            ('rewind-reached-parent', '(parent safety value).taken.2.world', '(old safety value)', 1),
            ('admit-negation-fixed-point', '(0 - (0x8000000000000000000000000000000000000000000000000000000000000000 : Word)) = 0x8000000000000000000000000000000000000000000000000000000000000000', '(0 - (0x8000000000000000000000000000000000000000000000000000000000000000 : Word)) ≠ 0x8000000000000000000000000000000000000000000000000000000000000000', 1),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    records = []
    for group, text, changes in mutation_cases():
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous constant negation mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'constant-negation-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'constant-negation-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
