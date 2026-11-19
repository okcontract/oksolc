#!/usr/bin/env python3
"""Audit native literal reads across actual child failure and publication.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
import constructor_argument_checks as arguments
import extract_rule_literal_input as admission

SHIFT = arguments.ITEM + 'ShiftInput.'
NS = arguments.ITEM + 'LiteralInput.'
TESTS = NS + 'Tests.'
GRAPH = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.'
CLAIMS = [SHIFT + name for name in ('operand_good', 'operand_after_frame')]
CLAIMS += [TESTS + name for name in ('existing_shift_routes', 'minimum_after_child',
    'materialize_after_read', 'modular_reads', 'alternating_reads', 'early_rejections',
    'actual_constant_failure', 'actual_nonempty_child', 'published_borrow', 'published_source', 'actual_publication_read')]


def bindings():
    return {'sites': admission.check(), 'constructors': arguments.bindings()}


def audit(claims):
    required = {
        SHIFT + 'operand_good': {SHIFT + 'operand_loaded'},
        SHIFT + 'operand_after_frame': {arguments.ITEM + 'good_frame', SHIFT + 'operand_good'},
        TESTS + 'existing_shift_routes': {SHIFT + 'zigLiteral'},
        TESTS + 'minimum_after_child': {SHIFT + 'operand_after_frame', 'Compiler.Algebraic.Effect.bind_success'},
        TESTS + 'materialize_after_read': {SHIFT + 'operand_good', 'Compiler.Algebraic.Effect.bind_success'},
        TESTS + 'modular_reads': {SHIFT + 'operand_good', NS + 'modularAdd', NS + 'modularMultiply'},
        TESTS + 'alternating_reads': {SHIFT + 'operand_good', NS + 'alternatingRight'},
        TESTS + 'early_rejections': {NS + 'subtractMaterializedLeft', NS + 'subtractMaterializedRight', NS + 'alternatingRight'},
        TESTS + 'actual_constant_failure': {arguments.ITEM + 'RecursiveTests.child_contract',
            arguments.ITEM + 'RecursiveTests.held_after_child', SHIFT + 'operand_good'},
        TESTS + 'actual_nonempty_child': {arguments.ITEM + 'RecursiveNonemptyTests.child_contract',
            arguments.ITEM + 'RecursiveNonemptyTests.held_after_child', SHIFT + 'operand_after_frame'},
        TESTS + 'published_borrow': {arguments.ITEM + 'RecursiveBorrowedTests.xor_contract',
            arguments.ITEM + 'RecursiveBorrowedTests.xor_input_at'},
        TESTS + 'published_source': {arguments.ITEM + 'RecursiveNonemptyTests.caller_source',
            arguments.ITEM + 'RecursiveNonemptyTests.zero_contract',
            arguments.ITEM + 'ReachablePrefixTests.initialized_prefix',
            'Compiler.Extraction.Memory.Arguments.Normalization.represented_frame', arguments.OWNED + 'Good.backed',
            arguments.OWNED + 'Insertion.Native.CallerInputTests.source_inputs'},
        TESTS + 'actual_publication_read': {arguments.ITEM + 'AlgebraicInput.Tests.published_child',
            TESTS + 'published_source', arguments.ITEM + 'AlgebraicInput.Tests.publication_literal',
            arguments.ARGUMENTS + 'prepare_success', arguments.ARGUMENTS + 'operation_prepared'},
    }
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError('native literal lost dependencies: ' + name + ': ' + ', '.join(sorted(missing)))
    return {'checkedDependencies': sorted(required), 'sourceBinding': bindings(),
            'allNonemptyLiteralSegmentsBound': True, 'postChildReadFromNativeFrame': True,
            'publishedCallerBorrowFeedsNextLiteral': True, 'publishedGraphBorrowDerivedFromFullXor': True,
            'publishedSourceDerivedFromInitializerAndNativeFrames': True,
            'completeOuterShiftVerified': False,
            'completeNativeQueryAndGuardConnectionVerified': False,
            'completeConstructorDependencyClosureVerified': False, 'recursiveInductionVerified': False}


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    directory = ROOT / 'lean/Compiler/Extraction'
    program = (directory / 'RuleLiteralInputProgram.lean').read_text()
    clients = (directory / 'InternerLiteralInputTests.lean').read_text()
    imports = list(dict.fromkeys(line for raw in (program, clients) for line in raw.splitlines()
        if line.startswith('import ') and line != 'import Compiler.Extraction.RuleLiteralInputProgram'))
    # Check the actual generated program together with its proof clients, so a
    # model mutation cannot be hidden by importing the unchanged definitions.
    text = '\n'.join(imports) + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n'
    text += without_imports(program) + '\n' + without_imports(clients)
    records = checked_controls(output, [mutation_check(output, 'literal-input-unchanged', text, True, env, lean)])
    changes = (
        ('read-before-child',
         'c.operation Dispatch.opSIGNEXTEND [← c.constant (if outerByte.toNat ≤ innerByte.toNat then outerByte else innerByte) debug, ← read inner 1] debug',
         'let operand ← read inner 1\n  c.operation Dispatch.opSIGNEXTEND [← c.constant (if outerByte.toNat ≤ innerByte.toNat then outerByte else innerByte) debug, operand] debug', 1),
        ('post-child-index', 'debug, ← read inner 1] debug', 'debug, ← read inner 0] debug', 2),
        ('view-offset', 'private abbrev read := @ShiftInput.operand',
         'private def read (source : View) (index : Nat) : GraphAction σ NodeId :=\n'
         '  ShiftInput.operand ⟨source.allocation, 0, source.length⟩ index', 1),
        ('materialization-read', 'c.materialize (← read nested 1) constant debug', 'c.materialize 0 constant debug', 1),
        ('modular-order', 'Dispatch.opADDMOD [← read nested 0, ← read nested 1, right]',
         'Dispatch.opADDMOD [← read nested 1, ← read nested 0, right]', 1),
        ('modular-arity', 'Dispatch.opMULMOD [← read nested 0, ← read nested 1, right]',
         'Dispatch.opMULMOD [← read nested 0, ← read nested 1]', 1),
        ('dynamic-index', 'Folding.Zig.checkedSub 1 innerIndex', 'Folding.Zig.checkedSub 2 innerIndex', 1),
        ('unary-opcode', 'Dispatch.opISZERO [← read third 0]', 'Dispatch.opNOT [← read third 0]', 1),
        ('wrong-failure', '(.error (.language .outOfMemory), childReturned safety after) ∧',
         '(.error (.language .capacity), childReturned safety after) ∧', 1),
        ('erase-publication', 'Arguments.Prepared [4, 0] (ready safety) rootSource',
         'Arguments.Prepared [4, 0] (initial safety) rootSource', 1),
        ('wrong-published-source', 'Good (CallerInputTests.argumentView false) [0] (ready safety)',
         'Good (CallerInputTests.argumentView false) [1] (ready safety)', 1),
        ('wrong-published-graph-buffer', 'Good RecursiveBorrowedTests.childSource [0, 1] (RecursiveBorrowedTests.ready safety)',
         'Good RecursiveBorrowedTests.childSource [1, 0] (RecursiveBorrowedTests.ready safety)', 1),
    )
    for name, before, after, count in changes:
        if text.count(before) != count:
            raise ValueError('ambiguous literal input mutation: ' + name)
        records += checked_controls(output, [mutation_check(output, 'literal-input-' + name,
            text.replace(before, after), False, env, lean)])
    return records
