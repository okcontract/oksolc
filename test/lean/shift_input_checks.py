#!/usr/bin/env python3
"""Audit source-bound shift input calls and their actual child failure.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
import constructor_argument_checks as arguments
import recursive_child_checks as recursive
import extract_rule_shift_input

SHIFT = arguments.ITEM + 'ShiftInput.'
TESTS = SHIFT + 'Tests.'
CLAIMS = ['Compiler.Extraction.Dispatch.shiftInput_some']
CLAIMS += [SHIFT + name for name in ('source_projection', 'operand_loaded', 'operand_fault', 'constant_forwarded',
    'constant_error', 'after_constant', 'after_constant_fault', 'operand_error', 'operand_first')]
CLAIMS += [TESTS + name for name in ('power_after_constant', 'exponent_after_constant', 'child_forwarded',
    'parent_operand', 'actual_child_failure', 'failed_child_skips_operand', 'exponent_bounds')]


def bindings():
    return {'sites': extract_rule_shift_input.check(), 'constructors': arguments.bindings()}


def audit(claims):
    required = {
        'Compiler.Extraction.Dispatch.shiftInput_some': {'Compiler.Extraction.Dispatch.shiftInput'},
        SHIFT + 'source_projection': {'Compiler.Extraction.Dispatch.shiftInput'},
        SHIFT + 'operand_loaded': {arguments.OWNED + 'TemporaryMemory.readId_of_load'},
        SHIFT + 'operand_fault': {SHIFT + 'operand'},
        SHIFT + 'constant_forwarded': {arguments.ITEM + 'constant'},
        SHIFT + 'constant_error': {'Compiler.Algebraic.Effect.bind_failure'},
        SHIFT + 'after_constant': {SHIFT + 'operand_loaded', arguments.ARGUMENTS + 'operation'},
        SHIFT + 'after_constant_fault': {'Compiler.Algebraic.Effect.bind_success', 'Compiler.Algebraic.Effect.bind_failure'},
        SHIFT + 'operand_error': {'Compiler.Algebraic.Effect.bind_failure'},
        SHIFT + 'operand_first': {'Compiler.Algebraic.Effect.bind_success'},
        TESTS + 'power_after_constant': {SHIFT + 'after_constant', SHIFT + 'zigLiteral'},
        TESTS + 'exponent_after_constant': {SHIFT + 'operand_first', SHIFT + 'operand_loaded'},
        TESTS + 'parent_operand': {recursive.TESTS + 'parent_established', SHIFT + 'operand_loaded'},
        TESTS + 'actual_child_failure': {recursive.TESTS + 'child_contract', recursive.TESTS + 'held_after_child',
            SHIFT + 'constant_error', SHIFT + 'operand_first', TESTS + 'parent_operand'},
        TESTS + 'failed_child_skips_operand': {recursive.TESTS + 'child_contract', SHIFT + 'constant_error'},
        TESTS + 'exponent_bounds': {SHIFT + 'operand_error'},
    }
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError('shift input lost dependencies: ' + name + ': ' + ', '.join(sorted(missing)))
    return {'checkedDependencies': sorted(required), 'sourceBinding': bindings(),
            'sourceSegments': 4, 'completeNativeConstructorUsed': True,
            'actualChildGrowthOOMAndLiveParentDerived': True,
            'continuationsAfterSuccessfulChildCheckedSeparately': True,
            'enclosingNativeQueryAndGuardPrefixesVerified': False,
            'initialPrefixIsSelectedInsertionContinuations': True,
            'recursiveInductionVerified': False, 'composedProductionTheoremVerified': False}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / name).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)

    operation = 'operation := Arguments.operation context.external context.budget context.allocator context.primitives context.queries'
    return (
        ('boundary', source('InternerShiftInput.lean'), (
            ('wrong-order', 'Dispatch.shiftInput (constructors context) constantFirst opcode',
             'Dispatch.shiftInput (constructors context) (!constantFirst) opcode', 1),
            ('wrong-index', 'match TemporaryMemory.readId before.memory.memory source index with',
             'match TemporaryMemory.readId before.memory.memory source (index + 1) with', 1),
            ('rewind-child', '(ran.1, ran.2.world)', '(ran.1, before)', 2),
            ('erase-source', operation, operation.replace('context.primitives context.queries',
             '(fun _ => context.primitives ⟨0, 0, 0⟩) context.queries'), 1),
            ('reverse-pair', operation,
             'operation := fun opcode values debug => Arguments.operation context.external context.budget context.allocator context.primitives context.queries opcode values.reverse debug', 1),
        )),
        ('execution', source('InternerShiftInputTests.lean'), (
            ('wrong-final-opcode', '(if site = .divide then Dispatch.opSHR else Dispatch.opSHL)',
             '(if site = .divide then Dispatch.opSHL else Dispatch.opSHR)', 1),
            ('read-exponent-late', 'Memory.load before.memory.memory (source.pointer 1)',
             'Memory.load after.memory.memory (source.pointer 1)', 1),
            ('wrong-result', '(.error (.language .outOfMemory), childReturned safety after) ∧',
             '(.error (.language .capacity), childReturned safety after) ∧', 1),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    records = []
    for group, text, changes in mutation_cases():
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous shift input mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'shift-input-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            # Keep the forwarding theorem intact when mutating the child result.
            changed = text.replace(before, after, 1) if name == 'rewind-child' else text.replace(before, after)
            records += checked_controls(output, [mutation_check(output, 'shift-input-' + group + '-' + name, changed, False, env, lean)])
    return records
