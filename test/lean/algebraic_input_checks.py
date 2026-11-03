#!/usr/bin/env python3
"""Audit all Algebraic.apply inputs through the complete native constructors.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from collections import Counter

from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
import constructor_argument_checks as arguments
import constructor_inventory
import extract_compiler

NS = arguments.ITEM + 'AlgebraicInput.'
TESTS = NS + 'Tests.'
NONEMPTY = arguments.ITEM + 'RecursiveNonemptyTests.'
CLAIMS = [NS + name for name in ('source_body', 'operation_forwarded', 'constant_forwarded',
    'captures', 'constants', 'literal_input', 'unary', 'negation', 'boolean', 'unary_input',
    'negation_error', 'boolean_error', 'negation_input', 'boolean_input')]
CLAIMS += [TESTS + name for name in ('actual_boolean_failure', 'published_child',
    'publication_literal', 'actual_negation_input')]
CLAIMS += [NONEMPTY + 'child_source']


def bindings():
    source = extract_compiler.SOURCE.read_bytes()
    if extract_compiler.extract_construction(source) != extract_compiler.CONSTRUCTION.read_bytes():
        raise ValueError('source-extracted Algebraic.apply body is stale')
    sites = constructor_inventory.sites(source, {'apply'})
    shapes = Counter((site['callee'], site['storage'], site['arity']) for site in sites)
    if shapes != Counter({('makeConstant', 'empty', 0): 4,
                          ('makeOperation', 'temporary', 1): 4,
                          ('makeOperation', 'temporary', 2): 1}):
        raise ValueError('Algebraic.apply constructor input closure changed: ' + repr(shapes))
    return {'constructors': arguments.bindings(), 'sourceSites': sites,
            'scope': 'all nine constructor sites of Algebraic.apply; scalar left/right parameters',
            'sharedExtractedControl': True, 'nativeChildInductionStillRequired': True,
            'completeDispatcherInputsVerified': False}


def audit(claims):
    required = {
        NS + 'source_body': {'Compiler.Algebraic.zigApply', NS + 'run'},
        NS + 'operation_forwarded': {arguments.ARGUMENTS + 'operation', 'Compiler.Extraction.Interner.buildOpcode'},
        NS + 'constant_forwarded': {arguments.ITEM + 'constant'},
        NS + 'literal_input': {arguments.ARGUMENTS + 'prepare_success', arguments.ARGUMENTS + 'operation_prepared'},
        NS + 'unary_input': {NS + 'unary', NS + 'literal_input'},
        NS + 'negation_error': {NS + 'negation', 'Compiler.Algebraic.Effect.bind_failure'},
        NS + 'boolean_error': {NS + 'boolean', 'Compiler.Algebraic.Effect.bind_failure'},
        NS + 'negation_input': {NS + 'negation', NS + 'literal_input', 'Compiler.Algebraic.Effect.bind_success'},
        NS + 'boolean_input': {NS + 'boolean', NS + 'literal_input', 'Compiler.Algebraic.Effect.bind_success'},
        NONEMPTY + 'child_source': {NS + 'unary_input', NONEMPTY + 'parent_established'},
        NONEMPTY + 'parent_continuation': {NONEMPTY + 'child_source', NONEMPTY + 'parent_zero'},
        NONEMPTY + 'complete_contract': {NONEMPTY + 'full_contract'},
        TESTS + 'actual_boolean_failure': {NS + 'boolean_error', NONEMPTY + 'child_contract', NONEMPTY + 'held_after_child'},
        TESTS + 'published_child': {NS + 'constant_forwarded', NONEMPTY + 'zero_contract'},
        TESTS + 'actual_negation_input': {NS + 'negation_input', TESTS + 'published_child', TESTS + 'publication_literal'},
    }
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError('algebraic input lost dependencies: ' + name + ': ' + ', '.join(sorted(missing)))
    return {'checkedDependencies': sorted(required), 'sourceBinding': bindings(),
            'completeNativeConstructorUsedAtAllAlgebraicSites': True,
            'selectedParentReturnUsesSharedInputRoute': True,
            'realChildFailureStopsSecondLiteral': True,
            'realPublicationFeedsOuterNegationInput': True,
            'completeOuterNegationOutcomeVerified': False,
            'completeConstructorDependencyClosureVerified': False,
            'recursiveInductionVerified': False, 'composedProductionTheoremVerified': False}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / name).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)

    model = source('InternerAlgebraicInput.lean')
    # A false forwarding statement can make downstream rewrites diverge. This
    # labeled control isolates that theorem; the unchanged full module and its
    # proof clients remain in the positive control and fresh replay.
    forwarding = model.split('theorem constant_forwarded')[0] + '\nend ' + NS[:-1] + '\n'
    return (
        ('forwarding', forwarding, (
            ('wrong-opcode', '(Interner.buildOpcode opcode) values debug',
             '(Interner.buildOpcode .ISZERO) values debug', 1),
        )),
        ('model', model, (
            ('wrong-scalar', 'zigApply replacement (builder context) left right debug',
             'zigApply replacement (builder context) right left debug', 1),
            ('wrong-returned-id', '(builder context).makeOperation .ISZERO [first] debug) := by',
             '(builder context).makeOperation .ISZERO [left] debug) := by', 1),
            ('discard-failure-world', 'run context replacement left right debug before = (.error fault, after) := by',
             'run context replacement left right debug before = (.error fault, before) := by', 2),
            ('negation-input-from-entry', 'Arguments.Prepared [zero, if replacement == .neg_left then left else right] middle source prepared ∧',
             'Arguments.Prepared [zero, if replacement == .neg_left then left else right] before source prepared ∧', 1),
            ('boolean-input-from-entry', 'Arguments.Prepared [first] middle source prepared ∧',
             'Arguments.Prepared [first] before source prepared ∧', 1),
        )),
        ('reached', source('InternerAlgebraicInputTests.lean'), (
            ('erase-successful-child', '(afterPublication safety right).2.graph = (ready safety).graph',
             '(afterPublication safety right).2.graph = (initial safety).graph', 1),
            ('retain-first-literal', '.memory.memory.heap.lookup childSource.allocation = none ∧',
             '.memory.memory.heap.lookup childSource.allocation ≠ none ∧', 1),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    records = []
    for group, text, changes in mutation_cases():
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous algebraic input mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'algebraic-input-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'algebraic-input-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
