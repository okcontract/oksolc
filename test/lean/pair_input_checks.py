#!/usr/bin/env python3
"""Audit scalar pair source bindings and native child composition.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
import constructor_argument_checks as arguments
import extract_rule_pair_input as admission

NS = arguments.ITEM + 'PairInput.'
TESTS = NS + 'Tests.'
CLAIMS = [NS + name for name in ('constant_forwarded', 'materialize_forwarded', 'scalars_forwarded',
    'input', 'first_error', 'second_error', 'first_input', 'second_input')]
CLAIMS += [TESTS + name for name in ('after_child', 'actual_failure', 'publication_literal',
    'actual_publication_input', 'arithmetic_rejections', 'add_observed', 'add_established', 'add_identity',
    'add_simplified', 'add_literal', 'add_publication', 'add_result', 'add_contract',
    'publication_source', 'publication_equivalent', 'publication_contract', 'publication_zero')]
CLAIMS += ['Compiler.Extraction.Dispatch.Effects.pair_scalars']


def bindings():
    return {'sites': admission.check(), 'constructors': arguments.bindings()}


def audit(claims):
    recursive = arguments.ITEM + 'NativeRecursion.'
    nonempty = arguments.ITEM + 'RecursiveNonemptyTests.'
    call = arguments.ITEM + 'RecursiveTests.Call.'
    graph = arguments.OWNED + 'NativeGraph.Facts.'
    required = {
        NS + 'materialize_forwarded': {arguments.ITEM + 'materialize'},
        NS + 'scalars_forwarded': {arguments.ARGUMENTS + 'operation'},
        NS + 'input': {arguments.ARGUMENTS + 'prepare_success', arguments.ARGUMENTS + 'operation_prepared'},
        NS + 'first_error': {'Compiler.Algebraic.Effect.bind_failure'},
        NS + 'second_error': {'Compiler.Algebraic.Effect.bind_failure'},
        NS + 'first_input': {NS + 'input', 'Compiler.Algebraic.Effect.bind_success'},
        NS + 'second_input': {NS + 'input', 'Compiler.Algebraic.Effect.bind_success'},
        TESTS + 'after_child': {'Compiler.Algebraic.Effect.bind_success', NS + 'oppositeOuter', NS + 'addMaterializedDifference'},
        TESTS + 'actual_failure': {arguments.ITEM + 'RecursiveTests.child_contract',
            arguments.ITEM + 'RecursiveTests.held_after_child', NS + 'first_error', NS + 'second_error'},
        TESTS + 'actual_publication_input': {arguments.ITEM + 'AlgebraicInput.Tests.published_child',
            TESTS + 'publication_literal', NS + 'second_input'},
        TESTS + 'arithmetic_rejections': {NS + 'modPower', NS + 'oppositeOuter', NS + 'reassociateConstants'},
        TESTS + 'add_established': {call + 'establish', nonempty + 'parent_literal'},
        TESTS + 'add_identity': {'Compiler.Extraction.Dispatch.simplifyWithInputs',
            'Compiler.Extraction.Dispatch.binaryStageWithInputs'},
        TESTS + 'add_simplified': {TESTS + 'add_identity', recursive + 'dispatcher_snapshot', graph + 'reads',
            nonempty + 'first_constant', nonempty + 'zero_constant'},
        TESTS + 'add_literal': {nonempty + 'parent_literal'},
        TESTS + 'add_publication': {graph + 'publish_absent', call + 'prefix_results',
            arguments.OWNED + 'Insertion.Native.CallerInput.graph_custody', TESTS + 'add_established'},
        TESTS + 'add_result': {TESTS + 'add_simplified', TESTS + 'add_publication', call + 'route',
            arguments.ARGUMENTS + 'operation_prepared', recursive + 'operation_succ'},
        TESTS + 'add_contract': {TESTS + 'add_result', TESTS + 'add_literal', TESTS + 'add_publication',
            graph + 'cleanup', call + 'returned_frame', arguments.ARGUMENTS + 'Prepared.retire', nonempty + 'caller_source'},
        TESTS + 'publication_source': {NS + 'addMaterializedDifference', NS + 'subtractConstant', recursive + 'unfold'},
        TESTS + 'publication_equivalent': {TESTS + 'publication_source', recursive + 'ConstantTests.prefix_result',
            recursive + 'ConstantTests.zero_equivalent', 'Compiler.Algebraic.Effect.bind_success'},
        TESTS + 'publication_contract': {TESTS + 'publication_equivalent', TESTS + 'add_contract'},
    }
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError('scalar pair lost dependencies: ' + name + ': ' + ', '.join(sorted(missing)))
    return {'checkedDependencies': sorted(required), 'sourceBinding': bindings(),
            'allScalarPairLiteralSegmentsBound': True, 'actualGrowthFailureRetainsParent': True,
            'actualPublicationFeedsOuterLiteral': True, 'completeOuterAdditionVerified': False,
            'initializedZeroAdditionReturnsThroughOuterCleanup': True,
            'initializedZeroAdditionScope': 'constant/materializer zero -> ADD(non-Push row 0, returned zero ID); '
                'same recursive context and full initialization, both safety layouts, all positive depths; successful publication only',
            'completeConstructorDependencyClosureVerified': False, 'recursiveInductionVerified': False}


def composed_cases():
    prefix = (
        'import Compiler.Extraction.InternerPairInputTests\n'
        'open Compiler.Algebraic Compiler.Extraction Compiler.Extraction.Cache Compiler.Extraction.Storage\n'
        'open Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall\n'
        'open Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem\n'
        'open PairInput.Tests RecursiveNonemptyTests\n'
        'open RecursiveTests (debug)\n'
        'set_option pp.maxSteps 8\nset_option pp.deepTerms false\n'
        'attribute [local irreducible] publicationProgram ready addParent OwnedKeys.store '
        'PairInput.addMaterializedDifference PairInput.subtractConstant '
        'NativeRecursion.ConstantTests.children ReachablePrefixTests.sequence\n')
    return (
        ('source', prefix +
         'example (safety materialized : Bool) (depth : Nat) :\n'
         '    publicationProgram safety materialized (depth + 1) =\n'
         '      (do let _ ← ReachablePrefixTests.sequence (NativeRecursion.ConstantTests.children safety (depth + 1)) 3\n'
         '          if materialized then PairInput.addMaterializedDifference (addContext safety depth) 0 99 0 debug\n'
         '          else PairInput.subtractConstant (addContext safety depth) 0 0 debug) (Insertion.Native.CallerInputTests.world safety) :=\n'
         '  publication_source safety materialized depth\n', (
            ('truncated-prefix', '(depth + 1)) 3\n', '(depth + 1)) 2\n'),
            ('wrong-materialized-value', '(addContext safety depth) 0 99 0 debug', '(addContext safety depth) 0 99 1 debug'),
            ('wrong-source-operand', 'PairInput.subtractConstant (addContext safety depth) 0 0 debug',
             'PairInput.subtractConstant (addContext safety depth) 4 0 debug'),
        )),
        ('return', prefix +
         'example (safety materialized : Bool) (depth : Nat) :\n'
         '    (publicationProgram safety materialized (depth + 1)).1 = .ok 0 :=\n'
         '  (publication_contract safety materialized depth).1\n'
         'example (safety materialized : Bool) (depth : Nat) :\n'
         '    NativeGraph.Facts safety 7 6 ⟨ReachablePrefixTests.backing, 0⟩ 5\n'
         '      (publicationProgram safety materialized (depth + 1)).2 (rows safety) :=\n'
         '  (publication_contract safety materialized depth).2.1\n'
         'example (safety materialized : Bool) (depth : Nat) :\n'
         '    (publicationProgram safety materialized (depth + 1)).2.memory.memory.heap.lookup rootSource.allocation = none :=\n'
         '  (publication_contract safety materialized depth).2.2.1\n'
         'example (safety materialized : Bool) (depth : Nat) :\n'
         '    Good (Insertion.Native.CallerInputTests.argumentView false) [0] (publicationProgram safety materialized (depth + 1)).2 :=\n'
         '  (publication_contract safety materialized depth).2.2.2.2.1\n'
         'example (safety materialized : Bool) (depth : Nat) :\n'
         '    (publicationProgram safety materialized (depth + 1)).2.memory.effects.keys =\n'
         '      OwnedKeys.store (addParent safety).taken.2.world.memory.effects.keys (addParent safety).key\n'
         '        ⟨(addParent safety).normalized.address, 0⟩ :=\n'
         '  (publication_contract safety materialized depth).2.2.2.2.2.2\n', (
            ('wrong-result', '.1 = .ok 0 :=', '.1 = .ok 4 :='),
            ('wrong-capacity', '⟨ReachablePrefixTests.backing, 0⟩ 5', '⟨ReachablePrefixTests.backing, 0⟩ 6'),
            ('retain-literal', 'rootSource.allocation = none :=', 'rootSource.allocation ≠ none :='),
            ('wrong-caller-value', 'argumentView false) [0]', 'argumentView false) [1]'),
            ('wrong-published-value', 'normalized.address, 0⟩ :=', 'normalized.address, 4⟩ :='),
        )),
        ('native-query', prefix +
         'example (safety : Bool) (depth : Nat) :\n'
         '    ((addContext safety depth).primitives rootSource (addParent safety).address (addParent safety).native).simplify\n'
         '      (addParent safety).key (addParent safety).normalized (addParent safety).taken.2.world =\n'
         '        (.ok (some 0), (addParent safety).taken.2.world) := add_simplified safety depth\n', (
            ('wrong-identity', '(.ok (some 0),', '(.ok (some 4),'),
            ('rewind-reached-world', '(.ok (some 0), (addParent safety).taken.2.world)', '(.ok (some 0), ready safety)'),
        )),
        ('exhaustion', prefix +
         'example (safety materialized : Bool) : publicationProgram safety materialized 0 =\n'
         '    (.error (.language .unsupported), Insertion.Native.CallerInputTests.world safety) :=\n'
         '  publication_zero safety materialized\n', (
            ('exhaustion-as-oom', '.language .unsupported', '.language .outOfMemory'),
            ('published-on-exhaustion', 'Insertion.Native.CallerInputTests.world safety)', 'ready safety)'),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    records = []
    for file, changes in (
        ('InternerPairInput.lean', (
            ('scalar-order', 'opcode [a, b] debug := by', 'opcode [b, a] debug := by'),
            ('materialize-value', 'context.queries id value debug before', 'context.queries id (value + 1) debug before'),
            ('child-rewinds-world', 'debug before = (.error fault, after) :=', 'debug before = (.error fault, before) :='),
            ('input-from-entry', 'Arguments.Prepared [a, b] middle source prepared ∧',
             'Arguments.Prepared [a, b] before source prepared ∧'),
        )),
        ('InternerPairInputTests.lean', (
            ('wrong-child-order', 'Dispatch.opSHL [id, operand] debug after', 'Dispatch.opSHL [operand, id] debug after'),
            ('wrong-opcode', 'Dispatch.opADD [operand, id] debug after', 'Dispatch.opSUB [operand, id] debug after'),
            ('wrong-failure', '(.error (.language .outOfMemory), RecursiveTests.childReturned safety after) ∧',
             '(.error (.language .capacity), RecursiveTests.childReturned safety after) ∧'),
            ('erase-publication', '(afterPublication safety).2.graph = (ready safety).graph',
             '(afterPublication safety).2.graph = (initial safety).graph'),
        )),
    ):
        raw = (ROOT / 'lean/Compiler/Extraction' / file).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        text = imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)
        records += checked_controls(output, [mutation_check(output, file[:-5] + '-unchanged', text, True, env, lean)])
        for name, before, after in changes:
            expected = 2 if name in {'child-rewinds-world', 'input-from-entry'} else 1
            if text.count(before) != expected:
                raise ValueError('ambiguous scalar pair mutation: ' + name)
            records += checked_controls(output, [mutation_check(output, 'scalar-pair-' + name,
                text.replace(before, after), False, env, lean)])
    for group, text, changes in composed_cases():
        for name, before, _ in changes:
            if text.count(before) != 1:
                raise ValueError('ambiguous composed scalar pair mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'scalar-pair-composed-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after in changes:
            records += checked_controls(output, [mutation_check(output, 'scalar-pair-composed-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
