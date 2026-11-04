#!/usr/bin/env python3
"""Audit the named-local dispatcher input through recursive child and parent return.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
import constructor_argument_checks as arguments
import native_recursion_checks as recursive
import native_graph_checks as graph
import view_input_checks as views

NS = arguments.ITEM + 'NativeLocal.'
TESTS = NS + 'Tests.'
BINARY = arguments.ITEM + 'BinaryPreludeTests.'
NORMAL = 'Compiler.Extraction.Memory.Arguments.Normalization.'
CLAIMS = [NS + name for name in ('snapshot', 'selected', 'input_contract')]
CLAIMS += [TESTS + name for name in ('parent_observed', 'parent_established', 'source_query',
    'local_input', 'cache_observed', 'cache_route', 'cache_result', 'local_result', 'local_native', 'dispatch_route', 'constant_guards',
    'operation_guards', 'operation_agreement', 'parent_simplified', 'parent_continuation', 'root_literal',
    'parent_room', 'root_route', 'root_prepared', 'local_parent', 'parent_publication', 'reduced_result', 'reduced_native',
    'first_publication', 'observed_route', 'result_observed', 'completed', 'root_independent', 'program_equivalent', 'program_contract',
    'root_one', 'program_one', 'exhaustion_retained')]
CLAIMS += [arguments.OWNED + 'Caller.initialize_origin']
CLAIMS += [BINARY + name for name in ('prefix_observed', 'literal', 'established', 'simplified',
    'inner_contract', 'route', 'rows_count', 'contract')]


def bindings():
    return {'views': views.bindings(), 'recursiveFamily': recursive.bindings(),
            'scope': 'shared dropRepeatedLocal query and selector, native copy/overwrite and complete recursive constructor; '
                     'AND publication -> AND parent -> named-local cache-hit child -> parent publication and cleanup; '
                     'native graph and temporary retirement derived through initialization, child frame and parent return',
            'nativeZigGateRun': False, 'completeConstructorDependencyClosureVerified': False,
            'recursiveInductionVerified': False}


def audit(claims):
    nested = 'Compiler.Extraction.Nested.'
    required = {
        arguments.OWNED + 'Caller.initialize_origin': {arguments.OWNED + 'Caller.initialize_origin_frame',
            NORMAL + 'caller_buffer', NORMAL + 'init_frame',
            arguments.OWNED + 'Caller.initialize_verified', arguments.OWNED + 'Caller.initialize_graph'},
        NS + 'snapshot': {recursive.TIMING + 'drop_repeated', recursive.READS + 'query'},
        NS + 'selected': {NS + 'snapshot', nested + 'dropRepeatedLocal', recursive.NS + 'local_succ'},
        NS + 'input_contract': {graph.NS + 'Facts.reads', NS + 'selected', graph.NS + 'Facts.queried_input',
            graph.NS + 'Facts.frame', views.NS + 'local_input', views.NS + 'local_prepared',
            views.NS + 'local_rejected', arguments.ITEM + 'ShiftInput.operand_good',
            arguments.ARGUMENTS + 'Prepared.key_apart'},
        TESTS + 'parent_established': {BINARY + 'contract', BINARY + 'literal_facts',
            arguments.ITEM + 'RecursiveTests.Call.establish'},
        TESTS + 'source_query': {TESTS + 'parent_established'},
        TESTS + 'local_input': {NS + 'input_contract', TESTS + 'parent_established',
            TESTS + 'parent_observed', TESTS + 'source_query'},
        TESTS + 'cache_route': {arguments.ITEM + 'invoke_cached'},
        TESTS + 'cache_result': {TESTS + 'cache_route', arguments.OWNED + 'deinit_detached'},
        TESTS + 'local_result': {TESTS + 'cache_result', TESTS + 'cache_observed', views.NS + 'local_prepared',
            arguments.OWNED + 'deinit_detached'},
        TESTS + 'local_native': {TESTS + 'local_input', arguments.ITEM + 'invoke_cached_native',
            TESTS + 'cache_result', graph.NS + 'Facts.frame',
            arguments.ARGUMENTS + 'Prepared.retire'},
        TESTS + 'constant_guards': {TESTS + 'parent_established',
            arguments.ITEM + 'RecursiveBorrowedTests.constant_nonpush'},
        TESTS + 'operation_agreement': {TESTS + 'parent_established', graph.NS + 'Facts.operations'},
        TESTS + 'parent_simplified': {recursive.NS + 'dispatcher_snapshot', graph.NS + 'Facts.reads', TESTS + 'dispatch_route', TESTS + 'local_result', views.NS + 'local_forwarded',
            TESTS + 'constant_guards', TESTS + 'operation_guards', TESTS + 'source_query'},
        TESTS + 'root_route': {TESTS + 'parent_continuation', TESTS + 'parent_simplified',
            arguments.ITEM + 'RecursiveTests.Call.route', arguments.ARGUMENTS + 'operation_prepared'},
        TESTS + 'root_prepared': {TESTS + 'root_literal', arguments.ARGUMENTS + 'prepare_success'},
        TESTS + 'local_parent': {TESTS + 'local_native', TESTS + 'root_prepared',
            recursive.NS + 'GraphFrame.retained_parent', recursive.NS + 'CallFrame.caller'},
        TESTS + 'parent_publication': {TESTS + 'local_native', TESTS + 'local_parent', graph.NS + 'Facts.publish_absent'},
        TESTS + 'reduced_result': {TESTS + 'parent_publication', arguments.OWNED + 'deinit_detached'},
        TESTS + 'reduced_native': {TESTS + 'local_native', TESTS + 'parent_publication', TESTS + 'root_prepared',
            graph.NS + 'Facts.cleanup', arguments.ARGUMENTS + 'Prepared.retire',
            arguments.ITEM + 'RecursiveTests.Call.returned_frame'},
        TESTS + 'result_observed': {TESTS + 'reduced_native', TESTS + 'root_prepared', TESTS + 'reduced_result',
            graph.NS + 'Facts.operations', TESTS + 'local_input'},
        TESTS + 'observed_route': {TESTS + 'first_publication', recursive.TESTS + 'binary_equivalent',
            'Compiler.Algebraic.Effect.bind_success'},
        TESTS + 'completed': {TESTS + 'program', recursive.NS + 'unfold', views.NS + 'localOperation',
            nested + 'dropRepeatedLocal', arguments.OWNED + 'TemporaryArguments.unwind',
            TESTS + 'observed_route', TESTS + 'root_route', TESTS + 'result_observed'},
        TESTS + 'root_independent': {TESTS + 'root_route', TESTS + 'rootWith', recursive.NS + 'step', views.NS + 'localOperation'},
        TESTS + 'program_equivalent': {recursive.TESTS + 'binary_equivalent', TESTS + 'root_independent',
            BINARY + 'contract', 'Compiler.Algebraic.Effect.bind_success'},
        TESTS + 'program_contract': {TESTS + 'program_equivalent', TESTS + 'completed', TESTS + 'local_input', TESTS + 'reduced_native',
            arguments.OWNED + 'LocalArguments.prepare_storage',
            TESTS + 'operation_agreement', TESTS + 'constant_guards'},
        TESTS + 'root_one': {recursive.NS + 'dispatcher_snapshot', graph.NS + 'Facts.reads', TESTS + 'dispatch_route', arguments.ITEM + 'RecursiveTests.Call.route',
            arguments.ARGUMENTS + 'operation_prepared'},
        TESTS + 'exhaustion_retained': {TESTS + 'program_one', TESTS + 'parent_established'},
        BINARY + 'inner_contract': {arguments.ITEM + 'RecursiveTests.Call.spare_publication', BINARY + 'simplified'},
        BINARY + 'contract': {BINARY + 'inner_contract', BINARY + 'route', graph.FACTS + 'cleanup'},
    }
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError('named-local composition lost dependencies: ' + name + ': ' + ', '.join(sorted(missing)))
    return {'checkedDependencies': sorted(required), 'sourceBinding': bindings(),
            'nativeSourceAndSelectorDerived': True, 'copyOverwriteAndKeySeparationDerived': True,
            'actualRecursiveLocalChildAndParentReturn': True, 'allSufficientDepthsVerified': True,
            'cacheHitInitializationFrameDerived': True, 'finalNativeGraphAndTemporaryRetirementDerived': True,
            'exhaustionRetainsParent': True, 'initialPrefixIsSelectedInsertionContinuations': False, 'initialPrefixUsesSameRecursiveContext': True,
            'completeNativeGraphInvariantVerified': False, 'completeConstructorDependencyClosureVerified': False,
            'successfulRecursiveGrowthVerified': False, 'completePublicationRollbackVerified': False,
            'recursiveInductionVerified': False, 'composedProductionTheoremVerified': False}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / name).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)

    return (
        ('input', source('InternerNativeLocal.lean'), (
            ('wrong-selector-load', 'ShiftInput.operand (view source) 1 before = (.ok right, before)',
             'ShiftInput.operand (view source) 0 before = (.ok right, before)', 1),
            ('wrong-native-opcode', '(Owner.headerAddress ⟨owner, 0⟩) nested opcode =',
             '(Owner.headerAddress ⟨owner, 0⟩) nested (opcode + 1) =', 1),
            ('alias-owned-key', 'target.allocation ≠ old.address', 'target.allocation = old.address', 1),
            ('failure-rewinds', '= (.error fault, reached)', '= (.error fault, before)', 2),
        )),
        ('return', source('InternerNativeLocalReturnTests.lean'), (
            ('late-root-cleanup',
             'memory := Compiler.ZigAir.Memory.cleanup (BinaryPreludeTests.ready safety false).memory.memory.nextId reached.memory.memory',
             'memory := Compiler.ZigAir.Memory.cleanup ((BinaryPreludeTests.ready safety false).memory.memory.nextId + 1) reached.memory.memory', 1),
            ('wrong-parent-handoff',
             'some (parent safety).normalized, true⟩⟩) := by',
             'some (parent safety).normalized, false⟩⟩) := by', 1),
        )),
        ('frame',
         'import Compiler.Extraction.InternerNativeLocalTests\n'
         'set_option pp.maxSteps 8\nset_option pp.deepTerms false\n'
         'open Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeLocal.Tests\n'
         'open Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall\n'
         'open Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native\n'
         'open Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem\n'
         'attribute [local irreducible] localReturned copied rootArguments reduced\n'
         'example (safety : Bool) (id : Nat) (cell : Compiler.ZigAir.Memory.Allocation)\n'
         '    (found : (parent safety).taken.2.world.memory.memory.heap.lookup id = some cell) :\n'
         '    (localReturned safety).2.memory.memory.heap.lookup id = some cell :=\n'
         '  (local_native safety).2.2.2.1 id cell found\n'
         'example (safety : Bool) :\n'
         '    NativeGraph.Facts safety 7 6 ⟨ReachablePrefixTests.backing, 0⟩ 5 (reduced safety).2 (BinaryPreludeTests.rows safety false) :=\n'
         '  (reduced_native safety).1\n', (
            ('stale-parent-lifetime', '(localReturned safety).2.memory.memory.heap.lookup id = some cell :=',
             '(localReturned safety).2.memory.memory.heap.lookup (id + 1) = some cell :=', 1),
            ('wrong-final-native-owner', 'NativeGraph.Facts safety 7 6', 'NativeGraph.Facts safety 7 7', 1),
        )),
        # Reuse the checked complete execution; mutation controls alter its
        # public conclusions without re-evaluating every closed prefix. The
        # executable route itself is mutated by the input and forwarding gates.
        ('postconditions',
         'import Compiler.Extraction.InternerNativeLocalTests\n'
         'open Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeLocal.Tests\n'
         'open Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall\n'
         'example (safety : Bool) (depth : Nat) : (program safety (depth + 2)).1 = .ok 4 :=\n'
         '  (program_contract safety depth).1\n'
         'example (safety : Bool) (depth : Nat) :\n'
         '    (program safety (depth + 2)).2.memory.memory.heap.lookup localSource.allocation = none :=\n'
         '  (program_contract safety depth).2.2.1\n'
         'example (safety : Bool) (depth : Nat) :\n'
         '    (program safety (depth + 2)).2.memory.effects.keys (parent safety).key = some ⟨30, 4⟩ :=\n'
         '  (program_contract safety depth).2.2.2.2.2.1\n'
         'example (safety : Bool) : ordinary (program safety 1).1 = false :=\n'
         '  (exhaustion_retained safety).1\n', (
            ('wrong-result', '.1 = .ok 4 :=', '.1 = .ok 0 :=', 1),
            ('wrong-published-owner', '= some ⟨30, 4⟩ :=', '= some ⟨29, 4⟩ :=', 1),
            ('retain-local', 'localSource.allocation = none :=', 'localSource.allocation ≠ none :=', 1),
            ('exhaustion-ordinary', 'ordinary (program safety 1).1 = false :=',
             'ordinary (program safety 1).1 = true :=', 1),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    records = []
    for group, text, changes in mutation_cases():
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous named-local mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'native-local-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'native-local-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
