#!/usr/bin/env python3
"""Connect named and borrowed views to native item construction and child return.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
import constructor_argument_checks as arguments
import borrowed_constructor_checks as borrowed
import extract_local_arguments as local
import constructor_inventory

NS = arguments.ITEM + 'ViewInput.'
TESTS = NS + 'Tests.'
NONEMPTY = arguments.ITEM + 'RecursiveNonemptyTests.'
BORROWED = arguments.ITEM + 'RecursiveBorrowedTests.'
GRAPH = arguments.OWNED + 'Insertion.Native.CallerGrowingChainTests.'
CLAIMS = [NS + name for name in ('forwards', 'borrowed_forwards', 'queried_input', 'local_input',
    'local_prepared', 'local_rejected', 'local_forwarded')]
CLAIMS += [TESTS + name for name in ('byte_site', 'comparison_sites', 'arithmetic_sites', 'shift_mask_site',
    'local_observed', 'local_constructor', 'local_failure', 'actual_view_child', 'graph_child_route',
    'actual_graph_child', 'publication_input')]
CLAIMS += [arguments.OWNED + 'LocalArguments.' + name for name in
    ('initPair_success', 'copy_storage', 'overwrite_success', 'prepare_storage')]


def bindings():
    inventory = constructor_inventory.check()
    return {'borrowed': borrowed.bindings(), 'namedLocal': local.check(),
            'constructors': arguments.bindings(), 'inventory': inventory,
            'scope': 'nine borrowed callbacks and named local continuation through complete item/caller; native query input and key separation',
            'nativeZigGateRun': False, 'completeNativeQueryAndGuardConnectionVerified': False,
            'completeConstructorDependencyClosureVerified': False, 'recursiveInductionVerified': False}


def audit(claims):
    required = {
        arguments.OWNED + 'LocalArguments.initPair_success': {arguments.OWNED + 'TemporaryArguments.writePair_success'},
        arguments.OWNED + 'LocalArguments.copy_storage': {arguments.OWNED + 'LocalArguments.initPair_success',
            arguments.OWNED + 'TemporaryMemory.allocated_array'},
        arguments.OWNED + 'LocalArguments.overwrite_success': {arguments.OWNED + 'TemporaryArguments.orderedStores_success',
            'Compiler.ZigAir.Memory.store_retains_shape'},
        arguments.OWNED + 'LocalArguments.prepare_storage': {arguments.OWNED + 'LocalArguments.copy_storage',
            arguments.OWNED + 'LocalArguments.overwrite_success'},
        NS + 'forwards': {NS + 'operation', arguments.ITEM + 'operation'},
        NS + 'borrowed_forwards': {NS + 'constructors', NS + 'operation'},
        NS + 'local_forwarded': {NS + 'constructors', NS + 'localOperation'},
        NS + 'queried_input': {arguments.OWNED + 'BorrowedQuery.Native.accepted',
            'Compiler.Extraction.Storage.operation_found', 'Compiler.Extraction.OwnedKeys.Apart'},
        NS + 'local_input': {arguments.OWNED + 'LocalArguments.prepare_verified',
            arguments.OWNED + 'LocalArguments.prepare_storage', arguments.ARGUMENTS + 'Prepared'},
        NS + 'local_prepared': {NS + 'localOperation', arguments.ITEM + 'operation', arguments.OWNED + 'TemporaryArguments.unwind'},
        NS + 'local_rejected': {NS + 'localOperation'},
        TESTS + 'byte_site': {'Compiler.Extraction.Dispatch.binaryStageWithInputs', NS + 'constructors'},
        TESTS + 'comparison_sites': {'Compiler.Extraction.Dispatch.unaryStageWithInputs', NS + 'constructors'},
        TESTS + 'arithmetic_sites': {'Compiler.Extraction.Dispatch.unaryStageWithInputs', NS + 'constructors'},
        TESTS + 'shift_mask_site': {'Compiler.Extraction.ShiftMasks.removeCoveredShiftMask', NS + 'constructors'},
        TESTS + 'local_constructor': {NS + 'local_input', NS + 'local_prepared', TESTS + 'local_observed'},
        TESTS + 'local_failure': {NS + 'local_rejected', arguments.OWNED + 'LocalArguments.Tests.rejected_second_load_keeps_allocation'},
        TESTS + 'actual_view_child': {NONEMPTY + 'child_allocation', NONEMPTY + 'child_result',
            NONEMPTY + 'held_after_child', GRAPH + 'GraphFacts.frame', arguments.ITEM + 'good_frame'},
        TESTS + 'graph_child_route': {NS + 'operation', BORROWED + 'childFull'},
        TESTS + 'actual_graph_child': {TESTS + 'graph_child_route', BORROWED + 'child_contract',
            BORROWED + 'held_after_child', BORROWED + 'xor_query', BORROWED + 'child_input'},
        TESTS + 'publication_input': {BORROWED + 'xor_contract', BORROWED + 'xor_input_at',
            arguments.ITEM + 'LiteralInput.Tests.published_borrow'},
    }
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError('native view input lost dependencies: ' + name + ': ' + ', '.join(sorted(missing)))
    return {'checkedDependencies': sorted(required), 'sourceBinding': bindings(),
            'namedLocalNativeInputDerived': True, 'borrowedCallbacksUseCompleteItemConstructor': True,
            'nativeQueryDerivesContentsAndKeySeparation': True, 'actualGraphBorrowSurvivesChildGrowthFailure': True,
            'completeNativeQueryAndGuardConnectionVerified': False, 'recursiveInductionVerified': False}


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    directory = ROOT / 'lean/Compiler/Extraction'
    model = (directory / 'InternerViewInput.lean').read_text()
    clients = (directory / 'InternerViewInputTests.lean').read_text()
    # The shared XOR/EQ execution is built, audited and replayed by the root.
    # Keep copied-boundary controls separate from that imported execution;
    # its reached borrow and parent frame have explicit controls below.
    start = clients.index('/-- Reuse the existing complete EQ child')
    end = clients.index('/-- Full XOR publication establishes', start)
    clients = clients[:start] + clients[end:]
    imports = list(dict.fromkeys(line for raw in (model, clients) for line in raw.splitlines()
        if line.startswith('import ') and line != 'import Compiler.Extraction.InternerViewInput'))
    text = '\n'.join(imports) + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n'
    # Graph-frame clients now import NativeGraph, which itself consumes
    # ViewInput. Keep the copied model and its clients in one distinct namespace
    # so controls exercise the copy without redeclaring the imported boundary.
    copied = without_imports(model) + '\n' + without_imports(clients)
    text += copied.replace('ConstructorItem.ViewInput', 'ConstructorItem.ViewInputControl')
    records = checked_controls(output, [mutation_check(output, 'view-input-unchanged', text, True, env, lean)])
    changes = (
        ('borrowed-offset', '(context.primitives source) context.queries source opcode values debug before\n  (ran.1, ran.2.world)',
         '(context.primitives source) context.queries ⟨source.allocation, 0, source.length⟩ opcode values debug before\n  (ran.1, ran.2.world)'),
        ('borrowed-address', 'operation context ⟨address, 0, values.length⟩ opcode values debug\n',
         'operation context ⟨address + 1, 0, values.length⟩ opcode values debug\n'),
        ('borrowed-extent', 'operation context ⟨address, 0, values.length⟩ opcode values debug\n',
         'operation context ⟨address, 0, 0⟩ opcode values debug\n'),
        ('skip-overwrite', 'match LocalArguments.zigLocal source selected repeated repeatedIsFirst before with',
         'match LocalArguments.zigLocal source selected repeated false before with'),
        ('local-rewinds-world', 'debug prepared)\n', 'debug before)\n'),
        ('local-erase-parent', '| (.ok target, prepared) => TemporaryArguments.unwind before.memory.memory.nextId',
         '| (.ok target, prepared) => TemporaryArguments.unwind 0'),
        ('local-forgets-overwrite',
         'context.queries target opcode (if repeatedIsFirst then [left, right].set selected repeated else [left, right]) debug prepared)',
         'context.queries target opcode [left, right] debug prepared)'),
        ('local-error-rewinds', '| (.error fault, reached) => (.error fault, reached)',
         '| (.error fault, reached) => (.error fault, before)'),
        ('borrowed-child-wrong-word', 'Good childSource [0] ((child safety).returnedWorld (failedWorld safety after)) ∧',
         'Good childSource [1] ((child safety).returnedWorld (failedWorld safety after)) ∧'),
    )
    for name, before, after in changes:
        if text.count(before) != 1:
            raise ValueError('ambiguous native view mutation: ' + name)
        records += checked_controls(output, [mutation_check(output, 'view-input-' + name,
            text.replace(before, after), False, env, lean)])
    reached = (
        'import Compiler.Extraction.InternerViewInputTests\n'
        'open Compiler.Algebraic Compiler.Extraction.Cache\n'
        'open Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall\n'
        'open Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem\n'
        'open RecursiveBorrowedTests\nopen RecursiveTests (debug)\n'
        'set_option pp.maxSteps 8\nset_option pp.deepTerms false\n'
        'attribute [local irreducible] childReturned childSource rootSource\n'
        'example (safety : Bool) : ∃ after,\n'
        '    ViewInput.operation (childContext safety) childSource 20 [0, 1] debug (child safety).before =\n'
        '      (.error (.language .outOfMemory), childReturned safety after) ∧\n'
        '    Good childSource [0, 1] (childReturned safety after) ∧\n'
        '    Held 7 rootSource [4] (parent safety).normalized (childReturned safety after) := by\n'
        '  obtain ⟨after, _, _, called, good, held, _⟩ := ViewInput.Tests.actual_graph_child safety\n'
        '  exact ⟨after, called, good, held⟩\n')
    records += checked_controls(output, [mutation_check(output, 'view-input-reached-graph-unchanged', reached, True, env, lean)])
    for name, before, after in (
            ('wrong-borrow', 'Good childSource [0, 1]', 'Good childSource [1, 0]'),
            ('wrong-parent', 'Held 7 rootSource [4]', 'Held 7 rootSource [0]')):
        if reached.count(before) != 1:
            raise ValueError('ambiguous reached graph mutation: ' + name)
        records += checked_controls(output, [mutation_check(output, 'view-input-reached-graph-' + name,
            reached.replace(before, after), False, env, lean)])
    return records
