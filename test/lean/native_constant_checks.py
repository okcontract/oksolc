#!/usr/bin/env python3
"""Audit native Push publication through the recursive child and parent return.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_zig_air_proofs import mutation_check
import constructor_argument_checks as arguments
import native_recursion_checks as recursive
import native_graph_checks as graph
import recursive_nonempty_checks as nonempty

TESTS = recursive.NS + 'ConstantTests.'
EQUAL = recursive.NS + 'EqualTests.'
CHILD = arguments.ITEM + 'RecursiveTests.'
CALL = arguments.ITEM + 'RecursiveTests.Call.'
CONSTANT = 'Compiler.Extraction.RepresentativeArray.Constant.'
CLAIMS = [TESTS + name for name in ('context_same', 'prefix_result', 'program_zero', 'zero_insertion', 'zero_equivalent', 'child_simplifier',
    'child_equivalent', 'parent_continuation', 'root_equivalent', 'program_equivalent',
    'program_contract', 'root_one', 'program_one', 'exhaustion_retained')]
CLAIMS += [CONSTANT + 'Data.frame', graph.FACTS + 'data_after', CALL + 'spare_native']
CLAIMS += [EQUAL + name for name in ('child_equivalent', 'parent_continuation', 'root_equivalent',
    'program_equivalent', 'program_contract', 'root_one', 'program_one', 'exhaustion_retained', 'program_zero')]


def bindings():
    return {'constructors': nonempty.bindings(), 'recursiveFamily': recursive.bindings(),
            'scope': 'native initialization -> four full operation constructors -> Push-zero publication -> EQ parent -> recursive ISZERO nonempty growth OOM '
                     '-> child, parent and outer cleanup; also EQ(x,x) -> Push-one growth OOM in the same context; '
                     'constant queries derived from native graph fields',
            'allSufficientDepths': True, 'completeNativeGraphInvariantVerified': False,
            'generalRecursiveInductionVerified': False}


def audit(claims):
    required = {
        TESTS + 'prefix_result': {TESTS + 'context_same', recursive.TESTS + 'prefix_result'},
        CONSTANT + 'Data.frame': {'Compiler.Extraction.AssemblyItem.Fields.readTyped_frame'},
        graph.FACTS + 'data_after': {graph.NS + 'data_frame'},
        CALL + 'spare_native': {graph.FACTS + 'data_after',
            arguments.OWNED + 'Insertion.Native.CallerInput.spare_success'},
        TESTS + 'zero_insertion': {arguments.OWNED + 'Insertion.Native.insert'},
        TESTS + 'zero_equivalent': {TESTS + 'zero_insertion', CALL + 'route',
            nonempty.TESTS + 'zero_contract', recursive.NS + 'constant_succ'},
        TESTS + 'child_simplifier': {recursive.NS + 'dispatcher_snapshot', graph.NS + 'Facts.reads', nonempty.TESTS + 'iszero_miss', nonempty.TESTS + 'child_established'},
        TESTS + 'child_equivalent': {TESTS + 'child_simplifier', CALL + 'route',
            recursive.NS + 'operation_succ', arguments.ARGUMENTS + 'operation_prepared'},
        TESTS + 'parent_continuation': {recursive.NS + 'dispatcher_snapshot', graph.NS + 'Facts.reads', TESTS + 'child_equivalent', nonempty.TESTS + 'iszero_failure',
            nonempty.TESTS + 'parent_zero'},
        TESTS + 'root_equivalent': {TESTS + 'parent_continuation', CALL + 'route',
            nonempty.TESTS + 'child_contract', arguments.ARGUMENTS + 'operation_prepared'},
        TESTS + 'program_equivalent': {TESTS + 'prefix_result', TESTS + 'zero_equivalent', TESTS + 'root_equivalent',
            'Compiler.Algebraic.Effect.bind_success'},
        TESTS + 'program_contract': {TESTS + 'program_equivalent', nonempty.TESTS + 'complete_contract',
            graph.FACTS + 'native', graph.NS + 'Facts.constants', graph.NS + 'Facts.operations',
            TESTS + 'child_equivalent', nonempty.TESTS + 'held_after_child', nonempty.TESTS + 'parent_zero'},
        TESTS + 'root_one': {recursive.NS + 'dispatcher_snapshot', graph.NS + 'Facts.reads', nonempty.TESTS + 'iszero_failure', nonempty.TESTS + 'parent_zero',
            recursive.NS + 'exhausted', CALL + 'route'},
        TESTS + 'program_one': {TESTS + 'prefix_result', TESTS + 'zero_equivalent', TESTS + 'root_one'},
        TESTS + 'exhaustion_retained': {TESTS + 'program_one', nonempty.TESTS + 'parent_established',
            nonempty.TESTS + 'parent_zero', graph.FACTS + 'native'},
        EQUAL + 'child_equivalent': {recursive.TESTS + 'same_call', recursive.NS + 'constant_succ',
            CHILD + 'child_established', CHILD + 'childFull'},
        EQUAL + 'parent_continuation': {recursive.NS + 'dispatcher_snapshot', graph.NS + 'Facts.reads',
            CHILD + 'equal_failure', CHILD + 'parent_constant', EQUAL + 'child_equivalent', CALL + 'simplify_error'},
        EQUAL + 'root_equivalent': {EQUAL + 'parent_continuation', CHILD + 'parent_continuation',
            recursive.TESTS + 'same_call', CHILD + 'complete_route', arguments.ARGUMENTS + 'operation_prepared'},
        EQUAL + 'program_equivalent': {TESTS + 'prefix_result', TESTS + 'zero_equivalent', EQUAL + 'root_equivalent',
            'Compiler.Algebraic.Effect.bind_success'},
        EQUAL + 'program_contract': {EQUAL + 'program_equivalent', CHILD + 'complete_contract', graph.FACTS + 'native',
            EQUAL + 'child_equivalent', CHILD + 'child_contract', CHILD + 'held_after_child'},
        EQUAL + 'root_one': {recursive.NS + 'dispatcher_snapshot', graph.NS + 'Facts.reads', CHILD + 'equal_failure',
            CHILD + 'parent_constant', recursive.NS + 'exhausted', CALL + 'simplify_error', CALL + 'route'},
        EQUAL + 'program_one': {TESTS + 'prefix_result', TESTS + 'zero_equivalent', EQUAL + 'root_one'},
        EQUAL + 'exhaustion_retained': {EQUAL + 'program_one', CHILD + 'parent_established', graph.FACTS + 'native'},
    }
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError('native constant composition lost dependencies: ' + name + ': ' + ', '.join(sorted(missing)))
    return {'checkedDependencies': sorted(required), 'sourceBinding': bindings(),
            'pushDataDerivedFromPublicationAndFrames': True, 'nativeConstantQueriesDerivedForAllIds': True,
            'oneContextForConstantAndRecursiveFailure': True, 'allSufficientDepthsVerified': True,
            'exhaustionRetainsPublishedPushAndLiveParent': True,
            'equalOperandsConstantChildUsesSameInitializedContext': True,
            'equalOperandsRetainsOriginalCallerArray': True,
            'initialPrefixIsSelectedInsertionContinuations': False,
            'completeNativeGraphInvariantVerified': False, 'completeConstructorDependencyClosureVerified': False,
            'successfulRecursiveGrowthVerified': False, 'completePublicationRollbackVerified': False,
            'recursiveInductionVerified': False, 'composedProductionTheoremVerified': False}


def mutation_cases():
    prefix = (
        'import Compiler.Extraction.InternerNativeConstantTests\n'
        'open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage\n'
        'open Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall\n'
        'open Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem\n'
        'open Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ConstantTests\n'
        'open RecursiveNonemptyTests\nopen RecursiveTests (debug)\n'
        'open Compiler.Extraction.RepresentativeArray\n'
        'set_option pp.maxSteps 8\nset_option pp.deepTerms false\n'
        'attribute [local irreducible] children ready ReachablePrefixTests.sequence Constant.value Compiler.Extraction.Storage.ConstantRead.run\n')
    equal = (
        'import Compiler.Extraction.InternerNativeConstantTests\n'
        'open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage\n'
        'open Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall\n'
        'open Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem\n'
        'open NativeRecursion.EqualTests RecursiveTests\n'
        'open NativeRecursion.ConstantTests (children)\n'
        'set_option pp.maxSteps 8\nset_option pp.deepTerms false\n'
        'attribute [local irreducible] children RecursiveNonemptyTests.ready rootArguments ReachablePrefixTests.sequence\n')
    return (
        ('equal-program', equal +
         'example (safety : Bool) (depth : Nat) :\n'
         '    (do let _ ← ReachablePrefixTests.sequence (children safety (depth + 2)) 3\n'
         '        let _ ← (children safety (depth + 2)).constant 0 debug\n'
         '        (children safety (depth + 2)).operation 20 [0, 0] debug) (Insertion.Native.CallerInputTests.world safety) = complete safety :=\n'
         '  program_equivalent safety depth\n', (
            ('wrong-operands', '.operation 20 [0, 0] debug)', '.operation 20 [0, 4] debug)', 1),
            ('truncated-prefix', '(children safety (depth + 2)) 3\n', '(children safety (depth + 2)) 2\n', 1),
            ('wrong-push', '.constant 0 debug\n', '.constant 1 debug\n', 1),
            ('stale-world', '(children safety (depth + 2)).operation 20 [0, 0] debug)',
             '(fun _ => (children safety (depth + 2)).operation 20 [0, 0] debug (RecursiveNonemptyTests.initial safety)))', 1),
        )),
        ('equal-postconditions', equal +
         'example (safety : Bool) (depth : Nat) : (program safety (depth + 2)).1 = .error (.language .outOfMemory) :=\n'
         '  (program_contract safety depth).1\n'
         'example (safety : Bool) (depth : Nat) :\n'
         '    (program safety (depth + 2)).2.memory.memory.heap.lookup rootSource.allocation = none :=\n'
         '  (program_contract safety depth).2.2.1\n'
         'example (safety : Bool) (depth : Nat) :\n'
         '    Good (Insertion.Native.CallerInputTests.argumentView false) [0] (program safety (depth + 2)).2 :=\n'
         '  (program_contract safety depth).2.2.2.2.1\n', (
            ('wrong-result', '.1 = .error (.language .outOfMemory) :=', '.1 = .error (.language .capacity) :=', 1),
            ('retain-literal', 'rootSource.allocation = none :=', 'rootSource.allocation ≠ none :=', 1),
            ('wrong-caller-value', 'argumentView false) [0]', 'argumentView false) [1]', 1),
        )),
        ('equal-child', equal +
         'example (safety : Bool) (depth : Nat) :\n'
         '    ∃ after, (children safety (depth + 1)).constant 1 debug (child safety).before =\n'
         '        (.error (.language .outOfMemory), childReturned safety after) ∧\n'
         '      Held 7 rootSource [0, 0] (parent safety).normalized (childReturned safety after) ∧\n'
         '      (∀ id cell, (parent safety).taken.2.world.memory.memory.heap.lookup id = some cell →\n'
         '        (childReturned safety after).memory.memory.heap.lookup id = some cell) :=\n'
         '  (program_contract safety depth).2.2.2.2.2.2\n', (
            ('wrong-child', '.constant 1 debug (child safety).before', '.constant 0 debug (child safety).before', 1),
            ('wrong-parent-values', 'Held 7 rootSource [0, 0]', 'Held 7 rootSource [0, 1]', 1),
            ('lost-parent-allocation', '(childReturned safety after).memory.memory.heap.lookup id = some cell',
             '(childReturned safety after).memory.memory.heap.lookup id = none', 1),
        )),
        ('equal-exhaustion', equal +
         'example (safety : Bool) : program safety 0 =\n'
         '    (.error (.language .unsupported), Insertion.Native.CallerInputTests.world safety) := program_zero safety\n'
         'example (safety : Bool) : program safety 1 =\n'
         '    (.error (.language .unsupported), (parent safety).taken.2.world) := program_one safety\n'
         'example (safety : Bool) : ordinary (program safety 1).1 = false :=\n'
         '  (exhaustion_retained safety).1\n'
         'example (safety : Bool) : Held 7 rootSource [0, 0] (parent safety).normalized (program safety 1).2 :=\n'
         '  (exhaustion_retained safety).2.1\n', (
            ('exhaustion-as-oom', '.language .unsupported', '.language .outOfMemory', 2),
            ('published-on-exhaustion', 'Insertion.Native.CallerInputTests.world safety)', 'RecursiveNonemptyTests.ready safety)', 1),
            ('erase-reached-parent', '(parent safety).taken.2.world)', 'old safety)', 1),
            ('exhaustion-ordinary', 'ordinary (program safety 1).1 = false :=', 'ordinary (program safety 1).1 = true :=', 1),
            ('wrong-held-values', 'Held 7 rootSource [0, 0]', 'Held 7 rootSource [1, 0]', 1),
        )),
        ('program', prefix +
         'example (safety : Bool) (depth : Nat) :\n'
         '    (do let _ ← ReachablePrefixTests.sequence (children safety (depth + 2)) 3\n'
         '        let id ← (children safety (depth + 2)).constant 0 debug\n'
         '        (children safety (depth + 2)).operation 20 [0, id] debug) (Insertion.Native.CallerInputTests.world safety) = complete safety :=\n'
         '  program_equivalent safety depth\n', (
            ('wrong-returned-id', '.operation 20 [0, id] debug)', '.operation 20 [0, 0] debug)', 1),
            ('truncated-prefix', '(children safety (depth + 2)) 3\n', '(children safety (depth + 2)) 2\n', 1),
            ('stale-world', '(children safety (depth + 2)).operation 20 [0, id] debug)',
             '(fun _ => (children safety (depth + 2)).operation 20 [0, id] debug (initial safety)))', 1),
        )),
        ('postconditions', prefix +
         'example (safety : Bool) (depth : Nat) : (program safety (depth + 2)).1 = .error (.language .outOfMemory) :=\n'
         '  (program_contract safety depth).1\n'
         'example (safety : Bool) (depth : Nat) :\n'
         '    (program safety (depth + 2)).2.memory.memory.heap.lookup rootSource.allocation = none :=\n'
         '  (program_contract safety depth).2.2.1\n'
         'example (safety : Bool) (depth : Nat) (id : NodeId) :\n'
         '    Constant.value (program safety (depth + 2)).2.memory.memory (Owner.headerAddress ⟨6, 0⟩) id =\n'
         '      .ok (Compiler.Extraction.Storage.constantProgram.run (rows safety) id) :=\n'
         '  (program_contract safety depth).2.2.2.2.2.1 id\n'
         'example (safety : Bool) : ordinary (program safety 1).1 = false :=\n'
         '  (exhaustion_retained safety).1\n'
         'example (safety : Bool) :\n'
         '    Constant.value (program safety 1).2.memory.memory (Owner.headerAddress ⟨6, 0⟩) 4 = .ok (.ok (some 0)) :=\n'
         '  (exhaustion_retained safety).2.2.2\n', (
            ('wrong-result', '.1 = .error (.language .outOfMemory) :=', '.1 = .error (.language .capacity) :=', 1),
            ('retain-parent-literal', 'rootSource.allocation = none :=', 'rootSource.allocation ≠ none :=', 1),
            ('wrong-native-constant', 'Storage.constantProgram.run (rows safety) id',
             'Storage.constantProgram.run (rows safety) (id + 1)', 1),
            ('exhaustion-ordinary', 'ordinary (program safety 1).1 = false :=',
             'ordinary (program safety 1).1 = true :=', 1),
            ('wrong-push-value', '= .ok (.ok (some 0)) :=', '= .ok (.ok (some 1)) :=', 1),
        )),
        ('reached-parent', prefix +
         'example (safety : Bool) (depth : Nat) :\n'
         '    ∃ after, (children safety (depth + 1)).operation 21 [0] debug (parent safety).taken.2.world =\n'
         '        (.error (.language .outOfMemory), childReturned safety after) ∧\n'
         '      Held 7 rootSource [0, 4] (parent safety).normalized (childReturned safety after) ∧\n'
         '      (∀ id cell, (parent safety).taken.2.world.memory.memory.heap.lookup id = some cell →\n'
         '        (childReturned safety after).memory.memory.heap.lookup id = some cell) :=\n'
         '  (program_contract safety depth).2.2.2.2.2.2.2.2\n', (
            ('wrong-parent-values', 'Held 7 rootSource [0, 4]', 'Held 7 rootSource [4, 0]', 1),
            ('lost-parent-allocation', '(childReturned safety after).memory.memory.heap.lookup id = some cell',
             '(childReturned safety after).memory.memory.heap.lookup id = none', 1),
        )),
        ('initial-exhaustion', prefix +
         'example (safety : Bool) : program safety 0 =\n'
         '    (.error (.language .unsupported), Insertion.Native.CallerInputTests.world safety) := program_zero safety\n', (
            ('exhaustion-as-oom', '.language .unsupported', '.language .outOfMemory', 1),
            ('published-on-exhaustion', 'Insertion.Native.CallerInputTests.world safety)', 'ready safety)', 1),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    records = []
    for group, text, changes in mutation_cases():
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous native constant mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'native-constant-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'native-constant-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
