#!/usr/bin/env python3
"""Audit actual recursive growth, parent publication and outer cleanup.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from pathlib import Path
from check_zig_air_proofs import mutation_check
import constructor_argument_checks as arguments
import native_recursion_checks as recursive
import native_graph_checks as graph
import recursive_nonempty_checks as nonempty

TESTS = arguments.ITEM + 'RecursiveGrowthTests.'
CALL = arguments.ITEM + 'RecursiveTests.Call.'
PUBLICATION = arguments.OWNED + 'Publication.'
NATIVE = arguments.OWNED + 'Insertion.Native.'
CALLER = arguments.OWNED + 'Caller.'
CLAIMS = [TESTS + name for name in (
    'prefix_equivalent', 'prefix_result', 'program_zero',
    'installed_valid', 'backing_fits', 'child_native', 'prefix_keys', 'prefix_geometry', 'parent_input', 'child_entry',
    'child_simplifier', 'child_result', 'child_contract', 'parent_publication',
    'parent_ownership', 'parent_simplifier', 'parent_continuation', 'root_result', 'parent_mark', 'root_native', 'zero_insertion',
    'zero_equivalent', 'program_equivalent', 'selected_words', 'reached_words',
    'failed_root_result', 'failed_root_native', 'program_failed_equivalent', 'program_failed_words',
    'program_contract', 'program_inputs', 'root_one', 'program_one', 'exhaustion_retained')]
CLAIMS += [PUBLICATION + 'publish_absent', graph.NS + 'Facts.publish_absent', graph.NS + 'Facts.release',
           nonempty.TESTS + 'iszero_result', graph.NS + 'Facts.operand', graph.NS + 'Facts.operand_after_append']

CLAIMS += [NATIVE + 'CallerInput.graph_custody', NATIVE + 'CallerInput.graph_custody_after_growth',
           NATIVE + 'CallerInput.source_private_after_publication', CALLER + 'GraphCustody.publication']
CLAIMS += [graph.NS + 'Facts.' + name for name in ('publication_completed', 'publish', 'finish_publication')]
CLAIMS += [arguments.OWNED + 'Good.backed']


def bindings():
    return {'constructors': nonempty.bindings(), 'recursiveFamily': recursive.bindings(),
            'scope': 'native initialization -> four full operation constructors -> Push-zero publication -> EQ parent -> actual recursive ISZERO with '
                     'nonempty relocation and publication -> parent publication success/OOM and all outer cleanup',
            'allSufficientDepths': True, 'completeNativeGraphInvariantVerified': False,
            'generalRecursiveInductionVerified': False}


def audit(claims):
    required = {
        TESTS + 'prefix_equivalent': {recursive.TESTS + 'same_call', recursive.TESTS + 'miss_continuation',
            recursive.TESTS + 'prefix_insertion', arguments.ITEM + 'ReachablePrefixTests.entered',
            arguments.ITEM + 'ReachablePrefixTests.simplified', recursive.NS + 'operation_succ'},
        TESTS + 'prefix_result': {TESTS + 'prefix_equivalent', arguments.ITEM + 'ReachablePrefixTests.step_result'},
        NATIVE + 'CallerInput.graph_custody': {NATIVE + 'CallerInput.custody', CALLER + 'Origin.fresh'},
        NATIVE + 'CallerInput.graph_custody_after_growth': {NATIVE + 'CallerInput.custody_after_growth',
            CALLER + 'Origin.registry', CALLER + 'GraphCustody.operands', 'Compiler.ZigAir.Memory.valid_lookup'},
        NATIVE + 'CallerInput.source_private_after_publication': {CALLER + 'Origin.source_private_after_publication', CALLER + 'Origin.freshNative',
            arguments.OWNED + 'Good.backed', 'Compiler.Extraction.OwnedKeys.store'},
        arguments.OWNED + 'Good.backed': {'Compiler.ZigAir.Memory.access_success_region'},
        CALLER + 'GraphCustody.publication': {CALLER + 'Custody.apart'},
        graph.NS + 'Facts.publication_completed': {'Compiler.Extraction.OwnedKeys.Physical.Completed.preserves',
            'Compiler.Extraction.OwnedKeys.Physical.Completed.graph_resident',
            'Compiler.Extraction.OwnedKeys.Physical.Completed.non_arguments_frame',
            'Compiler.Extraction.RepresentativeArray.DescriptorRelation.frame'},
        graph.NS + 'Facts.publish': {CALLER + 'GraphCustody.publication', PUBLICATION + 'publish_success',
            PUBLICATION + 'publish_oom', graph.NS + 'Facts.publication_completed', PUBLICATION + 'completion_held'},
        graph.NS + 'Facts.finish_publication': {graph.NS + 'Facts.publish', arguments.OWNED + 'finish_taken',
            graph.NS + 'Facts.cleanup_post', graph.NS + 'Facts.release', 'Compiler.Extraction.Memory.Arguments.Normalization.free_empty',
            'Compiler.Extraction.Memory.Arguments.Normalization.free_valid'},
        TESTS + 'installed_valid': {CALL + 'installed_facts', arguments.OWNED + 'Insertion.Native.CallerInput.prepare'},
        TESTS + 'backing_fits': {TESTS + 'installed_valid'},
        TESTS + 'parent_input': {arguments.ARGUMENTS + 'Prepared.native_apart',
            arguments.ARGUMENTS + 'Prepared.key_apart', recursive.NS + 'InputFrame.caller',
            nonempty.TESTS + 'parent_literal', nonempty.TESTS + 'parent_established'},
        TESTS + 'child_entry': {recursive.NS + 'CallFrame.enter_child', recursive.NS + 'CallFrame.arguments',
            TESTS + 'parent_input', arguments.ARGUMENTS + 'Prepared.key_apart'},
        TESTS + 'child_native': {TESTS + 'backing_fits', CALL + 'growing_native',
            arguments.OWNED + 'Insertion.Native.CallerInput.growing_success',
            arguments.OWNED + 'Insertion.Native.CallerInput.checked_execution', graph.FACTS + 'data_after'},
        TESTS + 'child_simplifier': {recursive.NS + 'dispatcher_snapshot', graph.NS + 'Facts.reads', nonempty.TESTS + 'iszero_miss', nonempty.TESTS + 'child_established'},
        TESTS + 'child_result': {TESTS + 'child_simplifier', CALL + 'route',
            arguments.OWNED + 'Insertion.Native.CallerInput.finish_native',
            recursive.NS + 'operation_succ', arguments.ARGUMENTS + 'operation_prepared'},
        TESTS + 'child_contract': {TESTS + 'child_entry', recursive.NS + 'CallFrame.locals', recursive.NS + 'CallFrame.cleanup', TESTS + 'child_native', TESTS + 'child_result', graph.FACTS + 'cleanup',
            TESTS + 'prefix_keys', TESTS + 'prefix_geometry', NATIVE + 'CallerInput.graph_custody',
            NATIVE + 'CallerInput.graph_custody_after_growth', NATIVE + 'CallerInput.prepare',
            NATIVE + 'CallerInput.source_private_after_publication', arguments.ARGUMENTS + 'Prepared.key_apart',
            TESTS + 'parent_input', arguments.ARGUMENTS + 'Prepared.native_apart', arguments.OWNED + 'Good.backed'},
        PUBLICATION + 'publish_absent': {PUBLICATION + 'publish', 'Compiler.Extraction.OwnedKeys.Code.execute'},
        graph.NS + 'Facts.publish_absent': {PUBLICATION + 'publish_absent',
            'Compiler.Extraction.OwnedKeys.after_live', 'Compiler.Extraction.OwnedKeys.store_unique',
            'Compiler.Extraction.OwnedKeys.store_apart'},
        graph.NS + 'Facts.release': {'Compiler.Extraction.Memory.Arguments.ReleasePost.frame',
            'Compiler.Extraction.RepresentativeArray.DescriptorRelation.frame',
            'Compiler.Extraction.AssemblyItem.Query.frame', 'Compiler.ZigAir.Memory.Heap.lookup_ne_of_type_ne'},
        TESTS + 'parent_ownership': {CALLER + 'GraphCustody.operands', CALLER + 'Custody.apart', TESTS + 'prefix_keys'},
        TESTS + 'parent_simplifier': {recursive.NS + 'dispatcher_snapshot', graph.NS + 'Facts.reads',
            nonempty.TESTS + 'iszero_result'},
        TESTS + 'failed_root_result': {TESTS + 'parent_simplifier', CALL + 'route', recursive.NS + 'operation_succ',
            arguments.ARGUMENTS + 'operation_prepared'},
        TESTS + 'failed_root_native': {TESTS + 'child_contract', TESTS + 'parent_ownership',
            TESTS + 'failed_root_result', graph.NS + 'Facts.finish_publication', graph.NS + 'Facts.release',
            arguments.OWNED + 'finish_taken', graph.NS + 'Facts.cleanup',
            arguments.ARGUMENTS + 'Prepared.retire'},
        TESTS + 'program_failed_equivalent': {TESTS + 'prefix_result', TESTS + 'zero_equivalent', 'Compiler.Algebraic.Effect.bind_success'},
        TESTS + 'program_failed_words': {TESTS + 'program_failed_equivalent', TESTS + 'failed_root_native',
            TESTS + 'selected_words'},
        TESTS + 'parent_publication': {graph.NS + 'Facts.publish', TESTS + 'prefix_keys',
            nonempty.TESTS + 'parent_established', nonempty.TESTS + 'child_established'},
        TESTS + 'parent_continuation': {recursive.NS + 'dispatcher_snapshot', graph.NS + 'Facts.reads', nonempty.TESTS + 'iszero_result', nonempty.TESTS + 'parent_zero'},
        TESTS + 'root_result': {TESTS + 'parent_continuation', CALL + 'route', recursive.NS + 'operation_succ',
            arguments.ARGUMENTS + 'operation_prepared'},
        TESTS + 'parent_mark': {nonempty.TESTS + 'parent_literal', arguments.ARGUMENTS + 'Prepared.counter'},
        TESTS + 'root_native': {TESTS + 'child_contract', TESTS + 'parent_publication', TESTS + 'root_result',
            graph.NS + 'Facts.cleanup', arguments.ARGUMENTS + 'Prepared.retire'},
        TESTS + 'zero_equivalent': {TESTS + 'zero_insertion', CALL + 'route', nonempty.TESTS + 'zero_contract'},
        TESTS + 'program_equivalent': {TESTS + 'prefix_result', TESTS + 'zero_equivalent', 'Compiler.Algebraic.Effect.bind_success'},
        TESTS + 'reached_words': {TESTS + 'root_native', TESTS + 'selected_words'},
        graph.NS + 'Facts.operand': {arguments.OWNED + 'BorrowedQuery.Native.observed',
            arguments.OWNED + 'BorrowedQuery.accepted_good', arguments.ITEM + 'ShiftInput.operand_good'},
        graph.NS + 'Facts.operand_after_append': {graph.NS + 'Facts.operand', 'Compiler.Extraction.Storage.operation_found'},
        TESTS + 'program_inputs': {TESTS + 'program_contract', graph.NS + 'Facts.operand_after_append'},
        TESTS + 'program_contract': {TESTS + 'program_equivalent', TESTS + 'root_native', TESTS + 'reached_words',
            graph.NS + 'Facts.constants', graph.NS + 'Facts.operations'},
        TESTS + 'root_one': {recursive.NS + 'dispatcher_snapshot', graph.NS + 'Facts.reads', nonempty.TESTS + 'iszero_failure', nonempty.TESTS + 'parent_zero',
            recursive.NS + 'exhausted', CALL + 'route'},
        TESTS + 'program_one': {TESTS + 'prefix_result', TESTS + 'zero_equivalent', TESTS + 'root_one'},
        TESTS + 'exhaustion_retained': {TESTS + 'program_one', graph.FACTS + 'native'},
    }
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError('recursive growth lost dependencies: ' + name + ': ' + ', '.join(sorted(missing)))
    return {'checkedDependencies': sorted(required), 'sourceBinding': bindings(),
            'actualRecursiveChildRelocationAndParentPublicationVerified': True,
            'parentPublicationOwnershipDerivedAtChildReturn': True,
            'parentSourcePrivacyFromLiteralAndChildNativeFreshness': True,
            'generalPublicationReplacementAndOuterCleanupFromReachedFrame': True,
            'parentOperandSeparationFromActualChildDuplicate': True, 'argumentContentInequalityPremise': False,
            'parentProbeOomRetainsChildGrowthAndKey': True, 'parentProbeOomCleansNormalizedAndLiteral': True, 'allSufficientDepthsVerified': True,
            'finalNativeQueriesAndKnownWordsDerived': True, 'oldOperandReadsDerivedAfterRelocation': True, 'exhaustionRetainsLiveParent': True,
            'initialPrefixIsSelectedInsertionContinuations': False,
            'completeConstructorDependencyClosureVerified': False, 'completeNativeGraphInvariantVerified': False,
            'completePublicationRollbackVerified': False, 'recursiveInductionVerified': False,
            'composedProductionTheoremVerified': False}


def mutation_cases():
    prefix = (
        'import Compiler.Extraction.InternerRecursiveGrowthTests\n'
        'open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage\n'
        'open Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall\n'
        'open Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem\n'
        'open Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveGrowthTests\n'
        'open RecursiveNonemptyTests\nopen RecursiveTests (debug)\n'
        'open Compiler.Extraction.RepresentativeArray\n'
        'set_option pp.maxSteps 8\nset_option pp.deepTerms false\n'
        'attribute [local irreducible] program root children ready ReachablePrefixTests.sequence RecursiveTests.Call.normalized Constant.value Compiler.Extraction.Storage.ConstantRead.run\n')
    execution = prefix + (
        'example (safety : Bool) (depth : Nat) :\n'
        '    (do let _ ← ReachablePrefixTests.sequence (children safety (depth + 2)) 3\n'
        '        let id ← (children safety (depth + 2)).constant 0 debug\n'
        '        (children safety (depth + 2)).operation 20 [0, id] debug) (Insertion.Native.CallerInputTests.world safety) = root safety (depth + 2) :=\n'
        '  by simpa only [program] using program_equivalent safety depth\n')
    source_regions = prefix + (
        'open Compiler.ZigAir.Memory.WordArray\n'
        'open Compiler.Extraction.Memory.Arguments.Normalization\n'
        'attribute [local irreducible] NativeRecursion.InputFrame RecursiveTests.Call.constructed\n'
        'example (values : List NodeId) (before after : World (Publication.Effects Nat))\n'
        '    (source : View) (ready : Arguments.Prepared values before source after)\n'
        '    (valid : Valid before.memory) (id : Nat) (cell : Compiler.ZigAir.Memory.Allocation)\n'
        '    (found : before.memory.memory.heap.lookup id = some cell) (nonempty : source.length ≠ 0) :\n'
        '    source.allocation ≠ id :=\n'
        '  ready.native_apart values before after source valid id cell found nonempty\n'
        'example (source : View) (values : List NodeId) (before : World (Publication.Effects Nat))\n'
        '    (good : Good source values before) (nonempty : source.length ≠ 0) :\n'
        '    ∃ cell, before.memory.memory.heap.lookup source.allocation = some cell := good.backed nonempty\n'
        'example (safety : Bool) : NativeRecursion.InputFrame safety 7 6 (rows safety) rootSource [0, 4]\n'
        '    (parent safety).normalized (parent safety).taken.2.world := (parent_input safety).1\n')
    post = prefix + (
        'example (safety : Bool) (depth : Nat) : (program safety (depth + 2)).1 = .ok 5 :=\n'
        '  (program_contract safety depth).1\n'
        'example (safety : Bool) (depth : Nat) :\n'
        '    NativeGraph.Facts safety 7 6 ⟨backing safety, 0⟩ 13 (program safety (depth + 2)).2 (appendedRows safety) :=\n'
        '  (program_contract safety depth).2.1\n'
        'example (safety : Bool) (depth : Nat) :\n'
        '    (program safety (depth + 2)).2.memory.memory.heap.lookup rootSource.allocation = none :=\n'
        '  (program_contract safety depth).2.2.1\n'
        'example (safety : Bool) (depth : Nat) :\n'
        '    (program safety (depth + 2)).2.memory.memory.heap.lookup ReachablePrefixTests.backing = none :=\n'
        '  (program_contract safety depth).2.2.2.2.1\n'
        'example (safety : Bool) (depth : Nat) :\n'
        '    (program safety (depth + 2)).2.memory.effects.keys (parent safety).key = some ⟨(parent safety).normalized.address, 5⟩ :=\n'
        '  (program_contract safety depth).2.2.2.2.2.1\n'
        'example (safety : Bool) (depth : Nat) : (program safety (depth + 2)).2.graph.read 5 = some 1 :=\n'
        '  (program_contract safety depth).2.2.2.2.2.2.1\n'
        'example (safety : Bool) : ordinary (program safety 1).1 = false :=\n'
        '  (exhaustion_retained safety).1\n')
    failed = prefix + (
        'example (safety : Bool) (depth : Nat) : (program safety (depth + 2) false).1 = .error (.language .outOfMemory) :=\n'
        '  (program_failed_words safety depth).1\n'
        'example (safety : Bool) (depth : Nat) : (program safety (depth + 2) false).2.graph.read 5 = some 1 :=\n'
        '  (program_failed_words safety depth).2.1\n'
        'example (safety : Bool) (depth : Nat) :\n'
        '    (failedRoot safety (depth + 2)).2.memory.effects.keys (parent safety).key = none :=\n'
        '  (failed_root_native safety depth).2.2.1\n'
        'example (safety : Bool) (depth : Nat) :\n'
        '    (failedRoot safety (depth + 2)).2.memory.effects.keys (child safety).key = some ⟨(child safety).normalized.address, 5⟩ :=\n'
        '  (failed_root_native safety depth).2.2.2.1\n'
        'example (safety : Bool) (depth : Nat) :\n'
        '    Compiler.Extraction.Memory.Arguments.Normalization.Consumed (parent safety).normalized (failedRoot safety (depth + 2)).2.memory :=\n'
        '  (failed_root_native safety depth).2.2.2.2.1\n'
        'example (safety : Bool) (depth : Nat) :\n'
        '    (failedRoot safety (depth + 2)).2.memory.memory.heap.lookup rootSource.allocation = none :=\n'
        '  (failed_root_native safety depth).2.2.2.2.2.1\n')
    custody = (Path(__file__).resolve().parents[2] / 'lean/Compiler/Extraction/InternerCallerGraphCustody.lean').read_text()
    release = (Path(__file__).resolve().parents[2] / 'lean/Compiler/Extraction/InternerNativeGraphFrame.lean').read_text()
    publication = (Path(__file__).resolve().parents[2] / 'lean/Compiler/Extraction/InternerNativeGraphPublication.lean').read_text()
    cleanup = (Path(__file__).resolve().parents[2] / 'lean/Compiler/Extraction/InternerNativeGraphPublicationCleanup.lean').read_text()
    native_input = (Path(__file__).resolve().parents[2] / 'lean/Compiler/Extraction/InternerNativeInput.lean').read_text()
    return (
        ('initialized-prefix', prefix +
         'example (safety publishOK : Bool) (depth n : Nat) (bounded : n < 4) :\n'
         '    ReachablePrefixTests.sequence (children safety (depth + 1) publishOK) n (Insertion.Native.CallerInputTests.world safety) =\n'
         '      (.ok (BitVec.ofNat 32 n), ReachablePrefixTests.before safety n) := prefix_result safety depth n bounded publishOK\n'
         'example (safety publishOK : Bool) : program safety 0 publishOK =\n'
         '    (.error (.language .unsupported), Insertion.Native.CallerInputTests.world safety) := program_zero safety publishOK\n', (
            ('wrong-prefix-depth', '(children safety (depth + 1) publishOK)', '(children safety depth publishOK)', 1),
            ('exhaustion-as-oom', '.language .unsupported', '.language .outOfMemory', 1),
            ('published-on-exhaustion', 'Insertion.Native.CallerInputTests.world safety) := program_zero',
             'ready safety) := program_zero', 1),
        )),
        ('publication-cleanup', cleanup, (
            ('lost-original-values', 'held : Held allocator source values owned before.world',
             'held : Held allocator source [] owned before.world', 1),
            ('wrong-failure-owner', 'else Consumed owned after.world.memory',
             'else Consumed { owned with address := owned.address + 1 } after.world.memory', 1),
        )),
        ('source-regions', source_regions, (
            ('aliased-allocation', 'source.allocation ≠ id :=', 'source.allocation = id :=', 1),
            ('reached-as-initial', 'found : before.memory.memory.heap.lookup id',
             'found : after.memory.memory.heap.lookup id', 1),
            ('unbound-region', 'heap.lookup source.allocation = some cell := good.backed',
             'heap.lookup (source.allocation + 1) = some cell := good.backed', 1),
            ('wrong-parent-input', 'rootSource [0, 4]\n', 'rootSource [4, 0]\n', 1),
            ('stale-parent-world', '(parent safety).taken.2.world := (parent_input safety).1',
             '(parent safety).constructed := (parent_input safety).1', 1),
        )),
        ('graph-custody', custody, (
            ('wrong-source-privacy', 'privateSource : SourcePrivate source world.memory.effects.keys',
             'privateSource : SourcePrivate { source with allocation := source.allocation + 1 } world.memory.effects.keys', 1),
            ('aliased-child-key', 'published : keys = OwnedKeys.store before.memory.effects.keys key ⟨normalized.address, id⟩',
             'published : keys = OwnedKeys.store before.memory.effects.keys key ⟨parent.allocation, id⟩', 1),
            ('alias-new-operands', 'fresh : row.argumentsAddress = taken.world.memory.memory.nextId',
             'fresh : row.argumentsAddress = parent.address', 1),
            ('wrong-old-operands', 'slice.address ≠ row.argumentsAddress',
             'slice.address ≠ row.argumentsAddress + 1', 1),
        )),
        ('failed-parent', failed, (
            ('success-as-oom', '(program safety (depth + 2) false).1', '(program safety (depth + 2) true).1', 1),
            ('lost-child-word', '.graph.read 5 = some 1', '.graph.read 5 = none', 1),
            ('published-parent', '(parent safety).key = none', '(parent safety).key = some ⟨(parent safety).normalized.address, 5⟩', 1),
            ('lost-child-key', '(child safety).key = some ⟨(child safety).normalized.address, 5⟩', '(child safety).key = none', 1),
            ('consume-child', 'Consumed (parent safety).normalized', 'Consumed (child safety).normalized', 1),
            ('retain-literal', 'rootSource.allocation = none', 'rootSource.allocation ≠ none', 1),
        )),
        ('release', release, (
            ('wrong-key-separation', '(fun address => owned.items ≠ [] ∧ address = owned.address)', '(fun address => owned.items ≠ [] ∧ address = owned.address + 1)', 2),
            ('aliased-operands', 'owned.address ≠ row.argumentsAddress)', 'owned.address = row.argumentsAddress)', 2),
            ('wrong-owner-correspondence', 'facts.valid.related allocator owned.address owned.items nonempty (live.resolve_left nonempty)',
             'facts.valid.related allocator (owned.address + 1) owned.items nonempty (live.resolve_left nonempty)', 1),
        )),
        ('execution', execution, (
            ('wrong-child-id', '.operation 20 [0, id] debug)', '.operation 20 [0, 0] debug)', 1),
            ('truncated-prefix', '(children safety (depth + 2)) 3\n', '(children safety (depth + 2)) 2\n', 1),
            ('stale-world', '(children safety (depth + 2)).operation 20 [0, id] debug)',
             '(fun _ => (children safety (depth + 2)).operation 20 [0, id] debug (initial safety)))', 1),
        )),
        ('postconditions', post, (
            ('wrong-result', '.1 = .ok 5 :=', '.1 = .ok 4 :=', 1),
            ('wrong-capacity', '⟨backing safety, 0⟩ 13', '⟨backing safety, 0⟩ 5', 1),
            ('retain-literal', 'rootSource.allocation = none :=', 'rootSource.allocation ≠ none :=', 1),
            ('retain-old-backing', 'ReachablePrefixTests.backing = none :=',
             'ReachablePrefixTests.backing ≠ none :=', 1),
            ('wrong-parent-owner', 'some ⟨(parent safety).normalized.address, 5⟩ :=',
             'some ⟨(child safety).normalized.address, 5⟩ :=', 1),
            ('wrong-word', '.graph.read 5 = some 1 :=', '.graph.read 5 = some 0 :=', 1),
            ('exhaustion-ordinary', 'ordinary (program safety 1).1 = false :=', 'ordinary (program safety 1).1 = true :=', 1),
        )),
        ('native-input', native_input, (
            ('annotation-as-value', '.ok source.items[index]', '.ok annotation', 2),
            ('wrong-query-owner', 'Owner.headerAddress ⟨owner, 0⟩', 'Owner.headerAddress ⟨owner + 1, 0⟩', 1),
            ('dropped-prefix', 'world (before ++ added)', 'world added', 1),
        )),
        ('publication', publication, (
            ('wrong-installed-key-owner', 'have keys : after.table = OwnedKeys.store before.memory.effects.keys key ⟨owned.address, id⟩',
             'have keys : after.table = OwnedKeys.store before.memory.effects.keys key ⟨owned.address + 1, id⟩', 1),
            ('missing-freshness', '(fresh : OwnedKeys.Fresh before.memory.effects.keys key ⟨owned.address, id⟩)', '(fresh : True)', 1),
            ('missing-graph-separation', 'owned.address ≠ row.argumentsAddress)', 'owned.address = row.argumentsAddress → True)', 1),
            ('missing-ownership', 'live : SliceValid allocator before.memory.heap owned', 'live : True', 1),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    records = []
    for group, text, changes in mutation_cases():
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous recursive growth mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'recursive-growth-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'recursive-growth-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
