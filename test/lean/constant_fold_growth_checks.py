#!/usr/bin/env python3
"""Audit folded constant growth through both actual parent publication outcomes.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
import constructor_argument_checks as arguments
import constant_word_checks as words
import constant_fold_checks as fold
import recursive_growth_checks as growth
import native_graph_checks as graph
import native_recursion_checks as recursive

TESTS = arguments.ITEM + 'ConstantFoldGrowthTests.'
STORAGE = 'Compiler.Extraction.Storage.'
CLAIMS = [STORAGE + 'insert_prepared_congr', words.APPEND + 'spare_allocators']
CLAIMS += [words.CALL + name for name in ('installed_facts', 'growing_native', 'spare_insertion_same')]
CLAIMS += [TESTS + name for name in (
    'installed_facts', 'created_address', 'backing_fits', 'child_native', 'source_private', 'child_contract',
    'constant_insertion', 'constant_equivalent', 'child_equivalent', 'parent_simplified', 'inner_contract',
    'root_route', 'root_contract', 'child_keys', 'root_keys', 'native_words', 'program_equivalent',
    'program_contract', 'program_preserves_words', 'root_one', 'program_one', 'exhaustion_retained', 'program_zero')]


def bindings():
    return {'recursiveFamily': growth.bindings(),
            'scope': 'native initialization and four operation constructors; arbitrary-word publication; '
                     'ISZERO of the actual returned ID; actual folded constant child through nonempty relocation; '
                     'parent publication success/OOM and all enclosing returns',
            'productionBranch': fold.bindings()['productionBranch'],
            'all256BitWords': True, 'bothSafetyLayouts': True, 'allDepthsAtLeastTwo': True,
            'observationExhaustionIsUnsupported': True,
            'completeConstructorDependencyClosureVerified': False,
            'completeNativeGraphInvariantVerified': False, 'generalAllocationOutcomesVerified': False,
            'recursiveInductionVerified': False, 'composedProductionTheoremVerified': False}


def audit(claims):
    required = {
        STORAGE + 'insert_prepared_congr': {STORAGE + 'insertProgram', STORAGE + 'Program.execute'},
        words.APPEND + 'spare_allocators': {'Compiler.Extraction.RepresentativeArray.Capacity.ensure_unchanged'},
        words.CALL + 'installed_facts': {words.NATIVE + 'CallerInput.prepare'},
        words.CALL + 'growing_native': {words.NATIVE + 'CallerInput.growing_success',
            words.NATIVE + 'CallerInput.checked_execution', graph.FACTS + 'data_after'},
        words.CALL + 'spare_insertion_same': {STORAGE + 'insert_prepared_congr', words.APPEND + 'spare_allocators',
            words.APPEND + 'spare_same', words.NATIVE + 'CallerInput.prepare', words.NATIVE + 'CallerInput.checked_execution'},
        TESTS + 'installed_facts': {words.CALL + 'installed_facts', fold.TESTS + 'child_duplicate',
            fold.TESTS + 'child_created', fold.TESTS + 'child_cloned'},
        TESTS + 'created_address': {'Compiler.Extraction.AssemblyItem.Creation.create_shape'},
        TESTS + 'backing_fits': {TESTS + 'installed_facts', TESTS + 'created_address', words.MEMORY + 'RegionAllocation.fits_above'},
        TESTS + 'child_native': {words.CALL + 'growing_native', TESTS + 'backing_fits', fold.TESTS + 'child_unlocked'},
        TESTS + 'source_private': {arguments.ARGUMENTS + 'Prepared.key_apart', arguments.ARGUMENTS + 'Prepared.native_apart'},
        TESTS + 'child_contract': {TESTS + 'child_native', words.CALL + 'publication_return', TESTS + 'source_private',
            words.CALL + 'route', words.NATIVE + 'CallerInput.finish_native', words.NATIVE + 'CallerInput.graph_custody'},
        TESTS + 'constant_insertion': {words.CALL + 'spare_insertion_same', words.PUBLICATION + 'duplicate_result',
            words.PUBLICATION + 'created', words.PUBLICATION + 'cloned'},
        TESTS + 'constant_equivalent': {TESTS + 'constant_insertion', recursive.TESTS + 'same_call',
            words.PUBLICATION + 'contract', recursive.NS + 'constant_succ'},
        TESTS + 'child_equivalent': {recursive.TESTS + 'same_call', recursive.NS + 'constant_succ'},
        TESTS + 'parent_simplified': {TESTS + 'child_equivalent', fold.TESTS + 'iszero_result',
            recursive.NS + 'dispatcher_snapshot', graph.NS + 'Facts.reads', words.PUBLICATION + 'value_read'},
        TESTS + 'inner_contract': {TESTS + 'child_contract', TESTS + 'parent_simplified', words.CALL + 'route',
            graph.NS + 'Facts.finish_publication', growth.PUBLICATION + 'publish_absent', growth.PUBLICATION + 'publish_oom',
            arguments.OWNED.removesuffix('OwnedCall.') + 'free_valid', words.CALL + 'returned_cell', words.CALL + 'cleanup_missing'},
        TESTS + 'root_contract': {TESTS + 'inner_contract', TESTS + 'root_route', graph.NS + 'Facts.cleanup',
            arguments.ARGUMENTS + 'Prepared.retire', words.CALL + 'cleanup_missing'},
        TESTS + 'child_keys': {TESTS + 'child_contract', fold.TESTS + 'established'},
        TESTS + 'root_keys': {TESTS + 'inner_contract', TESTS + 'child_keys', TESTS + 'root_contract'},
        TESTS + 'native_words': {graph.NS + 'Facts.constants', STORAGE + 'representative_correct'},
        TESTS + 'program_equivalent': {growth.TESTS + 'prefix_result', TESTS + 'constant_equivalent',
            'Compiler.Algebraic.Effect.bind_success'},
        TESTS + 'program_contract': {TESTS + 'program_equivalent', TESTS + 'root_contract', TESTS + 'native_words', TESTS + 'root_keys'},
        TESTS + 'program_preserves_words': {TESTS + 'program_contract', words.PUBLICATION + 'contract'},
        TESTS + 'root_one': {fold.TESTS + 'iszero_failure', recursive.NS + 'exhausted', words.CALL + 'route'},
        TESTS + 'exhaustion_retained': {TESTS + 'program_one', fold.TESTS + 'established', words.PUBLICATION + 'value_read'},
    }
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError('constant fold growth lost dependencies: ' + name + ': ' + ', '.join(sorted(missing)))
    return {'checkedDependencies': sorted(required), 'sourceBinding': bindings(),
            'actualFoldedConstantGrowthAndParentReturnVerified': True,
            'exactInitialSpareAllocatorIndependenceVerified': True,
            'childNativeWordsAndKeysRetainedAcrossParentFailure': True,
            'completeConstructorDependencyClosureVerified': False, 'completeNativeGraphInvariantVerified': False,
            'generalAllocationOutcomesVerified': False, 'recursiveInductionVerified': False,
            'composedProductionTheoremVerified': False}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / (name + '.lean')).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)

    module = source('InternerNativeConstantFoldGrowthTests')
    # Diagnostic-only program fixture; the complete source remains the audited
    # and freshly replayed module. Abstract the children while rejecting changed
    # sequencing instead of reducing unrelated native memory histories.
    program = ('import Compiler.Extraction.InternerNativeConstantFoldGrowthTests\n'
        'set_option pp.maxSteps 8\nset_option pp.deepTerms false\n'
        'namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.FoldGrowthControls\n'
        'open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul\n'
        'open Insertion Insertion.Native RecursiveTests ConstantFoldTests ConstantFoldGrowthTests\n'
        'attribute [local irreducible] RecursiveGrowthTests.children\n' +
        module[module.index('def program ('):module.index('/-- Full initialization,')])
    prefix = ('import Compiler.Extraction.InternerNativeConstantFoldGrowthTests\n'
        'set_option pp.maxSteps 8\nset_option pp.deepTerms false\n'
        'open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul\n'
        'open Compiler.Extraction.Memory.Arguments.Normalization\n'
        'open OwnedCall OwnedCall.ConstructorItem OwnedCall.ConstructorItem.ConstantFoldTests\n'
        'open OwnedCall.ConstructorItem.ConstantFoldGrowthTests\n'
        'open Compiler.Extraction.RepresentativeArray\n')
    post = prefix + (
        'example (safety publishOK : Bool) (depth : Nat) (value : Word) :\n'
        '    (program safety (depth + 2) value publishOK).1 =\n'
        '      (if publishOK then .ok 5 else .error (.language .outOfMemory)) := (program_contract safety depth value publishOK).1\n'
        'example (safety publishOK : Bool) (depth : Nat) (value : Word) :\n'
        '    Constant.value (program safety (depth + 2) value publishOK).2.memory.memory (Owner.headerAddress ⟨6, 0⟩) 5 =\n'
        '      .ok (.ok (some (Unary.iszero.eval value))) := (program_contract safety depth value publishOK).2.2.2.1\n'
        'example (safety publishOK : Bool) (depth : Nat) (value : Word) :\n'
        '    (program safety (depth + 2) value publishOK).2.memory.effects.keys = resultKeys safety value publishOK :=\n'
        '  (program_contract safety depth value publishOK).2.2.2.2.1\n'
        'example (safety publishOK : Bool) (depth : Nat) (value : Word) :\n'
        '    (program safety (depth + 2) value publishOK).2.memory.memory.heap.lookup (rootSource safety value).allocation = none :=\n'
        '  (program_contract safety depth value publishOK).2.2.2.2.2.1\n'
        'example (safety publishOK : Bool) (depth : Nat) (value : Word) :\n'
        '    (program safety (depth + 2) value publishOK).2.memory.memory.heap.lookup ReachablePrefixTests.backing = none :=\n'
        '  (program_contract safety depth value publishOK).2.2.2.2.2.2.2.1\n'
        'example (safety : Bool) (depth : Nat) (value : Word) :\n'
        '    Consumed (parent safety value).normalized (program safety (depth + 2) value false).2.memory :=\n'
        '  (program_contract safety depth value false).2.2.2.2.2.2.2.2.1\n')
    shallow = prefix + (
        'example (safety publishOK : Bool) (value : Word) : ordinary (program safety 1 value publishOK).1 = false :=\n'
        '  (exhaustion_retained safety value publishOK).1\n'
        'example (safety publishOK : Bool) (value : Word) : program safety 1 value publishOK =\n'
        '    (.error (.language .unsupported), (parent safety value).taken.2.world) := program_one safety value publishOK\n'
        'example (safety publishOK : Bool) (value : Word) : program safety 0 value publishOK =\n'
        '    (.error (.language .unsupported), Insertion.Native.CallerInputTests.world safety) := program_zero safety value publishOK\n')
    return (
        ('prepared-control', source('StoragePreparedRollback'), (
            ('omit-append-agreement', 'appendSame : calls.attempt .append preparationOwnership ready = other.attempt .append preparationOwnership ready',
             'appendSame : calls.attempt .append preparationOwnership ready = calls.attempt .append preparationOwnership ready', 1),
        )),
        ('spare-input', source('InternerRecursiveSpareAllocationTests'), (
            ('allow-full-backing', 'spare : rows.length < capacity', 'spare : rows.length ≤ capacity', 1),
        )),
        ('allocation', source('InternerConstantFoldGrowthAllocationTests'), (
            ('unaligned-backing', '⟨416, 8⟩ 8192 := by', '⟨416, 8⟩ 8193 := by', 1),
            ('stale-lifetime', 'def backing (safety : Bool) (value : Word) := (child safety value).clone.2.memory.nextId',
             'def backing (safety : Bool) (value : Word) := (child safety value).clone.2.memory.nextId + 1', 1),
        )),
        ('execution', program, (
            ('wrong-returned-id', '.operation 21 [id] debug)', '.operation 21 [id + 1] debug)', 1),
            ('truncated-prefix', 'publishOK) 3\n', 'publishOK) 2\n', 1),
            ('stale-world', '(RecursiveGrowthTests.children safety depth publishOK).operation 21 [id] debug)',
             '(fun _ => (RecursiveGrowthTests.children safety depth publishOK).operation 21 [id] debug (ConstantInputTests.initial safety)))', 1),
        )),
        ('postconditions', post, (
            ('wrong-result', 'if publishOK then .ok 5', 'if publishOK then .ok 4', 1),
            ('lost-folded-word', '.ok (.ok (some (Unary.iszero.eval value))) :=', '.ok (.ok (some value)) :=', 1),
            ('wrong-publication-outcome', '= resultKeys safety value publishOK :=', '= resultKeys safety value (!publishOK) :=', 1),
            ('retain-literal', '(rootSource safety value).allocation = none :=', '(rootSource safety value).allocation ≠ none :=', 1),
            ('retain-old-backing', 'ReachablePrefixTests.backing = none :=', 'ReachablePrefixTests.backing ≠ none :=', 1),
            ('retain-failed-parent-owner',
             'Consumed (parent safety value).normalized (program safety (depth + 2) value false).2.memory :=',
             'Compiler.Extraction.Memory.SliceValid 7 (program safety (depth + 2) value false).2.memory.heap (parent safety value).normalized :=', 1),
        )),
        ('depth', shallow, (
            ('ordinary-exhaustion', 'publishOK).1 = false :=', 'publishOK).1 = true :=', 1),
            ('exhaustion-as-oom', '.language .unsupported', '.language .outOfMemory', 2),
            ('erase-parent-on-exhaustion', '(parent safety value).taken.2.world) := program_one',
             '(old safety value)) := program_one', 1),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    records = []
    for group, text, changes in mutation_cases():
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous constant fold growth mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'fold-growth-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'fold-growth-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
