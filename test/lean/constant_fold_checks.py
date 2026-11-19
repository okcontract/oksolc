#!/usr/bin/env python3
"""Audit actual arbitrary-word folding through child growth OOM and return.
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

TESTS = arguments.ITEM + 'ConstantFoldTests.'
NATIVE = recursive.NS + 'FoldConstantTests.'
CALL = words.CALL
MEMORY = words.MEMORY
LOCK = 'Compiler.Extraction.RepresentativeArray.Owner.NativeLock.'
DUPLICATION = 'Compiler.Extraction.Memory.Arguments.Duplication.'
CLAIMS = [MEMORY + 'WordCopy.copyFrom_address', MEMORY + 'WordCopy.copy_address',
          MEMORY + 'RegionAllocation.fits_above', DUPLICATION + 'run_address',
          arguments.OWNED + 'TemporaryUnary.prepare_address', LOCK + 'checkHeader_after_length_store',
          CALL + 'prepared_allocations', CALL + 'normalized_empty', CALL + 'cleanup_missing', CALL + 'simplifier_oom']
CLAIMS += [TESTS + name for name in ('allocations', 'literal', 'prepared', 'initialized', 'taken', 'parent_missed', 'observed', 'established', 'folded_apart',
    'child_allocations', 'child_prepared', 'child_normalized', 'child_missed', 'child_observed', 'child_established',
    'child_duplicate', 'child_creation_fits', 'child_created', 'child_cloned', 'child_unlocked',
    'child_reads', 'child_contract', 'iszero_result', 'iszero_failure')]
CLAIMS += [NATIVE + name for name in ('child_equivalent', 'parent_simplified', 'inner_contract', 'root_route',
    'root_contract', 'program_equivalent', 'program_contract', 'root_one', 'program_one', 'exhaustion_retained', 'program_zero')]


def bindings():
    return {'recursiveFamily': words.bindings(),
            'scope': 'full native initialization and four operation constructors; arbitrary-word publication; '
                     'ISZERO of its actual returned identifier; first-stage fold to the actual constant child; '
                     'nonempty growth allocation OOM; child, parent and literal returns',
            'productionBranch': 'src/libevmasm/rule_list.zig:simplifyWithOptions:constant_arguments/foldConstants/makeConstant',
            'all256BitWords': True, 'bothSafetyLayouts': True, 'allDepthsAtLeastTwo': True,
            'observationExhaustionIsUnsupported': True,
            'completeConstructorDependencyClosureVerified': False,
            'generalAllocationOutcomesVerified': False, 'recursiveInductionVerified': False}


def audit(claims):
    required = {
        MEMORY + 'WordCopy.copyFrom_address': {MEMORY + 'store_keeps_counters'},
        MEMORY + 'RegionAllocation.fits_above': {MEMORY + 'valid_lookup', MEMORY + 'lookup_of_mem_valid'},
        LOCK + 'checkHeader_after_length_store': {MEMORY + 'load_disjoint_after_store'},
        DUPLICATION + 'run_address': {MEMORY + 'WordCopy.copy_address'},
        CALL + 'prepared_allocations': {MEMORY + 'allocate_at_same_address', arguments.ITEM + 'prepare_verified'},
        CALL + 'normalized_empty': {DUPLICATION + 'run_empty'},
        TESTS + 'literal': {words.PUBLICATION + 'contract', arguments.OWNED + 'TemporaryUnary.prepare_verified',
            arguments.OWNED + 'TemporaryUnary.prepare_address', MEMORY + 'allocate_at_same_address'},
        TESTS + 'prepared': {TESTS + 'literal', CALL + 'prepared_allocations'},
        TESTS + 'taken': {CALL + 'borrowed_taken', DUPLICATION + 'run_admitted', DUPLICATION + 'run_address'},
        TESTS + 'child_prepared': {CALL + 'prepared_allocations', TESTS + 'taken', TESTS + 'established'},
        TESTS + 'child_normalized': {CALL + 'normalized_empty', TESTS + 'child_prepared'},
        TESTS + 'child_missed': {TESTS + 'folded_apart', words.PUBLICATION + 'contract', words.INPUT + 'missed'},
        TESTS + 'child_creation_fits': {MEMORY + 'RegionAllocation.fits_above', TESTS + 'child_duplicate'},
        TESTS + 'child_unlocked': {words.PUBLICATION + 'contract', LOCK + 'checkHeader_eq_of_lookup',
            LOCK + 'checkHeader_after_length_store'},
        TESTS + 'child_contract': {CALL + 'constant_growth_contract', arguments.ITEM + 'constant_growing_empty_oom',
            TESTS + 'child_creation_fits', TESTS + 'child_unlocked', TESTS + 'child_observed'},
        TESTS + 'iszero_result': {'Compiler.Extraction.Folding.folding_correct', 'Compiler.Extraction.Dispatch.constantStage'},
        TESTS + 'iszero_failure': {TESTS + 'iszero_result'},
        CALL + 'simplifier_oom': {arguments.OWNED + 'held_retained', arguments.OWNED + 'finish_taken',
            arguments.OWNED.removesuffix('OwnedCall.') + 'free_valid', CALL + 'route', CALL + 'returned_frame', CALL + 'cleanup_missing'},
        NATIVE + 'child_equivalent': {recursive.TESTS + 'same_call', recursive.NS + 'constant_succ', TESTS + 'child_established'},
        NATIVE + 'parent_simplified': {recursive.NS + 'dispatcher_snapshot', graph.NS + 'Facts.reads',
            TESTS + 'iszero_failure', NATIVE + 'child_equivalent', words.PUBLICATION + 'value_read'},
        NATIVE + 'inner_contract': {TESTS + 'child_contract', CALL + 'simplifier_oom', NATIVE + 'parent_simplified'},
        NATIVE + 'root_contract': {NATIVE + 'inner_contract', NATIVE + 'root_route',
            arguments.ARGUMENTS + 'Prepared.retire', graph.FACTS + 'cleanup'},
        NATIVE + 'program_equivalent': {words.WORD + 'constant_equivalent', recursive.NS + 'ConstantTests.prefix_result',
            'Compiler.Algebraic.Effect.bind_success'},
        NATIVE + 'program_contract': {NATIVE + 'program_equivalent', NATIVE + 'root_contract',
            graph.FACTS + 'native', words.PUBLICATION + 'value_read'},
        NATIVE + 'root_one': {TESTS + 'iszero_failure', recursive.NS + 'exhausted', CALL + 'route'},
        NATIVE + 'exhaustion_retained': {NATIVE + 'program_one', TESTS + 'established', words.PUBLICATION + 'value_read'},
    }
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError('constant fold connection lost dependencies: ' + name + ': ' + ', '.join(sorted(missing)))
    return {'checkedDependencies': sorted(required), 'sourceBinding': bindings(),
            'actualFoldedConstantChildAndParentReturnVerified': True,
            'unlockedOwnerDerivedThroughPublishedLengthStore': True,
            'publishedWordRetainedAcrossChildFailure': True,
            'completeConstructorDependencyClosureVerified': False, 'completeNativeGraphInvariantVerified': False,
            'generalAllocationOutcomesVerified': False, 'recursiveInductionVerified': False,
            'composedProductionTheoremVerified': False}


def mutation_cases():
    def source(path):
        raw = (ROOT / 'lean/Compiler' / path).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)

    # Keep a changed store address at the statement boundary. Expanding the
    # generic store implementation is irrelevant to rejecting that mutation.
    lock = source('Extraction/RepresentativeOwnerLock.lean').replace(
        '/-- Updating the representative length',
        'section\nattribute [local irreducible] store\n\n/-- Updating the representative length').replace(
        'structure Initialized', 'end\n\nstructure Initialized')
    program = source('Extraction/InternerNativeConstantFoldTests.lean').replace(
        '/-- Use the actual identifier',
        'section\nattribute [local irreducible] ConstantTests.children\n\n/-- Use the actual identifier').replace(
        '/-- Native initialization, arbitrary-word publication',
        'end\n\n/-- Native initialization, arbitrary-word publication')
    return (
        ('copy', source('ZigAir/MemoryWordCopy.lean'), (
            ('rewind-high-water', '(copy state source target).2.nextAddress = state.nextAddress',
             '(copy state source target).2.nextAddress = state.nextAddress + 1', 1),
        )),
        ('lock', lock, (
            ('overwrite-lock', '(stored : store before (.pointer (.pointer true false usize) ⟨lifetime, representativesOffset + Append.lengthOffset⟩)',
             '(stored : store before (.pointer (.pointer true false usize) ⟨lifetime, representativesLockOffset⟩)', 1),
        )),
        ('cleanup', source('Extraction/InternerRecursiveCallFailureTests.lean'), (
            ('omit-child-graph-frame', '(sameGraph : world.graph = call.taken.2.world.graph)',
             '(sameGraph : world.graph = world.graph)', 1),
        )),
        ('input', source('Extraction/InternerConstantFoldInputTests.lean'), (
            ('stale-literal', '⟨(old safety value).memory.memory.nextId, 0, 1⟩',
             '⟨(old safety value).memory.memory.nextId + 1, 0, 1⟩', 1),
        )),
        ('child-input', source('Extraction/InternerConstantFoldChildInputTests.lean'), (
            ('wrong-folded-word', 'constantRequest (Unary.iszero.eval value)', 'constantRequest value', 1),
            ('reuse-parent-lifetime', '⟨(child safety value).before.memory.memory.nextId + 1, 0⟩',
             '⟨(child safety value).before.memory.memory.nextId, 0⟩', 1),
        )),
        ('allocation', source('Extraction/InternerConstantFoldAllocationTests.lean'), (
            ('locked-owner', '(Owner.headerAddress ⟨6, 0⟩) = .ok () := by',
             '(Owner.headerAddress ⟨6, 0⟩) = .error .memoryValidity := by', 1),

        )),
        ('dispatch', source('Extraction/InternerConstantFoldDispatchTests.lean'), (
            ('wrong-child-argument', '(called : constructors.constant (Unary.iszero.eval value) metadata before',
             '(called : constructors.constant value metadata before', 2),
        )),
        ('program', program, (
            ('wrong-returned-operand', '(children safety depth).operation 21 [id] debug',
             '(children safety depth).operation 21 [id + 1] debug', 1),
            ('double-parent-free', '.memory.effects.allocator + 101', '.memory.effects.allocator + 202', 1),
            ('wrong-final-native-word', '.ok (.ok (some value))', '.ok (.ok (some (value + 1)))', 2),
            ('exhaustion-as-oom', '(.error (.language .unsupported), CallerInputTests.world safety)',
             '(.error (.language .outOfMemory), CallerInputTests.world safety)', 1),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    records = []
    for group, text, changes in mutation_cases():
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous constant fold mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'constant-fold-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'constant-fold-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
