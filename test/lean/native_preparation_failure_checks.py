#!/usr/bin/env python3
"""Audit preparation OOM ownership and complete source-ordered cleanup.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NATIVE = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.'
NORMAL = 'Compiler.Extraction.Memory.Arguments.Normalization.'
STORAGE = 'Compiler.Extraction.Storage.'
CREATION = 'Compiler.Extraction.AssemblyItem.Creation.'
CLAIMS = [STORAGE + 'insert_' + stage + '_oom' for stage in ('duplicate', 'create', 'clone')]
CLAIMS += [NATIVE + name for name in ('release_keeps_arguments', 'duplicate_failed', 'free_keeps_dead',
    'normalized_cleanup', 'argument_cleanup', 'arguments_consumed',
    'duplicate_oom_execution', 'create_oom_execution', 'clone_oom_execution')]
CLAIMS += [NATIVE + 'PreparationFailureTests.' + name for name in (
    'admitted', 'live', 'represented', 'failure_results', 'duplicate_contract', 'create_contract', 'clone_contract',
    'cleanup_effects', 'allocation_history', 'original_allocations')]


def audit(claims):
    required = {STORAGE + 'insert_' + stage + '_oom': {STORAGE + 'insertProgram', STORAGE + 'Program.execute'}
                for stage in ('duplicate', 'create', 'clone')}
    required.update({
        NATIVE + 'duplicate_failed': {NORMAL + 'take_refines', NORMAL + 'OwnedCall.Insertion.borrowed_ready',
                                     NORMAL + 'OwnedCall.Publication.external_admitted'},
        NATIVE + 'normalized_cleanup': {NORMAL + 'free_valid', NATIVE + 'free_keeps_dead', NATIVE + 'callbacks'},
        NATIVE + 'argument_cleanup': {NORMAL + 'free_valid', NATIVE + 'release_keeps_arguments',
                                     NATIVE + 'normalized_cleanup', NATIVE + 'free_keeps_dead'},
        NATIVE + 'duplicate_oom_execution': {NATIVE + 'duplicate_failed', NATIVE + 'normalized_cleanup',
                                           STORAGE + 'insert_duplicate_oom', NATIVE + 'execution'},
        NATIVE + 'create_oom_execution': {NATIVE + 'duplicate_taken', CREATION + 'create_oom',
            NATIVE + 'argument_cleanup', NATIVE + 'arguments_consumed', STORAGE + 'insert_create_oom', NATIVE + 'execution'},
        NATIVE + 'clone_oom_execution': {NATIVE + 'duplicate_taken', CREATION + 'create_verified',
            CREATION + 'NativeFields.represented_after_create', CREATION + 'NativeFields.clone_oom',
            'Compiler.Extraction.AssemblyClone.Physical.run_oom', 'Compiler.Extraction.AssemblyItem.destroy_verified',
            NATIVE + 'argument_cleanup', NATIVE + 'arguments_consumed', STORAGE + 'insert_clone_oom', NATIVE + 'execution'},
    })
    for stage in ('duplicate', 'create', 'clone'):
        required[NATIVE + 'PreparationFailureTests.' + stage + '_contract'] = {
            NATIVE + stage + '_oom_execution', NATIVE + 'PreparationFailureTests.failure_results',
            NATIVE + 'AppendOwnershipTests.initial_valid'}
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('preparation failure lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'preparationOomOwnersDerived': True,
            'completeDeterministicSourceProgramOnPreparationOom': True, 'outerNormalizedCleanupConnected': True,
            'reachedEffectsAndAllocationHistoryRetained': True, 'emptySentinelOwnershipChecked': True,
            'initialGraphAndInputPremisesExplicit': True, 'completePublicationRollbackVerified': False,
            'nonemptyGrowthIntegrated': False, 'recursiveConstructorsVerified': False}


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    directory = ROOT / 'lean/Compiler/Extraction'
    source = ('import Compiler.Extraction.InternerInsertionPreparation\n'
              'import Compiler.Extraction.InternerInsertionCleanupEffects\n'
              'import Compiler.Extraction.StoragePreparedRollback\n')
    source += '\n'.join(without_imports((directory / name).read_text()) for name in (
        'StoragePreparationFailure.lean', 'InternerInsertionPreparationFailure.lean'))
    changes = (
        ('successful-outcome', '((.ok (some .allocationFailure),', '((.ok (some .success),', 7),
        ('omit-outer-cleanup', '(Storage.Cleanup.sequence [.arguments, .normalized]).run Storage.duplicatedOwnership',
         '(Storage.Cleanup.sequence [.arguments]).run Storage.duplicatedOwnership', 1),
        ('omit-object-cleanup', '(Storage.Cleanup.sequence [.allocation, .arguments, .normalized]).run Storage.createdOwnership',
         '(Storage.Cleanup.sequence [.arguments, .normalized]).run Storage.createdOwnership', 1),
        ('duplicate-succeeded', 'before.memory = (.error .outOfMemory, failed)',
         'before.memory = (.error (.release (.ownership .wrongAllocator)), failed)', 1),
        ('creation-succeeded', 'allocator input.item duplicated = (.error .outOfMemory, failed)',
         'allocator input.item duplicated = (.ok 0, failed)', 1),
        ('clone-succeeded', 'allocator input allocated = (.error .outOfMemory, failed)',
         'allocator input allocated = (.ok input, failed)', 1),
        ('wrong-source', 'Represents before.memory.memory itemSource input',
         'Represents before.memory.memory ⟨itemSource.allocation + 1, itemSource.offset⟩ input', 1),
        ('destroy-before-clone', '(memory destroyed).effects = release ops.objects object failed',
         '(memory destroyed).effects = release ops.objects object allocated', 1),
        ('rewind-history', '(memory after).memory.nextId = allocated.memory.nextId',
         '(memory after).memory.nextId = duplicated.memory.nextId', 1),
        ('retain-item', '(memory after).heap object = none ∧', '(memory after).heap object ≠ none ∧', 1),
        ('erase-frame', '(memory after).heap id = before.memory.heap id ∧', '(memory after).heap id = none ∧', 1),
        ('free-empty', 'if operands.items.isEmpty then (memory before).effects',
         'if operands.items.isEmpty then (Publication.external ops.arguments).free operands (memory before)', 1),
    )
    for name, before, _, count in changes:
        if source.count(before) != count:
            raise ValueError('ambiguous preparation failure mutation: ' + name)
    records = checked_controls(output, [mutation_check(output, 'preparation-failure-unchanged', source, True, env, lean)])
    for name, before, after, _ in changes:
        records += checked_controls(output, [mutation_check(output, 'preparation-failure-' + name,
                                                           source.replace(before, after), False, env, lean)])
    return records
