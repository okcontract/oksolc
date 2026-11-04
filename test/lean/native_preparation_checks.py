#!/usr/bin/env python3
"""Audit preparation-derived owners in full spare-capacity publication rollback.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NATIVE = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.'
NORMAL = 'Compiler.Extraction.Memory.Arguments.Normalization.'
CREATION = 'Compiler.Extraction.AssemblyItem.Creation.'
STORAGE = 'Compiler.Extraction.Storage.'
CLAIMS = [CREATION + 'NativeFields.clone_callback_installed', STORAGE + 'insert_prepared_oom']
CLAIMS += [NATIVE + name for name in ('create_keys', 'clone_duplicate_keys', 'clone_keys', 'arguments_keys',
    'ownsArguments_complete', 'arguments_retained', 'duplicate_taken', 'prepare_owned', 'deterministic_spare_oom')]
CLAIMS += [NATIVE + 'PreparationTests.' + name for name in (
    'preparation_results', 'probe_result', 'derived_contract', 'reached_observations', 'source_rejection')]


def audit(claims):
    required = {
        CREATION + 'NativeFields.clone_callback_installed': {
            'Compiler.Extraction.AssemblyClone.NativeFields.clone_install', CREATION + 'NativeFields.finish_assigned'},
        STORAGE + 'insert_prepared_oom': {STORAGE + 'insertProgram', STORAGE + 'Program.execute', STORAGE + 'releaseAll_append'},
        NATIVE + 'arguments_keys': {NORMAL + 'takeOwned', 'Compiler.Extraction.Memory.Arguments.Duplication.run_reached_effects'},
        NATIVE + 'duplicate_taken': {NORMAL + 'take_refines', NORMAL + 'OwnedCall.Insertion.borrowed_ready',
            NORMAL + 'OwnedCall.Publication.external_admitted'},
        NATIVE + 'prepare_owned': {NATIVE + 'duplicate_taken', NATIVE + 'arguments_retained', NATIVE + 'arguments_keys',
            NATIVE + 'create_keys', NATIVE + 'clone_keys', CREATION + 'create_verified',
            CREATION + 'NativeFields.clone_callback_installed', 'Compiler.Extraction.AssemblyClone.Physical.run_valid'},
        NATIVE + 'deterministic_spare_oom': {NATIVE + 'prepare_owned', NATIVE + 'spare_publication_oom_cleanup',
            NATIVE + 'execution', STORAGE + 'insert_prepared_oom'},
        NATIVE + 'PreparationTests.derived_contract': {NATIVE + 'deterministic_spare_oom', NATIVE + 'PreparationTests.preparation_results',
            NATIVE + 'AppendOwnershipTests.initial_valid'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('native preparation lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'ownersDerivedFromActualPreparation': True,
            'completeSourceProgramOnSparePublicationOom': True, 'outerNormalizedCleanupConnected': True,
            'initialGraphAndInputPremisesExplicit': True, 'nativeHashMapRefinementVerified': False,
            'nonemptyGrowthIntegrated': False, 'completePublicationRollbackVerified': False,
            'recursiveConstructorsVerified': False}


def controls(output, env, lean):
    # Reuse the owning gate's resource/syntax guard; import after module loading
    # because that gate also registers this extension.
    from assembly_item_creation_checks import checked_controls
    directory = ROOT / 'lean/Compiler/Extraction'
    source = ('import Compiler.Extraction.InternerInsertionAppendOwnership\n'
              'import Compiler.Extraction.InternerInsertionValidity\n'
              'import Compiler.Extraction.PublicationNormalizationEffects\n')
    source += '\n'.join(without_imports((directory / name).read_text()) for name in (
        'InternerInsertionPreparationEffects.lean', 'InternerInsertionItemPreparation.lean', 'InternerInsertionPreparation.lean',
        'StoragePreparedRollback.lean', 'InternerInsertionPreparedRollback.lean'))
    records = checked_controls(output, [mutation_check(output, 'native-preparation-unchanged', source, True, env, lean)])
    changes = (
        ('wrong-duplicate', 'before = (.ok (operands, remaining), after)',
         'before = (.ok (normalized, remaining), after)', 1),
        ('wrong-created-object', 'allocator input.item duplicated = (.ok object, allocated)',
         'allocator input.item duplicated = (.ok (object + 1), allocated)', 3),
        ('wrong-source-object', 'Represents (memory before).memory itemSource input',
         'Represents (memory before).memory ⟨itemSource.allocation + 1, itemSource.offset⟩ input', 2),
        ('wrong-cloned-value', 'allocator input allocated = (.ok copied, middle)',
         'allocator input allocated = (.ok input, middle)', 5),
        ('alias-normalized-owner', 'normalized.address ≠ operands.address', 'normalized.address = operands.address', 1),
        ('erase-old-registry', 'installed.heap id = (memory before).heap id', 'installed.heap id = none', 2),
        ('erase-key-table', '(memory ready).effects.keys = (memory before).effects.keys',
         '(memory ready).effects.keys = (fun _ => none)', 2),
        ('deny-installation', 'install copied object middle = .ok (memory ready)',
         'install copied object middle ≠ .ok (memory ready)', 2),
        ('wrong-program-outcome', '((.ok (some .allocationFailure), (Cleanup.sequence [.lastValue, .pop, .normalized]).run publicationOwnership), after)',
         '((.ok (some .success), (Cleanup.sequence [.lastValue, .pop, .normalized]).run publicationOwnership), after)', 1),
        ('omit-outer-cleanup', '((.ok (some .allocationFailure), (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).run handed), after)',
         '((.ok (some .allocationFailure), (Storage.Cleanup.sequence [.lastValue, .pop]).run handed), after)', 1),
        ('retain-published-row', 'Memory.Vector allocator (memory after).heap lifetime cells',
         'Memory.Vector allocator (memory after).heap lifetime (cells ++ cells)', 1),
        ('probe-before-preparation', 'ops.probe key (Publication.forget (memory (append runtimeSafety allocate allocator container cells input key normalized\n'
         '        ((key.eval meaning before.graph.read).getD 0) preparationOwnership (preparedFrame object copied operands installed)).2))',
         'ops.probe key (Publication.forget before.memory)', 1),
    )
    for name, before, after, count in changes:
        if source.count(before) != count:
            raise ValueError('ambiguous preparation mutation: ' + name)
        records += checked_controls(output, [mutation_check(output, 'native-preparation-' + name,
                                                           source.replace(before, after), False, env, lean)])
    return records
