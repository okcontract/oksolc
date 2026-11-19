#!/usr/bin/env python3
"""Audit successful native insertion publication and exact key replacement.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NATIVE = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.'
PUBLICATION = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication.'
PHYSICAL = 'Compiler.Extraction.OwnedKeys.Physical.'
ARRAY = 'Compiler.Extraction.RepresentativeArray.'
STORAGE = 'Compiler.Extraction.Storage.'
CLAIMS = [PHYSICAL + 'Completed.registry_frame', PHYSICAL + 'Completed.registry_dead',
          PUBLICATION + 'publish_success', STORAGE + 'insert_prepared_success']
CLAIMS += [NATIVE + name for name in ('preparation_graph_frame', 'publication_rows', 'deterministic_growing_success')]
CLAIMS += [NATIVE + 'GrowingSuccessTests.' + name for name in (
    'initial_valid', 'preparation_results', 'backing_response', 'probe_result', 'derived_contract', 'reached_observations')]


def audit(claims):
    required = {
        PHYSICAL + 'Completed.registry_frame': {'Compiler.Extraction.OwnedKeys.retire_frame'},
        PUBLICATION + 'publish_success': {PHYSICAL + 'run_local_spec', PUBLICATION + 'admit_complete',
            'Compiler.Extraction.OwnedKeys.retire_slice'},
        STORAGE + 'insert_prepared_success': {STORAGE + 'insertProgram', STORAGE + 'Program.execute', STORAGE + 'Cleanup.execute'},
        NATIVE + 'preparation_graph_frame': {NATIVE + 'arguments_retained', PUBLICATION + 'Input.frame', ARRAY + 'DescriptorRelation.frame'},
        NATIVE + 'publication_rows': {PUBLICATION + 'publish_success', PHYSICAL + 'Completed.registry_frame',
            PHYSICAL + 'Completed.registry_dead', ARRAY + 'DescriptorRelation.query', 'Compiler.ZigAir.Memory.Heap.lookup_ne_of_type_ne'},
        NATIVE + 'deterministic_growing_success': {NATIVE + 'prepare_owned', NATIVE + 'preparation_graph_frame',
            NATIVE + 'growing_append_owned', NATIVE + 'publication_rows', STORAGE + 'insert_prepared_success'},
        NATIVE + 'GrowingSuccessTests.derived_contract': {NATIVE + 'deterministic_growing_success',
            NATIVE + 'GrowingSuccessTests.preparation_results', NATIVE + 'GrowingSuccessTests.backing_response',
            NATIVE + 'GrowingSuccessTests.probe_result'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('publication success lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'completeDeterministicGrowingSuccess': True,
            'existingKeyReplacementConnected': True, 'normalizedKeyTransferDerived': True,
            'nativeDescriptorQueriesDerived': True, 'initialGraphAndInputPremisesExplicit': True,
            'nativeMapImplementationVerified': False, 'completeGraphCorrespondenceVerified': False,
            'completePublicationRollbackVerified': False, 'recursiveConstructorsVerified': False}


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls

    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / name).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        display = '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\nset_option pp.notation false\n'
        return imports + display + without_imports(raw)

    cases = (
        ('frame', source('OwnedKeysPhysicalFrame.lean'), (
            ('erase-unrelated', 'after.memory.heap id = before.memory.heap id', 'after.memory.heap id = none', 1),
            ('revive-old-key', 'after.memory.heap old.address = none', 'after.memory.heap old.address = before.memory.heap old.address', 1),
        )),
        ('publication', source('InternerPublicationSuccess.lean'), (
            ('ignore-failed-probe', '= (true, effects)', '= (false, effects)', 1),
            ('wrong-published-id', 'commit key id before (.ok (), after)', 'commit key (id + 1) before (.ok (), after)', 1),
            ('lose-incoming-owner', 'SliceValid allocator after.memory.heap owned := by',
             'SliceValid allocator after.memory.heap { owned with address := id.toNat } := by', 1),
        )),
        ('control', source('StoragePreparedRollback.lean'), (
            ('retain-normalized-flag', 'publicationOwnership).setFlag .normalized false',
             'publicationOwnership).setFlag .normalized true', 1),
            ('wrong-success-result', '((.ok (some .success), publishedOwnership), after)',
             '((.ok (some .allocationFailure), publishedOwnership), after)', 2),
        )),
        ('preparation', source('InternerInsertionPreparation.lean'), (
            ('wrong-owner-lifetime', 'after.memory.memory.heap.lookup container = some ownerCell',
             'after.memory.memory.heap.lookup (container + 1) = some ownerCell', 1),
            ('forget-key-frame', '(keys : after.memory.effects.keys = before.memory.effects.keys)', '(keys : True)', 1),
        )),
        ('rows', source('InternerInsertionPublicationSuccess.lean'), (
            ('wrong-key-owner', 'OwnedKeys.store (memory before).effects.keys key ⟨normalized.address,',
             'OwnedKeys.store (memory before).effects.keys key ⟨lifetime,', 1),
            ('rewind-history', '(memory after).memory.nextId = (memory before).memory.nextId',
             '(memory after).memory.nextId = 0', 1),
            ('discard-probe-effects', '| none => effects\n', '| none => (memory before).effects.allocator\n', 1),
            ('release-incoming-key', 'ops.arguments.free (OwnedKeys.slice key old)', 'ops.arguments.free normalized', 1),
            ('revive-replaced-key', '(memory after).heap old.address = none', '(memory after).heap old.address = (memory before).heap old.address', 1),
            ('wrong-query-id', '(DescriptorRelation.values id.toNat)', '(DescriptorRelation.values (id.toNat + 1))', 1),
        )),
        ('complete', source('InternerInsertionGrowingSuccess.lean'), (
            ('wrong-outcome', '((.ok (some .success), Storage.publishedOwnership), after)',
             '((.ok (some .allocationFailure), Storage.publishedOwnership), after)', 1),
            ('publish-duplicate', 'OwnedKeys.store before.memory.effects.keys key ⟨normalized.address,',
             'OwnedKeys.store before.memory.effects.keys key ⟨operands.address,', 1),
            ('revive-old-backing', '(memory after).heap oldLifetime = none', '(memory after).heap oldLifetime = before.memory.heap oldLifetime', 1),
            ('wrong-row-object', '⟨copied.item, value, object, operands.items, key.sequence, operands.address⟩',
             '⟨copied.item, value, object + 1, operands.items, key.sequence, operands.address⟩', 2),
            ('wrong-created-object', 'allocator input.item duplicated = (.ok object, allocated)',
             'allocator input.item duplicated = (.ok (object + 1), allocated)', 1),
        )),
    )
    for group, text, changes in cases:
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous publication success mutation: ' + group + '-' + name)
    records = []
    for group, text, changes in cases:
        records += checked_controls(output, [mutation_check(output, 'publication-success-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'publication-success-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
