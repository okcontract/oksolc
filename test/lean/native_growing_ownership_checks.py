#!/usr/bin/env python3
"""Audit preparation-derived ownership through growing insertion and cleanup.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NATIVE = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.'
ARRAY = 'Compiler.Extraction.RepresentativeArray.'
PUBLICATION = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication.'
CLAIMS = [NATIVE + name for name in ('representative_pointees', 'growing_append_owned',
    'growing_publication_oom_cleanup', 'deterministic_growing_oom')]
CLAIMS += [NATIVE + 'GrowingTests.' + name for name in (
    'initial_frame', 'initial_valid', 'preparation_results', 'backing_response', 'probe_result',
    'derived_contract', 'reached_observations', 'retained_allocations', 'backing_oom', 'invalid_backing_response')]


def audit(claims):
    required = {
        NATIVE + 'representative_pointees': {'Compiler.Extraction.AssemblyClone.NativeFields.Represents.frame',
            'Compiler.Extraction.AssemblyClone.Physical.Reads.frame', 'Compiler.ZigAir.Memory.Heap.lookup_ne_of_type_ne'},
        ARRAY + 'Append.Registered.growing_verified': {ARRAY + 'Append.Execution.spare_verified',
            ARRAY + 'Backing.Fallback.storage', ARRAY + 'Backing.Fallback.owner_shape'},
        NATIVE + 'growing_append_owned': {NATIVE + 'representative_pointees', ARRAY + 'Append.Registered.growing_verified'},
        NATIVE + 'growing_publication_oom_cleanup': {NATIVE + 'growing_append_owned', PUBLICATION + 'Input.frame',
            PUBLICATION + 'publish_oom', NATIVE + 'rollback_normalized_verified'},
        NATIVE + 'deterministic_growing_oom': {NATIVE + 'prepare_owned', NATIVE + 'growing_publication_oom_cleanup',
            ARRAY + 'DescriptorRelation.frame', 'Compiler.Extraction.Storage.insert_prepared_oom'},
        NATIVE + 'GrowingTests.derived_contract': {NATIVE + 'deterministic_growing_oom',
            NATIVE + 'GrowingTests.preparation_results', NATIVE + 'GrowingTests.backing_response', NATIVE + 'GrowingTests.probe_result'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('growing ownership lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'growingPublicationOomCleanupOwnersDerived': True,
            'completeDeterministicGrowingPublicationOom': True, 'outerNormalizedCleanupConnected': True,
            'initialGraphAndInputPremisesExplicit': True, 'actualAllocatorVtableBindingVerified': False,
            'completePublicationRollbackVerified': False, 'recursiveConstructorsVerified': False}


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    directory = ROOT / 'lean/Compiler/Extraction'

    def source(name):
        raw = (directory / name).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        # Bound diagnostics only; proof limits and acceptance guards stay unchanged.
        display = '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\nset_option pp.notation false\n'
        return imports + display + without_imports(raw)

    cases = (
        ('frame', source('InternerInsertionPointeeFrame.lean'), (
            ('lose-item', 'AssemblyItem.Owned allocator object after ∧', 'AssemblyItem.Owned allocator (object + 1) after ∧', 1),
            ('lose-payload-bytes', 'AssemblyClone.Physical.Reads after.memory payload.data) := by',
             'AssemblyClone.Physical.Reads after.memory { payload.data with address := object }) := by', 1),
            ('item-target', 'before.heap id = none ∨ ∃ old, Memory.Vector allocator before.heap id old',
             'before.heap id = some ⟨allocator, .item stored.item⟩ ∨ ∃ old, Memory.Vector allocator before.heap id old', 1),
        )),
        ('owners', source('InternerInsertionGrowingOwnership.lean'), (
            ('wrong-row-object', '= .ok ⟨object, 0⟩ ∧', '= .ok ⟨object + 1, 0⟩ ∧', 1),
            ('alias-row-arguments', '.ok (.slice Expression.argumentsType ⟨operands.address, 0⟩ operands.items.length) ∧',
             '.ok (.slice Expression.argumentsType ⟨normalized.address, 0⟩ operands.items.length) ∧', 1),
            ('discard-old-release', 'allocator := freeBacking allocator oldCell.base (oldCapacity * 32) 8 allocationEffects',
             'allocator := allocationEffects', 1),
            ('revive-old-backing', '(memory after).heap oldLifetime = none',
             '(memory after).heap oldLifetime = (memory before).heap oldLifetime', 2),
            ('rewind-lifetime', '(memory after).memory.nextId = lifetime + 1', '(memory after).memory.nextId = lifetime', 1),
            ('free-relocated-container', 'Memory.Vector allocator (memory after).heap (memory before).memory.nextId cells',
             '(memory after).heap (memory before).memory.nextId = none', 1),
            ('discard-probe-effects', 'memory failed = { memory appended with effects := { (memory appended).effects with allocator := probeEffects } }',
             'memory failed = memory before', 1),
            ('alias-argument-owners', '(separate : operands.items ≠ [] → normalized.items ≠ [] → normalized.address ≠ operands.address)',
             '(separate : True)', 1),
            ('release-wrong-buffer', 'allocator normalized (memory popped) = (.ok (), memory after)',
             'allocator operands (memory popped) = (.ok (), memory after)', 1),
        )),
        ('complete', source('InternerInsertionGrowingPrepared.lean'), (
            ('wrong-outcome', '((.ok (some .allocationFailure), (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).run handed), after)',
             '((.ok (some .success), (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).run handed), after)', 1),
            ('omit-outer-cleanup', '((.ok (some .allocationFailure), (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).run handed), after)',
             '((.ok (some .allocationFailure), (Storage.Cleanup.sequence [.lastValue, .pop]).run handed), after)', 1),
            ('rewind-history', '(memory after).memory.nextId = middle.memory.nextId + 1',
             '(memory after).memory.nextId = middle.memory.nextId', 1),
            ('wrong-created-object', 'allocator input.item duplicated = (.ok object, allocated)',
             'allocator input.item duplicated = (.ok (object + 1), allocated)', 1),
            ('wrong-cloned-value', 'allocator input allocated = (.ok copied, middle)',
             'allocator input allocated = (.ok input, middle)', 1),
        )),
    )
    for group, text, changes in cases:
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous growing ownership mutation: ' + group + '-' + name)
    records = []
    for group, text, changes in cases:
        records += checked_controls(output, [mutation_check(output, 'growing-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'growing-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
