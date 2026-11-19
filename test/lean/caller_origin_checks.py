#!/usr/bin/env python3
"""Audit caller-derived normalized ownership and publication admission.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NORMAL = 'Compiler.Extraction.Memory.Arguments.Normalization.'
CALLER = NORMAL + 'OwnedCall.Caller.'
PUBLICATION = NORMAL + 'OwnedCall.Publication.'
CLAIMS = [NORMAL + 'initialized_take_origin', CALLER + 'initialize_origin', CALLER + 'take_origin', CALLER + 'Origin.deinit']
CLAIMS += [PUBLICATION + name for name in ('region_keys', 'word_keys', 'allocation_keys', 'duplication_keys',
    'take_keys', 'reserve_keys', 'prepare_keys', 'init_keys', 'caller_init_keys', 'caller_take_keys', 'caller_input')]
CLAIMS += [PUBLICATION + 'OriginTests.' + name for name in ('initial_good', 'prefix_results', 'initial_keys',
    'derived_input', 'reached_observations', 'outer_deinit', 'duplicate_oom', 'incomplete_initialization')]


def audit(claims):
    required = {
        NORMAL + 'initialized_take_origin': {NORMAL + 'init_refines', NORMAL + 'init_frame', NORMAL + 'take_refines'},
        CALLER + 'initialize_origin': {CALLER + 'initialize_origin_frame', NORMAL + 'caller_buffer', NORMAL + 'init_frame',
            CALLER + 'initialize_verified', CALLER + 'initialize_graph'},
        CALLER + 'take_origin': {NORMAL + 'caller_buffer', NORMAL + 'initialized_take_origin', NORMAL + 'normalized_projection'},
        CALLER + 'Origin.deinit': {NORMAL + 'OwnedCall.deinit_detached'},
        PUBLICATION + 'caller_input': {CALLER + 'take_origin', PUBLICATION + 'caller_init_keys',
            PUBLICATION + 'caller_take_keys', NORMAL + 'OwnedCall.key_arguments'},
        PUBLICATION + 'OriginTests.derived_input': {PUBLICATION + 'caller_input', PUBLICATION + 'OriginTests.initial_good',
            PUBLICATION + 'OriginTests.prefix_results', PUBLICATION + 'OriginTests.initial_keys'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('caller ownership lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'actualCallerScratchAndTakeConnected': True,
            'originalRegistrySeparationDerived': True, 'publicationIncomingOwnerDerived': True,
            'outerDetachedCleanupDerived': True, 'initialKeyLivenessAndSourceSeparationExplicit': True,
            'nativeMapImplementationVerified': False, 'recursivePreservationVerified': False,
            'completeGraphInitializationVerified': False}


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls

    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / name).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\nset_option pp.notation false\n' + without_imports(raw)

    cases = (
        ('normalization', source('NormalizationTransferOrigin.lean'), (
            ('alias-original-owner', 'before.heap id = some block → slice.address ≠ id)',
             'before.heap id = some block → slice.address = id)'),
            ('wrong-normalized-values', 'slice.items = normalized commutative source values ∧', 'slice.items = values ∧'),
            ('erase-detachment', 'Taken allocator source values handle prepared slice remaining after ∧',
             'Taken allocator source values handle prepared slice handle after ∧'),
        )),
        ('caller', source('InternerCallerOrigin.lean'), (
            ('erase-initialization-frame', 'prepared.world.memory.memory.heap.lookup id = some cell',
             'prepared.world.memory.memory.heap.lookup id = none'),
            ('erase-initialization-registry', 'prepared.world.memory.heap id = some block',
             'prepared.world.memory.heap id = none'),
            ('handoff-before-insertion', 'scope : after.scope = ⟨some remaining, some slice, false⟩',
             'scope : after.scope = ⟨some remaining, some slice, true⟩'),
            ('erase-original-allocation', 'after.world.memory.memory.heap.lookup id = some cell',
             'after.world.memory.memory.heap.lookup id = none'),
            ('alias-unregistered-native-owner',
             'freshNative : ∀ id cell, before.memory.memory.heap.lookup id = some cell → slice.address ≠ id',
             'freshNative : ∀ id cell, before.memory.memory.heap.lookup id = some cell → slice.address = id'),
            # Initialization and take have the same actual scratch allocator.
            ('wrong-native-buffer-extent', '(.array 2 word)', '(.array 1 word)', 3),
        )),
        ('effects', source('PublicationNormalizationEffects.lean'), (
            ('drop-table-on-take', 'allocator handle before).2.effects.keys = before.effects.keys',
             'allocator handle before).2.effects.keys = (fun _ => none)'),
            ('drop-table-on-init', 'source buffer values before).2.effects.keys = before.effects.keys',
             'source buffer values before).2.effects.keys = (fun _ => none)'),
        )),
        ('input', source('InternerCallerPublicationInput.lean'), (
            ('wrong-key-input', '(made : Interner.makeKey request values = .ok key)',
             '(made : Interner.makeKey request [] = .ok key)'),
            ('wrong-old-key-allocator', '(live : ∀ old, before.memory.effects.keys key = some old → SliceValid allocator before.memory.heap (OwnedKeys.slice key old))',
             '(live : ∀ old, before.memory.effects.keys key = some old → SliceValid (allocator + 1) before.memory.heap (OwnedKeys.slice key old))'),
            ('wrong-source-invariant', 'source.length ≠ 0 → source.allocation ≠ old.address)',
             'source.length = 0 → source.allocation ≠ old.address)'),
        )),
        ('fixtures', source('InternerCallerOriginTests.lean'), (
            ('wrong-offset-copy', '| .offsetBorrow => ⟨0, 1, 2⟩', '| .offsetBorrow => ⟨0, 0, 2⟩'),
            ('reuse-replaced-owner', 'if case = .scratch then 5 else 4, sorted case',
             'if case = .scratch then 5 else 2, sorted case'),
            ('discard-oom-effects', 'failed.2.world.memory.effects.allocator = 9',
             'failed.2.world.memory.effects.allocator = 5'),
            ('discard-partial-allocation', 'incompleteResult.2.world.memory.heap 4 = some ⟨11, .arguments [3, 1, 2]⟩',
             'incompleteResult.2.world.memory.heap 4 = none'),
        )),
    )
    for group, text, changes in cases:
        for name, before, _, *occurrences in changes:
            if text.count(before) != (occurrences[0] if occurrences else 1):
                raise ValueError('ambiguous caller origin mutation: ' + group + '-' + name)
    records = []
    for group, text, changes in cases:
        records += checked_controls(output, [mutation_check(output, 'caller-origin-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, *_ in changes:
            records += checked_controls(output, [mutation_check(output, 'caller-origin-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
