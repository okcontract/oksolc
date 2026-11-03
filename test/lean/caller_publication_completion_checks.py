#!/usr/bin/env python3
"""Audit actual caller publication, handoff and outer argument cleanup.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NS = 'Compiler.Extraction.Memory.Arguments.Normalization.'
PUB = NS + 'OwnedCall.Publication.'
CLAIMS = [PUB + name for name in ('complete_taken', 'Completion.closed', 'Completion.linked',
    'force_after_take', 'caller_owned_publication')]
CLAIMS += [PUB + 'CompletionTests.' + name for name in ('initial_good', 'foreign_different',
    'initial_keys', 'prefix_results', 'derived_completion', 'reached_observations')]


def audit(claims):
    required = {
        PUB + 'complete_taken': {PUB + 'publish_success', PUB + 'publish_oom', NS + 'free_valid',
            'Compiler.Extraction.OwnedKeys.after_live', 'Compiler.Extraction.OwnedKeys.store_unique',
            NS + 'OwnedCall.Caller.Origin.freshNative', NS + 'OwnedCall.finish'},
        PUB + 'Completion.linked': {'Compiler.Extraction.OwnedKeys.view_store'},
        PUB + 'force_after_take': {'Compiler.Extraction.Interner.ForceCode.controlOwned', NS + 'OwnedCall.take'},
        PUB + 'caller_owned_publication': {PUB + 'caller_input', PUB + 'complete_taken', PUB + 'force_after_take'},
        PUB + 'CompletionTests.derived_completion': {PUB + 'caller_owned_publication',
            PUB + 'CompletionTests.initial_keys', PUB + 'CompletionTests.prefix_results'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('caller publication lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'actualOwnedContinuationConnected': True,
            'outerNormalizedCleanupDerived': True, 'globalKeyLivenessAndUniquenessPreserved': True,
            'cacheProjectionPreserved': True, 'exactProbeAndFreeEffectsPreserved': True,
            'initialGraphAndKeyInvariantsExplicit': True, 'cacheRoutingVerified': False,
            'nativeMapProbeImplementationVerified': False, 'recursiveChildPreservationVerified': False,
            'completePublicationRollbackVerified': False}


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls

    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / name).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\nset_option pp.notation false\n' + without_imports(raw)

    cases = (
        ('completion', source('InternerPublicationCompletion.lean'), (
            ('retain-oom-ownership', 'else ⟨none, none, false⟩', 'else ⟨none, some owned, false⟩', 1),
            ('wrong-published-id', 'keys : after.world.memory.effects.keys = if accepted then OwnedKeys.store taken.memory.effects.keys key ⟨owned.address, id⟩',
             'keys : after.world.memory.effects.keys = if accepted then OwnedKeys.store taken.memory.effects.keys key ⟨owned.address, id + 1⟩', 1),
            ('rewind-lifetime-history', 'nextId : after.world.memory.memory.nextId = taken.memory.memory.nextId',
             'nextId : after.world.memory.memory.nextId = before.memory.memory.nextId', 1),
            ('discard-oom-free-effects', 'else if owned.items.isEmpty then effects else host.free owned { forget taken.memory with effects }',
             'else effects', 1),
            ('revive-replaced-native-key', 'after.world.memory.memory.heap.lookup old.address = none',
             'after.world.memory.memory.heap.lookup old.address = taken.memory.memory.heap.lookup old.address', 1),
            ('lose-global-key-liveness', 'live : OwnedKeys.Live allocator ⟨after.world.memory.effects.keys, after.world.memory.heap⟩',
             'live : OwnedKeys.Live (allocator + 1) ⟨after.world.memory.effects.keys, after.world.memory.heap⟩', 1),
            ('omit-initial-key-uniqueness', '(unique : OwnedKeys.Unique before.memory.effects.keys)',
             '(unique : OwnedKeys.Unique (fun _ => none))', 1),
        )),
        ('caller', source('InternerCallerPublicationCompletion.lean'), (
            ('publish-after-failed-take', '(transferred : take (external host) allocator prepared = (.ok (), taken))',
             '(transferred : take (external host) allocator prepared = (.error (.language .outOfMemory), taken))', 2),
            ('wrong-key-construction', '(made : Interner.makeKey request values = .ok key)',
             '(made : Interner.makeKey request values.reverse = .ok key)', 2),
            ('convert-oom-to-success', '(if accepted then .ok () else .error (.language .outOfMemory), after)',
             '(.ok (), after)', 1),
        )),
        ('fixtures', source('InternerCallerPublicationCompletionTests.lean'), (
            ('reverse-probe-outcome', '(accepted, memory.effects * 10 + 1)', '(!accepted, memory.effects * 10 + 1)', 1),
            ('wrong-unrelated-key-payload', 'if case = .replacement then [] else [99]',
             'if case = .replacement then [] else [98]', 1),
            ('retain-incoming-after-oom', 'accepted && !(slice case).items.isEmpty, true,',
             '!(slice case).items.isEmpty, true,', 1),
            ('discard-unrelated-key', 'some ⟨2, 12⟩) := by', 'none) := by', 1),
        )),
    )
    for group, text, changes in cases:
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous caller publication mutation: ' + group + '-' + name)
    records = []
    for group, text, changes in cases:
        records += checked_controls(output, [mutation_check(output, 'caller-publication-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'caller-publication-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
