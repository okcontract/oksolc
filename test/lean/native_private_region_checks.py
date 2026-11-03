"""Audit private native reservation through the existing graph invariant.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as expressions
from constructor_joint_checks import app
from native_resource_admission_checks import telescope
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check
from check_word_swap import ROOT
from native_map_write_checks import GRAPH, require

MODULE = 'Compiler.Extraction.InternerNativeGraphPrivateRegionTests'
TESTS = GRAPH + 'PrivateRegionTests.'
REGION = 'Compiler.ZigAir.Memory.RegionAllocation.'
CORE = ['Facts.reserve_private', 'Facts.reserve_private_success', 'PrivateRegion.oom']
REGRESSIONS = ['recursive_reservation', 'recursive_fields', 'successful_region', 'failed_region',
               'overlap_rejected', 'unaligned_rejected', 'empty_skips_host']
CLAIMS = [GRAPH + n for n in CORE] + [TESTS + n for n in REGRESSIONS]


def audit(rows):
    indexed = {row['theorem']: row for row in rows}
    dependencies = {
        GRAPH + 'Facts.reserve_private': {GRAPH + 'Facts.frame', REGION + 'reserve_heap_other',
            REGION + 'reserve_preserves_valid',
            'Compiler.Extraction.Memory.Arguments.Normalization.Valid.private_memory_frame',
            'Compiler.Extraction.Memory.Arguments.Normalization.Injected.fresh'},
        GRAPH + 'Facts.reserve_private_success': {GRAPH + 'Facts.reserve_private', REGION + 'reserve_admitted',
            REGION + 'extend_lookup', 'Compiler.Extraction.Memory.Arguments.Normalization.Injected.fresh'},
        GRAPH + 'PrivateRegion.oom': {REGION + 'reserve_failed'},
        TESTS + 'recursive_reservation': {GRAPH + 'Facts.reserve_private', GRAPH + 'Tests.recursive_after',
            GRAPH + 'Facts.operations', GRAPH + 'Facts.constants'},
        TESTS + 'recursive_fields': {TESTS + 'recursive_reservation', GRAPH + 'Facts.write_map'},
    }
    for name, needed in dependencies.items():
        require(needed <= set(indexed[name]['dependencies']), 'private reservation lost composition: ' + name)
    for name in CORE:
        require(not any(part.endswith('Tests') for dep in indexed[GRAPH + name]['dependencies'] for part in dep.split('.')),
                'private reservation depends on a fixture')
    common = ['σ', 'safety', 'allocator', 'owner', 'capacity', 'data', 'before', 'rows', 'facts']
    binders = {
        GRAPH + 'Facts.reserve_private': common + ['type', 'allocate'],
        GRAPH + 'Facts.reserve_private_success': common + ['type', 'layout', 'base', 'allocate', 'effects',
            'shaped', 'nonzero', 'bounded', 'response', 'fits'],
        GRAPH + 'PrivateRegion.oom': ['σ', 'before', 'type', 'layout', 'allocate', 'effects', 'valid',
            'shaped', 'nonzero', 'bounded', 'response'],
    }
    for name, expected in binders.items():
        value = indexed[name]['statement']
        fields, lets, root, scope = telescope(value)
        require(list(fields) == expected and not lets, 'private reservation gained a final-state or outcome premise: ' + name)
        if name == GRAPH + 'Facts.reserve_private':
            initial, context = fields['facts']
            require([expressions.named(value, a, context) for a in app(value, initial, GRAPH + 'Facts')] ==
                    ['σ', 'safety', 'allocator', 'owner', 'data', 'capacity', 'before', 'rows'],
                    'private reservation changed its initial graph')
            args = app(value, root, GRAPH + 'Facts')
            require([expressions.named(value, a, scope) for a in args[:6] + args[7:]] ==
                    ['σ', 'safety', 'allocator', 'owner', 'data', 'capacity', 'rows'],
                    'private reservation changed its resulting graph')
            result = app(value, args[6], 'Prod.snd')[-1]
            require([expressions.named(value, a, scope) for a in app(value, result, GRAPH + 'PrivateRegion.reserve')] ==
                    ['σ', 'type', 'allocate', 'before'], 'private reservation discarded its actual native result')
    for name in REGRESSIONS:
        fields, _, _, _ = telescope(indexed[TESTS + name]['statement'])
        expected = ['safety', 'depth', 'type', 'allocate'] if name.startswith('recursive_') else []
        if name == 'recursive_fields':
            expected += ['slot', 'value', 'typed', 'valid', 'active']
        require(list(fields) == expected, 'private reservation regression gained an assumption: ' + name)
    return {'checkedDependencies': sorted(dependencies), 'checkedStatements': sorted(binders),
            'allReservationOutcomesPreserveNativeGraph': True, 'actualNativeMemoryAndEffectsRetained': True,
            'nativeBucketLayoutAndOwnershipVerified': False, 'nativeHashMapVerified': False}


def controls(output, env, lean):
    source = (ROOT / 'lean/Compiler/Extraction/InternerNativeGraphPrivateRegions.lean').read_text()
    records = [mutation_check(output, 'private-region-unchanged', source, True, env, lean)]
    for name, before, after in (
        ('discard-memory', '⟨before.memory.heap, memory,', '⟨before.memory.heap, before.memory.memory,'),
        ('discard-effects', '⟨before.memory.effects.keys, effects⟩',
         '⟨before.memory.effects.keys, before.memory.effects.allocator⟩'),
        ('discard-registry', '⟨before.memory.heap, memory,', '⟨(fun _ => none), memory,'),
        ('discard-keys', '⟨before.memory.effects.keys, effects⟩', '⟨(fun _ => none), effects⟩'),
        ('discard-result', '(result, { before with memory :=', '(.ok none, { before with memory :='),
    ):
        require(source.count(before) == 1, 'ambiguous private region mutation: ' + name)
        records.append(mutation_check(output, 'private-region-' + name,
                                      source.replace(before, after, 1), False, env, lean))
    return checked_controls(output, records)
