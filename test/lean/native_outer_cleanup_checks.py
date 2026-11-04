#!/usr/bin/env python3
"""Audit the normalized-argument cleanup derived through native rollback.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import re

from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NATIVE = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.'
STORAGE = 'Compiler.Extraction.Storage.'
CLAIMS = [STORAGE + 'releaseAll_append', NATIVE + 'rollback_normalized_verified']
CLAIMS += [NATIVE + 'OuterCleanupTests.' + name for name in (
    'initial_valid', 'derived_contract', 'effects_and_death', 'alias_rejected_after_pop', 'wrong_allocator_rejected')]


def audit(claims):
    required = {
        STORAGE + 'releaseAll_append': {STORAGE + 'releaseAll', STORAGE + 'Release.execute'},
        NATIVE + 'rollback_normalized_verified': {
            NATIVE + 'rollback_verified', STORAGE + 'releaseAll_append',
            'Compiler.Extraction.Memory.Arguments.Normalization.free_valid',
            'Compiler.ZigAir.Memory.Heap.lookup_ne_of_type_ne',
            'Compiler.Extraction.RepresentativeArray.readField_eq_of_lookup'},
        NATIVE + 'OuterCleanupTests.derived_contract': {
            NATIVE + 'rollback_normalized_verified', NATIVE + 'OuterCleanupTests.initial_valid'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('outer cleanup lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'normalizedCleanupDerivedFromInitialOwnership': True,
            'emptySentinelsNeedNoSeparation': True, 'aliasAndAllocatorRejectionsRetainCleanup': True,
            'universalCallerOwnershipEstablished': False, 'completePublicationRollbackVerified': False,
            'recursiveConstructorsVerified': False}


def controls(output, env, lean):
    source = ('import Compiler.Extraction.InternerInsertionRollbackProofs\n' +
              without_imports((ROOT / 'lean/Compiler/Extraction/InternerInsertionOuterCleanup.lean').read_text()))
    records = [mutation_check(output, 'outer-cleanup-unchanged', source, True, env, lean)]
    changes = (
        ('omit-normalized-release', '[.lastValue, .pop, .normalized]', '[.lastValue, .pop]', 3),
        ('release-normalized-first', '[.lastValue, .pop, .normalized]', '[.normalized, .lastValue, .pop]', 3),
        ('allow-double-free', '(separate : arguments.items ≠ [] → normalized.items ≠ [] → normalized.address ≠ arguments.address)',
         '(separate : True)', 1),
        ('forget-normalized-owner', '(normalizedLive : Memory.SliceValid allocator (memory before).heap normalized)',
         '(normalizedLive : True)', 1),
        ('rewind-history', '(memory after).memory.nextId = (memory before).memory.nextId',
         '(memory after).memory.nextId = 0', 1),
        ('discard-reached-effects', 'else (Publication.external ops.arguments).free normalized (memory popped))',
         'else (Publication.external ops.arguments).free normalized (memory before))', 1),
        ('retain-vector-tail', 'Memory.Vector allocator (memory after).heap lifetime cells',
         'Memory.Vector allocator (memory after).heap lifetime (cells ++ [last])', 1),
        ('retain-length', '.ok (.slice itemsType ⟨lifetime, 0⟩ cells.length, .scalar (.int false 64 capacity))',
         '.ok (.slice itemsType ⟨lifetime, 0⟩ (cells.length + 1), .scalar (.int false 64 capacity))', 1),
    )
    for name, before, after, count in changes:
        if source.count(before) != count:
            raise ValueError('ambiguous outer cleanup mutation: ' + name)
        records.append(mutation_check(output, 'outer-cleanup-' + name, source.replace(before, after), False, env, lean))
    for record in records:
        diagnostic = (output / (record['name'] + '.stdout')).read_text()
        if re.search(r'maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant|unknown tactic', diagnostic, re.I):
            raise ValueError('outer cleanup control hit a resource or syntax failure: ' + record['name'])
    return records
