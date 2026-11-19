#!/usr/bin/env python3
"""Audit reached native payload cleanup and insertion's value errdefer.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import re

from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

MEMORY = 'Compiler.ZigAir.Memory.'
ITEM = 'Compiler.Extraction.AssemblyItem.'
DEINIT = 'Compiler.Extraction.AssemblyItemDeinit.'
NATIVE = DEINIT + 'Native.'
INSERTION = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.'
CLAIMS = [MEMORY + 'invalidate_retains_shape', ITEM + 'session_frame']
CLAIMS += [NATIVE + name for name in (
    'payload_data', 'read_represented', 'finish_retains', 'finish_rejected', 'finish_verified', 'run_verified')]
CLAIMS += [NATIVE + 'Tests.' + name for name in (
    'initial_valid', 'initial_members', 'initial_ownership', 'derived_contract', 'actual_destruction',
    'all_members_uninitialized', 'history_and_arguments', 'absent_and_empty', 'rejected_payload',
    'failed_invalidation_keeps_release', 'field_failures', 'projection_preserves_offset')]
CLAIMS += [INSERTION + name for name in ('value_callback', 'releaseValue_success', 'releaseValue_rejected')]
CLAIMS += [INSERTION + 'CleanupTests.' + name for name in (
    'native_payload_wins', 'rejection_keeps_reached', 'missing_object', 'source_callback')]


def audit(claims):
    required = {
        MEMORY + 'invalidate_retains_shape': {MEMORY + 'invalidate_contents', MEMORY + 'invalidate_frame'},
        ITEM + 'session_frame': {'Compiler.Extraction.Memory.Arguments.Normalization.represented_frame'},
        NATIVE + 'read_represented': {'Compiler.Extraction.AssemblyClone.NativeFields.Represents.typed',
                                     ITEM + 'Fields.verbatim', NATIVE + 'payload_data'},
        NATIVE + 'finish_verified': {MEMORY + 'invalidate_of_access', MEMORY + 'invalidate_valid',
                                     MEMORY + 'invalidate_retains_shape', ITEM + 'session_frame'},
        NATIVE + 'run_verified': {NATIVE + 'run', NATIVE + 'read_represented', DEINIT + 'run_verified',
                                  ITEM + 'after_payload', NATIVE + 'finish_verified'},
        NATIVE + 'Tests.derived_contract': {NATIVE + 'run_verified'},
        INSERTION + 'value_callback': {INSERTION + 'callbacks', INSERTION + 'releaseValue', NATIVE + 'run'},
        INSERTION + 'releaseValue_rejected': {INSERTION + 'releaseValue', NATIVE + 'run'},
        INSERTION + 'CleanupTests.source_callback': {INSERTION + 'callbacks', INSERTION + 'releaseValue', NATIVE + 'run'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('native item cleanup lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'nativePayloadReadAndInvalidationVerified': True,
            'insertionValueCleanupAttached': True, 'rejectionRetainsCompletedRelease': True,
            'nativeExpressionDestructorAttached': False, 'nativePublicationRollbackVerified': False,
            'completeGraphCorrespondenceVerified': False}


def controls(output, env, lean):
    source = ('import Compiler.Extraction.AssemblyCloneFieldFixtures\n'
              'import Compiler.Extraction.InternerInsertionTests\n'
              'import Compiler.Extraction.RepresentativeRegisteredAppend\n'
              'import Compiler.ZigAir.MemoryInvalidation\n'
              'import Compiler.Extraction.ExpressionInvalidation\n'
              'import Compiler.Extraction.RepresentativeRegisteredPop\n')
    # Symbolic source/ownership equations keep rejection diagnostics bounded.
    # Full native behavior fixtures remain audited roots and fresh-replay inputs.
    source += '\n'.join(without_imports((ROOT / 'lean/Compiler/Extraction' / name).read_text()) for name in (
        'AssemblyItemDeinitNative.lean', 'ExpressionDeinitFields.lean', 'ExpressionDeinitNative.lean',
        'RepresentativeLastExpression.lean', 'InternerInsertionNative.lean'))
    records = [mutation_check(output, 'native-item-deinit-unchanged', source, True, env, lean)]
    changes = (
        ('reset-offset', '.ok ⟨data.allocation, length, data.offset⟩', '.ok ⟨data.allocation, length, 0⟩'),
        ('wrong-payload-field', 'entry.1 == AssemblyItem.verbatim_dataOffset', 'entry.1 == AssemblyItem.verbatim_argumentsOffset'),
        ('skip-native-read', 'match readPayload before.memory object with',
         'match (Except.ok none : Except Compiler.ZigAir.Memory.Fault (Option Bytes)) with'),
        ('skip-payload-free', 'let (result, reached) := AssemblyItemDeinit.run external allocator payload before',
         'let (result, reached) := AssemblyItemDeinit.run external allocator none before'),
        ('wrong-allocator', 'let (result, reached) := AssemblyItemDeinit.run external allocator payload before',
         'let (result, reached) := AssemblyItemDeinit.run external (allocator + 1) payload before'),
        ('skip-invalidation', 'match Compiler.ZigAir.Memory.invalidate reached.memory true AssemblyItem.viewType object with',
         'match (Except.ok reached.memory : Except Compiler.ZigAir.Memory.Fault Compiler.ZigAir.Memory.State) with'),
        ('discard-release', '| .ok () => finish object reached.memory', '| .ok () => finish object before'),
        ('false-invalidated-marker', '| .error reason => (.error (.memory reason), ⟨reached, false⟩)',
         '| .error reason => (.error (.memory reason), ⟨reached, true⟩)'),
        ('old-logical-cleanup', '| .value => releaseValue ops allocator before',
         '| .value => let (result, reached) := base.release .value owner before; (result.mapError Fault.base, reached)'),
        ('discard-rejected-state', '| .error reason => (.error (.cleanup reason), next)',
         '| .error reason => (.error (.cleanup reason), before)'),
        ('retain-clone-local', '| .ok () => (.ok (), { next with item := { next.item with clone := { next.item.clone with value := none } } })',
         '| .ok () => (.ok (), next)'),
    )
    for name, before, after in changes:
        if source.count(before) != 1:
            raise ValueError('ambiguous native item deinit mutation: ' + name)
        records.append(mutation_check(output, 'native-item-deinit-' + name, source.replace(before, after), False, env, lean))
    for record in records:
        diagnostic = (output / (record['name'] + '.stdout')).read_text()
        if re.search(r'maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant|unknown tactic', diagnostic, re.I):
            raise ValueError('native item deinit control hit a resource or syntax failure: ' + record['name'])
        if not record['expectedAcceptance'] and not re.search(
                r'error: (?:unsolved goals|Application type mismatch|Type mismatch|Tactic[^\n]*failed)', diagnostic):
            raise ValueError('native item deinit control lacks a semantic proof failure: ' + record['name'])
    return records
