#!/usr/bin/env python3
"""Audit native insertion callback memory, ownership handoffs and rejection.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import re

from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

MODULE = 'Compiler.Extraction.InternerInsertionNativeTests'
NATIVE = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.'
REGISTERED = 'Compiler.Extraction.RepresentativeArray.Append.Registered.'
CLAIMS = [REGISTERED + name for name in ('finish_reached', 'reached', 'admit_vector', 'admit_first', 'completed', 'rejected', 'oom')]
CLAIMS += [NATIVE + name for name in ('allocation_keys', 'append_callback')]
CLAIMS += [NATIVE + 'Controls.' + name for name in ('creation_oom_effects', 'pop_rejected', 'owner_rejected', 'header_read', 'length_rejected')]
CLAIMS += [NATIVE + 'Tests.' + name for name in (
    'registered_run', 'same_execution', 'accepted_queries', 'transferred_borrow',
    'deterministic_success', 'actual_descriptor', 'append_oom', 'publication_scope', 'publication_normalized',
    'publication_vector', 'publication_capacity', 'publication_old_row', 'registry_rejections',
    'partial_store_retained', 'header_mismatch_rejected', 'missing_locals', 'early_oom',
    'source_rejection_retained', 'nonempty_growth_scope')]


def audit(claims):
    registry = 'Compiler.Extraction.AssemblyClone.NativeFields.RegistryTests.'
    query = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.BorrowedQuery.Native.'
    required = {
        REGISTERED + 'reached': {REGISTERED + 'run', REGISTERED + 'finish_reached'},
        REGISTERED + 'completed': {REGISTERED + 'run', 'Compiler.Extraction.RepresentativeArray.readHeader_items'},
        NATIVE + 'append_callback': {NATIVE + 'callbacks', REGISTERED + 'run'},
        NATIVE + 'Tests.registered_run': {REGISTERED + 'completed', REGISTERED + 'admit_first',
                                         REGISTERED + 'admit_vector', registry + 'registered_execution'},
        NATIVE + 'Tests.same_execution': {NATIVE + 'callbacks',
            'Compiler.Extraction.AssemblyItem.Creation.NativeFields.operations', REGISTERED + 'run'},
        NATIVE + 'Tests.accepted_queries': {NATIVE + 'Tests.same_execution', registry + 'registered_execution', query + 'of_resident'},
        NATIVE + 'Tests.transferred_borrow': {NATIVE + 'Tests.accepted_queries', registry + 'accepted_borrow'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('native insertion lost checked dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'nativeAppendRetainsReachedMemoryAndEffects': True,
            'reachedInsertionLocalsSupplyDescriptor': True, 'sourceBoundTransferQueriesVerified': True,
            'nativePublicationRollbackVerified': False, 'nonemptyGrowthIntegrated': False,
            'completeGraphCorrespondenceVerified': False, 'recursiveConstructorsVerified': False}


def controls(output, env, lean):
    directory = ROOT / 'lean/Compiler/Extraction'
    imports = ('import Compiler.Extraction.InternerInsertionTests\n'
               'import Compiler.Extraction.RepresentativeRemapGrowth\n'
               'import Compiler.Extraction.AssemblyItemDeinitNative\n'
               'import Compiler.Extraction.ExpressionDeinitNative\n'
               'import Compiler.Extraction.RepresentativeLastExpression\n'
               'import Compiler.Extraction.RepresentativeRegisteredPop\n')
    # Keep rejection probes small: expanding a corrupted complete insertion
    # state can exhaust diagnostic pretty-printing. Full execution fixtures
    # remain in the audited module and fresh replay; guards stay unchanged.
    source = imports + '\n'.join(without_imports((directory / name).read_text()) for name in (
        'RepresentativeRegisteredAppend.lean', 'RepresentativeRegisteredCapacity.lean',
        'RepresentativeRegisteredGrowthAppend.lean', 'InternerInsertionNative.lean', 'InternerInsertionNativeControls.lean'))
    changes = (
        ('discard-native-memory', 'let reached : Session σ := { before with memory, effects }',
         'let reached : Session σ := { before with effects }'),
        ('fault-is-oom', '| .error reason => (.error (.memory reason), reached)\n  | .ok none',
         '| .error _ => (.ok false, reached)\n  | .ok none'),
        ('omit-registered-row', '(some ⟨allocator, .representatives (cells ++ [cell])⟩)) })',
         '(some ⟨allocator, .representatives cells⟩)) })'),
        ('discard-created-item', '(result.mapError Fault.item, { before with item := reached })',
         '(result.mapError Fault.item, before)'),
        ('old-boolean-append', '| .append => append runtimeSafety allocate allocator container cells input key normalized value owner before growth',
         '| .append => let (result, reached) := base.attempt .append owner before; (result.mapError Fault.base, reached)'),
        ('ignore-registry-owner', 'if owner = allocator then .ok () else .error .wrongAllocator',
         'if true then .ok () else .error .wrongAllocator'),
        ('ignore-header-length', 'type = itemsType ∧ data.offset = 0 ∧ length = cells.length + 1',
         'type = itemsType ∧ data.offset = 0'),
        ('discard-key-table', '(result, { effects with allocator := reached })', '(result, ⟨fun _ => none, reached⟩)'),
        ('wrong-argument-local', '(cell input key normalized value owner before) (memory before)\n      | some calls',
         '({ cell input key normalized value owner before with arguments := normalized.items, argumentsAddress := normalized.address }) (memory before)\n      | some calls'),
        ('fake-pop', '| .pop => pop allocator container before', '| .pop => (.ok (), before)'),
    )
    for name, before, _ in changes:
        if source.count(before) != 1:
            raise ValueError('ambiguous native insertion mutation: ' + name)
    records = [mutation_check(output, 'native-insertion-unchanged', source, True, env, lean)]
    for name, before, after in changes:
        records.append(mutation_check(output, 'native-insertion-' + name, source.replace(before, after), False, env, lean))
    records.append(mutation_check(output, 'native-insertion-kernel-reflexivity-rejects',
                                  'import ' + MODULE + '\nexample : (1 : Nat) = 2 := by insertion_kernel_rfl\n', False, env, lean))
    for record in records:
        diagnostic = (output / (record['name'] + '.stdout')).read_text()
        if re.search(r'maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant|unknown tactic', diagnostic, re.I):
            raise ValueError('native insertion control hit a resource or syntax failure: ' + record['name'])
        if not record['expectedAcceptance'] and not re.search(
                r'error: (?:unsolved goals|Application type mismatch|Type mismatch|Tactic[^\n]*failed)', diagnostic):
            raise ValueError('native insertion control lacks a semantic proof failure: ' + record['name'])
    return records
