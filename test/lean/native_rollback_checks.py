#!/usr/bin/env python3
"""Audit native destruction/pop composition from initial ownership.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import re

from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NATIVE = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.'
DEINIT = 'Compiler.Extraction.ExpressionDeinit.Native.'
CLAIMS = [DEINIT + 'run_owner_verified', NATIVE + 'rollback_equation', NATIVE + 'rollback_verified']
CLAIMS += [NATIVE + 'RollbackTests.' + name for name in (
    'lookup_other', 'initial_valid', 'derived_contract', 'logical_cleanup', 'allocator_effects',
    'empty_sentinel', 'destructor_rejection', 'pop_rejection')]


def audit(claims):
    memory = 'Compiler.ZigAir.Memory.'
    array = 'Compiler.Extraction.RepresentativeArray.'
    required = {
        DEINIT + 'run_owner_verified': {DEINIT + 'run_verified', memory + 'Heap.lookup_ne_of_type_ne',
                                        memory + 'invalidate_frame', 'Compiler.Extraction.Memory.Arguments.Normalization.free_empty'},
        NATIVE + 'rollback_equation': {'Compiler.Extraction.Storage.Cleanup.execute', NATIVE + 'callbacks',
                                        NATIVE + 'releaseLast', NATIVE + 'pop'},
        NATIVE + 'rollback_verified': {DEINIT + 'run_owner_verified', NATIVE + 'releaseLast_success',
                                       array + 'Last.from_array', array + 'readField_eq_of_lookup',
                                       array + 'Pop.Registered.verified', 'Compiler.Extraction.Storage.Cleanup.execute'},
        NATIVE + 'RollbackTests.derived_contract': {NATIVE + 'rollback_verified', NATIVE + 'RollbackTests.initial_valid'},
        NATIVE + 'Tests.publication_scope': {'Compiler.Extraction.Storage.insertProgram', NATIVE + 'callbacks',
                                            NATIVE + 'releaseLast', NATIVE + 'pop'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('native rollback lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'ownerHeaderFrameDerived': True,
            'initialOwnershipDerivesCleanupPop': True, 'cleanupSequenceRejectionsRetainReachedState': True,
            'stackAndPersistentOwnersChecked': True, 'emptySentinelMayAliasOwner': True,
            'universalCallerOwnershipEstablished': False, 'completePublicationRollbackVerified': False,
            'completeGraphCorrespondenceVerified': False, 'recursiveConstructorsVerified': False}


def controls(output, env, lean):
    source = ('import Compiler.Extraction.InternerInsertionExecution\n'
              'import Compiler.Extraction.AssemblyItemCreationFields\n'
              'import Compiler.Extraction.RepresentativeRegisteredGrowthAppend\n'
              'import Compiler.Extraction.AssemblyItemDeinitNative\n'
              'import Compiler.Extraction.ExpressionDeinitFrameProofs\n'
              'import Compiler.Extraction.RepresentativeLastExpression\n'
              'import Compiler.Extraction.RepresentativeRegisteredPop\n'
              'import Compiler.Extraction.RepresentativeOwnerLayout\n')
    source += '\n'.join(without_imports((ROOT / 'lean/Compiler/Extraction' / name).read_text()) for name in (
        'InternerInsertionNative.lean', 'ExpressionDeinitOwnerFrame.lean', 'InternerInsertionRollbackProofs.lean'))
    records = [mutation_check(output, 'native-rollback-unchanged', source, True, env, lean)]
    # Corrupt the actual callbacks/sequence, then overclaim frames and final
    # observations. These universal contracts must fail independently of the
    # concrete fixtures; no final header or final-validity premise is added.
    changes = (
        ('skip-destruction', '| .lastValue => releaseLast ops allocator container before', '| .lastValue => (.ok (), before)', 1),
        ('skip-pop', '| .pop => pop allocator container before', '| .pop => (.ok (), before)', 1),
        ('wrong-pop-owner', '| .pop => pop allocator container before', '| .pop => pop allocator (container + 1) before', 1),
        ('skip-sequence-pop', 'Storage.Cleanup.sequence [.lastValue, .pop]', 'Storage.Cleanup.sequence [.lastValue]', 3),
        ('reverse-sequence', 'Storage.Cleanup.sequence [.lastValue, .pop]', 'Storage.Cleanup.sequence [.pop, .lastValue]', 3),
        ('forget-owner-type', '(ownerTyped : ownerCell.type = Owner.viewType runtimeSafety)', '(ownerTyped : True)', 2),
        ('frame-dead-item', 'after.memory.memory.heap.lookup owner = before.memory.heap.lookup owner',
         'after.memory.memory.heap.lookup object = before.memory.heap.lookup object', 1),
        ('rewind-lifetime', 'after.memory.memory.nextId = before.memory.nextId', 'after.memory.memory.nextId = 0', 1),
        ('discard-effects', '(memory after).effects = reached.memory.effects', '(memory after).effects = (memory before).effects', 1),
        ('keep-vector-tail', 'Memory.Vector allocator (memory after).heap lifetime cells',
         'Memory.Vector allocator (memory after).heap lifetime (cells ++ [last])', 1),
        ('keep-header-length', '.ok (.slice itemsType ⟨lifetime, 0⟩ cells.length, .scalar (.int false 64 capacity))',
         '.ok (.slice itemsType ⟨lifetime, 0⟩ (cells.length + 1), .scalar (.int false 64 capacity))', 1),
        ('clear-invalidation', 'after.item.clone.execution.invalidated = true', 'after.item.clone.execution.invalidated = false', 1),
    )
    for name, before, after, count in changes:
        if source.count(before) != count:
            raise ValueError('ambiguous native rollback mutation: ' + name)
        records.append(mutation_check(output, 'native-rollback-' + name, source.replace(before, after), False, env, lean))
    for record in records:
        diagnostic = (output / (record['name'] + '.stdout')).read_text()
        if re.search(r'maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant|unknown tactic', diagnostic, re.I):
            raise ValueError('native rollback control hit a resource or syntax failure: ' + record['name'])
        if not record['expectedAcceptance'] and not re.search(
                r'error: (?:unsolved goals|Application type mismatch|Type mismatch|Tactic[^\n]*failed)', diagnostic):
            raise ValueError('native rollback control lacks a semantic proof failure: ' + record['name'])
    return records
