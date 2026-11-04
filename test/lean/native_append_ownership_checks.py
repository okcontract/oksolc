#!/usr/bin/env python3
"""Audit spare append ownership through publication OOM and outer cleanup.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import re

from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NATIVE = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.'
PUBLICATION = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication.'
CLAIMS = [PUBLICATION + 'publish_oom', NATIVE + 'spare_append_owned', NATIVE + 'spare_publication_oom_cleanup']
CLAIMS += [NATIVE + 'AppendOwnershipTests.' + name for name in (
    'initial_valid', 'ready_eq', 'created_result', 'cloned_result', 'installed', 'derived_contract', 'observations',
    'admission_rejection', 'missing_clone_rejection')]


def audit(claims):
    required = {
        PUBLICATION + 'publish_oom': {PUBLICATION + 'publish', 'Compiler.Extraction.OwnedKeys.Physical.run'},
        NATIVE + 'spare_append_owned': {
            'Compiler.Extraction.RepresentativeArray.DescriptorRelation.spare_registered',
            'Compiler.Extraction.RepresentativeArray.Append.Execution.spare_verified',
            'Compiler.Extraction.RepresentativeArray.Append.Registered.completed',
            'Compiler.Extraction.AssemblyClone.NativeFields.Represents.frame',
            'Compiler.ZigAir.Memory.Heap.lookup_ne_of_type_ne'},
        NATIVE + 'spare_publication_oom_cleanup': {
            NATIVE + 'spare_append_owned', PUBLICATION + 'admit_complete', PUBLICATION + 'publish_oom',
            NATIVE + 'rollback_normalized_verified'},
        NATIVE + 'AppendOwnershipTests.installed': {
            'Compiler.Extraction.AssemblyClone.NativeFields.clone_install',
            'Compiler.Extraction.AssemblyItem.Creation.create_verified'},
        NATIVE + 'AppendOwnershipTests.derived_contract': {
            NATIVE + 'spare_publication_oom_cleanup', NATIVE + 'AppendOwnershipTests.installed'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('append ownership lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'spareAppendDerivesRollbackOwners': True,
            'publicationOomRetainsReachedEffects': True, 'outerCleanupUsesReachedNativeState': True,
            'initialCloneAndGraphPremisesExplicit': True, 'nativeHashMapRefinementVerified': False,
            'nonemptyGrowthIntegrated': False, 'completePublicationRollbackVerified': False,
            'recursiveConstructorsVerified': False}


def controls(output, env, lean):
    source = ('import Compiler.Extraction.InternerInsertionAppendPointees\n' +
              without_imports((ROOT / 'lean/Compiler/Extraction/InternerInsertionAppendOwnership.lean').read_text()))
    records = [mutation_check(output, 'append-ownership-unchanged', source, True, env, lean)]
    changes = (
        ('allow-full-backing', '(spare : cells.length < capacity)', '(spare : cells.length ≤ capacity)', 2),
        ('forget-clone-local', '(clonePresent : before.item.clone.value = some stored)', '(clonePresent : True)', 2),
        ('wrong-row-object', '= .ok ⟨object, 0⟩ ∧', '= .ok ⟨object + 1, 0⟩ ∧', 1),
        ('alias-row-to-normalized', '.ok (.slice Expression.argumentsType ⟨operands.address, 0⟩ operands.items.length) ∧',
         '.ok (.slice Expression.argumentsType ⟨normalized.address, 0⟩ operands.items.length) ∧', 1),
        ('probe-before-append', '(append runtimeSafety allocate allocator container cells input key normalized value ownership before).2))',
         'before))', 1),
        ('discard-probe-effects', 'memory failed = { memory appended with effects := { (memory appended).effects with allocator := probeEffects } }',
         'memory failed = memory before', 1),
        ('omit-normalized-release', '[.lastValue, .pop, .normalized]', '[.lastValue, .pop]', 2),
        ('allow-double-free', '(separate : operands.items ≠ [] → normalized.items ≠ [] → normalized.address ≠ operands.address)',
         '(separate : True)', 1),
        ('forget-normalized-owner', '(normalizedLive : Memory.SliceValid allocator (memory before).heap normalized)',
         '(normalizedLive : True)', 1),
        ('rewind-history', '(memory after).memory.nextId = (memory before).memory.nextId',
         '(memory after).memory.nextId = 0', 2),
    )
    for name, before, after, count in changes:
        if source.count(before) != count:
            raise ValueError('ambiguous append ownership mutation: ' + name)
        records.append(mutation_check(output, 'append-ownership-' + name, source.replace(before, after), False, env, lean))
    records.append(mutation_check(output, 'append-ownership-kernel-equality-rejection',
        'import Compiler.Extraction.InsertionKernelTestSupport\nexample : (1 : Nat) = 2 := by insertion_kernel_rfl\n',
        False, env, lean))
    for record in records:
        diagnostic = (output / (record['name'] + '.stdout')).read_text()
        if re.search(r'maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant|unknown tactic', diagnostic, re.I):
            raise ValueError('append ownership control hit a resource or syntax failure: ' + record['name'])
        if not record['expectedAcceptance'] and not re.search(
                r'unsolved goals|Type mismatch|Tactic [^\n]*(?:failed|proved)|Dependent elimination failed|Application type mismatch',
                diagnostic, re.I):
            raise ValueError('append ownership control has no semantic proof failure: ' + record['name'])
    return records
