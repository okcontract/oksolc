#!/usr/bin/env python3
"""Audit native representative length decrement and its registry refinement.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import re

from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

POP = 'Compiler.Extraction.RepresentativeArray.Pop.'
NATIVE = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.'
CLAIMS = [POP + name for name in ('read_rejected', 'empty', 'decrement', 'verified')]
CLAIMS += [POP + 'Registered.' + name for name in (
    'finish_reached', 'rejected', 'reached', 'finish_vector', 'finish_read_rejected',
    'finish_shape_rejected', 'finish_missing', 'finish_wrong_type', 'finish_wrong_owner', 'finish_stale', 'verified')]
CLAIMS += [NATIVE + name for name in ('pop_memory', 'pop_callback')]
CLAIMS += [NATIVE + 'PopTests.' + name for name in (
    'initial_valid', 'cleanup_valid', 'derived_contract', 'vector_restored', 'completed',
    'write_rejected', 'late_read_rejected', 'registry_rejected', 'boundary_rejected')]


def audit(claims):
    array = 'Compiler.Extraction.RepresentativeArray.'
    required = {
        POP + 'verified': {array + 'Owner.length_store_total', array + 'Append.Execution.owner_length_from_items',
                           array + 'Append.readItems_after_length_store_at', array + 'Append.readCapacity_after_length_store_at'},
        POP + 'Registered.verified': {POP + 'verified', POP + 'Registered.finish_vector', array + 'Backing.Registry.vector_write_valid',
                                      'Compiler.Extraction.Memory.resident_vector_write'},
        NATIVE + 'pop_callback': {NATIVE + 'callbacks', POP + 'Registered.run', POP + 'run'},
        NATIVE + 'PopTests.cleanup_valid': {NATIVE + 'releaseLast_verified'},
        NATIVE + 'PopTests.derived_contract': {NATIVE + 'PopTests.cleanup_valid', POP + 'Registered.verified'},
        NATIVE + 'Tests.publication_scope': {NATIVE + 'callbacks', NATIVE + 'releaseLast', NATIVE + 'pop', POP + 'run',
                                            'Compiler.Extraction.Storage.insertProgram'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('native pop lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'nativeHeaderAndRegistryPopVerified': True,
            'rejectionRetainsNativeWrite': True, 'nativePopCallbackAttached': True,
            'publicationRollbackFixturesVerified': True, 'universalCallerRollbackVerified': False,
            'completeGraphCorrespondenceVerified': False, 'recursiveConstructorsVerified': False}


def controls(output, env, lean):
    source = ('import Compiler.Extraction.RepresentativeGrowingAppend\n'
              'import Compiler.Extraction.RepresentativeBackingRegistry\n'
              'import Compiler.Extraction.NormalizationMemoryContracts\n')
    source += '\n'.join(without_imports((ROOT / 'lean/Compiler/Extraction' / name).read_text()) for name in (
        'RepresentativePop.lean', 'RepresentativeRegisteredPop.lean'))
    records = [mutation_check(output, 'native-pop-unchanged', source, True, env, lean)]
    changes = (
        ('read-capacity', 'let value ← readField state header Append.lengthOffset',
         'let value ← readField state header capacityOffset'),
        ('empty-is-success', 'if length ≤ 0 then .error .sourceBounds else', 'if length ≤ 0 then .ok state else'),
        ('skip-write', 'Append.writeLength state header (length.toNat - 1)', '.ok state'),
        ('wrong-decrement', 'Append.writeLength state header (length.toNat - 1)', 'Append.writeLength state header (length.toNat - 2)'),
        ('truncate-length', 'Append.writeLength state header (length.toNat - 1)',
         'Append.writeLength state header ((UInt32.ofNat length.toNat).toNat - 1)'),
        ('root-header', 'match Pop.run before.memory (Owner.headerAddress ⟨owner, 0⟩) with',
         'match Pop.run before.memory ⟨owner, 0⟩ with'),
        ('discard-native-write', '| .ok memory => finish allocator owner { before with memory }',
         '| .ok _ => finish allocator owner before'),
        ('hide-native-rejection', '| .error reason => (.error (.memory reason), before)', '| .error _ => (.ok (), before)'),
        ('hide-read-rejection', '| .error reason => (.error (.memory reason), reached)', '| .error _ => (.ok (), reached)'),
        ('ignore-offset', 'if type = itemsType ∧ data.offset = 0 then', 'if type = itemsType then'),
        ('ignore-type', 'if type = itemsType ∧ data.offset = 0 then', 'if data.offset = 0 then'),
        ('hide-absent-vector', '| none => (.error (.registry .unallocated), reached)', '| none => (.ok (), reached)'),
        ('hide-wrong-type', '| some _ => (.error (.registry .wrongType), reached)', '| some _ => (.ok (), reached)'),
        ('ignore-allocator', 'if actual ≠ allocator then', 'if False then'),
        ('ignore-length', 'if cells.length ≠ length + 1 then', 'if False then'),
        ('stale-registry', '.representatives cells.dropLast', '.representatives cells'),
        ('wrong-row', '.representatives cells.dropLast', '.representatives cells.tail'),
        ('discard-registry', '(some ⟨allocator, .representatives cells.dropLast⟩)', 'none'),
        ('reset-counter', '| .ok memory => finish allocator owner { before with memory }',
         '| .ok memory => finish allocator owner { before with memory := { memory with nextId := 0 } }'),
    )
    for name, before, after in changes:
        if source.count(before) != 1:
            raise ValueError('ambiguous native pop mutation: ' + name)
        records.append(mutation_check(output, 'native-pop-' + name, source.replace(before, after), False, env, lean))
    for record in records:
        diagnostic = (output / (record['name'] + '.stdout')).read_text()
        if re.search(r'maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant|unknown tactic', diagnostic, re.I):
            raise ValueError('native pop control hit a resource or syntax failure: ' + record['name'])
        if not record['expectedAcceptance'] and not re.search(
                r'error: (?:unsolved goals|Application type mismatch|Type mismatch|Tactic[^\n]*failed)', diagnostic):
            raise ValueError('native pop control lacks a semantic proof failure: ' + record['name'])
    return records
