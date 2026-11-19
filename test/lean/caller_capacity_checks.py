#!/usr/bin/env python3
"""Audit reached native insertion capacity and caller-derived normalized cleanup.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NATIVE = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.'
STORAGE = 'Compiler.Extraction.Storage.'
TESTS = NATIVE + 'CallerGrowingChainTests.CapacityTests.'
CLAIMS = [NATIVE + name for name in ('headerCount_read', 'checkedCount_read', 'checkedCount_mismatch',
          'checkedExecution_read', 'checkedExecution_rejected', 'CallerInput.free_incoming',
          'CallerInput.checked_execution', 'CallerInput.capacity_failure')]
CLAIMS += [STORAGE + 'insert_capacity_failure']
CLAIMS += [NATIVE + 'CountTests.' + name for name in ('native_boundary_reads', 'capacity_boundary',
          'capacity_field_not_read', 'mismatch_rejects', 'unreadable_rejects', 'only_normalized_cleanup')]
CLAIMS += [TESTS + name for name in ('initialized_entry', 'checked_preparation_oom')]


def audit(claims):
    required = {
        NATIVE + 'headerCount_read': {NATIVE + 'headerCount', 'Compiler.Extraction.RepresentativeArray.readItems'},
        NATIVE + 'checkedExecution_read': {NATIVE + 'checkedCount_read', NATIVE + 'executionWithRoom'},
        NATIVE + 'checkedExecution_rejected': {NATIVE + 'checkedExecution', NATIVE + 'checkedCount'},
        NATIVE + 'CallerInput.free_incoming': {
            'Compiler.Extraction.Memory.Arguments.Normalization.free_valid', NATIVE + 'free_keys', NATIVE + 'free_keeps_dead'},
        NATIVE + 'CallerInput.checked_execution': {NATIVE + 'CallerInput.native_frame', NATIVE + 'checkedExecution_read',
            'Compiler.Extraction.RepresentativeArray.readField_eq_of_lookup'},
        NATIVE + 'CallerInput.capacity_failure': {NATIVE + 'CallerInput.free_incoming',
            NATIVE + 'CallerInput.checked_execution', NATIVE + 'capacity_execution'},
        STORAGE + 'insert_capacity_failure': {STORAGE + 'insertProgram', STORAGE + 'Program.execute'},
        NATIVE + 'CountTests.only_normalized_cleanup': {STORAGE + 'insert_capacity_failure'},
        TESTS + 'initialized_entry': {NATIVE + 'CallerGrowingChainTests.initialized_prefix', NATIVE + 'CallerInput.checked_execution'},
        TESTS + 'checked_preparation_oom': {TESTS + 'initialized_entry',
            NATIVE + 'CallerGrowingChainTests.TransferredPreparationFailureTests.native_contract'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('native capacity lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'scope': 'native count binding and caller-entry capacity cleanup',
            'nativeHeaderReadBeforeCallbacks': True, 'rowCountMismatchExplicit': True,
            'bothDeterminismBranchesChecked': True, 'normalizedOwnershipDerivedFromCaller': True,
            'originalAllocationsKeysAndHistoryPreserved': True, 'initializedCallerEntryChecked': True,
            'largeCountFixturesAreHeaderOnly': True, 'recursiveChildTransportVerified': False,
            'wholeNativeGraphEstablishedByCountCheck': False, 'outerCapacityCompletionVerified': False,
            'nativeAllocatorVtableBindingVerified': False, 'nativeMapImplementationVerified': False,
            'completePublicationRollbackVerified': False, 'composedProductionTheoremVerified': False}


def mutation_cases():
    def source(*names):
        texts = [(ROOT / 'lean/Compiler/Extraction' / name).read_text() for name in names]
        defined = {'import Compiler.Extraction.' + name.removesuffix('.lean') for name in names}
        imports = sorted({line for text in texts for line in text.splitlines()
                          if line.startswith('import ') and line not in defined})
        return '\n'.join(imports) + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\nset_option pp.notation false\n' + '\n'.join(without_imports(text) for text in texts)
    return (
        ('count', source('InternerInsertionCount.lean'), (
            ('accept-maximum', 'count < 2 ^ 32 - 1', 'count ≤ 2 ^ 32 - 1', 1),
            ('wrong-id-bound', 'count < 2 ^ 32 - 1', 'count < 2 ^ 32', 1),
            ('wrong-owner', 'let items ← readItems state (Owner.headerAddress ⟨container, 0⟩)',
             'let items ← readItems state (Owner.headerAddress ⟨container + 1, 0⟩)', 1),
            ('capacity-field', 'let items ← readItems state (Owner.headerAddress ⟨container, 0⟩)',
             'let items ← readField state (Owner.headerAddress ⟨container, 0⟩) capacityOffset', 1),
            ('admit-mismatch', 'else .error (.mismatch count cells.length)', 'else .ok count', 1),
        )),
        ('caller', source('InternerCallerInsertionCapacity.lean'), (
            ('early-capacity', '(saturated : 2 ^ 32 - 1 ≤ cells.length)', '(saturated : 2 ^ 32 - 2 ≤ cells.length)', 1),
            ('capacity-is-oom', '((.ok (some .capacityFailure),', '((.ok (some .allocationFailure),', 2),
            ('retained-normalized-owner', 'Storage.Release.normalized.run Storage.normalizedOwnership', 'Storage.normalizedOwnership', 2),
            ('double-free-effect', 'else (Publication.external ops.arguments).free normalized taken.world.memory)',
             'else (Publication.external ops.arguments).free normalized { taken.world.memory with effects := (Publication.external ops.arguments).free normalized taken.world.memory })', 1),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    cases = mutation_cases()
    for group, text, changes in cases:
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous capacity mutation: ' + group + '-' + name)
    records = []
    for group, text, changes in cases:
        records += checked_controls(output, [mutation_check(output, 'capacity-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'capacity-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
