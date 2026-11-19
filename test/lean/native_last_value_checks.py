#!/usr/bin/env python3
"""Audit native last-row selection and insertion publication cleanup.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import re

from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

ARRAY = 'Compiler.Extraction.RepresentativeArray.'
NATIVE = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.'
EXPRESSION = 'Compiler.Extraction.ExpressionDeinit.Native.'
CLAIMS = [ARRAY + 'Append.selectNewElement_from_array']
CLAIMS += [ARRAY + 'Last.' + name for name in ('read_rejected', 'empty', 'from_array')]
CLAIMS += [NATIVE + name for name in (
    'releaseLast_unselected', 'releaseLast_success', 'releaseLast_rejected', 'last_value_callback', 'releaseLast_verified')]
CLAIMS += [NATIVE + 'LastTests.' + name for name in (
    'initial_valid', 'selected_last', 'derived_contract', 'actual_cleanup', 'late_failure',
    'selection_failures', 'final_write_failure', 'repeated_cleanup')]


def audit(claims):
    required = {
        ARRAY + 'Append.selectNewElement_from_array': {ARRAY + 'element_pointer', ARRAY + 'element_record_view',
                                                       ARRAY + 'Append.nextLength_bounded'},
        ARRAY + 'Last.from_array': {ARRAY + 'Last.select', ARRAY + 'Append.selectNewElement_from_array'},
        NATIVE + 'releaseLast_verified': {ARRAY + 'Last.from_array', EXPRESSION + 'run_verified', NATIVE + 'releaseLast_success'},
        NATIVE + 'last_value_callback': {NATIVE + 'callbacks', NATIVE + 'releaseLast', ARRAY + 'Last.select', EXPRESSION + 'run'},
        NATIVE + 'LastTests.derived_contract': {NATIVE + 'releaseLast_verified'},
        NATIVE + 'Tests.publication_scope': {NATIVE + 'callbacks', NATIVE + 'releaseLast', EXPRESSION + 'run',
                                            'Compiler.Extraction.Storage.insertProgram'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('native lastValue lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'nativeLastRowSelectionVerified': True,
            'nativeLastValueCallbackAttached': True, 'initialOwnershipDerivesCleanup': True,
            'rejectionRetainsCompletedCleanup': True, 'headerAndRegistryPopScope': 'nativePop',
            'nativePublicationRollbackVerified': False, 'completeGraphCorrespondenceVerified': False}


def controls(output, env, lean):
    source = ('import Compiler.Extraction.InternerInsertionTests\n'
              'import Compiler.Extraction.RepresentativeRegisteredGrowthAppend\n'
              'import Compiler.Extraction.ExpressionDeinitNativeProofs\n'
              'import Compiler.Extraction.RepresentativeRegisteredPop\n')
    # Universal selector/callback equations keep expected failures bounded;
    # complete execution fixtures remain audited and freshly replayed roots.
    source += '\n'.join(without_imports((ROOT / 'lean/Compiler/Extraction' / name).read_text()) for name in (
        'RepresentativeLastExpression.lean', 'InternerInsertionNative.lean', 'InternerInsertionLastProofs.lean'))
    records = [mutation_check(output, 'native-last-value-unchanged', source, True, env, lean)]
    changes = (
        ('empty-is-first-row', 'if length = 0 then .error .sourceBounds else',
         'if length = 0 then .ok ⟨0, 0⟩ else'),
        ('wrong-last-index', 'else Append.selectNewElement state header length',
         'else Append.selectNewElement state header (length + 1)'),
        ('truncate-native-length', 'else Append.selectNewElement state header length',
         'else Append.selectNewElement state header (UInt32.ofNat length).toNat'),
        ('wrong-header-offset', 'let value ← readItems state header',
         'let value ← readItems state { header with offset := 0 }'),
        ('wrong-owner-header', 'match Last.select (memory before).memory (Owner.headerAddress ⟨container, 0⟩) with',
         'match Last.select (memory before).memory ⟨container, 0⟩ with'),
        ('hide-selection-fault', '| .error reason => (.error (.lastRow reason), before)',
         '| .error _ => (.ok (), before)'),
        ('destroy-first-row', '(Publication.external ops.arguments) allocator descriptor (memory before)\n    let next',
         '(Publication.external ops.arguments) allocator { descriptor with offset := 0 } (memory before)\n    let next'),
        ('wrong-allocator', '(Publication.external ops.arguments) allocator descriptor (memory before)\n    let next',
         '(Publication.external ops.arguments) (allocator + 1) descriptor (memory before)\n    let next'),
        ('discard-failed-cleanup', '| .error reason => (.error (.expression reason), next)',
         '| .error reason => (.error (.expression reason), before)'),
        ('hide-destructor-fault', '| .error reason => (.error (.expression reason), next)',
         '| .error _ => (.ok (), next)'),
        ('discard-successful-cleanup', '| .ok () => (.ok (), { next with item := { next.item with object := none, clone := { next.item.clone with value := none, execution := reached } } })',
         '| .ok () => (.ok (), before)'),
        ('keep-object-local', 'object := none, clone := { next.item.clone with value := none, execution := reached }',
         'object := before.item.object, clone := { next.item.clone with value := none, execution := reached }'),
        ('keep-clone-local', 'object := none, clone := { next.item.clone with value := none, execution := reached }',
         'object := none, clone := { next.item.clone with execution := reached }'),
        ('lose-row-invalidation', 'value := none, execution := reached',
         'value := none, execution := { reached with invalidated := false }'),
        ('old-logical-destructor', '| .lastValue => releaseLast ops allocator container before',
         '| .lastValue => let (result, reached) := base.release .lastValue owner before; (result.mapError Fault.base, reached)'),
    )
    for name, before, after in changes:
        if source.count(before) != 1:
            raise ValueError('ambiguous native lastValue mutation: ' + name)
        records.append(mutation_check(output, 'native-last-value-' + name, source.replace(before, after), False, env, lean))
    for record in records:
        diagnostic = (output / (record['name'] + '.stdout')).read_text()
        if re.search(r'maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant|unknown tactic', diagnostic, re.I):
            raise ValueError('native lastValue control hit a resource or syntax failure: ' + record['name'])
        if not record['expectedAcceptance'] and not re.search(
                r'error: (?:unsolved goals|Application type mismatch|Type mismatch|Tactic[^\n]*failed)', diagnostic):
            raise ValueError('native lastValue control lacks a semantic proof failure: ' + record['name'])
    return records
