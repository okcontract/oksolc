#!/usr/bin/env python3
"""Audit the typed undefined-store prerequisite of native expression cleanup.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import re

from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

MEMORY = 'Compiler.ZigAir.Memory.'
EXPRESSION = 'Compiler.Extraction.Expression.'
CLAIMS = [MEMORY + name for name in (
    'Cells.forget_valid', 'Cells.lookup_forget', 'invalidate_of_access', 'invalidate_success',
    'invalidate_valid', 'invalidate_frame', 'invalidate_contents')]
CLAIMS += [EXPRESSION + name for name in ('invalidation_is_last', 'invalidate_root', 'invalidate_array')]
CLAIMS += [EXPRESSION + 'InvalidationTests.' + name for name in (
    'array_execution', 'array_from_geometry', 'every_leaf_uninitialized', 'earlier_row_unchanged', 'later_row_unchanged',
    'pointees_and_history_retained', 'root_execution', 'already_uninitialized', 'readonly_rejected',
    'wrong_view_rejected', 'stale_and_bounds_rejected', 'reinitialization_required')]


def audit(claims):
    required = {
        MEMORY + 'invalidate_valid': {MEMORY + 'invalidate', MEMORY + 'Cells.forget_valid', MEMORY + 'replace_typed_preserves_valid'},
        MEMORY + 'invalidate_contents': {MEMORY + 'invalidate', MEMORY + 'Cells.lookup_forget'},
        EXPRESSION + 'invalidation_is_last': {'Compiler.Extraction.ExpressionDeinit.expressionDeinitCode'},
        EXPRESSION + 'invalidate_array': {MEMORY + 'array_access', MEMORY + 'invalidate_of_access', MEMORY + 'invalidate_valid'},
        EXPRESSION + 'InvalidationTests.array_from_geometry': {EXPRESSION + 'invalidate_array'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('expression invalidation lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'typedRowInvalidationVerified': True,
            'otherLeavesAndLifetimeHistoryRetained': True, 'nativeDestructorAttachmentVerified': False,
            'nativePublicationRollbackVerified': False, 'completeGraphCorrespondenceVerified': False}


def controls(output, env, lean):
    source = ('import Compiler.Extraction.ExpressionFieldTests\n'
              'import Compiler.Extraction.ExpressionDeinitProgram\n'
              'import Compiler.ZigAir.MemoryArrayGeometry\n'
              'import Compiler.ZigAir.MemoryAllocationShape\n')
    source += '\n'.join(without_imports((ROOT / 'lean' / name).read_text()) for name in (
        'Compiler/ZigAir/MemoryInvalidation.lean', 'Compiler/Extraction/ExpressionInvalidation.lean',
        'Compiler/Extraction/ExpressionInvalidationTests.lean'))
    records = [mutation_check(output, 'expression-invalidation-unchanged', source, True, env, lean)]
    changes = (
        ('retain-leaves', 'cells.filter (fun entry => decide (entry.1 < offset ∨ offset + bytes ≤ entry.1))', 'cells'),
        ('erase-neighbors', 'cells.filter (fun entry => decide (entry.1 < offset ∨ offset + bytes ≤ entry.1))', '[]'),
        ('erase-next-boundary', 'entry.1 < offset ∨ offset + bytes ≤ entry.1', 'entry.1 < offset ∨ offset + bytes < entry.1'),
        ('ignore-pointer-permission', 'if !writable then .error .readOnly else', 'if false then .error .readOnly else'),
        ('ignore-owner-permission', 'let cell ← access state address layout true', 'let cell ← access state address layout false'),
        ('ignore-declared-view', 'if !acceptsView cell.type address.offset child then .error .unsupported else', 'if false then .error .unsupported else'),
        ('rewind-lifetime', '\n  .ok { state with heap := (state.heap.replace address.allocation', '\n  .ok { state with nextId := 0, heap := (state.heap.replace address.allocation'),
        ('wrong-row', 'Compiler.ZigAir.Memory.invalidate state true allocationType descriptor',
         'Compiler.ZigAir.Memory.invalidate state true allocationType { descriptor with offset := 0 }'),
    )
    for name, before, after in changes:
        if source.count(before) != 1:
            raise ValueError('ambiguous expression invalidation mutation: ' + name)
        records.append(mutation_check(output, 'expression-invalidation-' + name, source.replace(before, after), False, env, lean))
    for record in records:
        diagnostic = (output / (record['name'] + '.stdout')).read_text()
        if re.search(r'maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant|unknown tactic', diagnostic, re.I):
            raise ValueError('expression invalidation control hit a resource or syntax failure: ' + record['name'])
        if not record['expectedAcceptance'] and not re.search(
                r'error: (?:unsolved goals|Application type mismatch|Type mismatch|Tactic[^\n]*failed)', diagnostic):
            raise ValueError('expression invalidation control lacks a semantic proof failure: ' + record['name'])
    return records
