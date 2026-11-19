#!/usr/bin/env python3
"""Audit source-ordered native Expression destruction and reached field reads.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import re

from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

BASE = 'Compiler.Extraction.ExpressionDeinit.'
NATIVE = BASE + 'Native.'
NORMAL = 'Compiler.Extraction.Memory.Arguments.Normalization.'
EXPRESSION = 'Compiler.Extraction.Expression.'
CLAIMS = [BASE + name for name in ('executeStages_rejected', 'executeStages_advanced')]
CLAIMS += [NORMAL + name for name in ('free_empty', 'Valid.memory_frame')]
CLAIMS += [EXPRESSION + 'readField_frame']
CLAIMS += [NATIVE + 'Fields.' + name for name in (
    'item_read', 'item_frame', 'resolve_owned', 'resolve_empty', 'resolve_interior', 'resolve_extent', 'arguments_read')]
CLAIMS += [NATIVE + name for name in (
    'item_stage', 'allocation_stage', 'allocation_interior', 'arguments_stage', 'invalidation_stage', 'invalidate_session', 'run_verified')]
CLAIMS += [NATIVE + 'Tests.' + name for name in (
    'initial_valid', 'derived_contract', 'completed', 'row_and_history', 'late_read_rejection',
    'final_write_rejection', 'item_write_rejection', 'arguments_rejected', 'empty_sentinel', 'second_run_rejected')]


def audit(claims):
    required = {
        BASE + 'executeStages_rejected': {BASE + 'executeStages'},
        BASE + 'executeStages_advanced': {BASE + 'executeStages'},
        NORMAL + 'Valid.memory_frame': {NORMAL + 'represented_frame', NORMAL + 'Injected.retained'},
        EXPRESSION + 'readField_frame': {'Compiler.ZigAir.Memory.fieldPointer_eq_of_lookup',
                                         'Compiler.ZigAir.Memory.load_eq_of_lookup'},
        NATIVE + 'Fields.arguments_read': {NATIVE + 'Fields.resolve_owned', EXPRESSION + 'readField'},
        NATIVE + 'invalidate_session': {EXPRESSION + 'invalidate_array', NORMAL + 'Valid.memory_frame',
                                         'Compiler.ZigAir.Memory.invalidate_retains_shape'},
        NATIVE + 'run_verified': {NATIVE + 'run', BASE + 'executeStages', BASE + 'expressionDeinitCode',
                                  'Compiler.Extraction.AssemblyItemDeinit.Native.run_verified',
                                  'Compiler.Extraction.AssemblyItem.destroy_verified', NORMAL + 'free_valid',
                                  NATIVE + 'Fields.item_frame', NATIVE + 'Fields.arguments_read', NATIVE + 'invalidate_session'},
        NATIVE + 'Tests.derived_contract': {NATIVE + 'run_verified'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('native expression destruction lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'nativeExpressionDestructorVerified': True,
            'laterFieldReadsDerived': True, 'allCleanupStagesShareReachedMemory': True,
            'nativeLastValueCallbackAttached': False, 'nativePublicationRollbackVerified': False,
            'completeGraphCorrespondenceVerified': False}


def controls(output, env, lean):
    source = ('import Compiler.Extraction.ExpressionInvalidation\n'
              'import Compiler.Extraction.AssemblyItemDeinitNative\n'
              'import Compiler.Extraction.RepresentativeBackingRelease\n'
              'import Compiler.Extraction.ExpressionPayload\n')
    # Universal stage equations and ownership proofs give bounded diagnostics;
    # full native fixtures are independently audited and freshly replayed.
    source += '\n'.join(without_imports((ROOT / 'lean/Compiler/Extraction' / name).read_text()) for name in (
        'ExpressionDeinitFields.lean', 'ExpressionDeinitNative.lean', 'ExpressionDeinitNativeProofs.lean'))
    records = [mutation_check(output, 'native-expression-deinit-unchanged', source, True, env, lean)]
    changes = (
        ('wrong-item-field', 'let value ← (Expression.readField memory false descriptor Expression.itemOffset)',
         'let value ← (Expression.readField memory false descriptor Expression.argumentsOffset)'),
        ('erase-item-offset', 'else .ok address', 'else .ok { address with offset := 0 }'),
        ('wrong-argument-field', 'let value ← (Expression.readField before.memory false descriptor Expression.argumentsOffset)',
         'let value ← (Expression.readField before.memory false descriptor Expression.itemOffset)'),
        ('interior-arguments', 'if address.offset ≠ 0 then .error .bounds else', 'if false then .error .bounds else'),
        ('short-extent', 'if length ≠ values.length then .error .bounds else', 'if false then .error .bounds else'),
        ('empty-sentinel-root', 'if length = 0 then return ⟨address.allocation, []⟩',
         'if length = 0 ∧ address.offset = 0 then return ⟨address.allocation, []⟩'),
        ('discard-item-memory', '(result.mapError Fault.item, { before with memory := reached.memory })',
         '(result.mapError Fault.item, before)'),
        ('discard-allocation-memory', '(result.mapError Fault.allocation, { before with memory := reached })',
         '(result.mapError Fault.allocation, before)'),
        ('discard-argument-memory', '(result.mapError Fault.arguments, { before with memory := reached })',
         '(result.mapError Fault.arguments, before)'),
        ('wrong-argument-allocator', 'let (result, reached) := free external allocator slice before.memory',
         'let (result, reached) := free external (allocator + 1) slice before.memory'),
        ('interior-item-destroy', 'if object.offset ≠ 0 then (.error (.allocation (.ownership .bounds)), before) else',
         'if false then (.error (.allocation (.ownership .bounds)), before) else'),
        ('hide-final-write-fault', '| .error reason => (.error (.invalidation reason), before)', '| .error _ => (.ok (), before)'),
        ('skip-row-invalidation', 'match Expression.invalidate before.memory.memory descriptor with',
         'match (Except.ok before.memory.memory : Except Compiler.ZigAir.Memory.Fault Compiler.ZigAir.Memory.State) with'),
        ('destroy-reads-first-row', '| .itemAllocation =>\n    match Fields.item before.memory.memory descriptor with',
         '| .itemAllocation =>\n    match Fields.item before.memory.memory { descriptor with offset := 0 } with'),
        ('skip-final-stage', 'executeStages (step bytes objects external allocator descriptor) expressionDeinitCode ⟨before, false⟩',
         'executeStages (step bytes objects external allocator descriptor) (expressionDeinitCode.filter (fun stage => stage != .invalidate)) ⟨before, false⟩'),
    )
    for name, before, after in changes:
        if source.count(before) != 1:
            raise ValueError('ambiguous native expression deinit mutation: ' + name)
        records.append(mutation_check(output, 'native-expression-deinit-' + name, source.replace(before, after), False, env, lean))
    for record in records:
        diagnostic = (output / (record['name'] + '.stdout')).read_text()
        if re.search(r'maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant|unknown tactic', diagnostic, re.I):
            raise ValueError('native expression deinit control hit a resource or syntax failure: ' + record['name'])
        if not record['expectedAcceptance'] and not re.search(
                r'error: (?:unsolved goals|Application type mismatch|Type mismatch|Tactic[^\n]*failed)', diagnostic):
            raise ValueError('native expression deinit control lacks a semantic proof failure: ' + record['name'])
    return records
