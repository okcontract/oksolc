#!/usr/bin/env python3
"""Check concrete insertion contracts in both complete physical callers.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import json
import re
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

MODULE = 'Compiler.Extraction.InternerInsertionCallerTests'
BASE = 'Compiler.Extraction.Memory.Arguments.Normalization.'
NS = BASE + 'OwnedCall.Insertion.'
CLAIMS = ['Compiler.Extraction.Storage.' + name for name in (
    'Release.execute_preserves', 'releaseAll_preserves', 'Cleanup.execute_preserves', 'Program.execute_preserves')]
CLAIMS += [BASE + 'Insertion.' + name for name in (
    'erased_valid', 'logical_release_shape', 'typed_release_shape', 'arguments_release_valid', 'item_release_valid',
    'payload_release_valid', 'payload_run_valid', 'lifetime_stage_valid', 'lifetime_execute_valid', 'lifetime_run_valid',
    'clone_preserves', 'clone_callbacks_preserves', 'creation_preserves')]
CLAIMS += [NS + name for name in (
    'ownsArguments_sound', 'borrowed_ready', 'duplicate_valid', 'publication_valid', 'item_preserves', 'callbacks_preserve',
    'execution_valid', 'body_memory', 'body_semantics', 'insertion_memory', 'insertion_semantics', 'graph_contracts', 'production_verified')]
CLAIMS += [NS + name for name in (
    'clone_fields', 'creation_fields', 'item_fields', 'callbacks_fields', 'execution_fields', 'cell_fields', 'cell_binding')]
CLAIMS += [NS + 'Tests.' + name for name in (
    'admitted', 'initial_good', 'graph_valid', 'success', 'representative_descriptors', 'publication_oom', 'append_oom', 'clone_oom', 'creation_oom',
    'duplication_oom', 'transferred_success', 'transferred_oom', 'verified', 'consumed_source_rejected', 'wrong_key_rejected',
    'absent_graph_rejected', 'replacement', 'copy_fault_retains', 'missing_locals_rejected',
    'control_completes', 'fields_before_admission', 'admission_is_not_field_correspondence')]
CLAIMS += [NS + 'CallerTests.' + name for name in (
    'original_good', 'prepared', 'graph_valid', 'contracts', 'caller_verified', 'find_success', 'find_rollback',
    'force_success', 'force_oom', 'find_closed')]


def audit(output):
    claims = {c['theorem']: set(c['dependencies'])
              for c in json.loads((output / 'audit.json').read_bytes())['claims']}
    required = {
        NS + 'execution_valid': {NS + 'callbacks_preserve', 'Compiler.Extraction.Storage.Program.execute_preserves',
            'Compiler.Extraction.Storage.insertProgram', NS + 'execution'},
        NS + 'callbacks_preserve': {NS + 'duplicate_valid', NS + 'publication_valid', NS + 'item_preserves',
            BASE + 'Insertion.arguments_release_valid'},
        NS + 'body_memory': {NS + 'execution_valid', NS + 'admitOutput', BASE + 'represented_frame'},
        NS + 'body_semantics': {NS + 'execution', NS + 'admitOutput',
            NS + 'execution_fields', NS + 'cell_binding', 'Compiler.Extraction.Interner.InsertionExecution.verified'},
        NS + 'execution_fields': {NS + 'callbacks_fields', 'Compiler.Extraction.Storage.Program.execute_preserves',
            'Compiler.Extraction.Storage.insertProgram', NS + 'execution'},
        NS + 'callbacks_fields': {NS + 'item_fields', NS + 'callbacks_preserve', BASE + 'take_refines'},
        NS + 'clone_fields': {'Compiler.Extraction.AssemblyClone.clone_item'},
        NS + 'Tests.fields_before_admission': {NS + 'execution_fields', NS + 'Tests.control_completes'},
        NS + 'production_verified': {NS + 'insertion_memory', NS + 'insertion_semantics',
            BASE + 'OwnedCall.Publication.production_verified', BASE + 'OwnedCall.Recursive.production_verified',
            'Compiler.Extraction.AssemblyItem.Creation.create_verified', 'Compiler.Extraction.AssemblyClone.Physical.run_valid'},
        NS + 'CallerTests.caller_verified': {NS + 'graph_contracts', NS + 'CallerTests.prepared',
            BASE + 'OwnedCall.Semantic.find_verified', BASE + 'OwnedCall.Semantic.force_verified'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('insertion caller lost checked dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'physicalCallerInsertionContractsDerived': True,
            'physicalCallerPublicationContractsDerived': True, 'sameExecutionMemoryAndWords': True,
            'insertionOutputFieldCorrespondenceDerived': True,
            'nativeFieldAssignmentVerified': False, 'nativeContainerBindingVerified': False,
            'universalCallerAdmissionVerified': False, 'recursiveConstructorSimulationVerified': False}


def controls(output, env, lean):
    directory = ROOT / 'lean/Compiler/Extraction'
    source = 'import Compiler.Extraction.AssemblyItemCreationTests\nimport Compiler.Extraction.InternerPublicationTests\nimport Compiler.Extraction.AssemblyCloneProofs\nimport Compiler.Extraction.NormalizationMemoryFields\n' + '\n'.join(
        without_imports((directory / name).read_text()) for name in (
            'StorageExecutionInvariant.lean', 'InsertionMemoryValidity.lean', 'InsertionPrimitiveValidity.lean',
            'InternerInsertionExecution.lean', 'InternerInsertionValidity.lean', 'InternerInsertionFields.lean', 'InternerInsertionCaller.lean',
            'InternerInsertionProduction.lean', 'InternerInsertionTests.lean', 'InternerInsertionCallerTests.lean'))
    changes = (
        ('discard-duplicate-memory', 'let reached := withMemory before after\n      match result with',
         'let reached := before\n      match result with'),
        ('alias-duplicate', 'if owner.aliasesNormalized then some normalized else before.duplicate', 'some normalized'),
        ('skip-publication', 'Publication.publish ops.probe ops.arguments allocator source key normalized (BitVec.ofNat 32 count)\n        ⟨graph owner before, memory before⟩',
         '((Except.ok (), ⟨graph owner before, memory before⟩) : Except OwnedCall.Fault Unit × World (Publication.Effects σ))'),
        ('skip-normalized-release', 'let (result, after) := free (Publication.external ops.arguments) allocator normalized (memory before)',
         'let (result, after) := (Except.ok (), memory before)'),
        ('discard-creation-memory', '(result.mapError Rejection.creation, { before with item := after })\n    | .append',
         '(result.mapError Rejection.creation, before)\n    | .append'),
        ('skip-input-descriptor-check', 'decide (keyCode.run input.item normalized.items key.sequence = some key)', 'true'),
        ('skip-input-value-check', 'decide ((if input.item.kind == 2 then input.item.data else value) = value)', 'true'),
        ('corrupt-duplicate-fields', '(.ok true, { reached with duplicate := some slice })',
         '(.ok true, { reached with duplicate := some { slice with items := [] } })'),
        ('corrupt-item-fields', 'item := (state.item.clone.value.getD input).item',
         'item := { (state.item.clone.value.getD input).item with data := 0 }'),
        ('corrupt-sequence-field', 'sequence := key.sequence', 'sequence := key.sequence + 1'),
        ('skip-source-frame', 'decide (source.length = 0 ∨ (memory after).memory.heap.lookup source.allocation = before.memory.memory.heap.lookup source.allocation)', 'true'),
        ('skip-live-locals', '(outcome != some .success || (after.item.object.isSome && after.item.clone.value.isSome && (arguments normalized owner after).isSome))', 'true'),
        ('fault-is-oom', '| .error _ => (.error (.language .safetyFault), reached)', '| .error _ => (.error (.language .outOfMemory), reached)'),
        ('rollback-fault-state', '| .error _ => (.error (.language .safetyFault), reached)', '| .error _ => (.error (.language .safetyFault), before)'),
        ('wrong-cell-address', 'itemAddress := state.item.object.getD 0', 'itemAddress := 0'),
    )
    for name, before, _ in changes:
        if source.count(before) != 1:
            raise ValueError('ambiguous caller mutation: ' + name)
    records = [mutation_check(output, 'caller-insertion-unchanged', source, True, env, lean)]
    for name, before, after in changes:
        records.append(mutation_check(output, 'caller-insertion-' + name, source.replace(before, after), False, env, lean))
    for record in records:
        diagnostic = (output / (record['name'] + '.stdout')).read_text()
        if re.search(r'maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant|failed to synthesize|Invalid field', diagnostic, re.I):
            raise ValueError('caller control hit resource, syntax or elaboration failure: ' + record['name'])
        if not record['expectedAcceptance'] and not re.search(
                r'unsolved goals|Type mismatch|Tactic [^\n]*(?:failed|proved)|Dependent elimination failed|Application type mismatch', diagnostic, re.I):
            raise ValueError('caller negative has no semantic proof failure: ' + record['name'])
    return records
