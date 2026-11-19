#!/usr/bin/env python3
"""Connect source-bound byte cleanup to the same insertion rollback execution.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import json
import re
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

MODULE = 'Compiler.Extraction.ExpressionPayloadTests'
NS = 'Compiler.Extraction.ExpressionDeinit.Payload.'
CLAIMS = [NS + name for name in ('free_keeps_dead', 'run_verified', 'Post.preserves_borrow',
                                'last_value_preserved', 'insertion_verified')]
CLAIMS += [NS + 'Tests.' + name for name in (
    'initial_valid', 'taken_result', 'taken_valid', 'taken_payload', 'rollback_contract', 'complete_rollback',
    'allocation_fault_retains_payload_release', 'payload_fault_stops', 'empty_argument_sentinel',
    'borrowed_cells', 'allocation_history', 'exact_descriptors', 'insertion_words')]


def audit(output):
    claims = {c['theorem']: set(c['dependencies'])
              for c in json.loads((output / 'audit.json').read_bytes())['claims']}
    expression = 'Compiler.Extraction.ExpressionDeinit.'
    item = 'Compiler.Extraction.AssemblyItemDeinit.'
    memory = 'Compiler.Extraction.Memory.Arguments.Normalization.'
    required = {
        NS + 'run_verified': {NS + 'operations', NS + 'free_keeps_dead', expression + 'execute_equation',
                             item + 'run_verified', item + 'Released.arguments', memory + 'free_valid'},
        NS + 'last_value_preserved': {NS + 'run_verified', NS + 'insertionOperations',
                                     expression + 'insertionWith', expression + 'last_value_memory_equation'},
        NS + 'insertion_verified': {NS + 'last_value_preserved', 'Compiler.Extraction.Interner.InsertionExecution.verified'},
        NS + 'Tests.rollback_contract': {NS + 'last_value_preserved', NS + 'Tests.taken_valid', NS + 'Tests.taken_payload', memory + 'take_refines'},
        NS + 'Tests.insertion_words': {NS + 'insertion_verified', NS + 'Tests.complete_rollback'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('payload insertion lost checked dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'payloadCallbackIntegrated': True,
            'nativeDescriptorProjectionVerified': False, 'itemAllocationDestructionVerified': False,
            'universalRollbackAdmissionVerified': False}


def controls(output, env, lean):
    directory = ROOT / 'lean/Compiler/Extraction'
    source = 'import Compiler.Extraction.AssemblyItemDeinitTests\n' + '\n'.join(
        without_imports((directory / name).read_text()) for name in ('ExpressionPayload.lean', 'ExpressionPayloadTests.lean'))
    changes = (
        ('discard-payload-memory', '(result.mapError Sum.inl, after.memory)', '(result.mapError Sum.inl, before)'),
        ('discard-payload-fault', '(result.mapError Sum.inl, after.memory)', '(.ok (), after.memory)'),
        ('wrong-payload-pointer', 'AssemblyItemDeinit.run release allocator (payloads id) before',
         'AssemblyItemDeinit.run release allocator (payloads (id + 1)) before'),
        ('wrong-payload-allocator', 'AssemblyItemDeinit.run release allocator (payloads id) before',
         'AssemblyItemDeinit.run release 0 (payloads id) before'),
        ('discard-destroy-fault', '(result.mapError Sum.inr, reached)', '(.ok (), reached)'),
        ('discard-destroy-effects', '(result, { before with effects })', '(result, before)'),
        ('wrong-destroy-pointer', 'let (result, effects) := destroy id before', 'let (result, effects) := destroy (id + 1) before'),
        ('use-unchecked-callback', 'insertionWith (operations release allocator payloads destroy) external allocator last rest', 'rest'),
    )
    for name, before, _ in changes:
        if source.count(before) != 1:
            raise ValueError('ambiguous payload insertion mutation: ' + name)
    records = [mutation_check(output, 'payload-insertion-unchanged', source, True, env, lean)]
    for name, before, after in changes:
        records.append(mutation_check(output, 'payload-insertion-' + name, source.replace(before, after), False, env, lean))
    for record in records:
        diagnostic = (output / (record['name'] + '.stdout')).read_text()
        if re.search(r'maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant|failed to synthesize', diagnostic, re.I):
            raise ValueError('payload insertion control hit resource, syntax or elaboration failure: ' + record['name'])
        if not record['expectedAcceptance'] and not re.search(
                r'unsolved goals|Type mismatch|Tactic [^\n]*(?:failed|proved)|Dependent elimination failed|Application type mismatch', diagnostic, re.I):
            raise ValueError('payload insertion negative control has no semantic proof failure: ' + record['name'])
    return records
