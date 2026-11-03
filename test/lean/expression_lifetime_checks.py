#!/usr/bin/env python3
"""Check all three allocation lifetimes in source-bound expression rollback.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import json
import re
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

MODULE = 'Compiler.Extraction.ExpressionLifetimeTests'
NS = 'Compiler.Extraction.ExpressionDeinit.Lifetime.'
ITEM = 'Compiler.Extraction.AssemblyItem.'
CLAIMS = [ITEM + name for name in ('destroy_verified', 'Released.arguments', 'Released.keeps_dead', 'after_payload')]
CLAIMS += [NS + name for name in ('run_verified', 'last_value_preserved', 'insertion_verified')]
CLAIMS += [NS + 'Tests.' + name for name in (
    'initial_valid', 'object_owned', 'payload_owned', 'taken_result', 'taken_contract', 'rollback_contract',
    'complete_rollback', 'borrowed_cells_and_history', 'object_alias_dead', 'fields_unsupported',
    'scalar_store_unsupported', 'zero_alignment_rejects', 'wrong_allocator', 'wrong_block', 'wrong_extent',
    'wrong_identity', 'array_is_not_object', 'stack_rejected', 'readonly_rejected', 'malformed_rejected',
    'dead_rejected', 'later_fault_retains_payload_release', 'empty_argument_sentinel', 'absent_payload',
    'exact_descriptors', 'insertion_words')]
CLAIMS += ['Compiler.ZigAir.Memory.' + name for name in (
    'layout_alignment_positive', 'allocate_preserves_valid', 'Cells.read_eq_of_lookup', 'load_after_store')]


def audit(output):
    claims = {c['theorem']: set(c['dependencies'])
              for c in json.loads((output / 'audit.json').read_bytes())['claims']}
    expression = 'Compiler.Extraction.ExpressionDeinit.'
    payload = 'Compiler.Extraction.AssemblyItemDeinit.'
    memory = 'Compiler.Extraction.Memory.Arguments.Normalization.'
    required = {
        ITEM + 'destroy_verified': {ITEM + 'destroy', ITEM + 'viewType', 'Compiler.ZigAir.Memory.releaseOwned'},
        ITEM + 'after_payload': {ITEM + 'Owned', payload + 'Touches', payload + 'Post.frame'},
        NS + 'run_verified': {NS + 'operations', expression + 'execute_equation', expression + 'expressionDeinitCode',
                              payload + 'run_verified', payload + 'assemblyItemDeinitCode', ITEM + 'destroy_verified',
                              ITEM + 'after_payload', ITEM + 'Released.arguments', ITEM + 'Released.keeps_dead',
                              expression + 'Payload.free_keeps_dead', memory + 'free_valid'},
        NS + 'last_value_preserved': {NS + 'run_verified', expression + 'insertionWith', expression + 'last_value_memory_equation'},
        NS + 'insertion_verified': {NS + 'last_value_preserved', 'Compiler.Extraction.Interner.InsertionExecution.verified'},
        NS + 'Tests.taken_contract': {memory + 'take_refines', NS + 'Tests.taken_result'},
        NS + 'Tests.rollback_contract': {NS + 'last_value_preserved', NS + 'Tests.taken_contract'},
        NS + 'Tests.insertion_words': {NS + 'insertion_verified', NS + 'Tests.complete_rollback'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('expression lifetime lost checked dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'itemAllocationDestructionVerified': True,
            'nativeDescriptorProjectionVerified': False, 'universalRollbackAdmissionVerified': False}


def controls(output, env, lean):
    directory = ROOT / 'lean/Compiler/Extraction'
    source = ('import Compiler.Extraction.ExpressionPayloadTests\n'
              'import Compiler.Extraction.AssemblyItemFieldLayout\n'
              'import Compiler.ZigAir.MemoryInvariant\n') + '\n'.join(
        without_imports((directory / name).read_text()) for name in (
            'AssemblyItemAllocation.lean', 'ExpressionLifetime.lean', 'ExpressionLifetimeTests.lean'))
    changes = (
        ('retain-logical-object', '⟨heap, memory, external id before⟩', '⟨before.heap, memory, external id before⟩'),
        ('retain-physical-object', '⟨heap, memory, external id before⟩', '⟨heap, before.memory, external id before⟩'),
        ('discard-release-effects', '⟨heap, memory, external id before⟩', '⟨heap, memory, before.effects⟩'),
        ('discard-release-fault', '| .error fault => (.error fault, before)', '| .error _ => (.ok (), before)'),
        ('wrong-logical-owner', 'Memory.release before.heap allocator id', 'Memory.release before.heap 0 id'),
        ('wrong-physical-pointer', 'releaseOwned before.memory id viewType', 'releaseOwned before.memory (id + 1) viewType'),
        ('wrong-object-type', 'releaseOwned before.memory id viewType', 'releaseOwned before.memory id (.array 56 Compiler.ZigAir.Memory.WordArray.word)'),
        ('accept-byte-block', 'let .item _ := allocation.block', 'let .bytes _ := allocation.block'),
        ('bypass-object-release', '(AssemblyItem.destroy objects allocator)', '(fun _ before => (.ok (), before))'),
        ('bypass-destructor', 'insertionWith (operations bytes objects allocator payloads) external allocator last rest', 'rest'),
    )
    for name, before, _ in changes:
        if source.count(before) != 1:
            raise ValueError('ambiguous expression lifetime mutation: ' + name)
    records = [mutation_check(output, 'item-lifetime-unchanged', source, True, env, lean)]
    for name, before, after in changes:
        records.append(mutation_check(output, 'item-lifetime-' + name, source.replace(before, after), False, env, lean))
    for record in records:
        diagnostic = (output / (record['name'] + '.stdout')).read_text()
        if re.search(r'maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant|failed to synthesize', diagnostic, re.I):
            raise ValueError('expression lifetime control hit resource, syntax or elaboration failure: ' + record['name'])
        if not record['expectedAcceptance'] and not re.search(
                r'unsolved goals|Type mismatch|Tactic [^\n]*(?:failed|proved)|Dependent elimination failed|Application type mismatch', diagnostic, re.I):
            raise ValueError('expression lifetime negative control has no semantic proof failure: ' + record['name'])
    return records
