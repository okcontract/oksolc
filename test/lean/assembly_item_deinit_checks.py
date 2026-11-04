#!/usr/bin/env python3
"""Check source-bound item payload destruction in normalization's registry.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import json
import re
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
import extract_assembly_item_deinit as extraction
from test_assembly_item_deinit import MUTATIONS, change_body

MODULE = 'Compiler.Extraction.AssemblyItemDeinitTests'
NS = 'Compiler.Extraction.AssemblyItemDeinit.'
CLAIMS = [NS + name for name in ('free_verified', 'Released.arguments', 'run_equation', 'run_verified')]
CLAIMS += [NS + 'Tests.' + name for name in (
    'initial_valid', 'payload_owned', 'complete_contract', 'payload_dead', 'payload_alias_dead',
    'arguments_preserved', 'arguments_contract', 'allocation_history', 'absent_payload', 'empty_payload',
    'invalid_descriptor', 'double_free', 'wrong_allocator', 'wrong_registry_extent', 'arguments_not_bytes',
    'readonly_payload', 'stack_payload', 'wrong_typed_extent', 'signed_bytes_rejected', 'wrong_typed_element',
    'malformed_heap', 'missing_backing')]
CLAIMS += [NS + 'Tests.' + name for name in (
    'nonzero_offset_rejects', 'nonzero_offset_not_owned', 'empty_offset_no_release', 'offset_fault_keeps_value')]


def audit(output):
    claims = {c['theorem']: set(c['dependencies'])
              for c in json.loads((output / 'audit.json').read_bytes())['claims']}
    memory = 'Compiler.ZigAir.Memory.'
    required = {
        NS + 'free_verified': {NS + 'Owned', NS + 'free', memory + 'releaseOwned', memory + 'erase_preserves_valid',
                              'Compiler.Extraction.Memory.Arguments.related_erase',
                              'Compiler.Extraction.Memory.Arguments.Normalization.Injected.erased'},
        NS + 'Released.arguments': {NS + 'Owned', NS + 'Released.frame', 'Compiler.Extraction.Memory.SliceValid'},
        NS + 'run_equation': {NS + 'assemblyItemDeinitCode', NS + 'execute', NS + 'Stage.execute', NS + 'free'},
        NS + 'run_verified': {NS + 'run_equation', NS + 'free_verified', NS + 'Released.arguments'},
        NS + 'Tests.complete_contract': {NS + 'run_verified', NS + 'Tests.initial_valid', NS + 'Tests.payload_owned'},
        NS + 'Tests.arguments_contract': {NS + 'Tests.complete_contract', NS + 'Post.arguments'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('item payload lost checked dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'payloadRegistryReleaseChecked': True,
            'nonemptyPayloadReleaseRequiresBaseOffset': True,
            'nativeDescriptorProjectionVerified': False, 'itemAllocationDestructionVerified': False,
            'payloadCallbackIntegrated': False}


def controls(output, env, lean):
    directory = ROOT / 'lean/Compiler/Extraction'
    names = ('AssemblyItemDeinit.lean', 'AssemblyItemDeinitProgram.lean',
             'AssemblyItemDeinitProofs.lean', 'AssemblyItemDeinitTests.lean')
    sources = {name: without_imports((directory / name).read_text()) for name in names}
    prelude = 'import Compiler.Extraction.ExpressionDeinitTests\n'

    def assembled(parts):
        return prelude + '\n'.join(parts[name] for name in names)

    source = assembled(sources)
    changes = (
        ('skip-empty-guard', 'if slice.length = 0 then (.ok (), state) else', 'if false then (.ok (), state) else'),
        ('skip-offset-guard', 'if slice.offset ≠ 0 then (.error (.ownership .bounds), state) else',
         'if false then (.error (.ownership .bounds), state) else'),
        ('offset-before-empty', 'if slice.length = 0 then (.ok (), state) else\n  if slice.offset ≠ 0 then (.error (.ownership .bounds), state) else',
         'if slice.offset ≠ 0 then (.error (.ownership .bounds), state) else\n  if slice.length = 0 then (.ok (), state) else'),
        ('wrong-owner', 'Memory.release state.heap allocator slice.address', 'Memory.release state.heap 7 slice.address'),
        ('ignore-registry-extent', 'if length ≠ slice.length then', 'if false then'),
        ('retain-logical', '    .ok (heap, memory)\n  match checked', '    .ok (state.heap, memory)\n  match checked'),
        ('retain-physical', '    .ok (heap, memory)\n  match checked', '    .ok (heap, state.memory)\n  match checked'),
        ('discard-effects', 'external slice state⟩)', 'state.effects⟩)'),
        ('discard-fault', '(result.mapError Fault.release, { before with memory })', '(.ok (), { before with memory })'),
        ('reuse-invalidated', 'if before.invalidated then', 'if false then'),
        ('skip-invalidation', '| .invalidate => (.ok (), { before with invalidated := true })', '| .invalidate => (.ok (), before)'),
    )
    for name, before, _ in changes:
        if source.count(before) != 1:
            raise ValueError('ambiguous payload mutation: ' + name)
    records = [mutation_check(output, 'payload-unchanged', source, True, env, lean)]
    for name, before, after in changes:
        records.append(mutation_check(output, 'payload-' + name, source.replace(before, after), False, env, lean))
    original = extraction.SOURCE.read_bytes()
    variants = [('payload-source-unchanged', original, True)]
    variants += [('payload-source-' + name, change_body(original, before, after), False)
                 for name, (before, after) in MUTATIONS.items()]
    for name, native, accepted in variants:
        parts = {**sources, 'AssemblyItemDeinitProgram.lean': without_imports(extraction.extract(native).decode())}
        records.append(mutation_check(output, name, assembled(parts), accepted, env, lean))
    for record in records:
        diagnostic = (output / (record['name'] + '.stdout')).read_text()
        if re.search(r'maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant|failed to synthesize', diagnostic, re.I):
            raise ValueError('payload control hit resource, syntax or elaboration failure: ' + record['name'])
        if not record['expectedAcceptance'] and not re.search(
                r'unsolved goals|Type mismatch|Tactic [^\n]*(?:failed|proved)|Dependent elimination failed|Application type mismatch', diagnostic, re.I):
            raise ValueError('payload negative control has no semantic proof failure: ' + record['name'])
    return records
