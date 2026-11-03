#!/usr/bin/env python3
"""Check source-bound clone ownership in complete insertion rollback.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import json
import re
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
from test_compiler_assembly_clone import mutated

MODULE = 'Compiler.Extraction.AssemblyCloneInsertionTests'
NS = 'Compiler.Extraction.AssemblyClone.Physical.'
CLAIMS = [NS + name for name in (
    'readable_sound', 'copyAt_shape', 'extend_lookup', 'copyAt_valid', 'duplicate_valid',
    'copyAt_not_oom', 'duplicate_oom', 'run_valid', 'run_oom', 'Cloned.item', 'Cloned.arguments',
    'rollback_verified', 'Insertion.clone_callback', 'Insertion.last_value_callback')]
CLAIMS += [NS + 'Tests.' + name for name in (
    'source_found', 'initial_frame', 'initial_valid', 'initial_item', 'initial_arguments', 'clone_result',
    'clone_contract', 'source_readable', 'clone_retains_fields', 'independent_payload', 'complete_contract',
    'complete_cleanup', 'source_and_borrow_preserved', 'absent_no_allocation', 'empty_no_allocation',
    'oom_keeps_effects', 'oom_skips_reads', 'oom_skips_cleanup', 'overlap_rejected',
    'unreadable_retains_allocation', 'wrong_source_contents', 'readonly_source', 'collision_retains_typed_allocation')]
CLAIMS += [NS + 'Tests.' + name for name in (
    'offset_descriptor', 'offset_reads', 'offset_clone_result', 'offset_clone_contract', 'offset_copy_extent',
    'offset_readonly_source', 'offset_bounds_retain_allocation', 'offset_oom_skips_reads', 'offset_empty_skips_reads',
    'offset_rollback_contract', 'offset_cleanup')]
CLAIMS += [NS + 'Insertion.Tests.' + name for name in (
    'taken_ready', 'clone_result', 'clone_contract', 'reached_rollback', 'publication_rollback', 'physical_rollback',
    'append_rollback', 'clone_oom_cleanup', 'success_keeps_clone', 'source_fault_stops', 'invalidated_rejects', 'insertion_words')]
CLAIMS += ['Compiler.Extraction.AssemblyClone.' + name for name in ('clone_safe', 'clone_key', 'clone_denotation', 'clone_cleanup')]


def audit(output):
    claims = {c['theorem']: set(c['dependencies'])
              for c in json.loads((output / 'audit.json').read_bytes())['claims']}
    required = {
        NS + 'duplicate_valid': {NS + 'duplicate', NS + 'copyAt_valid', NS + 'readable_sound'},
        NS + 'run_valid': {'Compiler.Extraction.AssemblyClone.cloneCode', 'Compiler.Extraction.AssemblyClone.CloneCode.run',
                           NS + 'duplicate_valid', NS + 'Copied.offset'},
        NS + 'Tests.offset_clone_contract': {NS + 'run_valid', NS + 'Tests.offset_clone_result'},
        NS + 'Tests.offset_rollback_contract': {NS + 'rollback_verified', NS + 'Tests.offset_clone_result'},
        NS + 'run_oom': {NS + 'duplicate_oom', NS + 'copyAt_not_oom'},
        NS + 'rollback_verified': {NS + 'run_valid', NS + 'Cloned.item', NS + 'Cloned.arguments',
                                  'Compiler.Extraction.ExpressionDeinit.Lifetime.run_verified'},
        NS + 'Insertion.clone_callback': {NS + 'run_valid', NS + 'Insertion.operations'},
        NS + 'Insertion.last_value_callback': {'Compiler.Extraction.ExpressionDeinit.Lifetime.run_verified', NS + 'Insertion.operations'},
        NS + 'Insertion.Tests.reached_rollback': {NS + 'Insertion.last_value_callback', NS + 'Insertion.Tests.clone_contract',
                                                 'Compiler.Extraction.Memory.Arguments.Normalization.take_refines'},
        NS + 'Insertion.Tests.insertion_words': {'Compiler.Extraction.Interner.InsertionExecution.verified',
                                               NS + 'Insertion.Tests.clone_contract', NS + 'Insertion.Tests.publication_rollback'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('physical clone lost checked dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'cloneSuppliesPayloadOwnership': True,
            'payloadByteOffsetRetained': True, 'clonedPayloadStartsAtAllocationBase': True,
            'nativeByteCopyImplementationVerified': False, 'nativeFieldAssignmentVerified': False,
            'nativeItemCreationVerified': False, 'universalCallerAdmissionVerified': False}


def controls(output, env, lean):
    directory = ROOT / 'lean/Compiler/Extraction'
    names = ('AssemblyClone.lean', 'AssemblyCloneProgram.lean', 'AssemblyCloneMemory.lean', 'AssemblyClonePhysical.lean',
             'AssemblyCloneInsertion.lean', 'AssemblyClonePhysicalTests.lean', 'AssemblyCloneInsertionTests.lean')
    parts = [without_imports((directory / name).read_text()) for name in names]
    prelude = 'import Compiler.Extraction.ExpressionLifetimeTests\n'
    source = prelude + '\n'.join(parts)
    changes = (
        ('stack-payload', '⟨base, .array length AssemblyItemDeinit.byte, contents, true, false⟩',
         '⟨base, .array length AssemblyItemDeinit.byte, contents, true, true⟩'),
        ('discard-clone-error-state', '| .error error => (.error error, after)', '| .error error => (.error error, before)'),
        ('discard-clone-success-state', '(.ok (if code.returnCopy then copied else input), after)',
         '(.ok (if code.returnCopy then copied else input), before)'),
        ('wrong-request-size', 'let (response, effects) := request source.contents.length before',
         'let (response, effects) := request 0 before'),
        ('discard-oom-effects', '| none => (.error .outOfMemory, { before with effects })', '| none => (.error .outOfMemory, before)'),
        ('wrong-owner', 'let heap := write before.heap before.memory.nextId (some ⟨allocator, .bytes source.contents.length⟩)',
         'let heap := write before.heap before.memory.nextId (some ⟨0, .bytes source.contents.length⟩)'),
        ('shallow-destination', 'let destination : Bytes := ⟨before.memory.nextId, source.contents, 0⟩', 'let destination : Bytes := source'),
        ('drop-source-offset', '⟨bytes.address, bytes.offset + index⟩', '⟨bytes.address, index⟩'),
        ('drop-descriptor-offset', '⟨bytes.address, bytes.contents.length, bytes.offset⟩', '⟨bytes.address, bytes.contents.length, 0⟩'),
        ('retain-destination-offset', 'let destination : Bytes := ⟨before.memory.nextId, source.contents, 0⟩',
         'let destination : Bytes := ⟨before.memory.nextId, source.contents, source.offset⟩'),
        ('retain-empty-offset', 'if source.contents = [] then (.ok ⟨before.memory.nextId, [], 0⟩, before) else',
         'if source.contents = [] then (.ok ⟨before.memory.nextId, [], source.offset⟩, before) else'),
        ('copy-at-source-offset', '(index, number value)', '(source.offset + index, number value)'),
        ('drop-copied-cells', 'let copied : Session σ := ⟨heap, extend before source.contents.length base (copiedCells source), effects⟩',
         'let copied : Session σ := ⟨heap, extend before source.contents.length base [], effects⟩'),
        ('discard-source-fault-state', '(.error .sourceMismatch, prepared)', '(.error .sourceMismatch, { before with effects })'),
        ('discard-collision-state', '(.error .registryCollision, reached)', '(.error .registryCollision, { before with effects })'),
        ('discard-returned-value', '(.ok true, { reached with value := some copied })', '(.ok true, { reached with value := some input })'),
        ('semantic-fault-as-oom', '| .error fault => (.error (.clone fault), reached)', '| .error _ => (.ok false, reached)'),
        ('oom-as-semantic-fault', '| .error .outOfMemory => (.ok false, reached)',
         '| .error .outOfMemory => (.error (.clone .outOfMemory), reached)'),
    )
    for name, before, _ in changes:
        if source.count(before) != 1:
            raise ValueError('ambiguous physical clone mutation: ' + name)
    records = [mutation_check(output, 'physical-clone-unchanged', source, True, env, lean)]
    for name, before, after in changes:
        records.append(mutation_check(output, 'physical-clone-' + name, source.replace(before, after), False, env, lean))
    for name in ('lost_arguments', 'lost_returns', 'lost_bytes', 'shallow_payload', 'return_source'):
        generated, _ = mutated(name)
        candidate = prelude + '\n'.join([parts[0], without_imports(generated.decode()), *parts[2:]])
        records.append(mutation_check(output, 'physical-clone-source-' + name, candidate, False, env, lean))
    for record in records:
        diagnostic = (output / (record['name'] + '.stdout')).read_text()
        if re.search(r'maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant|failed to synthesize', diagnostic, re.I):
            raise ValueError('physical clone control hit resource, syntax or elaboration failure: ' + record['name'])
        if not record['expectedAcceptance'] and not re.search(
                r'unsolved goals|Type mismatch|Tactic [^\n]*(?:failed|proved)|Dependent elimination failed|Application type mismatch', diagnostic, re.I):
            raise ValueError('physical clone negative control has no semantic proof failure: ' + record['name'])
    return records
