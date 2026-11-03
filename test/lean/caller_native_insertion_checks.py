#!/usr/bin/env python3
"""Audit initialization-derived caller inputs and native insertion preparation.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NORMAL = 'Compiler.Extraction.Memory.Arguments.Normalization.'
NATIVE = NORMAL + 'OwnedCall.Insertion.Native.'
CLAIMS = [NATIVE + name for name in ('caller_input', 'initialized_keys', 'initialized_caller_input',
    'CallerInput.native_frame', 'CallerInput.outer_deinit', 'CallerInput.finish_insert',
    'CallerInput.handoff_insert', 'CallerInput.prepare')]
CLAIMS += [NATIVE + 'CallerInputTests.' + name for name in ('initializer', 'source_inputs', 'prefix_results',
    'derived_input', 'preparation', 'prepared_contract', 'initialized_owner', 'backing_response', 'probe_result',
    'insertion_oom_from_caller', 'insert_result', 'handoff_and_outer_cleanup', 'outer_cleanup_after_insertion',
    'rejection_retains_reached_locals', 'reached_observations', 'retired_owners', 'key_table_retained', 'original_allocations_retained')]


def audit(claims):
    required = {
        NATIVE + 'caller_input': {NORMAL + 'OwnedCall.Publication.caller_input',
            'Compiler.Extraction.AssemblyClone.NativeFields.Represents.frame',
            NORMAL + 'OwnedCall.Caller.Origin.fresh', 'Compiler.Extraction.Interner.makeKey'},
        NATIVE + 'initialized_caller_input': {NORMAL + 'OwnedCall.GraphInit.Ownership.initialize_verified',
            NATIVE + 'caller_input', NATIVE + 'initialized_keys'},
        NATIVE + 'initialized_keys': {NORMAL + 'OwnedCall.GraphInit.Ownership.keys',
            'Compiler.Extraction.ExpressionMap.Initialization.observeEmpty'},
        NATIVE + 'CallerInput.prepare': {NATIVE + 'prepare_reached',
            NORMAL + 'OwnedCall.Caller.Origin.memory', NORMAL + 'OwnedCall.Caller.Origin.registry',
            NATIVE + 'CallerInput.live', NATIVE + 'CallerInput.unique'},
        NATIVE + 'CallerInput.finish_insert': {NORMAL + 'OwnedCall.finish', NATIVE + 'CallerInput.outer_deinit'},
        NATIVE + 'CallerInput.handoff_insert': {NORMAL + 'OwnedCall.finish_handoff',
            NORMAL + 'OwnedCall.Caller.Origin.scope', NORMAL + 'OwnedCall.Caller.Origin.detached'},
        NATIVE + 'CallerInputTests.derived_input': {NATIVE + 'initialized_caller_input',
            NATIVE + 'CallerInputTests.initializer', NATIVE + 'CallerInputTests.prefix_results'},
        NATIVE + 'CallerInputTests.prepared_contract': {NATIVE + 'CallerInput.prepare',
            NATIVE + 'CallerInputTests.derived_input', NATIVE + 'CallerInputTests.preparation'},
        NATIVE + 'CallerInputTests.insertion_oom_from_caller': {NATIVE + 'deterministic_first_oom',
            NATIVE + 'CallerInputTests.derived_input', NATIVE + 'CallerInput.native_frame'},
        NATIVE + 'CallerInputTests.handoff_and_outer_cleanup': {NATIVE + 'CallerInput.handoff_insert',
            NATIVE + 'CallerInputTests.insert_result', NATIVE + 'CallerInputTests.derived_input'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('caller/native insertion lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required),
            'scope': 'native caller entry and deterministic preparation; initialized first-publication-OOM fixture',
            'initialKeyOwnershipDerivedFromNativeInitialization': True,
            'callerNormalizedOwnerAndNativeItemInputDerived': True, 'deterministicPreparationConnected': True,
            'globalKeyOwnershipPreservedDuringPreparation': True, 'actualHandoffAndOuterCleanupConnected': True,
            'nativeFirstPublicationOomFixtureConnected': True, 'nativeOwnerAllocationVerified': False,
            'fullCallerCacheRoutingVerified': False, 'nativeMapProbeImplementationVerified': False,
            'completePublicationRollbackVerified': False, 'recursiveChildPreservationVerified': False}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / name).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\nset_option pp.notation false\n' + without_imports(raw)

    return (
        ('input', source('InternerCallerInsertionInput.lean'), (
            ('wrong-incoming-allocator', 'origin : Caller.Origin allocator source request values before taken normalized remaining',
             'origin : Caller.Origin (allocator + 1) source request values before taken normalized remaining', 1),
            ('shift-native-item', 'item : AssemblyClone.NativeFields.Represents taken.world.memory.memory itemSource input',
             'item : AssemblyClone.NativeFields.Represents taken.world.memory.memory { itemSource with offset := itemSource.offset + 1 } input', 1),
            ('reverse-native-key', 'keyed : keyCode.run input.item normalized.items request.sequence',
             'keyed : keyCode.run input.item normalized.items.reverse request.sequence', 1),
            ('wrong-native-buffer-extent', '(.array 2 word)', '(.array 1 word)', 2),
            ('invent-initial-key', 'table = fun _ => none := by', 'table = fun _ => some ⟨0, 0⟩ := by', 1),
            ('wrong-initializer-allocator', 'GraphInit.Ownership.run runtimeSafety allocator raw',
             'GraphInit.Ownership.run runtimeSafety (allocator + 1) raw', 1),
            ('omit-handoff', '(do handoff; graph insert : Action', '(do graph insert : Action', 1),
            ('unwind-semantic-rejection', 'else (result, ⟨reached, { taken.scope with handedOff := true }⟩)',
             'else (result, ⟨reached, { taken.scope with lookup := none, handedOff := true }⟩)', 2),
        )),
        ('preparation', source('InternerCallerInsertionPreparation.lean'), (
            # The reached proof, entry specialization and cleanup footprint bind the same call.
            ('wrong-duplicate-allocator', 'duplicateCall : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator',
             'duplicateCall : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) (allocator + 1)', 3),
            ('wrong-normalized-owner', 'Memory.SliceValid allocator installed.heap normalized',
             'Memory.SliceValid (allocator + 1) installed.heap normalized', 2),
            ('alias-argument-owners', 'normalized.address ≠ operands.address) ∧', 'normalized.address = operands.address) ∧', 2),
            ('discard-old-key-table', 'installed.effects.keys = before.memory.effects.keys',
             'installed.effects.keys = (fun _ => none)', 1),
            ('erase-old-native-allocation', 'before.memory.memory.heap.lookup id = some cell → installed.memory.heap.lookup id = some cell',
             'before.memory.memory.heap.lookup id = some cell → installed.memory.heap.lookup id = none', 1),
            ('invent-reached-duplicate-address', 'copied.item = input.item ∧ operands.address = world.memory.memory.nextId',
             'copied.item = input.item ∧ operands.address = world.memory.memory.nextId + 1', 1),
            ('discard-reached-keys', 'OwnedKeys.Unique installed.effects.keys ∧ installed.effects.keys = world.memory.effects.keys ∧',
             'OwnedKeys.Unique installed.effects.keys ∧ installed.effects.keys = (fun _ => none) ∧', 1),
            ('omit-reached-publication-admission', '(publication : Publication.Input allocator source key normalized world)',
             '(publication : True)', 1),
        )),
        ('fixtures', source('InternerCallerInsertionInputTests.lean'), (
            ('wrong-argument-data', 'if empty then [] else [0]', 'if empty then [] else [1]', 1),
            ('nonempty-owner-alias', 'if empty then ⟨6, 19, 0⟩ else', 'if empty then ⟨6, 19, 1⟩ else', 1),
            ('borrowed-instead-of-owned', 'ArgumentSlice := ⟨9, values empty⟩', 'ArgumentSlice := ⟨0, values empty⟩', 1),
            ('reverse-publication-outcome', 'Insertion.Tests.ops (some .publish)', 'Insertion.Tests.ops', 1),
            ('discard-normalized-free-effects', 'if empty then 567823 else 8568025', 'if empty then 567823 else 8567924', 1),
            ('revive-retired-item', '(reached safety empty).memory.memory.heap.lookup (object empty)',
             '(ready safety empty).memory.heap.lookup (object empty)', 1),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    cases = mutation_cases()
    for group, text, changes in cases:
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous caller/native mutation: ' + group + '-' + name)
    records = []
    for group, text, changes in cases:
        records += checked_controls(output, [mutation_check(output, 'caller-native-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'caller-native-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
