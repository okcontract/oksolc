#!/usr/bin/env python3
"""Audit native publication ownership and initialized graph preservation.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

PHYSICAL = 'Compiler.Extraction.OwnedKeys.Physical.'
PUBLICATION = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication.'
NATIVE = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.'
TESTS = PUBLICATION + 'GraphTests.'
CLAIMS = [PHYSICAL + 'Completed.non_arguments_frame', PHYSICAL + 'Completed.graph_resident', NATIVE + 'publication_rows']
CLAIMS += [TESTS + name for name in ('initial_facts', 'prefix_results', 'derived_input', 'derived_contract',
                                  'live_keys_and_borrow', 'graph_key_separation', 'reached_observations', 'aliasing_retires_graph_argument')]


def audit(claims):
    required = {
        PHYSICAL + 'Completed.non_arguments_frame': {PHYSICAL + 'Completed.registry_frame'},
        PHYSICAL + 'Completed.graph_resident': {PHYSICAL + 'Completed.non_arguments_frame', 'Compiler.Extraction.OwnedKeys.frame_resident'},
        NATIVE + 'publication_rows': {PUBLICATION + 'publish_success', PHYSICAL + 'Completed.preserves', PHYSICAL + 'Completed.graph_resident'},
        TESTS + 'initial_facts': {NATIVE + 'CallerFirstSuccessTests.derived_contract'},
        TESTS + 'derived_input': {PUBLICATION + 'caller_input', NATIVE + 'CallerFirstSuccessTests.native_borrow_good',
                                 NATIVE + 'CallerFirstSuccessTests.borrowed_source_apart', TESTS + 'initial_facts'},
        TESTS + 'derived_contract': {PUBLICATION + 'complete_taken', PUBLICATION + 'publish_success', TESTS + 'derived_input',
                                    PHYSICAL + 'Completed.graph_resident', PHYSICAL + 'Completed.non_arguments_frame'},
        TESTS + 'live_keys_and_borrow': {TESTS + 'derived_contract'},
        TESTS + 'graph_key_separation': {TESTS + 'derived_contract', TESTS + 'derived_input', 'Compiler.Extraction.OwnedKeys.store_apart'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('publication graph lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'globalKeyOwnershipConnectedToNativePublication': True,
            'residentGraphAndNativePointeeFramesDerived': True, 'payloadAllocationFrameDerived': True,
            'initializedNativeBorrowToCallerReplacementAndOuterCleanupConnected': True,
            'graphKeyAliasingNegativeFixture': True, 'initialSeparationExplicit': True,
            'nativeMapImplementationVerified': False, 'repeatedInsertionVerified': False,
            'nonemptyGrowthFromInitializationVerified': False, 'recursiveChildPreservationVerified': False,
            'completePublicationRollbackVerified': False, 'composedProductionTheoremVerified': False}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / name).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\nset_option pp.notation false\n' + without_imports(raw)
    return (
        ('proof', source('OwnedKeysPhysicalGraph.lean'), (
            ('wrong-block-separation', '(different : allocation.block ≠ .arguments key.arguments)', '(different : allocation.block ≠ .bytes 0)', 1),
            ('erase-retained-allocation', 'after.memory.heap address = before.memory.heap address ∧', 'after.memory.heap address = none ∧', 1),
            ('wrong-resident-allocator', 'Memory.GraphResident allocator after.memory.heap cells ∧', 'Memory.GraphResident (allocator + 1) after.memory.heap cells ∧', 1),
            ('retire-live-item', 'after.memory.memory.heap.lookup cell.itemAddress = before.memory.memory.heap.lookup cell.itemAddress ∧',
             'after.memory.memory.heap.lookup cell.itemAddress = none ∧', 1),
        )),
        ('fixtures', source('InternerPublicationGraphTests.lean'), (
            ('borrow-owned-key', 'def source (empty : Bool) := view (operands empty)',
             'def source (empty : Bool) := view (Insertion.Native.CallerInputTests.normalized empty)', 1),
            ('duplicate-oom-as-success', 'def host := Normalization.Tests.success',
             'def host := Normalization.Tests.external (fun _ => true)', 1),
            ('leave-outer-owner', '.2.scope = ⟨none, some (owned empty), true⟩', '.2.scope = ⟨none, some (owned empty), false⟩', 1),
            ('retire-payload', '= [true, true, true, true]', '= [true, false, true, true]', 1),
            ('revive-retired-key', 'heap.lookup 9).isSome = empty', 'heap.lookup 9).isSome = true', 1),
            ('retain-aliased-argument', '(aliasPublication safety).2.memory.heap (operands false).address = none',
             '(aliasPublication safety).2.memory.heap (operands false).address = (aliased safety).memory.heap (operands false).address', 1),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    cases = mutation_cases()
    for group, text, changes in cases:
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous publication-graph mutation: ' + group + '-' + name)
    records = []
    for group, text, changes in cases:
        records += checked_controls(output, [mutation_check(output, 'publication-graph-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'publication-graph-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
