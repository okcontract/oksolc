#!/usr/bin/env python3
"""Audit caller-connected spare insertion and initialized repeated native borrows.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NATIVE = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.'
TESTS = NATIVE + 'CallerSpareSuccessTests.'
CLAIMS = [NATIVE + 'CallerInput.spare_success'] + [TESTS + name for name in (
    'initial_representation', 'initial_geometry', 'derived_input', 'preparation_results', 'probe_result',
    'derived_contract', 'insert_result', 'handoff_and_outer_cleanup', 'graph_and_key_projection',
    'accepted_queries', 'native_borrows', 'borrowed_source_apart', 'reached_lifetimes')]


def audit(claims):
    required = {
        NATIVE + 'CallerInput.spare_success': {NATIVE + 'spare_success_reached', NATIVE + 'CallerInput.graph_custody',
            NATIVE + 'CallerInput.native_frame'},
        TESTS + 'initial_representation': {NATIVE + 'CallerFirstSuccessTests.derived_contract'},
        TESTS + 'derived_input': {NATIVE + 'caller_input', NATIVE + 'CallerFirstSuccessTests.native_borrow_good',
            NATIVE + 'CallerFirstSuccessTests.borrowed_source_apart', TESTS + 'initial_representation'},
        TESTS + 'derived_contract': {NATIVE + 'CallerInput.spare_success', TESTS + 'derived_input',
            TESTS + 'initial_representation', TESTS + 'initial_geometry', TESTS + 'preparation_results', TESTS + 'probe_result'},
        TESTS + 'handoff_and_outer_cleanup': {NATIVE + 'CallerInput.handoff_insert', TESTS + 'insert_result'},
        TESTS + 'graph_and_key_projection': {'Compiler.Extraction.OwnedKeys.view_store', NATIVE + 'CallerFirstSuccessTests.graph_and_key_projection'},
        TESTS + 'accepted_queries': {TESTS + 'derived_contract'},
        TESTS + 'native_borrows': {TESTS + 'accepted_queries', TESTS + 'graph_and_key_projection'},
        TESTS + 'borrowed_source_apart': {TESTS + 'derived_contract'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('spare successful caller lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required),
            'scope': 'caller-connected deterministic spare success; two actual insertions from initialized fixtures',
            'nativeGraphAndGlobalKeyOwnershipDerived': True, 'payloadOwnershipAndContentsDerived': True,
            'oldAndNewNativeBorrowsAndNextCallerSeparationDerived': True, 'actualHandoffAndOuterCleanupConnected': True,
            'initialCorrespondenceAndKeySeparationExplicit': True, 'itemTagDomainExplicit': True,
            'nativeMapImplementationVerified': False, 'fullCallerCacheRoutingVerified': False,
            'nonemptyGrowthFromInitializedCallerVerified': False, 'completePublicationRollbackVerified': False,
            'recursiveChildPreservationVerified': False, 'composedProductionTheoremVerified': False}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / name).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\nset_option pp.notation false\n' + without_imports(raw)
    return (
        ('proof', source('InternerCallerInsertionSpareSuccess.lean'), (
            ('allow-full-backing', '(spare : cells.length < capacity)', '(spare : cells.length ≤ capacity)', 1),
            ('wrong-normalized-allocator', 'Memory.SliceValid allocator (memory after).heap normalized',
             'Memory.SliceValid (allocator + 1) (memory after).heap normalized', 1),
            ('key-buffer-as-native-row', 'DescriptorRelation.Prefix (memory after).memory lifetime (cells ++ [row])',
             'DescriptorRelation.Prefix (memory after).memory lifetime (cells ++ [{ row with argumentsAddress := normalized.address }])', 1),
            ('wrong-key-owner', '⟨normalized.address, BitVec.ofNat 32 cells.length⟩', '⟨operands.address, BitVec.ofNat 32 cells.length⟩', 1),
            ('wrong-published-id', '⟨normalized.address, BitVec.ofNat 32 cells.length⟩', '⟨normalized.address, 0⟩', 1),
            ('shift-payload', 'AssemblyClone.Physical.Reads (memory after).memory payload.data)',
             'AssemblyClone.Physical.Reads (memory after).memory { payload.data with offset := payload.data.offset + 1 })', 1),
            ('erase-original-allocation', '(memory after).memory.heap.lookup id = some native) ∧',
             '(memory after).memory.heap.lookup id = none) ∧', 1),
            ('rewind-history', '(memory after).memory.nextId = middle.memory.nextId',
             '(memory after).memory.nextId = taken.world.memory.memory.nextId', 1),
            ('revive-retired-key', '(memory after).heap old.address = none ∧',
             '(memory after).heap old.address = before.memory.heap old.address ∧', 1),
        )),
        ('fixtures', source('InternerCallerInsertionSpareSuccessTests.lean'), (
            ('alias-duplicate-to-normalized', '⟨if empty then 13 else 16, values empty⟩', '⟨if empty then 13 else 15, values empty⟩', 1),
            ('publication-oom-as-success', 'def ops := CallerFirstSuccessTests.ops',
             'def ops := { CallerFirstSuccessTests.ops with probe := fun _ state => (false, state.effects * 10 + 8) }', 1),
            ('wrong-result-id', '= (.ok 1, reached safety empty)', '= (.ok 0, reached safety empty)', 1),
            ('leave-outer-owner', '⟨none, some (normalized empty), true⟩', '⟨none, some (normalized empty), false⟩', 1),
            ('invent-borrowed-contents', 'Good (view slice) slice.items (reached safety empty)', 'Good (view slice) [1] (reached safety empty)', 1),
            ('retire-old-payload', '= [true, true, true, true, true, true, true, true]', '= [true, false, true, true, true, true, true, true]', 1),
            ('revive-retired-key', 'heap.lookup 9).isSome = empty', 'heap.lookup 9).isSome = true', 1),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    cases = mutation_cases()
    for group, text, changes in cases:
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous spare-success mutation: ' + group + '-' + name)
    records = []
    for group, text, changes in cases:
        records += checked_controls(output, [mutation_check(output, 'caller-spare-success-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'caller-spare-success-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
