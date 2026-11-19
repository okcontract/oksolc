#!/usr/bin/env python3
"""Audit first successful insertion and subsequent native borrowed queries.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NATIVE = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.'
TESTS = NATIVE + 'CallerFirstSuccessTests.'
CLAIMS = [NATIVE + 'CallerInput.first_success'] + [TESTS + name for name in (
    'initial_key_table', 'probe_result', 'derived_contract', 'insert_result', 'handoff_and_outer_cleanup',
    'graph_and_key_projection', 'accepted_queries', 'native_borrow_good', 'borrowed_source_apart', 'original_allocations_retained', 'live_allocations')]


def audit(claims):
    required = {
        NATIVE + 'CallerInput.first_success': {NATIVE + 'first_success_reached', NATIVE + 'first_append_owned',
            NATIVE + 'publication_rows', 'Compiler.Extraction.Storage.insert_prepared_success',
            'Compiler.Extraction.AssemblyItem.Creation.create_registered',
            'Compiler.Extraction.AssemblyClone.Physical.Cloned.registered', 'Compiler.Extraction.OwnedKeys.store_unique', 'Compiler.Extraction.OwnedKeys.store_apart',
            'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.BorrowedQuery.Native.of_resident',
            'Compiler.Extraction.RepresentativeArray.Operation.query', 'Compiler.Extraction.AssemblyItem.Query.of_members'},
        TESTS + 'initial_key_table': {NATIVE + 'initialized_keys'},
        TESTS + 'derived_contract': {NATIVE + 'CallerInput.first_success', NATIVE + 'CallerInputTests.derived_input',
            TESTS + 'initial_key_table', NATIVE + 'CallerInputTests.backing_response', TESTS + 'probe_result'},
        TESTS + 'handoff_and_outer_cleanup': {NATIVE + 'CallerInput.handoff_insert', TESTS + 'insert_result'},
        TESTS + 'graph_and_key_projection': {'Compiler.Extraction.OwnedKeys.view_store'},
        TESTS + 'accepted_queries': {TESTS + 'derived_contract'},
        TESTS + 'native_borrow_good': {TESTS + 'accepted_queries', TESTS + 'graph_and_key_projection'},
        TESTS + 'borrowed_source_apart': {TESTS + 'derived_contract'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('first successful caller lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required),
            'scope': 'first deterministic insertion from caller origin and empty-container facts; initialized memory fixtures',
            'nonemptyNativeGraphAndGlobalKeyOwnershipDerived': True, 'payloadOwnershipAndContentsDerived': True,
            'nativeBorrowedQueriesAndGoodDerived': True, 'borrowedSourceKeySeparationDerived': True, 'actualHandoffAndOuterCleanupConnected': True,
            'initialNativeInputAndOwnerPremisesExplicit': True, 'itemTagDomainExplicit': True,
            'nativeMapImplementationVerified': False, 'recursiveChildPreservationVerified': False,
            'nonemptyGrowthFromInitializedCallerVerified': False, 'composedProductionTheoremVerified': False}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / name).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\nset_option pp.notation false\n' + without_imports(raw)
    return (
        ('proof', source('InternerCallerInsertionFirstSuccess.lean'), (
            ('wrong-normalized-allocator', 'Memory.SliceValid allocator (memory after).heap normalized',
             'Memory.SliceValid (allocator + 1) (memory after).heap normalized', 1),
            ('key-buffer-as-native-row', 'DescriptorRelation.Prefix (memory after).memory middle.memory.nextId [row]',
             'DescriptorRelation.Prefix (memory after).memory middle.memory.nextId [{ row with argumentsAddress := normalized.address }]', 1),
            ('wrong-key-owner', 'OwnedKeys.store before.memory.effects.keys key ⟨normalized.address, 0⟩',
             'OwnedKeys.store before.memory.effects.keys key ⟨operands.address, 0⟩', 1),
            ('wrong-published-id', '⟨normalized.address, 0⟩', '⟨normalized.address, 1⟩', 1),
            ('shift-payload', 'AssemblyClone.Physical.Reads (memory after).memory payload.data)',
             'AssemblyClone.Physical.Reads (memory after).memory { payload.data with offset := payload.data.offset + 1 })', 1),
            ('erase-original-allocation', '(memory after).memory.heap.lookup id = some cell) ∧',
             '(memory after).memory.heap.lookup id = none) ∧', 1),
            ('rewind-history', '(memory after).memory.nextId = middle.memory.nextId + 1',
             '(memory after).memory.nextId = middle.memory.nextId', 1),
            ('admit-invalid-kind', '((input.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues →',
             '(True →', 1),
        )),
        ('fixtures', source('InternerCallerInsertionFirstSuccessTests.lean'), (
            ('publication-oom-as-success', '(true, state.effects * 10 + 8)', '(false, state.effects * 10 + 8)', 1),
            ('discard-published-row', '.graph.representatives = some [row safety empty]', '.graph.representatives = some []', 2),
            ('wrong-native-opcode', '(Owner.headerAddress ⟨6, 0⟩) 0 254 =', '(Owner.headerAddress ⟨6, 0⟩) 0 253 =', 1),
            ('invent-borrowed-contents', 'Good (view (operands empty)) (operands empty).items (reached safety empty)',
             'Good (view (operands empty)) [1] (reached safety empty)', 1),
            ('wrong-borrowed-source-separation', '(view (operands empty)).allocation ≠ old.address := by',
             '(view (operands empty)).allocation ≠ old.address + 1 := by', 1),
            ('free-live-normalized-owner', '= [true, true, true, true, true]', '= [true, true, true, false, true]', 1),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    cases = mutation_cases()
    for group, text, changes in cases:
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous first-success mutation: ' + group + '-' + name)
    records = []
    for group, text, changes in cases:
        records += checked_controls(output, [mutation_check(output, 'caller-first-success-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'caller-first-success-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
