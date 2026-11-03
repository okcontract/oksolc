#!/usr/bin/env python3
"""Audit caller-connected nonempty growth from initialized production components.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NATIVE = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.'
TESTS = NATIVE + 'CallerGrowingChainTests.'
CLAIMS = [NATIVE + name for name in ('CallerInput.extended_arguments_apart', 'append_cell', 'publication_cell',
    'prepared_publication_cell', 'CallerInput.growing_success')]
CLAIMS += [TESTS + name for name in ('first_result', 'observations_0', 'observations_1', 'observations_2',
    'observations_3', 'observations_4', 'reached_observations', 'prefix_results', 'preparation_results',
    'initial_prefix', 'GraphFacts.first_borrow', 'Prefix.parent_good', 'Prefix.source_private', 'Prefix.caller_input', 'GraphFacts.input_apart',
    'Prefix.completed', 'GraphFacts.capacity_read', 'spare_step', 'initialized_prefix', 'prepared_geometry',
    'ready_contract', 'backing_fits', 'growing_contract', 'parent_borrow_after_growth', 'allocator_effects')]


def audit(claims):
    required = {
        NATIVE + 'CallerInput.growing_success': {NATIVE + 'growing_success_reached', NATIVE + 'prepare_reached', NATIVE + 'extended_arguments_apart',
            NATIVE + 'growing_append_owned', NATIVE + 'publication_rows', NATIVE + 'prepared_publication_cell',
            'Compiler.Extraction.Storage.insert_prepared_success', 'Compiler.Extraction.OwnedKeys.Physical.Completed.graph_resident',
            'Compiler.Extraction.RepresentativeArray.Operation.query', 'Compiler.Extraction.AssemblyItem.Query.of_members'},
        NATIVE + 'prepared_publication_cell': {NATIVE + 'append_cell', NATIVE + 'publication_cell'},
        TESTS + 'initial_prefix': {NATIVE + 'CallerFirstSuccessTests.derived_contract'},
        TESTS + 'Prefix.caller_input': {NATIVE + 'caller_input', TESTS + 'Prefix.parent_good', TESTS + 'Prefix.source_private', TESTS + 'prefix_results'},
        TESTS + 'Prefix.completed': {NATIVE + 'CallerInput.handoff_insert', TESTS + 'Prefix.caller_input'},
        TESTS + 'spare_step': {NATIVE + 'CallerInput.spare_success', TESTS + 'Prefix.completed', TESTS + 'GraphFacts.input_apart'},
        TESTS + 'initialized_prefix': {TESTS + 'initial_prefix', TESTS + 'spare_step'},
        TESTS + 'ready_contract': {NATIVE + 'CallerInput.prepare', TESTS + 'initialized_prefix', TESTS + 'preparation_results'},
        TESTS + 'backing_fits': {TESTS + 'ready_contract', TESTS + 'prepared_geometry'},
        TESTS + 'growing_contract': {NATIVE + 'CallerInput.growing_success', TESTS + 'initialized_prefix',
            TESTS + 'backing_fits', TESTS + 'Prefix.completed', TESTS + 'GraphFacts.input_apart'},
        TESTS + 'parent_borrow_after_growth': {TESTS + 'growing_contract', TESTS + 'GraphFacts.first_borrow'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('initialized growing caller lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required),
            'scope': 'deterministic successful nonempty relocation; six initialized insertion continuations in both owner layouts and argument cases',
            'initialOwnershipFromEarlierInsertionAndPublicationDerived': True,
            'nativeGraphAndGlobalKeyOwnershipDerived': True, 'liveParentBorrowAcrossGrowthDerived': True,
            'cloneFieldsPayloadOwnershipAndContentsDerived': True, 'actualHandoffAndOuterCleanupConnected': True,
            'oldBackingAndReplacedKeyRetirementDerived': True, 'exactAllocatorEffectsChecked': True,
            'genericInitialCorrespondenceAndKeySeparationExplicit': True, 'itemTagDomainExplicit': True,
            'capturedRefusingRemapIdentityExplicit': True, 'nativeAllocatorVtableBindingVerified': False,
            'nativeMapImplementationVerified': False, 'fullCallerCacheRoutingVerified': False,
            'generalGrowingFailureCompositionVerified': False, 'completePublicationRollbackVerified': False,
            'recursiveChildPreservationVerified': False, 'composedProductionTheoremVerified': False}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / name).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\nset_option pp.notation false\n' + without_imports(raw)
    return (
        ('proof', source('InternerCallerInsertionGrowingSuccess.lean'), (
            ('allow-spare', '(full : oldCapacity < Append.nextLength cells.length)', '(full : oldCapacity ≤ Append.nextLength cells.length)', 1),
            ('wrong-key-owner', '⟨normalized.address, BitVec.ofNat 32 cells.length⟩', '⟨operands.address, BitVec.ofNat 32 cells.length⟩', 2),
            ('wrong-published-id', '⟨normalized.address, BitVec.ofNat 32 cells.length⟩', '⟨normalized.address, 0⟩', 2),
            ('key-buffer-as-native-row', 'DescriptorRelation.Prefix (memory after).memory middle.memory.nextId (cells ++ [row])',
             'DescriptorRelation.Prefix (memory after).memory middle.memory.nextId (cells ++ [{ row with argumentsAddress := normalized.address }])', 1),
            ('revive-backing', '(memory after).heap oldLifetime = none ∧', '(memory after).heap oldLifetime = before.memory.heap oldLifetime ∧', 1),
            ('revive-key', '(memory after).heap old.address = none ∧', '(memory after).heap old.address = before.memory.heap old.address ∧', 1),
            ('rewind-history', '(memory after).memory.nextId = middle.memory.nextId + 1', '(memory after).memory.nextId = middle.memory.nextId', 1),
            ('erase-parent', '(memory after).memory.heap.lookup id = some native) ∧', '(memory after).memory.heap.lookup id = none) ∧', 1),
            ('shift-payload', 'AssemblyClone.Physical.Reads (memory after).memory payload.data)',
             'AssemblyClone.Physical.Reads (memory after).memory { payload.data with offset := payload.data.offset + 1 })', 1),
            ('wrong-projected-row', 'cell input key normalized value Storage.publishedOwnership after = row := by',
             'cell input key normalized value Storage.publishedOwnership after = { row with itemAddress := normalized.address } := by', 1),
        )),
        ('chain', source('InternerCallerInsertionGrowingChainTests.lean'), (
            ('spare-at-full-capacity', '(spare : n < 4)', '(spare : n ≤ 4)', 1),
            ('wrong-prefix-length', '(cells safety empty n).length = n + 1', '(cells safety empty n).length = n + 2', 1),
            ('invent-borrowed-contents', 'Good (parent empty) (request empty).arguments world', 'Good (parent empty) [1] world', 1),
            ('lose-outer-handoff', '⟨none, some (normalized safety empty n), true⟩', '⟨none, some (normalized safety empty n), false⟩', 1),
        )),
        ('fixtures', source('InternerCallerInsertionGrowingSuccessTests.lean'), (
            ('wrong-backing-lifetime', 'if empty then 27 else 39', 'if empty then 28 else 40', 1),
            ('keep-old-capacity', 'GraphFacts safety (grownLifetime empty) 13', 'GraphFacts safety (grownLifetime empty) 5', 1),
            ('wrong-result-id', 'run safety empty 5 = (.ok 5,', 'run safety empty 5 = (.ok 4,', 1),
            ('lose-outer-handoff', '⟨none, some (normalized safety empty 4), true⟩', '⟨none, some (normalized safety empty 4), false⟩', 1),
            ('omit-old-release', '* 10 + 7) * 10 + 9)', '* 10 + 7) * 10 + 0)', 1),
            ('omit-key-release', '(if empty then 0 else 101)', '(if empty then 0 else 0)', 1),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    cases = mutation_cases()
    for group, text, changes in cases:
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous growing-success mutation: ' + group + '-' + name)
    records = []
    for group, text, changes in cases:
        records += checked_controls(output, [mutation_check(output, 'caller-growing-success-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'caller-growing-success-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
