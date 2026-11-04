#!/usr/bin/env python3
"""Audit private argument-buffer preservation through native relocating insertion.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

CALLER = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.'
NATIVE = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.'
TESTS = NATIVE + 'CallerGrowingChainTests.CustodyTests.'
CLAIMS = [CALLER + 'Custody.good', CALLER + 'Origin.custody_after_publication',
          NATIVE + 'CallerInput.custody', NATIVE + 'CallerInput.custody_after_growth', NATIVE + 'CallerInput.growing_success']
CLAIMS += [TESTS + name for name in ('normalized_custody', 'normalized_words', 'published_not_private', 'empty_custody', 'parent_custody', 'parent_after_growth')]


def audit(claims):
    required = {
        CALLER + 'Custody.good': {'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.borrowed_ready'},
        NATIVE + 'CallerInput.custody': {NATIVE + 'CallerInput.fresh', CALLER + 'Origin.held'},
        CALLER + 'Origin.custody_after_publication': {CALLER + 'Origin.fresh', CALLER + 'Custody.apart'},
        NATIVE + 'CallerInput.custody_after_growth': {CALLER + 'Origin.custody_after_publication', CALLER + 'Origin.fresh', CALLER + 'Custody.apart',
            'Compiler.Extraction.OwnedKeys.store'},
        NATIVE + 'CallerInput.growing_success': {NATIVE + 'CallerInput.custody_after_growth', CALLER + 'Custody.good',
            NATIVE + 'growing_append_owned', NATIVE + 'publication_rows'},
        TESTS + 'normalized_custody': {NATIVE + 'CallerGrowingChainTests.initialized_prefix', NATIVE + 'CallerInput.custody'},
        TESTS + 'normalized_words': {TESTS + 'normalized_custody', CALLER + 'Custody.good'},
        TESTS + 'parent_custody': {NATIVE + 'CallerGrowingChainTests.initialized_prefix', 'Compiler.Extraction.Memory.GraphResident'},
        TESTS + 'parent_after_growth': {NATIVE + 'CallerGrowingChainTests.growing_contract', TESTS + 'parent_custody'},
        TESTS + 'published_not_private': {NATIVE + 'CallerGrowingChainTests.growing_contract', CALLER + 'Custody.apart'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('caller custody lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required),
            'scope': 'private argument-buffer custody across deterministic native relocation and key replacement',
            'custodyFromActualCallerTake': True, 'parentBackingSeparationDerived': True,
            'parentNewKeySeparationFromChildFreshness': True, 'exactParentWordsFromNativeValidity': True,
            'custodyDoesNotAuthorizeConsumption': True, 'emptySentinelDoesNotOwnAllocation': True,
            'finalGoodOrGraphEqualityPremise': False, 'fullRecursiveChildCallerConnected': False,
            'parentSourceAndItemTransportComplete': False, 'partialFailureCustodyComplete': False,
            'completePublicationRollbackVerified': False, 'composedProductionTheoremVerified': False}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / name).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\nset_option pp.notation false\n' + without_imports(raw)
    return (
        ('custody', source('InternerCallerCustody.lean'), (
            ('invent-parent-words', 'Good (view slice) slice.items', 'Good (view slice) [1]', 1),
            ('change-allocator', '    Custody allocator parent after := by',
             '    Custody (allocator + 1) parent after := by', 1),
            ('publish-parent-buffer', 'key ⟨normalized.address, id⟩', 'key ⟨parent.address, id⟩', 1),
            ('allow-backing-alias', '(vector : Memory.Vector allocator before.memory.heap oldLifetime cells)',
             '(vector : before.memory.heap oldLifetime = some ⟨allocator, .arguments parent.items⟩)', 1),
        )),
        ('fixtures', source('InternerCallerCustodyTests.lean'), (
            ('invent-normalized-words', 'Good (view (normalized safety empty 4)) (CallerInputTests.values empty)',
             'Good (view (normalized safety empty 4)) [1]', 1),
            ('published-still-private', 'Caller.Custody 7 (normalized safety empty 4) (taken safety empty 4).2.world.memory',
             'Caller.Custody 7 (normalized safety empty 4) (before safety empty 5).memory', 1),
            ('invent-grown-parent-words', 'Good (parent empty) (CallerInputTests.values empty)', 'Good (parent empty) [1]', 1),
            ('nonempty-sentinel', 'Caller.Custody 7 ⟨address, []⟩ memory', 'Caller.Custody 7 ⟨address, [0]⟩ memory', 1),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    records = []
    for group, text, changes in mutation_cases():
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous custody mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'caller-custody-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'caller-custody-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
