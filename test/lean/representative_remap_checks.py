#!/usr/bin/env python3
"""Audit source-bound remap refusal through nonempty growth and parent frames.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NS = 'Compiler.Extraction.RepresentativeArray.'
CLAIMS = [NS + 'Growth.prepare_growing']
CLAIMS += [NS + 'Remap.' + name for name in ('zero_new', 'empty_old', 'byte_overflow', 'refuses', 'positive_reached', 'positive_no_success')]
CLAIMS += [NS + 'Growth.Registered.' + name for name in ('reached_cases', 'parent_borrow', 'fallback_execution', 'verified')]
CLAIMS += [NS + 'Growth.Registered.Tests.' + name for name in ('actual_refusal', 'reached_fallback', 'derived_contract',
    'reached_observations', 'oom_keeps_old_vector', 'parent_across_all_outcomes', 'unknown_callback_and_wrong_owner',
    'wrapper_guards', 'partial_copy_retained', 'failed_response_retained', 'publication_failure_retained')]


def audit(claims):
    required = {
        NS + 'Growth.prepare_growing': {NS + 'Growth.prepare', NS + 'Growth.choose'},
        NS + 'Remap.refuses': {NS + 'Remap.run', NS + 'Remap.noRemap', NS + 'Backing.Release.checked_of_owned'},
        NS + 'Growth.Registered.reached_cases': {NS + 'Growth.Registered.run', NS + 'Remap.positive_reached', NS + 'Remap.positive_no_success'},
        NS + 'Growth.Registered.parent_borrow': {NS + 'Growth.Registered.reached_cases', NS + 'Backing.Fallback.parent_borrow', NS + 'Backing.Fallback.storage'},
        NS + 'Growth.Registered.fallback_execution': {NS + 'Growth.prepare_growing', NS + 'allocatedSlice_nonempty',
            NS + 'readItemsData_from_loaded', NS + 'Remap.refuses', NS + 'Growth.Registered.run'},
        NS + 'Growth.Registered.verified': {NS + 'Growth.Registered.fallback_execution', NS + 'DescriptorRelation.fallback_registered'},
        NS + 'Growth.Registered.Tests.derived_contract': {NS + 'Growth.Registered.verified', NS + 'DescriptorRelation.Tests.prefix_from_initialization'},
        NS + 'Growth.Registered.Tests.parent_across_all_outcomes': {NS + 'Growth.Registered.parent_borrow'},
    }
    for name, wanted in required.items():
        if not wanted <= claims[name]:
            raise ValueError('remap growth lost dependencies: ' + name + ': ' + ', '.join(sorted(wanted - claims[name])))
    return {'checkedDependencies': sorted(required), 'capturedNoRemapBodyVerified': True,
            'nonemptyRefusalFallbackComposed': True, 'reachedParentBorrowPreserved': True,
            'callbackIdentityDerivedFromOwner': False, 'otherRemapCallbacksVerified': False,
            'nativeInsertionGrowthIntegrated': False, 'recursiveConstructorsVerified': False}


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    directory = ROOT / 'lean/Compiler/Extraction'
    source = 'import Compiler.Extraction.RepresentativeFallbackRegistryTests\n'
    # Bound only diagnostic printing of deliberately false concrete equations.
    source += 'set_option pp.maxSteps 8\nset_option pp.deepTerms false\n'
    source += '\n'.join(without_imports((directory / name).read_text()) for name in (
        'RepresentativeRemapProgram.lean', 'RepresentativeRemap.lean',
        'RepresentativeRemapGrowth.lean', 'RepresentativeRemapGrowthTests.lean'))
    changes = (
        ('callback-returns-pointer', ': Option Nat := none', ': Option Nat := some _base', 1),
        ('wrong-zero-guard', 'if capacity = 0 then\n', 'if capacity = 1 then\n', 1),
        ('old-length-overflow', 'else if capacity * 32 ≥ addressLimit', 'else if oldCapacity * 32 ≥ addressLimit', 1),
        ('wrong-allocator', 'match Backing.Release.check allocator data oldCapacity before with',
         'match Backing.Release.check (allocator + 1) data oldCapacity before with', 1),
        ('short-extent', 'match Backing.Release.check allocator data oldCapacity before with',
         'match Backing.Release.check allocator data (oldCapacity - 1) before with', 1),
        ('unknown-is-refusal', '| .unsupported => (.error (.memory .unsupported), before)', '| .unsupported => (.ok none, before)', 1),
        ('free-new-capacity', '| .ok none => Backing.Fallback.run allocate release allocator header data oldCapacity capacity reached',
         '| .ok none => Backing.Fallback.run allocate release allocator header data capacity capacity reached', 1),
        ('wrong-saved-pointer', '| .ok none => Backing.Fallback.run allocate release allocator header data oldCapacity capacity reached',
         '| .ok none => Backing.Fallback.run allocate release allocator header header oldCapacity capacity reached', 1),
        ('omit-fallback', '| .ok none => Backing.Fallback.run allocate release allocator header data oldCapacity capacity reached',
         '| .ok none => (.ok (some ()), reached)', 1),
        ('rewind-lifetime', 'after.memory.nextId = before.memory.nextId + 1', 'after.memory.nextId = before.memory.nextId', 1),
        ('erase-parent', 'after.memory.heap.lookup parent.allocation = some cell', 'after.memory.heap.lookup parent.allocation = none', 1),
        ('retain-old-backing', 'after.heap source = none ∧', 'after.heap source ≠ none ∧', 1),
    )
    for name, before, _, count in changes:
        if source.count(before) != count:
            raise ValueError('ambiguous remap growth mutation: ' + name)
    records = checked_controls(output, [mutation_check(output, 'remap-growth-unchanged', source, True, env, lean)])
    for name, before, after, _ in changes:
        records += checked_controls(output, [mutation_check(output, 'remap-growth-' + name,
                                                           source.replace(before, after), False, env, lean)])
    return records
