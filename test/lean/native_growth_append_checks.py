#!/usr/bin/env python3
"""Audit source-selected nonempty growth at the native insertion append boundary.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

ARRAY = 'Compiler.Extraction.RepresentativeArray.'
APPEND = ARRAY + 'Append.Registered.'
NATIVE = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.'
CLAIMS = ['Compiler.ZigAir.Memory.store_keeps_missing', ARRAY + 'Capacity.prepare_selected',
          ARRAY + 'Backing.Relocation.owner_shape', ARRAY + 'Backing.Fallback.owner_shape',
          ARRAY + 'Capacity.Registered.parent_borrow', ARRAY + 'Append.Execution.assumeCapacity_missing']
CLAIMS += [APPEND + name for name in ('growth_reached', 'spare_continuation', 'growing_verified', 'growth_parent_borrow')]
CLAIMS += [APPEND + 'GrowthTests.' + name for name in ('initial_valid', 'allocation_fits', 'derived_contract',
    'all_outcomes_parent', 'failed_growth', 'wrong_allocator', 'partial_copy', 'partial_publication')]
CLAIMS += [NATIVE + name for name in ('growth_release_keys', 'growth_release_effects', 'append_growth_callback', 'GrowthTests.forwarded', 'GrowthTests.derived_queries')]


def audit(claims):
    required = {
        ARRAY + 'Backing.Fallback.owner_shape': {ARRAY + 'Backing.Relocation.owner_shape', ARRAY + 'Backing.Registry.success_owned'},
        ARRAY + 'Capacity.Registered.parent_borrow': {ARRAY + 'Growth.Registered.parent_borrow', ARRAY + 'Capacity.prepare_selected'},
        APPEND + 'growing_verified': {ARRAY + 'Growth.Registered.fallback_execution', ARRAY + 'DescriptorRelation.fallback_registered',
            ARRAY + 'Backing.Fallback.owner_shape', ARRAY + 'DescriptorRelation.spare_registered',
            APPEND + 'spare_continuation', ARRAY + 'Append.Execution.assumeCapacity_missing', ARRAY + 'Capacity.Registered.growing'},
        APPEND + 'growth_parent_borrow': {APPEND + 'growth_reached', ARRAY + 'Capacity.Registered.parent_borrow',
            ARRAY + 'Append.Execution.assumeCapacity_word_frame', ARRAY + 'Append.Execution.assumeCapacity_storage'},
        APPEND + 'GrowthTests.derived_contract': {APPEND + 'growing_verified', APPEND + 'GrowthTests.initial_valid',
            ARRAY + 'DescriptorRelation.AppendTests.spare_derived_queries'},
        NATIVE + 'append_growth_callback': {NATIVE + 'callbacks', NATIVE + 'append', APPEND + 'runWithGrowth'},
        NATIVE + 'GrowthTests.derived_queries': {NATIVE + 'GrowthTests.forwarded', APPEND + 'GrowthTests.derived_contract'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('growing append lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'nonemptyNativeAppendConnected': True,
            'sharedSourceControl': True, 'allOutcomesParentBorrow': True, 'initialCorrespondencePremisesExplicit': True,
            'actualAllocatorVtableBindingVerified': False, 'growingPublicationCleanupOwnersDerived': False,
            'completePublicationRollbackVerified': False, 'recursiveConstructorsVerified': False}


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    directory = ROOT / 'lean/Compiler/Extraction'
    core = ('import Compiler.Extraction.RepresentativeRegisteredAppend\n'
            'import Compiler.Extraction.RepresentativeRemapGrowth\n'
            'import Compiler.Extraction.RepresentativeDescriptorRegistryTests\n'
            'import Compiler.Extraction.InsertionKernelTestSupport\n')
    core += 'set_option pp.maxSteps 8\nset_option pp.deepTerms false\nset_option pp.notation false\n'
    core += '\n'.join(without_imports((directory / name).read_text()) for name in (
        'RepresentativeRegisteredCapacity.lean', 'RepresentativeRegisteredGrowthAppend.lean',
        'RepresentativeRegisteredGrowthAppendProofs.lean', 'RepresentativeRegisteredGrowthAppendFrame.lean'))
    core += '\nexample (reason : Compiler.Extraction.Memory.Fault) : ' + APPEND + 'growthFault (.ownership reason) = .registry reason := rfl\n'
    fixtures = ('import Compiler.Extraction.RepresentativeRegisteredGrowthAppendProofs\n'
                'import Compiler.Extraction.RepresentativeRegisteredGrowthAppendFrame\n'
                'import Compiler.Extraction.RepresentativeDescriptorRegistryTests\n'
                'import Compiler.Extraction.InsertionKernelTestSupport\n'
                'set_option pp.maxSteps 8\nset_option pp.deepTerms false\nset_option pp.notation false\n')
    fixtures += without_imports((directory / 'RepresentativeRegisteredGrowthAppendTests.lean').read_text())
    native_source = (directory / 'InternerInsertionNative.lean').read_text()
    native = '\n'.join(line for line in native_source.splitlines() if line.startswith('import ')) + '\n'
    native += ('import Compiler.Extraction.RepresentativeRegisteredGrowthAppendTests\n'
               'import Compiler.Extraction.AssemblyItemCreationFieldTests\n')
    native += 'set_option pp.maxSteps 8\nset_option pp.deepTerms false\nset_option pp.notation false\n'
    native += without_imports(native_source)
    cases = (
        ('core', core, (
            ('revive-old-backing', 'finish allocator owner cells cell before reached reached.heap',
             'finish allocator owner cells cell before reached before.heap', 1),
            ('discard-growth-registry', '(after.heap, after.effects))', '(context.1, after.effects))', 1),
            ('discard-release-effects', '(after.heap, after.effects))', '(after.heap, context.2))', 1),
            ('replace-ownership-fault', '| .ownership reason => .registry reason', '| .ownership reason => .memory .unsupported', 1),
            ('wrong-capacity-call', 'allocator header capacity before\n\ntheorem unchanged',
             'allocator header minimum before\n\ntheorem unchanged', 1),
            ('wrong-appended-item', '⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩ cell.arguments.length\n    (Storage.idFor cells).toNat cell.sequence.toNat (before.heap, before.effects)\n  let reached',
             '⟨cell.argumentsAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩ cell.arguments.length\n    (Storage.idFor cells).toNat cell.sequence.toNat (before.heap, before.effects)\n  let reached', 1),
            ('rewind-history', 'after.memory.nextId = before.memory.nextId + 1 ∧', 'after.memory.nextId = before.memory.nextId ∧', 1),
            ('keep-old-native-backing', 'after.heap source = none ∧ after.memory.heap.lookup source = none ∧',
             'after.heap source = none ∧ after.memory.heap.lookup source = before.memory.heap.lookup source ∧', 1),
            ('lose-parent-permission', 'after.heap.lookup parent.allocation = some parentCell ∧',
             'after.heap.lookup parent.allocation = some {parentCell with writable := false} ∧', 1),
        )),
        ('fixtures', fixtures, (
            ('rewind-partial-publication', 'result.2.heap 2 = none ∧ result.2.memory.heap.lookup 2 = none',
             'result.2.heap 2 = (before safety).heap 2 ∧ result.2.memory.heap.lookup 2 = none', 1),
        )),
        ('native', native, (
            ('omit-captured-growth', '| .append => append runtimeSafety allocate allocator container cells input key normalized value owner before growth',
             '| .append => append runtimeSafety allocate allocator container cells input key normalized value owner before none', 1),
            ('lose-key-table', '{ effects with allocator := calls.release allocator base bytes alignment effects.allocator }',
             '{ keys := fun _ => none, allocator := calls.release allocator base bytes alignment effects.allocator }', 1),
            ('wrong-release-extent', '{ effects with allocator := calls.release allocator base bytes alignment effects.allocator }',
             '{ effects with allocator := calls.release allocator base 0 alignment effects.allocator }', 1),
            ('use-original-registry', '(result.mapError Fault.append, withMemory before reached)\n\n/-- The value errdefer',
             '(result.mapError Fault.append, withMemory before {reached with heap := (memory before).heap})\n\n/-- The value errdefer', 1),
        )),
    )
    for group, source, changes in cases:
        for name, before, _, count in changes:
            if source.count(before) != count:
                raise ValueError('ambiguous growing append mutation: ' + group + '-' + name + ': ' + str(source.count(before)))
    records = []
    for group, source, changes in cases:
        records += checked_controls(output, [mutation_check(output, 'growing-' + group + '-unchanged', source, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'growing-' + group + '-' + name,
                                                               source.replace(before, after), False, env, lean)])
    return records
