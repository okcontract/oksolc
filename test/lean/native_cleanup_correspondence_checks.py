#!/usr/bin/env python3
"""Audit native row/footprint preservation through actual insertion cleanup.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

MEMORY = 'Compiler.ZigAir.Memory.'
EXPRESSION = 'Compiler.Extraction.Expression.'
DEINIT = 'Compiler.Extraction.ExpressionDeinit.Native.'
NATIVE = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.'
ARRAY = 'Compiler.Extraction.RepresentativeArray.'
CLAIMS = [MEMORY + 'fieldPointer_after_invalidate', MEMORY + 'load_disjoint_after_invalidate',
          EXPRESSION + 'readField_before_invalidate', EXPRESSION + 'prefix_before_invalidate', DEINIT + 'run_framed']
CLAIMS += [NATIVE + name for name in ('rollback_verified', 'rollback_normalized_verified', 'growing_append_owned',
    'growing_publication_oom_cleanup', 'deterministic_growing_oom', 'GrowingTests.derived_contract')]


def audit(claims):
    required = {
        MEMORY + 'fieldPointer_after_invalidate': {MEMORY + 'invalidate_success', MEMORY + 'fieldPointer_replace_cells'},
        MEMORY + 'load_disjoint_after_invalidate': {MEMORY + 'invalidate_success', MEMORY + 'Cells.lookup_forget',
            MEMORY + 'Cells.read_eq_of_lookup', MEMORY + 'access_replace_cells'},
        EXPRESSION + 'prefix_before_invalidate': {EXPRESSION + 'readField_before_invalidate'},
        EXPRESSION + 'readField_before_invalidate': {MEMORY + 'fieldPointer_after_invalidate', MEMORY + 'load_disjoint_after_invalidate'},
        DEINIT + 'run_framed': {DEINIT + 'run_verified', EXPRESSION + 'prefix_before_invalidate',
            MEMORY + 'invalidate_frame', ARRAY + 'DescriptorRelation.frame',
            'Compiler.Extraction.AssemblyItem.Released.keeps_dead', 'Compiler.Extraction.ExpressionDeinit.Payload.free_keeps_dead'},
        NATIVE + 'rollback_verified': {DEINIT + 'run_framed', DEINIT + 'RunFrame.released', ARRAY + 'Pop.Registered.verified'},
        NATIVE + 'rollback_normalized_verified': {NATIVE + 'rollback_verified', ARRAY + 'DescriptorRelation.frame',
            'Compiler.Extraction.ExpressionDeinit.Payload.free_keeps_dead'},
        NATIVE + 'growing_publication_oom_cleanup': {NATIVE + 'growing_append_owned', NATIVE + 'rollback_normalized_verified',
            MEMORY + 'Allocation.SameShape.trans'},
        NATIVE + 'deterministic_growing_oom': {NATIVE + 'prepare_owned', NATIVE + 'growing_publication_oom_cleanup',
            ARRAY + 'DescriptorRelation.query', 'Compiler.Extraction.Storage.insert_prepared_oom'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('cleanup correspondence lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'nativePrefixRetainedThroughOuterCleanup': True,
            'allRepresentativeFieldQueriesDerived': True, 'relocatedBackingOwnershipRetained': True,
            'ownerGeometryDerivedThroughGrowthAndCleanup': True, 'allDestroyedAllocationsRemainDead': True,
            'retiredBackingRemainsDead': True, 'completeGraphCorrespondenceVerified': False,
            'completePublicationRollbackVerified': False, 'recursiveConstructorsVerified': False}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler' / name).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        display = '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\nset_option pp.notation false\n'
        return imports + display + without_imports(raw)

    return (
        ('memory', source('ZigAir/MemoryInvalidationFrame.lean'), (
            ('shift-selector', 'fieldPointer after (.pointer (.pointer writable many owner) address) offset =',
             'fieldPointer after (.pointer (.pointer writable many owner) address) (offset + 8) =', 1),
            ('omit-slice-length-leaf', '∀ position ∈ readType.readOffsets readOffset,', '∀ position ∈ [readOffset],', 1),
            ('include-erased-boundary', 'position < target.offset ∨ target.offset + layout.bytes ≤ position',
             'position ≤ target.offset ∨ target.offset + layout.bytes ≤ position', 1),
        )),
        ('row', source('Extraction/ExpressionInvalidationFrame.lean'), (
            ('include-destroyed-row', '(earlier : other < index)', '(earlier : other ≤ index)', 1),
            ('destroy-previous-row', 'invalidate before ⟨lifetime, cells.length * 32⟩',
             'invalidate before ⟨lifetime, (cells.length - 1) * 32⟩', 1),
        )),
        ('destructor', source('Extraction/ExpressionDeinitFrameProofs.lean'), (
            ('erase-outside-registry', '→ after.heap id = before.heap id', '→ after.heap id = none', 1),
            ('erase-outside-allocation', '→ after.memory.heap.lookup id = before.memory.heap.lookup id',
             '→ after.memory.heap.lookup id = none', 1),
            ('revive-dead-registry', '    after.heap id = none ∧ after.memory.heap.lookup id = none\n  released :',
             '    after.heap id = before.heap object ∧ after.memory.heap.lookup id = none\n  released :', 1),
            ('revive-released-registry', '    after.heap id = none ∧ after.memory.heap.lookup id = none\n\n/--',
             '    after.heap id ≠ none ∧ after.memory.heap.lookup id = none\n\n/--', 1),
            ('revive-released-native', '    after.heap id = none ∧ after.memory.heap.lookup id = none\n\n/--',
             '    after.heap id = none ∧ after.memory.heap.lookup id ≠ none\n\n/--', 1),
            ('release-empty-sentinel', '(arguments.items ≠ [] ∧ id = arguments.address) →',
             '(True ∧ id = arguments.address) →', 1),
        )),
        ('rollback-post', source('Extraction/InternerInsertionRollbackProofs.lean'), (
            ('move-owner', 'ownerCell.SameShape finalOwner', 'ownerCell.SameShape { finalOwner with base := finalOwner.base + 1 }', 1),
            ('revive-released-native', '        (memory after).heap id = none ∧ (memory after).memory.heap.lookup id = none) := by',
             '        (memory after).heap id = none ∧ (memory after).memory.heap.lookup id ≠ none) := by', 1),
        )),
        ('outer-post', source('Extraction/InternerInsertionOuterCleanup.lean'), (
            ('change-owner-lifetime', 'ownerCell.SameShape finalOwner',
             'ownerCell.SameShape { finalOwner with stack := !finalOwner.stack }', 1),
            ('release-empty-normalized', '(normalized.items ≠ [] ∧ id = normalized.address) →',
             '(True ∧ id = normalized.address) →', 1),
            ('revive-released', '        (memory after).heap id = none ∧ (memory after).memory.heap.lookup id = none) := by',
             '        (memory after).heap id = none ∧ (memory after).memory.heap.lookup id ≠ none) := by', 1),
        )),
        ('growing-post', source('Extraction/InternerInsertionGrowingOwnership.lean'), (
            ('change-owner-write-permission', 'ownerCell.SameShape finalOwner',
             'ownerCell.SameShape { finalOwner with writable := !finalOwner.writable }', 2),
            ('revive-released', '        (memory after).heap id = none ∧ (memory after).memory.heap.lookup id = none) := by',
             '        (memory after).heap id ≠ none ∧ (memory after).memory.heap.lookup id = none) := by', 1),
        )),
        ('complete', source('Extraction/InternerInsertionGrowingPrepared.lean'), (
            ('retain-old-backing', '(memory after).heap oldLifetime = none',
             '(memory after).heap oldLifetime = before.memory.heap oldLifetime', 1),
            ('own-dead-backing', 'Backing.Release.Owned allocator ⟨middle.memory.nextId, 0⟩ capacity (memory after)',
             'Backing.Release.Owned allocator ⟨oldLifetime, 0⟩ capacity (memory after)', 1),
            ('wrong-row-id', '(DescriptorRelation.values id.toNat)', '(DescriptorRelation.values (id.toNat + 1))', 2),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    cases = mutation_cases()
    for group, text, changes in cases:
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous cleanup correspondence mutation: ' + group + '-' + name)
    records = []
    for group, text, changes in cases:
        records += checked_controls(output, [mutation_check(output, 'cleanup-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'cleanup-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
