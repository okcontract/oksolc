#!/usr/bin/env python3
"""Audit generic constructor preparation, native outcomes and local returns.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
import constructor_argument_checks as arguments
import constant_word_checks as words

ITEM = arguments.ITEM
CALL = words.CALL
NATIVE = words.NATIVE
CLAIMS = [ITEM + name for name in ('prepare_with_scratch', 'returnWorld_valid', 'returnWorld_cell',
    'returnWorld_frame', 'invoke_after_take', 'invoke_native_constant')]
CLAIMS += [NATIVE + 'CallerInput.insert_allocation_failure', NATIVE + 'CallerInput.growing_empty_oom',
           ITEM + 'constant_growing_empty_oom', 'Compiler.Extraction.RepresentativeArray.readHeader_capacity']
GENERAL = tuple(CLAIMS)
CLAIMS += [CALL + name for name in ('prepared_allocations', 'route', 'returned_valid', 'returned_cell',
    'returned_frame', 'constant_growth_contract')]


def audit(claims):
    required = {
        ITEM + 'prepare_with_scratch': {ITEM + 'prepare_verified', words.MEMORY + 'allocate_at_same_address'},
        ITEM + 'returnWorld_valid': {arguments.OWNED.removesuffix('OwnedCall.') + 'Valid.cleanup'},
        ITEM + 'returnWorld_cell': {words.MEMORY + 'cleanup_lookup_older', words.MEMORY + 'valid_lookup'},
        ITEM + 'returnWorld_frame': {ITEM + 'returnWorld_cell'},
        ITEM + 'invoke_after_take': {ITEM + 'invoke_prepared', arguments.OWNED + 'Caller.find_after_take'},
        ITEM + 'invoke_native_constant': {ITEM + 'invoke_after_take', NATIVE + 'CallerInput.finish_native'},
        NATIVE + 'CallerInput.insert_allocation_failure': {NATIVE + 'CallerInput.native_frame', NATIVE + 'insert_allocation_failure'},
        CALL + 'prepared_allocations': {ITEM + 'prepare_with_scratch'},
        CALL + 'route': {ITEM + 'invoke_after_take'},
        CALL + 'returned_valid': {ITEM + 'returnWorld_valid'},
        CALL + 'returned_cell': {ITEM + 'returnWorld_cell'},
        CALL + 'returned_frame': {ITEM + 'returnWorld_frame'},
        NATIVE + 'CallerInput.growing_empty_oom': {NATIVE + 'CallerInput.growing_allocation_oom',
            'Compiler.Extraction.AssemblyItem.Creation.create_from_response',
            'Compiler.Extraction.Memory.Arguments.Duplication.run_empty', 'Compiler.Extraction.RepresentativeArray.readHeader_capacity'},
        ITEM + 'constant_growing_empty_oom': {NATIVE + 'CallerInput.growing_empty_oom', NATIVE + 'CallerInput.insert_allocation_failure',
            ITEM + 'invoke_native_constant', ITEM + 'returnWorld_frame', arguments.OWNED + 'NativeGraph.Facts.frame'},
        'Compiler.Extraction.RepresentativeArray.readHeader_capacity': {'Compiler.Extraction.RepresentativeArray.readHeader_items'},
        CALL + 'constant_growth_contract': {ITEM + 'constant_growing_empty_oom', CALL + 'prefix_results'},
    }
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError('constructor composition lost dependencies: ' + name + ': ' + ', '.join(sorted(missing)))
    for name in GENERAL:
        fixtures = {dependency for dependency in claims[name]
                    if any(part.endswith('Tests') for part in dependency.split('.'))}
        if fixtures:
            raise ValueError('generic constructor proof depends on fixtures: ' + name + ': ' + ', '.join(sorted(fixtures)))
    return {'checkedDependencies': sorted(required), 'fixtureIndependentPreparationAndReturns': True,
            'constantNativeOutcomeRouting': True, 'emptyGrowthOomAndFullReturn': True, 'recursiveInductionVerified': False,
            'generalAllocationOutcomesVerified': False, 'composedProductionTheoremVerified': False}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / (name + '.lean')).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)

    empty_source = source('InternerCallerInsertionEmptyGrowthFailure')
    proof = empty_source.index(' := by\n', empty_source.index('theorem CallerInput.growing_empty_oom'))
    boundary = ('import Compiler.Extraction.InternerCallerInsertionEmptyGrowthFailure\n' +
        empty_source[:proof].replace('theorem CallerInput.growing_empty_oom', 'theorem empty_growth_boundary') +
        ' := by\n  exact entry.growing_empty_oom ops allocate freeBacking safety allocator owner oldBacking oldCapacity capacity\n'
        '    context returnAddress base source address meaning request values input key normalized lookup constructed taken rows\n'
        '    facts admitted empty noPayload oldNonempty full selected size room createEffects allocationEffects\n'
        '    createResponse fits allocation unlocked\n'
        'end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native\n')

    return (
        ('preparation', source('InternerConstructorItem'), (
            ('wrong-scratch-identity', '⟨constructed.memory.memory.nextId, 0⟩, scratch)',
             '⟨before.memory.memory.nextId, 0⟩, scratch)', 1),
            ('rewind-address-counter', 'scratch.nextAddress = last.nextAddress',
             'scratch.nextAddress = witness.nextAddress', 1),
        )),
        ('return', source('InternerConstructorNativeReturn'), (
            ('erase-old-stack', 'cleanup itemMark\n', 'cleanup 0\n', 1),
            ('skip-item-return', 'memory := Compiler.ZigAir.Memory.cleanup before.memory.memory.nextId\n             (Compiler.ZigAir.Memory.cleanup constructed.memory.memory.nextId done.2.world.memory.memory)',
             'memory := Compiler.ZigAir.Memory.cleanup constructed.memory.memory.nextId done.2.world.memory.memory', 1),
            ('rewind-rejection', 'else (ran.1, ⟨ran.2, ⟨some lookup, some normalized, true⟩⟩)',
             'else (ran.1, ⟨taken.world, ⟨some lookup, some normalized, true⟩⟩)', 1),
            ('retain-transferred-lookup', '⟨none, some normalized, true⟩⟩)',
             '⟨some lookup, some normalized, true⟩⟩)', 1),
            ('operation-as-constant', '(kind : request.item.kind = 2)', '(kind : request.item.kind = 1)', 1),
        )),
        ('empty-growth', source('InternerCallerInsertionEmptyGrowthFailure'), (
            ('retain-destroyed-item', '(memory after).memory.heap.lookup taken.world.memory.memory.nextId = none',
             '(memory after).memory.heap.lookup taken.world.memory.memory.nextId ≠ none', 1),
            ('retain-destroyed-registry', '(memory after).heap taken.world.memory.memory.nextId = none',
             '(memory after).heap taken.world.memory.memory.nextId ≠ none', 1),
            ('invent-next-identity', '(memory after).memory.nextId = created.memory.nextId',
             '(memory after).memory.nextId = created.memory.nextId + 1', 1),
        )),
        ('empty-boundary', boundary, (
            ('nonempty-as-empty', '(empty : normalized.items = [])', '(empty : normalized.items ≠ [])', 1),
            ('owned-payload-as-borrowed', '(noPayload : input.verbatim = none)', '(noPayload : input.verbatim ≠ none)', 1),
        )),
        ('complete-growth', source('InternerConstructorConstantAllocationFailure'), (
            ('failure-as-success', '= (.error (.language .outOfMemory), ⟨reached, ⟨none, some normalized, true⟩⟩)',
             '= (.ok 0, ⟨reached, ⟨none, some normalized, true⟩⟩)', 1),
            ('drop-parent-allocation', '→ reached.memory.memory.heap.lookup id = some native',
             '→ reached.memory.memory.heap.lookup id = none', 1),
            ('drop-parent-keys', 'reached.memory.effects.keys = before.memory.effects.keys ∧',
             'reached.memory.effects.keys = (fun _ => none) ∧', 1),
        )),
        ('allocation', source('InternerCallerInsertionAllocationFailure'), (
            ('oom-as-exhaustion', '(.error (.language .outOfMemory), { taken.world with memory := memory after })',
             '(.error (.language .unsupported), { taken.world with memory := memory after })', 1),
            ('rewind-cleanup', '(.error (.language .outOfMemory), { taken.world with memory := memory after })',
             '(.error (.language .outOfMemory), taken.world)', 1),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    records = []
    for group, text, changes in mutation_cases():
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous constructor composition mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'constructor-composition-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'constructor-composition-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
