#!/usr/bin/env python3
"""Audit arbitrary-word publication and the actual materializer cache hit.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
import constructor_argument_checks as arguments
import constructor_item_checks as constructor
import native_constant_checks as constants
import native_graph_checks as graph
import native_recursion_checks as recursive

INPUT = arguments.ITEM + 'ConstantInputTests.'
PUBLICATION = arguments.ITEM + 'ConstantPublicationTests.'
CACHE = arguments.ITEM + 'ConstantCacheTests.'
WORD = recursive.NS + 'WordConstantTests.'
MEMORY = 'Compiler.ZigAir.Memory.'
APPEND = 'Compiler.Extraction.RepresentativeArray.Append.Registered.'
NATIVE = arguments.OWNED + 'Insertion.Native.'
CALL = arguments.ITEM + 'RecursiveTests.Call.'

CLAIMS = [MEMORY + 'allocate_at_same_address', APPEND + 'spare_same',
          CALL + 'spare_native', CALL + 'publication_return', CALL + 'spare_publication']
CLAIMS += [INPUT + name for name in ('allocations', 'prepared', 'stack', 'normalized', 'missed', 'observed', 'established')]
CLAIMS += [PUBLICATION + name for name in ('duplicate_result', 'creation_fits', 'created', 'cloned',
    'rows_count', 'value_read', 'contract')]
CLAIMS += [CACHE + name for name in ('allocations', 'prepared', 'stack', 'initialized', 'room', 'selected',
    'cached', 'invoked', 'entered_facts', 'returned_facts', 'locals_retired')]
CLAIMS += [WORD + name for name in ('constant_equivalent', 'materialize_equivalent',
    'program_equivalent', 'program_contract', 'program_zero')]


def bindings():
    return {'constructors': constructor.bindings(), 'recursiveFamily': constants.bindings(),
            'scope': 'same initialized constructor family: four operation constructors, arbitrary-word '
                     'constant/materializer publication, returned identifier passed to a materializer cache hit, '
                     'both local returns and a native read of the published word',
            'all256BitWords': True, 'bothSafetyLayouts': True, 'allPositiveDepths': True,
            'completeConstructorDependencyClosureVerified': False,
            'generalAllocationOutcomesVerified': False, 'recursiveInductionVerified': False}


def audit(claims):
    required = {
        INPUT + 'prepared': {arguments.ITEM + 'prepare_verified', INPUT + 'allocations'},
        INPUT + 'stack': {INPUT + 'prepared', MEMORY + 'allocate_at_same_address'},
        INPUT + 'observed': {INPUT + 'prepared', INPUT + 'stack', INPUT + 'normalized', INPUT + 'missed'},
        PUBLICATION + 'creation_fits': {INPUT + 'stack', INPUT + 'established',
            MEMORY + 'valid_lookup', MEMORY + 'lookup_of_mem_valid'},
        PUBLICATION + 'created': {PUBLICATION + 'creation_fits',
            'Compiler.Extraction.AssemblyItem.Creation.create_from_response'},
        CALL + 'spare_publication': {APPEND + 'spare_same', NATIVE + 'CallerInput.spare_success',
            NATIVE + 'CallerInput.finish_native', 'Compiler.Extraction.Cache.put_returns'},
        PUBLICATION + 'contract': {CALL + 'spare_publication', PUBLICATION + 'created',
            PUBLICATION + 'duplicate_result', PUBLICATION + 'cloned', INPUT + 'established'},
        PUBLICATION + 'value_read': {graph.FACTS + 'native', graph.NS + 'Facts.constants'},
        CACHE + 'prepared': {PUBLICATION + 'contract', MEMORY + 'allocate_at_same_address', arguments.ITEM + 'prepare_verified'},
        CACHE + 'stack': {CACHE + 'prepared', MEMORY + 'allocate_at_same_address'},
        CACHE + 'cached': {arguments.OWNED + 'Caller.find_cached', CACHE + 'initialized', CACHE + 'selected', CACHE + 'room'},
        CACHE + 'invoked': {CACHE + 'cached', arguments.ITEM + 'invoke_prepared', CACHE + 'stack'},
        CACHE + 'entered_facts': {graph.FACTS + 'frame',
            'Compiler.Extraction.Memory.Arguments.Normalization.caller_buffer', CACHE + 'prepared', CACHE + 'stack'},
        CACHE + 'returned_facts': {graph.FACTS + 'cleanup', CALL + 'returned_cell', CACHE + 'entered_facts'},
        CACHE + 'locals_retired': {MEMORY + 'cleanup_lookup_stack', MEMORY + 'allocate_retains_shape', CACHE + 'entered_facts'},
        WORD + 'constant_equivalent': {PUBLICATION + 'contract', recursive.TESTS + 'same_call', recursive.NS + 'constant_succ'},
        WORD + 'materialize_equivalent': {CACHE + 'invoked', recursive.NS + 'materialize_succ'},
        WORD + 'program_equivalent': {constants.TESTS + 'prefix_result', WORD + 'constant_equivalent',
            WORD + 'materialize_equivalent', 'Compiler.Algebraic.Effect.bind_success'},
        WORD + 'program_contract': {WORD + 'program_equivalent', CACHE + 'returned_facts', CACHE + 'locals_retired',
            PUBLICATION + 'value_read', graph.FACTS + 'native'},
    }
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError('constant word connection lost dependencies: ' + name + ': ' + ', '.join(sorted(missing)))
    return {'checkedDependencies': sorted(required), 'sourceBinding': bindings(),
            'arbitraryWordPublicationAndMaterializerCacheHitVerified': True,
            'actualAllocationCountersAndPublishedKeyDerived': True,
            'bothMaterializerLocalsRetired': True, 'allPreCacheNativeCellsRetained': True,
            'completeNativeGraphInvariantVerified': False, 'completeConstructorDependencyClosureVerified': False,
            'generalAllocationOutcomesVerified': False, 'recursiveInductionVerified': False,
            'composedProductionTheoremVerified': False}


def mutation_cases():
    def source(path):
        raw = (ROOT / 'lean/Compiler' / path).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)

    inputs = source('Extraction/InternerConstantInputTests.lean')
    inputs += ('\nexample (safety : Bool) (value : Contract.Yul.Word) :\n'
               f'    ({INPUT}call safety value).request.item.data = value := rfl\n')
    # Diagnostic-only opacity keeps a wrong operand from unfolding the whole
    # initialized heap. The unchanged copy must still elaborate first.
    program = source('Extraction/InternerNativeWordConstantTests.lean').replace(
        'theorem program_equivalent',
        'section\nattribute [local irreducible] ConstantTests.children\n\ntheorem program_equivalent').replace(
        'rw [children, materialize_succ]; exact constant_equivalent safety depth value',
        'simpa only [children, materialize_succ, ↓reduceIte] using constant_equivalent safety depth value').replace(
        'theorem program_zero',
        'end\n\ntheorem program_zero')
    return (
        ('allocation', source('ZigAir/MemoryAllocationLaws.lean'), (
            ('invalid-source-heap', '(valid : state.valid = true)', '(valid : state.valid = false)', 1),
            ('shift-reached-counter', 'actual.nextAddress = after.nextAddress', 'actual.nextAddress = after.nextAddress + 1', 1),
        )),
        ('spare', source('Extraction/RepresentativeRegisteredGrowthAppendProofs.lean'), (
            ('admit-address-limit', '(spare : cells.length < capacity) (width : Append.nextLength cells.length < addressLimit) :',
             '(spare : cells.length < capacity) (width : Append.nextLength cells.length ≤ addressLimit) :', 2),
            ('omit-descriptor-execution', 'run runtimeSafety allocate allocator owner cells cell before := by',
             '(.ok true, before) := by', 1),
        )),
        ('input', inputs, (
            ('wrong-word', 'constantRequest value', 'constantRequest (value + 1)', 1),
            ('stale-scratch-lifetime', '⟨(call safety value).before.memory.memory.nextId + 1, 0⟩',
             '⟨(call safety value).before.memory.memory.nextId + 2, 0⟩', 1),
        )),
        ('publication', source('Extraction/InternerConstantPublicationTests.lean'), (
            ('wrong-native-word', '.ok (.ok (some value))', '.ok (.ok (some (value + 1)))', 1),
            ('rewind-created-lifetime', '(initial safety).memory.memory.nextId + 3',
             '(initial safety).memory.memory.nextId + 2', 2),
        )),
        ('cache', source('Extraction/InternerConstantCacheTests.lean'), (
            ('wrong-published-id', '(call safety value).constructed.graph.table (call safety value).key = some 4 := by',
             '(call safety value).constructed.graph.table (call safety value).key = some 5 := by', 1),
            ('retain-local-allocations', '(call safety value).returnedWorld (entered safety value)', '(entered safety value)', 1),
        )),
        ('program', program, (
            ('wrong-materialized-word', '(children safety depth).materialize id value debug',
             '(children safety depth).materialize id (value + 1) debug', 1),
            ('wrong-final-native-word', '.ok (.ok (some value))', '.ok (.ok (some (value + 1)))', 1),
            ('exhaustion-as-oom', '(.error (.language .unsupported), CallerInputTests.world safety)',
             '(.error (.language .outOfMemory), CallerInputTests.world safety)', 1),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    records = []
    for group, text, changes in mutation_cases():
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous constant word mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'constant-word-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'constant-word-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
