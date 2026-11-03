#!/usr/bin/env python3
"""Audit native graph facts from initialization through recursive return.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
import constructor_argument_checks as arguments
import recursive_borrowed_checks as borrowed
import native_recursion_checks as recursive
import check_graph_init as graph

NS = arguments.OWNED + 'NativeGraph.'
TESTS = NS + 'Tests.'
FACTS = arguments.OWNED + 'Insertion.Native.CallerGrowingChainTests.GraphFacts.'
CLAIMS = [NS + name for name in ('Facts.operations', 'Facts.accepted', 'Facts.nonpush', 'Facts.constants',
    'Facts.queried_input', 'initialized', 'Facts.frame', 'Facts.cleanup')]
CLAIMS += [FACTS + name for name in ('native', 'frame', 'cleanup')]
CLAIMS += [TESTS + name for name in ('initialized_from_execution', 'initial_queries',
    'initial_offset_survives', 'recursive_after', 'recursive_queries', 'recursive_borrowed_input',
    'exhaustion_retained')]


def bindings():
    return {'initialization': graph.admission.check(), 'recursiveFamily': recursive.bindings(),
            'scope': 'parameterized native operation-query and ownership facts; empty offset sentinel, '
                     'native Push and non-Push guards, borrowed inputs and actual recursive cleanup',
            'initialOwnerStorageDeclared': True, 'completeNativeGraphInvariantVerified': False}


def audit(claims):
    representative = 'Compiler.Extraction.RepresentativeArray.'
    required = {
        NS + 'Facts.operations': {representative + 'Operation.query', representative + 'Operation.invalid_id'},
        NS + 'Facts.accepted': {NS + 'Facts.operations', arguments.OWNED + 'BorrowedQuery.Native.of_resident'},
        NS + 'Facts.nonpush': {representative + 'Constant.nonpush'},
        NS + 'Facts.constants': {representative + 'Constant.push', representative + 'Constant.invalid_id',
            NS + 'Facts.nonpush', NS + 'Facts.data'},
        NS + 'Facts.queried_input': {NS + 'Facts.operations', arguments.ITEM + 'ViewInput.queried_input'},
        NS + 'initialized': {graph.NS + 'Ownership.initialize_verified', graph.NS + 'Ownership.Established.shape'},
        NS + 'Facts.frame': {representative + 'DescriptorRelation.frame', 'Compiler.Extraction.AssemblyItem.Query.frame', representative + 'Constant.Data.frame'},
        NS + 'Facts.cleanup': {NS + 'Facts.frame', 'Compiler.Extraction.Memory.Arguments.Normalization.Valid.cleanup',
            'Compiler.Extraction.Memory.Arguments.Normalization.persistent_cleanup'},
        FACTS + 'native': {NS + 'Facts'},
        FACTS + 'frame': {NS + 'Facts.frame', NS + 'Facts.accepted', FACTS + 'native'},
        FACTS + 'cleanup': {NS + 'Facts.cleanup', NS + 'Facts.accepted', FACTS + 'native'},
        TESTS + 'initialized_from_execution': {NS + 'initialized', graph.NS + 'Ownership.Tests.source_initializer'},
        TESTS + 'initial_queries': {TESTS + 'initialized_from_execution', NS + 'Facts.operations'},
        TESTS + 'initial_offset_survives': {TESTS + 'initialized_from_execution', NS + 'Facts.cleanup',
            graph.NS + 'Ownership.Tests.allocator_effects_registry_and_parent_retained'},
        TESTS + 'recursive_after': {recursive.TESTS + 'program_contract', FACTS + 'native'},
        TESTS + 'recursive_queries': {TESTS + 'recursive_after', NS + 'Facts.operations'},
        TESTS + 'recursive_borrowed_input': {TESTS + 'recursive_after', NS + 'Facts.queried_input'},
        TESTS + 'exhaustion_retained': {recursive.TESTS + 'incomplete_retains_parent', FACTS + 'native'},
        borrowed.TESTS + 'xor_query_at': {NS + 'Facts.operations', FACTS + 'native'},
        borrowed.TESTS + 'xor_input_at': {NS + 'Facts.queried_input', FACTS + 'native'},
        borrowed.TESTS + 'constant_nonpush': {NS + 'Facts.nonpush', FACTS + 'native'},
        borrowed.TESTS + 'parent_iszero': {NS + 'Facts.operations', FACTS + 'native'},
        borrowed.TESTS + 'xor_native_reads': {NS + 'Facts.operations', NS + 'Facts.nonpush'},
    }
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError('native graph derivation lost dependencies: ' + name + ': ' + ', '.join(sorted(missing)))
    if FACTS + 'accepted' in claims[FACTS + 'native']:
        raise ValueError('native graph projection assumes the fixture cached query agreement')
    return {'checkedDependencies': sorted(required), 'sourceBinding': bindings(),
            'nativeOperationAgreementDerivedFromFields': True, 'nonpushGuardsDerivedFromFields': True,
            'initializedEmptyOffsetSentinelVerified': True, 'genericCleanupUsedByRecursiveProgram': True,
            'pushScalarDataCorrespondenceVerified': True, 'completePayloadCorrespondenceVerified': False,
            'nativeMapAndAllocatorBindingVerified': False, 'fullConstructorReachabilityFromInitializationVerified': False,
            'recursiveInductionVerified': False, 'composedProductionTheoremVerified': False}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / name).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)

    return (
        ('fields', source('InternerNativeGraph.lean'), (
            ('missing-push-data', 'data : ∀ logical ∈ rows, Constant.Data world.memory.memory logical',
             'data : ∀ logical ∈ rows, logical.item.kind = 2#32 → True', 1),
            ('wrong-constant-id', 'id =\n      .ok (Storage.constantProgram.run rows id)',
             '(id + 1) =\n      .ok (Storage.constantProgram.run rows id)', 1),
            ('missing-bounds', 'bounded : rows.length ≤ capacity', 'bounded : True', 1),
            ('missing-item-reads', 'native.type = AssemblyItem.viewType ∧ Operation.Item world.memory.memory logical',
             'native.type = AssemblyItem.viewType ∧ True', 1),
            ('missing-residency', 'resident : Memory.GraphResident allocator world.memory.heap rows', 'resident : True', 1),
            ('missing-key-separation', 'apart : OwnedKeys.Apart world.memory.effects.keys\n    (fun address => ∃ logical ∈ rows, logical.arguments ≠ [] ∧ address = logical.argumentsAddress)',
             'apart : True', 1),
        )),
        ('frame', source('InternerNativeGraphFrame.lean'), (
            ('wrong-owner', 'id = owner ∨', 'id = owner + 1 ∨', 1),
            ('erase-parent', 'Compiler.ZigAir.Memory.cleanup mark world.memory.memory',
             'Compiler.ZigAir.Memory.cleanup 0 world.memory.memory', 2),
        )),
        ('composed', source('InternerNativeGraphTests.lean'), (
            ('lost-sentinel-offset', 'Facts safety 7 3 sentinel 0 (owned safety) []',
             'Facts safety 7 3 ⟨sentinel.allocation, 0⟩ 0 (owned safety) []', 1),
            ('invent-sentinel-storage', '.memory.memory.heap.lookup sentinel.allocation = none ∧',
             '.memory.memory.heap.lookup sentinel.allocation ≠ none ∧', 1),
            ('wrong-recursive-opcode', 'id opcode =\n      .ok (((Interner.representativeReads',
             'id (opcode + 1) =\n      .ok (((Interner.representativeReads', 1),
            ('alias-next-input', '(view slice).allocation ≠ old.address :=', '(view slice).allocation = old.address :=', 1),
            ('exhaustion-ordinary', 'ordinary (program safety 1).1 = false ∧', 'ordinary (program safety 1).1 = true ∧', 1),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    records = []
    for group, text, changes in mutation_cases():
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous native graph mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'native-graph-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'native-graph-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
