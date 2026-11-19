#!/usr/bin/env python3
"""Audit complete caller routing into checked native growth and frame return.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

OWNED = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.'
NATIVE = OWNED + 'Insertion.Native.'
CHAIN = NATIVE + 'CallerGrowingChainTests.'
TESTS = CHAIN + 'RoutingTests.'
CLAIMS = [OWNED + 'Caller.find_after_take', OWNED + 'Caller.find_cached', NATIVE + 'find_after_simplify',
          NATIVE + 'CallerInput.find_after_simplify', CHAIN + 'GraphFacts.cleanup']
CLAIMS += [TESTS + name for name in ('made', 'missed', 'entry', 'room', 'classified', 'first_nonconstant', 'simplified',
          'native_contract', 'native_insert', 'full_result', 'full_contract', 'cached_entry', 'cached_result', 'rejected_result')]


def audit(claims):
    required = {
        OWNED + 'Caller.find_after_take': {'Compiler.Extraction.Interner.FindCode.controlRun',
            'Compiler.Extraction.Interner.FindCode.controlOwned', OWNED + 'Caller.initLookup', OWNED + 'take'},
        OWNED + 'Caller.find_cached': {'Compiler.Extraction.Interner.FindCode.controlRun', OWNED + 'finish'},
        NATIVE + 'find_after_simplify': {OWNED + 'Caller.find_after_take', NATIVE + 'callerPrimitives',
            NATIVE + 'finishInsertion', OWNED + 'graph'},
        NATIVE + 'CallerInput.find_after_simplify': {NATIVE + 'find_after_simplify', OWNED + 'ConstructorFrame.find',
            'Compiler.ZigAir.Memory.cleanup'},
        TESTS + 'entry': {NATIVE + 'caller_input', CHAIN + 'initialized_prefix', CHAIN + 'prefix_results', TESTS + 'missed'},
        TESTS + 'room': {'Compiler.Extraction.Interner.Queries.capacity_exact', CHAIN + 'initialized_prefix'},
        TESTS + 'classified': {'Compiler.Extraction.Interner.Queries.queries'},
        TESTS + 'first_nonconstant': {TESTS + 'entry', CHAIN + 'initialized_prefix', 'Compiler.Extraction.Storage.ConstantRead.run'},
        TESTS + 'simplified': {TESTS + 'first_nonconstant', 'Compiler.Extraction.Dispatch.simplify',
            'Compiler.Extraction.Dispatch.collectConstants', OWNED + 'Recursive.callbacks'},
        TESTS + 'native_contract': {TESTS + 'entry', NATIVE + 'CallerInput.growing_success', CHAIN + 'backing_fits'},
        CHAIN + 'GraphFacts.cleanup': {'Compiler.Extraction.Memory.Arguments.Normalization.Valid.cleanup',
            'Compiler.Extraction.Memory.Arguments.Normalization.persistent_cleanup',
            'Compiler.ZigAir.Memory.cleanup_lookup_older', OWNED + 'BorrowedQuery.Native.of_resident'},
        TESTS + 'native_insert': {NATIVE + 'CallerInput.checked_execution', NATIVE + 'insert', TESTS + 'entry'},
        TESTS + 'full_result': {NATIVE + 'CallerInput.find_after_simplify', NATIVE + 'CallerInput.finish_native',
            TESTS + 'native_insert', TESTS + 'simplified', TESTS + 'missed'},
        TESTS + 'full_contract': {TESTS + 'native_contract', TESTS + 'full_result', CHAIN + 'GraphFacts.cleanup',
            CHAIN + 'CustodyTests.parent_custody', OWNED + 'Caller.Custody.good'},
        TESTS + 'cached_result': {OWNED + 'Caller.find_cached', OWNED + 'deinit_detached', OWNED + 'Caller.initialize_graph',
            TESTS + 'cached_entry'},
        TESTS + 'rejected_result': {NATIVE + 'CallerInput.find_after_simplify', NATIVE + 'CallerInput.rejected_completed',
            CHAIN + 'CompletionTests.missing_owner', TESTS + 'simplified'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('native caller routing lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required),
            'scope': 'complete modeled find cache miss, actual dispatcher no-match, checked native relocation and frame return',
            'reachedSimplifierWorldForwarded': True, 'finalGoodOrGraphEqualityPremise': False,
            'cacheMissDerivedFromInitializedPrefix': True, 'dispatcherNoMatchForArbitraryRecursiveCallback': True,
            'nativeGraphAndParentCustodyAfterFrameReturnDerived': True,
            'cachedRequestDoesNotReachInsertion': True, 'rejectionRetainsReachedOwnersAndFrame': True,
            'initialPrefixIsSelectedInsertionContinuations': True, 'generalNestedRecursiveExecutionVerified': False,
            'nativeMapAndAllocatorBindingVerified': False, 'constantReadNativeAccessorComplete': False,
            'sourceArgumentItemClosureComplete': False, 'wordSemanticsCertificate': False,
            'completePublicationRollbackVerified': False, 'composedProductionTheoremVerified': False}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / name).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\nset_option pp.notation false\n' + without_imports(raw)
    return (
        ('routing', source('InternerCallerNativeRouting.lean'), (
            ('lose-take-state', 'request key deterministic taken', 'request key deterministic prepared', 1),
            ('cache-hit-is-oom', 'finish external allocator (.ok id) prepared',
             'finish external allocator (.error (.language .outOfMemory)) prepared', 1),
            ('rewind-simplifier-world', '⟨reached, taken.scope⟩ growth', 'taken growth', 2),
            ('wrong-native-determinism', 'input key slice deterministic growth }', 'input key slice false growth }', 1),
            ('erase-parent-stack', 'memory := Compiler.ZigAir.Memory.cleanup before.memory.memory.nextId ran.2.world.memory.memory',
             'memory := Compiler.ZigAir.Memory.cleanup 0 ran.2.world.memory.memory', 1),
            ('unwind-rejection', 'if ordinary ran.1 then', 'if !ordinary ran.1 then', 1),
        )),
        ('setup', source('InternerCallerNativeRoutingSetupTests.lean'), (
            ('cached-key-as-miss', 'sequence := 0', 'sequence := 77', 2),
            ('wrong-classification', 'queries.deterministic (request empty).item = .ok true',
             'queries.deterministic (request empty).item = .ok false', 1),
            ('invent-constant', ').constant 0 = .ok none', ').constant 0 = .ok (some 0)', 1),
        )),
        ('return', source('InternerCallerNativeRoutingReturnTests.lean'), (
            ('skip-stack-return', 'memory := Compiler.ZigAir.Memory.cleanup (before safety empty 4).memory.memory.nextId (memory after).memory',
             'memory := (memory after).memory', 1),
            ('wrong-result', '(.ok 5,', '(.ok 6,', 3),
            ('invent-parent-words', 'Good (parent empty) (values empty)', 'Good (parent empty) [1]', 1),
            ('rewind-history', '.world.memory.memory.nextId = grownLifetime empty + 1',
             '.world.memory.memory.nextId = grownLifetime empty', 1),
        )),
        ('boundaries', source('InternerCallerNativeRoutingTests.lean'), (
            ('cache-hit-grows', '(cached safety empty find).1 = .ok 4', '(cached safety empty find).1 = .ok 5', 1),
            ('rejection-as-oom', '(.error (.language .safetyFault),', '(.error (.language .outOfMemory),', 1),
            ('drop-rejected-lookup', '⟨some (lookup empty), some (normalized safety empty 4), true⟩',
             '⟨none, some (normalized safety empty 4), true⟩', 1),
            ('rejection-is-ordinary', 'ordinary (rejected safety empty find).1 = false',
             'ordinary (rejected safety empty find).1 = true', 1),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    records = []
    for group, text, changes in mutation_cases():
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous native routing mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'native-routing-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'native-routing-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
