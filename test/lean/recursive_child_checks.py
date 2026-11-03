#!/usr/bin/env python3
"""Check actual recursive constant-child growth OOM and parent cleanup.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
from build_toolchain import digest
import constructor_item_checks
import extract_storage
from extract_compiler import Unsupported
from extract_storage import function

OWNED = constructor_item_checks.OWNED
ITEM = constructor_item_checks.ITEM
TESTS = ITEM + 'RecursiveTests.'
NATIVE = OWNED + 'Insertion.Native.'
CONSTANT = 'Compiler.Extraction.RepresentativeArray.Constant.'
CLAIMS = [CONSTANT + name for name in ('read_nonpush', 'value_of_miss', 'invalid_id', 'nonpush')]
CLAIMS += [TESTS + name for name in ('Call.prefix_results', 'observed', 'root_observed', 'root_literal', 'root_facts',
    'Call.establish', 'parent_established', 'child_good', 'child_established', 'preparation_observed',
    'preparation_results', 'initial_reads', 'root_graph', 'child_reads', 'child_allocation', 'child_insert',
    'Call.route', 'Call.simplify_error', 'Call.simplifier_oom', 'Call.returned_valid', 'Call.returned_frame', 'child_result', 'child_contract',
    'child_constant_forwarded', 'parent_constant', 'equal_failure', 'parent_simplified', 'parent_continuation', 'held_after_child',
    'cleanup_missing', 'full_contract', 'prior_words', 'complete_route', 'complete_contract')]


def bindings():
    source = extract_storage.SOURCE.read_bytes()

    def checked(data):
        function(data, 'pub fn knownConstant(self: *const ExpressionClasses, id: Id) ?*const u256').expect(
            '{ const expression = self.representative(id) catch return null; '
            'if (expression.item.item_type != .Push) return null; return &expression.item.data_value; }')
        function(data, 'pub fn knownConstantValue(self: *const ExpressionClasses, id: Id) ?u256').expect(
            '{ const value = self.knownConstant(id) orelse return null; return value.*; }')
        if extract_storage.extract(data) != extract_storage.OUTPUT.read_bytes():
            raise ValueError('constant/storage source profile is stale')

    checked(source)
    controls = []
    for name, before, after in (
        ('wrong-tag', b'if (expression.item.item_type != .Push)', b'if (expression.item.item_type == .Push)'),
        ('wrong-field', b'return &expression.item.data_value;', b'return &expression.item.instruction_value;'),
        ('skip-load', b'return value.*;', b'return 0;'),
    ):
        if source.count(before) != 1:
            raise ValueError('ambiguous native constant source control: ' + name)
        try:
            checked(source.replace(before, after))
        except Unsupported as error:
            controls.append({'name': name, 'admitted': False, 'reason': str(error)})
        else:
            raise ValueError('unmodeled constant source was admitted: ' + name)
    return {'sourceSha256': digest(extract_storage.SOURCE), 'storageProfileSha256': digest(extract_storage.OUTPUT),
            'constructor': constructor_item_checks.bindings(), 'controls': controls,
            'scope': 'native non-Push constant misses used by EQ(x,x); complete Push correspondence remains open'}


def audit(claims):
    required = {
        CONSTANT + 'nonpush': {'Compiler.Extraction.RepresentativeArray.representative_from_array', CONSTANT + 'read_nonpush'},
        TESTS + 'Call.establish': {ITEM + 'caller_input', ITEM + 'prepare_success', NATIVE + 'CallerGrowingChainTests.GraphFacts.frame'},
        TESTS + 'initial_reads': {ITEM + 'RecursiveNonemptyTests.zero_contract'},
        TESTS + 'root_literal': {ITEM + 'RecursiveNonemptyTests.literal_facts', ITEM + 'RecursiveNonemptyTests.zero_contract'},
        TESTS + 'root_facts': {TESTS + 'root_literal', ITEM + 'RecursiveNonemptyTests.caller_source', ITEM + 'good_frame'},
        TESTS + 'child_established': {TESTS + 'parent_established', TESTS + 'Call.establish'},
        TESTS + 'child_allocation': {NATIVE + 'CallerInput.growing_allocation_oom', TESTS + 'child_established', TESTS + 'preparation_results'},
        TESTS + 'child_insert': {NATIVE + 'CallerInput.checked_execution', NATIVE + 'projected_unchanged', TESTS + 'child_reads'},
        TESTS + 'Call.route': {ITEM + 'invoke_prepared', OWNED + 'Caller.find_after_take', OWNED + 'ConstructorFrame.find'},
        TESTS + 'child_result': {TESTS + 'Call.route', NATIVE + 'CallerInput.finish_native', TESTS + 'child_insert'},
        TESTS + 'child_contract': {TESTS + 'child_allocation', TESTS + 'child_result', TESTS + 'Call.returned_frame'},
        TESTS + 'parent_constant': {CONSTANT + 'nonpush', TESTS + 'parent_established'},
        TESTS + 'child_constant_forwarded': {TESTS + 'childConstructors', ITEM + 'constant'},
        TESTS + 'equal_failure': {'Compiler.Extraction.Dispatch.simplifyWithInputs', 'Compiler.Extraction.Dispatch.binaryStageWithInputs'},
        TESTS + 'parent_simplified': {TESTS + 'equal_failure', TESTS + 'parent_constant', TESTS + 'childFull'},
        TESTS + 'Call.simplifier_oom': {OWNED + 'Caller.Origin.release_frame', TESTS + 'Call.route', OWNED + 'finish_taken'},
        TESTS + 'Call.simplify_error': {'Compiler.Extraction.Interner.FindCode.controlMiss', OWNED + 'Caller.execution'},
        TESTS + 'parent_continuation': {TESTS + 'parent_simplified', TESTS + 'Call.simplify_error'},
        TESTS + 'full_contract': {TESTS + 'child_contract', TESTS + 'parent_simplified', TESTS + 'Call.simplifier_oom',
            TESTS + 'Call.route', OWNED + 'finish_taken', OWNED.removesuffix('OwnedCall.') + 'free_valid',
            TESTS + 'Call.returned_frame', TESTS + 'Call.cleanup_missing'},
        TESTS + 'prior_words': {TESTS + 'full_contract'},
        TESTS + 'complete_route': {ITEM + 'Arguments.operation_prepared', ITEM + 'Arguments.returned_nonempty'},
        TESTS + 'complete_contract': {TESTS + 'full_contract', TESTS + 'complete_route', TESTS + 'root_literal',
            NATIVE + 'CallerGrowingChainTests.GraphFacts.cleanup', ITEM + 'Arguments.Prepared.retire',
            ITEM + 'RecursiveNonemptyTests.caller_source'},
    }
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError('recursive child connection lost dependencies: ' + name + ': ' + ', '.join(sorted(missing)))
    return {'checkedDependencies': sorted(required), 'sourceBinding': bindings(),
            'actualConstantChildThroughNonemptyGrowthAllocationFailure': True,
            'parentOwnershipAndOuterCleanupDerivedFromSameExecution': True,
            'allOlderNativeAllocationsAndRegisteredOwnersPreservedAcrossChild': True,
            'initialPrefixIsSelectedInsertionContinuations': False,
            'equalOperandsStartsFromFullNativePrefixAndPush': True,
            'outerLiteralRetiredAndOriginalCallerArrayRetained': True,
            'nativeConstantCorrespondenceScope': 'non-Push representative queried by this path',
            'completeConstructorDependencyClosureVerified': False, 'successfulRecursiveGrowthVerified': False,
            'nativeMapAndAllocatorBindingVerified': False, 'debugDescriptorPointeeLifetimeVerified': False,
            'completePublicationRollbackVerified': False, 'recursiveInductionVerified': False,
            'composedProductionTheoremVerified': False}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / name).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)

    # A wrong callback must fail at its generic forwarding boundary. Retain the
    # complete recursive proof in unchanged build/export/replay; reducing its
    # entire concrete world after a deliberately wrong argument is diagnostic
    # noise, not a useful rejection control.
    dispatch = source('InternerRecursiveChildDispatchTests.lean')
    boundary = '/-- The only queried representative'
    if dispatch.count(boundary) != 1 or dispatch.count('theorem parent_simplified') != 1:
        raise ValueError('ambiguous recursive child control boundary')
    callbacks = dispatch.split(boundary)[0] + '\nend ' + TESTS[:-1] + '\n'
    ordered = dispatch.split('theorem parent_simplified')[0] + '\nend ' + TESTS[:-1] + '\n'
    return (
        ('constant', source('RepresentativeConstant.lean'), (
            ('wrong-tag', 'if kind ≠ 2 then return none', 'if kind ≠ 1 then return none', 1),
            ('invent-value', '| .ok none => return .ok none', '| .ok none => return .ok (some 0)', 1),
        )),
        ('return', source('InternerRecursiveCallReturnTests.lean'), (
            # The generic return proof owns cleanup now; retain this control
            # at the fixture's application so a wrong parent mark still fails.
            ('erase-parent', 'returnWorld call.before.memory.memory.nextId (call.before.memory.memory.nextId + 1) world',
             'returnWorld 0 (call.before.memory.memory.nextId + 1) world', 1),
            ('discard-error-world', 'call.continuation p = (.error fault, ⟨world, call.taken.2.scope⟩)',
             'call.continuation p = (.error fault, call.taken.2)', 1),
        )),
        ('callbacks', callbacks, (
            ('skip-child', '\n    (ran.1, ran.2.world)', '\n    (.error (.language .outOfMemory), before)', 2),
            ('discard-debug', 'Interner.Queries.queries value metadata before\n    (ran.1, ran.2.world)',
             'Interner.Queries.queries value AssemblyItem.Initializers.Tests.invalidDebug before\n    (ran.1, ran.2.world)', 1),
            ('wrong-child', 'Interner.Queries.queries value metadata before\n    (ran.1, ran.2.world)',
             'Interner.Queries.queries 0 metadata before\n    (ran.1, ran.2.world)', 1),
        )),
        ('ordered', ordered, (
            ('wrong-equal-child', '(called : constructors.constant 1 metadata before',
             '(called : constructors.constant 0 metadata before', 1),
        )),
        ('postconditions', source('InternerRecursiveChildTests.lean'), (
            ('wrong-parent-result', 'full safety = (.error (.language .outOfMemory), (parent safety).returned cleaned)',
             'full safety = (.error (.language .capacity), (parent safety).returned cleaned)', 2),
            ('double-parent-free', '.memory.effects.allocator + 102', '.memory.effects.allocator + 204', 1),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    records = []
    for group, text, changes in mutation_cases():
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous recursive child mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'recursive-child-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'recursive-child-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
