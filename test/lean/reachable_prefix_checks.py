#!/usr/bin/env python3
"""Audit initialization through the actual recursive constructor prefixes.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import re

from build_toolchain import digest
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
import constructor_argument_checks as arguments
import native_recursion_checks as recursion
import check_representative_release as release

NS = arguments.ITEM + 'ReachablePrefixTests.'
CALL = arguments.ITEM + 'RecursiveTests.Call.'
NATIVE = arguments.OWNED + 'Insertion.Native.'
RELOCATION = 'Compiler.Extraction.RepresentativeArray.Backing.Relocation.'
CLAIMS = [NS + name for name in ('initial', 'observed', 'classified', 'count', 'simplified',
    'routed', 'invoked', 'first_entry', 'first_allocation', 'first_publication', 'first', 'next',
    'initialized_prefix', 'entered', 'step_result')]
CLAIMS += [CALL + 'entry', CALL + 'returned_cell', CALL + 'publication_return', NATIVE + 'CallerInput.first_success']
CLAIMS += [recursion.TESTS + name for name in ('same_call', 'miss_continuation', 'prefix_insertion', 'prefix_equivalent', 'prefix_result', 'program_zero')]
CLAIMS += [arguments.ITEM + 'NativeLocal.Tests.program_zero', RELOCATION + 'empty_source']
CLAIMS += [RELOCATION + 'Tests.' + name for name in ('empty_sentinel_publication', 'empty_sentinel_observations',
    'nonempty_interior_source_rejects', 'empty_interior_target_rejects')]


def bindings():
    source = ROOT / 'src/libevmasm/instruction.zig'
    text = source.read_text()
    values = {'ADDRESS': 0x30, 'ORIGIN': 0x32, 'CALLER': 0x33, 'CALLVALUE': 0x34}
    for name, value in values.items():
        matches = re.findall(r'^\s*' + name + r'\s*=\s*(0x[0-9a-fA-F]+),\s*$', text, re.M)
        if len(matches) != 1 or int(matches[0], 16) != value:
            raise ValueError('changed reachable-prefix opcode: ' + name)
    return {'instructionSourceSha256': digest(source), 'opcodes': values,
            'constructors': arguments.bindings(),
            'scope': 'four distinct empty-operand operation constructors from native initialization, '
                     'then AND/named-local, XOR/borrowed, constant failure or recursive growth '
                     'and either parent-publication outcome in the same context',
            'constantAndGrowthPrefixesStillSelected': False,
            'environmentWordSemanticsVerified': False, 'completeNativeGraphInvariantVerified': False,
            'recursiveInductionVerified': False}


def audit(claims):
    required = {
        NS + 'initial': {arguments.OWNED + 'NativeGraph.initialized', NATIVE + 'CallerInputTests.initializer'},
        CALL + 'entry': {arguments.ITEM + 'caller_input', arguments.ITEM + 'prepare_success'},
        CALL + 'returned_cell': {'Compiler.ZigAir.Memory.valid_lookup',
            'Compiler.ZigAir.Memory.cleanup_lookup_older'},
        CALL + 'returned_frame': {arguments.ITEM + 'returnWorld_frame'},
        CALL + 'publication_return': {NATIVE + 'CallerInput.finish_native',
            NATIVE + 'CallerGrowingChainTests.GraphFacts.cleanup', CALL + 'returned_cell'},
        NS + 'first_entry': {NS + 'initial', CALL + 'entry'},
        NATIVE + 'CallerInput.first_success': {NATIVE + 'prepared_publication_cell'},
        NS + 'first_publication': {NS + 'first_entry', NS + 'first_allocation',
            NATIVE + 'CallerInput.first_success', NATIVE + 'CallerInput.checked_execution'},
        NS + 'first': {NS + 'first_publication', CALL + 'publication_return', NS + 'invoked'},
        NS + 'next': {CALL + 'spare_publication', CALL + 'establish', NS + 'routed'},
        NS + 'initialized_prefix': {NS + 'first', NS + 'next'},
        NS + 'entered': {NS + 'initialized_prefix', NS + 'first_entry'},
        NS + 'step_result': {NS + 'initialized_prefix'},
        recursion.TESTS + 'same_call': {CALL + 'route'},
        recursion.TESTS + 'miss_continuation': {CALL + 'continuation', arguments.OWNED + 'Caller.execution'},
        recursion.TESTS + 'prefix_equivalent': {NS + 'entered', NS + 'simplified',
            recursion.TESTS + 'prefix_insertion', recursion.NS + 'operation_succ'},
        recursion.TESTS + 'prefix_result': {recursion.TESTS + 'prefix_equivalent', NS + 'step_result'},
        recursion.TESTS + 'program_equivalent': {recursion.TESTS + 'prefix_result'},
        arguments.ITEM + 'NativeLocal.Tests.program_equivalent': {recursion.TESTS + 'prefix_result'},
        arguments.ITEM + 'NativeRecursion.ConstantTests.program_equivalent': {arguments.ITEM + 'NativeRecursion.ConstantTests.prefix_result'},
        arguments.ITEM + 'RecursiveGrowthTests.program_equivalent': {arguments.ITEM + 'RecursiveGrowthTests.prefix_result'},
        arguments.ITEM + 'RecursiveGrowthTests.program_failed_equivalent': {arguments.ITEM + 'RecursiveGrowthTests.prefix_result'},
        RELOCATION + 'Tests.empty_sentinel_publication': {RELOCATION + 'empty_source'},
    }
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError('initialized recursive prefix lost dependencies: ' + name + ': ' + ', '.join(sorted(missing)))
    return {'checkedDependencies': sorted(required), 'sourceBinding': bindings(),
            'initialGraphDerivedFromNativeInitializer': True, 'fullConstructorsProducePrefix': True,
            'sameContextThroughParentAndChild': True, 'firstGrowthAcceptsEmptyInteriorSentinel': True,
            'callerAllocationFrameCarriedThroughPrefixAndReturns': True,
            'nonemptyInteriorSourceAndInteriorTargetRejected': True,
            'completeConstructorReachabilityVerified': False, 'composedProductionTheoremVerified': False}


def mutation_cases():
    raw = (ROOT / 'lean/Compiler/Extraction/InternerReachablePrefixSetupTests.lean').read_text()
    imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
    source = imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)
    frames = '''import Compiler.Extraction.InternerLiteralInputTests
set_option pp.maxSteps 8
set_option pp.deepTerms false
namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem
open Insertion Insertion.Native RecursiveTests
attribute [local irreducible] RecursiveNonemptyTests.ready
example (call : Call) (world : World (Publication.Effects Nat)) (valid : Valid call.before.memory)
    (id : Nat) (native : Compiler.ZigAir.Memory.Allocation)
    (found : call.before.memory.memory.heap.lookup id = some native)
    (kept : world.memory.memory.heap.lookup id = some native) :
    (call.returnedWorld world).memory.memory.heap.lookup id = some native :=
  call.returned_cell world valid id native found kept
example (safety : Bool) (n : Nat) (bounded : n < 4) (id : Nat)
    (native : Compiler.ZigAir.Memory.Allocation)
    (found : (CallerInputTests.world safety).memory.memory.heap.lookup id = some native)
    (prefixOwnerApart : id ≠ 6) (prefixBackingApart : id ≠ ReachablePrefixTests.backing) :
    (ReachablePrefixTests.before safety n).memory.memory.heap.lookup id = some native :=
  (ReachablePrefixTests.initialized_prefix safety n bounded).frame id native found prefixOwnerApart prefixBackingApart
example (safety : Bool) (id : Nat) (native : Compiler.ZigAir.Memory.Allocation)
    (found : (RecursiveNonemptyTests.initial safety).memory.memory.heap.lookup id = some native)
    (constantOwnerApart : id ≠ 6) (constantBackingApart : id ≠ ReachablePrefixTests.backing) :
    (RecursiveNonemptyTests.ready safety).memory.memory.heap.lookup id = some native :=
  (RecursiveNonemptyTests.zero_contract safety).2.2.2.2 id native found constantOwnerApart constantBackingApart
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem
'''
    return (('setup', source, (
        ('duplicate-key', '| 1 => 50', '| 1 => 48', 1),
        ('wrong-first-extent', 'bytes == 160', 'bytes == 161', 1),
        ('wrong-initial-owner', 'NativeGraph.Facts safety 7 6 CallerInputTests.sentinel',
         'NativeGraph.Facts safety 7 7 CallerInputTests.sentinel', 1),
    )), ('frames', frames, (
        ('return-cleans-live-cell', '(call.returnedWorld world).memory.memory.heap.lookup id',
         '(Compiler.ZigAir.Memory.cleanup id (call.returnedWorld world).memory.memory).heap.lookup id', 1),
        ('return-omits-reached-cell', '(kept : world.memory.memory.heap.lookup id',
         '(kept : call.before.memory.memory.heap.lookup id', 1),
        ('prefix-retains-mutated-owner', '(prefixOwnerApart : id ≠ 6)', '(prefixOwnerApart : id ≠ 7)', 1),
        ('prefix-retains-mutated-backing', '(prefixBackingApart : id ≠ ReachablePrefixTests.backing)',
         '(prefixBackingApart : id ≠ ReachablePrefixTests.backing + 1)', 1),
        ('constant-retains-mutated-backing', '(constantBackingApart : id ≠ ReachablePrefixTests.backing)',
         '(constantBackingApart : id ≠ ReachablePrefixTests.backing + 1)', 1),
        ('constant-wrong-target', '(RecursiveNonemptyTests.ready safety).memory.memory.heap.lookup id',
         '(RecursiveNonemptyTests.ready safety).memory.memory.heap.lookup (id + 1)', 1),
    )))


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    records = []
    for group, text, changes in mutation_cases():
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous reachable-prefix mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'reachable-prefix-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'reachable-prefix-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    records += checked_controls(output, release.controls(output, env, lean, names={
        'relocate-reject-empty-offset', 'relocate-ignore-source-offset', 'relocate-ignore-offset'}))
    return records
