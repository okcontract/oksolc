#!/usr/bin/env python3
"""Bind constructor-local item storage to the actual caller and native insertion.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
from build_toolchain import digest
import extract_constructor
from extract_compiler import Unsupported
from extract_storage import function

OWNED = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.'
ITEM = OWNED + 'ConstructorItem.'
TESTS = ITEM + 'Tests.'
MEMORY = 'Compiler.ZigAir.Memory.'
CLAIMS = [MEMORY + 'lookup_of_mem_valid', MEMORY + 'cleanup_lookup_stack']
CLAIMS += [ITEM + name for name in ('input_fields', 'prepare_of_calls', 'represented_of_reads',
    'prepare_verified', 'prepare_success', 'good_frame', 'invoke_prepared', 'invoke_rejected', 'caller_input')]
CLAIMS += [TESTS + name for name in ('observed', 'prefix_results', 'made_key', 'construction', 'entry',
    'constructed_graph', 'preparation_observed', 'preparation_results', 'ready_valid', 'backing_fits',
    'keys_absent', 'native_contract', 'simplified', 'native_insert', 'callee_result', 'full_result', 'full_contract',
    'operation_fields', 'constant_fields', 'materialize_forwarded', 'preparation_rejections', 'rejected_before_call',
    'missing_owner', 'rejection_retains_frames')]


def bindings():
    source, items, opcodes = (p.read_bytes() for p in
        (extract_constructor.SOURCE, extract_constructor.ITEMS, extract_constructor.OPCODES))

    def checked(data):
        emitted = extract_constructor.extract(data, items, opcodes)
        function(data, 'pub fn materializeConstant(self: *ExpressionClasses, _: Id, value: u256, debug_data: DebugData,) ExpressionError!Id').expect(
            '{ return self.makeConstant(value, debug_data); }')
        return emitted

    if checked(source) != extract_constructor.OUTPUT.read_bytes():
        raise ValueError('constructor request extraction is stale')
    controls = []
    for name, before, after in (
        ('wrong-item-pointer', b'return self.findDefault(&item, arguments);', b'return self.findDefault(undefined, arguments);'),
        ('discard-debug', b'AssemblyItem.initInstruction(instruction, debug_data)', b'AssemblyItem.initInstruction(instruction, .{})'),
        ('shift-arguments', b'return self.findDefault(&item, arguments);', b'return self.findDefault(&item, arguments[1..]);'),
        ('reuse-materialized-id', b'return self.makeConstant(value, debug_data);', b'return 0;'),
    ):
        if source.count(before) != 1:
            raise ValueError('ambiguous constructor item source control: ' + name)
        try:
            checked(source.replace(before, after))
        except Unsupported as error:
            controls.append({'name': name, 'admitted': False, 'reason': str(error)})
        else:
            raise ValueError('unmodeled constructor item source was admitted: ' + name)
    return {'sourceSha256': digest(extract_constructor.SOURCE), 'itemsSha256': digest(extract_constructor.ITEMS),
            'programSha256': digest(extract_constructor.OUTPUT), 'controls': controls,
            'scope': 'makeOperation/makeConstant local initialization, exact item pointer and argument forwarding; materializeConstant delegation',
            'debugDescriptorPointeeLifetimeVerified': False}


def audit(claims):
    native = OWNED + 'Insertion.Native.'
    required = {
        MEMORY + 'cleanup_lookup_stack': {MEMORY + 'lookup_of_mem_valid', MEMORY + 'cleanup'},
        ITEM + 'input_fields': {'Compiler.Extraction.AssemblyItem.Initializers.construct'},
        ITEM + 'prepare_verified': {ITEM + 'prepare_of_calls', ITEM + 'represented_of_reads',
            'Compiler.Extraction.AssemblyItem.Fields.assign_total',
            'Compiler.Extraction.AssemblyItem.Initializers.construct_typed',
            'Compiler.Extraction.Memory.Arguments.Normalization.Valid.private_memory_frame'},
        ITEM + 'prepare_success': {ITEM + 'prepare_verified', ITEM + 'prepare'},
        ITEM + 'caller_input': {ITEM + 'prepare_success', ITEM + 'good_frame', native + 'caller_input'},
        ITEM + 'invoke_prepared': {ITEM + 'invoke', OWNED + 'ConstructorFrame.find', MEMORY + 'cleanup'},
        ITEM + 'invoke_rejected': {ITEM + 'invoke', ITEM + 'prepare'},
        TESTS + 'construction': {ITEM + 'prepare_success', TESTS + 'prefix_results'},
        TESTS + 'entry': {ITEM + 'caller_input', TESTS + 'prefix_results', native + 'CallerGrowingChainTests.initialized_prefix'},
        TESTS + 'constructed_graph': {TESTS + 'construction', native + 'CallerGrowingChainTests.GraphFacts.frame'},
        TESTS + 'ready_valid': {native + 'CallerInput.prepare', TESTS + 'entry', TESTS + 'preparation_results'},
        TESTS + 'native_contract': {native + 'CallerInput.growing_success', TESTS + 'entry', TESTS + 'backing_fits'},
        TESTS + 'simplified': {OWNED + 'Recursive.callbacks', 'Compiler.Extraction.Dispatch.simplify', TESTS + 'construction'},
        TESTS + 'native_insert': {native + 'CallerInput.checked_execution', native + 'insert', TESTS + 'entry'},
        TESTS + 'callee_result': {native + 'CallerInput.find_after_simplify', native + 'CallerInput.finish_native', TESTS + 'native_insert'},
        TESTS + 'full_result': {ITEM + 'invoke_prepared', TESTS + 'callee_result'},
        TESTS + 'full_contract': {TESTS + 'native_contract', TESTS + 'full_result', MEMORY + 'cleanup_lookup_stack',
            native + 'CallerGrowingChainTests.GraphFacts.cleanup'},
        TESTS + 'rejected_before_call': {ITEM + 'invoke_rejected', TESTS + 'preparation_rejections'},
        TESTS + 'rejection_retains_frames': {ITEM + 'invoke_prepared', native + 'CallerInput.find_after_simplify',
            native + 'CallerInput.rejected_completed', TESTS + 'missing_owner', TESTS + 'simplified'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('constructor item connection lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'sourceBinding': bindings(),
            'nativeItemReadsDerivedFromActualConstructorLocal': True,
            'normalizationAndInsertionEntryDerivedFromSameExecution': True,
            'completeCloneMembersRetainedThroughGrowthAndReturn': True,
            'constructorLocalRetirementUsesValidLifetimeIdentity': True,
            'initializationFailuresDoNotEnterCaller': True, 'nativeRejectionRetainsConstructorAndCalleeFrames': True,
            'initialPrefixIsSelectedInsertionContinuations': True,
            'generalNestedRecursiveExecutionVerified': False, 'debugDescriptorPointeeLifetimeVerified': False,
            'nativeMapAndAllocatorBindingVerified': False, 'constantReadNativeAccessorComplete': False,
            'wordSemanticsCertificate': False, 'completePublicationRollbackVerified': False,
            'composedProductionTheoremVerified': False}


def mutation_cases():
    def source(name, directory='Compiler/Extraction'):
        raw = (ROOT / 'lean' / directory / name).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\nset_option pp.notation false\n' + without_imports(raw)
    # Keep a real caller of the lifetime contract in the control program.
    # Changed premises must fail that application as well as the implementation
    # proof; an omega-only diagnostic is not accepted by the shared strict gate.
    lifetime_client = '''
namespace Compiler.ZigAir.Memory
theorem constructor_item_cleanup_client (memory : State) (threshold identity : Nat) (allocation : Allocation)
    (valid : memory.valid = true) (found : memory.heap.lookup identity = some allocation)
    (hstack : allocation.stack = true) (hmark : threshold ≤ identity) :
    (cleanup threshold memory).heap.lookup identity = none :=
  cleanup_lookup_stack memory threshold identity allocation valid found hstack hmark
end Compiler.ZigAir.Memory
'''
    # An intentionally wrong returned world must fail the routing equality
    # without subsequently expanding the large graph postcondition. Check that
    # postcondition's public outputs separately against its proved contract.
    returned = source('InternerConstructorItemReturnTests.lean')
    boundary = '/-- The actual constructor local, caller, native growth and both returns derive'
    if returned.count(boundary) != 1:
        raise ValueError('ambiguous constructor return control boundary')
    returned = returned.split(boundary)[0] + '\nend ' + TESTS[:-1] + '\n'
    postconditions = '''import Compiler.Extraction.InternerConstructorItemReturnTests
namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.Tests
open Insertion.Native
open CallerGrowingChainTests (parent grownLifetime)
open CallerInputTests (values)
theorem constructor_return_client (safety empty : Bool) (find : Recursive.Find (Publication.Effects Nat)) :
    Good (parent empty) (values empty) (full safety empty find).2.world ∧
    (full safety empty find).2.world.memory.memory.nextId = grownLifetime empty + 1 := by
  obtain ⟨_, _, _, good, _, _, _, _, _, _, _, history⟩ := full_contract safety empty find
  exact ⟨good, history⟩
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.Tests
'''
    return (
        ('local', source('AssemblyItemConstructorLocal.lean'), (
            ('omit-defaults', '⟨item, AssemblyItem.Initializers.construct item debug, none⟩', '⟨item, debug, none⟩', 1),
            ('change-item-data', '⟨item, AssemblyItem.Initializers.construct item debug, none⟩',
             '⟨{ item with data := 1 }, AssemblyItem.Initializers.construct item debug, none⟩', 1),
            ('rewind-history', 'after.memory.memory.nextId = before.memory.memory.nextId + 1',
             'after.memory.memory.nextId = before.memory.memory.nextId', 1),
            ('register-stack-local', 'unregistered : after.memory.heap before.memory.memory.nextId = none',
             'unregistered : after.memory.heap before.memory.memory.nextId = some ⟨7, .item item⟩', 1),
        )),
        ('caller', source('InternerConstructorItem.lean'), (
            ('wrong-native-pointer', '    let ran := ConstructorFrame.find external budget allocator (p address (input request.item debug)) q source request prepared',
             '    let ran := ConstructorFrame.find external budget allocator (p ⟨0, 0⟩ (input request.item debug)) q source request prepared', 1),
            ('lose-source-offset', '    let ran := ConstructorFrame.find external budget allocator (p address (input request.item debug)) q source request prepared',
             '    let ran := ConstructorFrame.find external budget allocator (p address (input request.item debug)) q { source with first := 0 } request prepared', 1),
            ('erase-parent-stack', '\n        memory := Compiler.ZigAir.Memory.cleanup before.memory.memory.nextId ran.2.world.memory.memory',
             '\n        memory := Compiler.ZigAir.Memory.cleanup 0 ran.2.world.memory.memory', 1),
            ('unwind-rejection', '\n    if ordinary ran.1 then', '\n    if !ordinary ran.1 then', 1),
        )),
        ('lifetime', source('MemoryAllocationShape.lean', 'Compiler/ZigAir') + lifetime_client, (
            ('retire-persistent', '(stack : cell.stack = true) (recent : mark ≤ id)',
             '(stack : cell.stack = false) (recent : mark ≤ id)', 1),
            ('retire-parent', '(stack : cell.stack = true) (recent : mark ≤ id)',
             '(stack : cell.stack = true) (recent : id < mark)', 1),
        )),
        ('return', returned, (
            ('keep-constructor-local', 'memory := Compiler.ZigAir.Memory.cleanup (before safety empty).memory.memory.nextId (childReturned safety empty after).memory.memory',
             'memory := (childReturned safety empty after).memory.memory', 1),
            ('wrong-result', '(.ok 5,', '(.ok 6,', 3),
        )),
        ('postconditions', postconditions, (
            ('invent-parent-words', 'Good (parent empty) (values empty)', 'Good (parent empty) [1]', 1),
            ('rewind-history', '.world.memory.memory.nextId = grownLifetime empty + 1',
             '.world.memory.memory.nextId = grownLifetime empty', 1),
        )),
        ('boundaries', source('InternerConstructorItemTests.lean'), (
            ('discard-rejected-allocation', '(.error (.memory (.preparation (.memory .malformed))), allocatedBlank)',
             '(.error (.memory (.preparation (.memory .malformed))), blank)', 1),
            ('rejection-as-oom', '(.error (.language .safetyFault),', '(.error (.language .outOfMemory),', 1),
            ('drop-rejected-lookup', '⟨some (lookup empty), some (normalized empty), true⟩',
             '⟨none, some (normalized empty), true⟩', 1),
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
                raise ValueError('ambiguous constructor item mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'constructor-item-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'constructor-item-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
