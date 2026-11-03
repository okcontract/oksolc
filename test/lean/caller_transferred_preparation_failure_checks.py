#!/usr/bin/env python3
"""Audit caller-derived ownership on nondeterministic preparation OOM.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NATIVE = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.'
CHAIN = NATIVE + 'CallerGrowingChainTests.'
TESTS = CHAIN + 'TransferredPreparationFailureTests.'
STORAGE = 'Compiler.Extraction.Storage.'
CLAIMS = [STORAGE + 'insert_transferred_' + stage + '_oom' for stage in ('create', 'clone')]
CLAIMS += [NATIVE + 'CallerInput.' + name for name in
           ('transferred_argument_cleanup', 'transferred_create_oom', 'transferred_clone_oom')]
CLAIMS += [CHAIN + 'GraphFacts.frame', NATIVE + 'TransferredFailure.caller', TESTS + 'shared_completion']
MODULE = 'Compiler.Extraction.InternerCallerTransferredPreparationFailureTests'
CLAIMS += [TESTS + name for name in ('failure_results', 'completed', 'native_contract', 'derived_contract',
                                   'parent_borrow_after_oom', 'key_unchanged', 'effects_observed')]


def audit(claims):
    required = {
        STORAGE + 'insert_transferred_create_oom': {STORAGE + 'insertProgram', STORAGE + 'Program.execute'},
        STORAGE + 'insert_transferred_clone_oom': {STORAGE + 'insertProgram', STORAGE + 'Program.execute'},
        NATIVE + 'CallerInput.transferred_argument_cleanup': {
            'Compiler.Extraction.Memory.Arguments.Normalization.free_valid', NATIVE + 'free_keys', NATIVE + 'free_keeps_dead'},
        NATIVE + 'CallerInput.transferred_create_oom': {NATIVE + 'transferred_create_oom_execution', NATIVE + 'TransferredFailure.caller',
            'Compiler.Extraction.AssemblyItem.Creation.create_oom', NATIVE + 'create_keys', STORAGE + 'insert_transferred_create_oom'},
        NATIVE + 'CallerInput.transferred_clone_oom': {NATIVE + 'transferred_clone_oom_execution', NATIVE + 'TransferredFailure.caller',
            'Compiler.Extraction.AssemblyItem.Creation.create_verified', 'Compiler.Extraction.AssemblyClone.Physical.run_oom',
            'Compiler.Extraction.AssemblyItem.Creation.NativeFields.represented_after_create',
            'Compiler.Extraction.AssemblyItem.Creation.NativeFields.clone_oom',
            'Compiler.Extraction.AssemblyItem.destroy_verified', NATIVE + 'clone_keys', NATIVE + 'destroy_keys',
            STORAGE + 'insert_transferred_clone_oom'},
        CHAIN + 'GraphFacts.frame': {'Compiler.Extraction.RepresentativeArray.Operation.query',
            'Compiler.Extraction.RepresentativeArray.DescriptorRelation.frame',
            'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.BorrowedQuery.Native.of_resident'},
        NATIVE + 'TransferredFailure.caller': {NATIVE + 'PrivateFrame.allocations',
            'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Origin.freshNative'},
        TESTS + 'shared_completion': {'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.Enclosing.insertion_frame',
            NATIVE + 'preparation_oom_execution_at', TESTS + 'failure_results', NATIVE + 'NativeGrowingTests.reached_frame'},
        TESTS + 'completed': {CHAIN + 'initialized_prefix', NATIVE + 'CallerInput.handoff_insert'},
        TESTS + 'native_contract': {NATIVE + 'CallerInput.transferred_create_oom', NATIVE + 'CallerInput.transferred_clone_oom',
            CHAIN + 'initialized_prefix', TESTS + 'failure_results'},
        TESTS + 'derived_contract': {TESTS + 'native_contract', TESTS + 'completed', CHAIN + 'GraphFacts.frame'},
        TESTS + 'parent_borrow_after_oom': {TESTS + 'derived_contract', CHAIN + 'GraphFacts.first_borrow'},
        TESTS + 'key_unchanged': {TESTS + 'derived_contract'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('transferred preparation OOM lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    for name in ('native_contract', 'derived_contract'):
        if TESTS + 'effects_observed' in claims[TESTS + name]:
            raise ValueError('transferred preparation OOM used final fixture effects as ownership premises')
    return {'checkedDependencies': sorted(required), 'scope': 'ordinary creation and clone OOM after nondeterministic transfer',
            'callerOriginDerivesCleanupSeparation': True, 'singleArgumentOwnerReleasedOnce': True,
            'cloneObjectOwnershipAndDestructionDerived': True, 'nativeSourceReadbackConnected': True, 'reachedPreparationSharedWithJointItem': True,
            'oldGraphKeysAndParentBorrowPreserved': True, 'outerDetachedLookupCleanupConnected': True,
            'bothOwnerLayoutsAndEmptyNonemptyArgumentsChecked': True,
            'capacityAndRejectedPreparationCompositionVerified': False, 'generalGrowingFailureCompositionVerified': False,
            'nativeAllocatorVtableBindingVerified': False, 'nativeMapImplementationVerified': False,
            'completePublicationRollbackVerified': False, 'fullCallerCacheRoutingVerified': False,
            'recursiveChildPreservationVerified': False, 'composedProductionTheoremVerified': False}



def audit_statements(rows):
    import check_native_invocation as gate
    import constructor_joint_checks as joint
    import constructor_replay_choice_checks as choice
    statements = {row['theorem']: row['statement'] for row in rows}
    value = statements[TESTS + 'shared_completion']
    fields, root, context = gate.domains(value)
    if list(fields) != ['safety', 'empty', 'clone']:
        raise ValueError('shared transferred fixture assumes its final frame')
    args = joint.app(value, root, gate.NS + 'FramePost')
    choice.one_call(value, args[-1], context, gate.OWNED + 'finish')
    value = statements[NATIVE + 'TransferredFailure.caller']
    fields, root, context = gate.domains(value)
    if set(fields) != {'σ', 'allocator', 'source', 'address', 'request', 'values', 'input', 'key', 'before',
                      'taken', 'normalized', 'lookup', 'history', 'after', 'post', 'entry'}:
        raise ValueError('caller specialization added a preservation premise')
    args = joint.app(value, root, NATIVE + 'CallerPreparationFailure')
    if [gate.named(value, x, context) for x in args] != ['σ', 'allocator', 'normalized', 'before', 'history', 'after']:
        raise ValueError('caller specialization changed the actual origin or reached history')
    index, local = fields['post']
    args = joint.app(value, index, NATIVE + 'TransferredFailure')
    joint.path(value, args[2], local, (gate.OWNED + 'World.memory', gate.OWNED + 'State.world'), 'taken')
    return {'reachedPrivateFrameSpecializesCallerOrigin': True, 'existingFixtureConsumesSharedReducer': True,
            'finalFixtureFrameNotAssumed': True}


def mutation_cases():
    def source(name, stop=None):
        raw = (ROOT / 'lean/Compiler/Extraction' / name).read_text()
        if stop is not None:
            raw = raw.split(stop, 1)[0] + '\nend Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests\n'
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\nset_option pp.notation false\n' + without_imports(raw)
    fixtures = '''import Compiler.Extraction.InternerCallerTransferredPreparationFailureTests
namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.TransferredPreparationFailureTests.Controls
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open CallerInputTests (request key)
example (safety empty clone : Bool) : outcome safety empty clone = (.error (.language .outOfMemory),
    ⟨world safety empty clone, ⟨none, some (normalized safety empty 4), true⟩⟩) := (derived_contract safety empty clone).1
example (safety empty clone : Bool) : Good (parent empty) (request empty).arguments (world safety empty clone) :=
  (parent_borrow_after_oom safety empty clone).2
example (safety empty clone : Bool) :
    (world safety empty clone).memory.effects.keys (key empty) = some ⟨if empty then 22 else 30, 4⟩ := key_unchanged safety empty clone
example (safety empty clone : Bool) : (world safety empty clone).memory.effects.allocator = expectedEffects safety empty clone := by
  have observed := effects_observed safety empty clone
  generalize expectedEffects safety empty clone = expected at observed ⊢
  exact observed
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.TransferredPreparationFailureTests.Controls
'''
    return (
        ('program', source('StorageTransferredInsertion.lean'), (
            ('retain-normalized-defer', '.setFlag .normalized true).setFlag .normalized false',
             '.setFlag .normalized true).setFlag .normalized true', 1),
            ('create-double-release', '(Cleanup.sequence [.arguments]).run transferredArguments',
             '(Cleanup.sequence [.arguments, .normalized]).run transferredArguments', 1),
            ('clone-skip-object', '(Cleanup.sequence [.allocation, .arguments]).run transferredCreated',
             '(Cleanup.sequence [.arguments]).run transferredCreated', 1),
        )),
        ('cleanup', source('InternerCallerTransferredCleanup.lean'), (
            ('advance-history', 'nextId = history.memory.nextId', 'nextId = history.memory.nextId + 1', 1),
            ('erase-parent', '→ (memory after).memory.heap.lookup id = some cell', '→ (memory after).memory.heap.lookup id = none', 1),
            ('retain-arguments', 'consumed : Consumed normalized (memory after)', 'consumed : ¬ Consumed normalized (memory after)', 1),
            ('invalidate-row', 'marker : after.item.clone.execution.invalidated = false', 'marker : after.item.clone.execution.invalidated = true', 1),
            ('free-empty', 'if normalized.items.isEmpty then (memory reached).effects',
             'if normalized.items.isEmpty then (Publication.external ops.arguments).free normalized (memory reached)', 2),
        )),
        ('caller', source('InternerCallerTransferredPreparationFailure.lean'), (
            ('success-after-oom', '((.ok (some .allocationFailure),', '((.ok (some .success),', 2),
            ('clone-succeeded', 'allocator input allocated = (.error .outOfMemory, failed)',
             'allocator input allocated = (.ok input, failed)', 1),
            ('retain-object', '(memory after).heap object = none ∧', '(memory after).heap object ≠ none ∧', 1),
            ('rebase-caller-origin', 'CallerInput allocator source address request values input key before taken normalized lookup',
             'CallerInput allocator source address request values input key taken.world taken normalized lookup', 1),
        )),
        ('graph-frame', source('InternerCallerInsertionGrowingChainTests.lean', '\ntheorem initial_prefix'), (
            ('wrong-backing', 'GraphFacts safety backing capacity after rows := by',
             'GraphFacts safety (backing + 1) capacity after rows := by', 1),
            ('erase-rows', 'GraphFacts safety backing capacity after rows := by',
             'GraphFacts safety backing capacity after [] := by', 1),
        )),
        ('fixtures', fixtures, (
            ('detach-lookup', '⟨none, some (normalized safety empty 4), true⟩',
             '⟨some (lookup empty), some (normalized safety empty 4), true⟩', 1),
            ('lose-parent-values', 'Good (parent empty) (request empty).arguments', 'Good (parent empty) [1]', 1),
            ('replace-old-key', 'some ⟨if empty then 22 else 30, 4⟩', 'some ⟨if empty then 25 else 35, 5⟩', 1),
            ('charge-second-free', '= expectedEffects safety empty clone := by',
             '= expectedEffects safety empty clone + (if empty then 0 else 101) := by', 1),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    cases = mutation_cases()
    for group, text, changes in cases:
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous transferred preparation mutation: ' + group + '-' + name)
    records = []
    for group, text, changes in cases:
        records += checked_controls(output, [mutation_check(output, 'transferred-preparation-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'transferred-preparation-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
