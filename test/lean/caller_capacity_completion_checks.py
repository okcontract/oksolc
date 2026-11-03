#!/usr/bin/env python3
"""Audit native insertion result projection and actual capacity caller completion.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NATIVE = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.'
TESTS = NATIVE + 'CallerGrowingChainTests.CompletionTests.'
CLAIMS = [NATIVE + name for name in ('body_rejected', 'body_native_fault', 'insert_unrepresented', 'projected_unchanged',
          'CallerPreparationFailure.borrow', 'CallerInput.finish_native', 'CallerInput.capacity_completed', 'CallerInput.rejected_completed')]
CLAIMS += [TESTS + name for name in ('initialized_body', 'preparation_oom', 'missing_owner', 'rejection_retains_owner')]


def audit(claims):
    required = {
        NATIVE + 'body_rejected': {NATIVE + 'checkedExecution_rejected', NATIVE + 'body'},
        NATIVE + 'body_native_fault': {NATIVE + 'checkedExecution', NATIVE + 'body',
            'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.projected'},
        NATIVE + 'projected_unchanged': {'Compiler.Extraction.Interner.InsertionExecution.project',
            'Compiler.Extraction.Storage.nodesAfter'},
        NATIVE + 'CallerPreparationFailure.borrow': {NATIVE + 'CallerPreparationFailure.native',
            'Compiler.Extraction.Memory.Arguments.Normalization.represented_frame',
            'Compiler.ZigAir.Memory.access_success_region'},
        NATIVE + 'CallerInput.finish_native': {NATIVE + 'CallerInput.handoff_insert', NATIVE + 'finishInsertion', NATIVE + 'insert'},
        NATIVE + 'CallerInput.capacity_completed': {NATIVE + 'CallerInput.capacity_failure', NATIVE + 'body_unpublished',
            NATIVE + 'CallerInput.finish_native', NATIVE + 'CallerPreparationFailure.borrow'},
        NATIVE + 'CallerInput.rejected_completed': {NATIVE + 'body_rejected', NATIVE + 'CallerInput.finish_native'},
        TESTS + 'initialized_body': {NATIVE + 'CallerGrowingChainTests.CapacityTests.initialized_entry',
            NATIVE + 'CallerGrowingChainTests.initialized_prefix'},
        TESTS + 'preparation_oom': {TESTS + 'initialized_body', NATIVE + 'CallerInput.finish_native',
            NATIVE + 'CallerGrowingChainTests.TransferredPreparationFailureTests.native_contract',
            NATIVE + 'CallerGrowingChainTests.TransferredPreparationFailureTests.derived_contract'},
        TESTS + 'rejection_retains_owner': {NATIVE + 'CallerInput.rejected_completed', TESTS + 'missing_owner'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('capacity completion lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'scope': 'native insertion adapter and caller-entry capacity completion',
            'sameNativeExecutionAndProjection': True, 'capacityGraphEqualityDerived': True,
            'outerHandoffAndDetachedCleanupConnected': True, 'allPriorWordViewsPreserved': True,
            'rejectionKeepsReachedOwnership': True, 'initializedPreparationOomConnected': True,
            'finalGoodOrGraphEqualityPremise': False, 'recursiveChildTransportVerified': False,
            'fullCallerCacheRoutingVerified': False, 'nativeAllocatorVtableBindingVerified': False,
            'nativeMapImplementationVerified': False, 'completePublicationRollbackVerified': False,
            'composedProductionTheoremVerified': False}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / name).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\nset_option pp.notation false\n' + without_imports(raw)
    fixtures = '''import Compiler.Extraction.InternerCallerInsertionCapacityCompletionTests
namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.CompletionTests.Controls
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open CallerInputTests (request)
example (safety empty clone : Bool) : (completed safety empty clone).1 = .error (.language .outOfMemory) :=
  congrArg Prod.fst (preparation_oom safety empty clone).1
example (safety empty clone : Bool) : Good (parent empty) (request empty).arguments (completed safety empty clone).2.world :=
  (preparation_oom safety empty clone).2.2.1
example (safety empty deterministic : Bool) : rejected safety empty deterministic = (.error (.language .safetyFault),
    ⟨(taken safety empty 4).2.world, ⟨some (lookup empty), some (normalized safety empty 4), true⟩⟩) :=
  (rejection_retains_owner safety empty deterministic).1
example (safety empty deterministic : Bool) : ordinary (rejected safety empty deterministic).1 = false :=
  (rejection_retains_owner safety empty deterministic).2.2
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.CompletionTests.Controls
'''
    return (
        ('body', source('InternerInsertionNativeBody.lean'), (
            ('count-is-oom', '| .error _ => (.error (.language .safetyFault), before)',
             '| .error _ => (.error (.language .outOfMemory), before)', 1),
            ('native-is-oom', '| .error _ => .error (.language .safetyFault)',
             '| .error _ => .error (.language .outOfMemory)', 1),
            ('discard-reached-memory', 'let reached := Insertion.projected cells before key (cell input key normalized value owner after) owner after',
             'let reached := before', 1),
            ('missing-rows-as-oom', '| none => (.error (.language .safetyFault), before)',
             '| none => (.error (.language .outOfMemory), before)', 1),
            ('rewind-cursor', '= { before with memory := memory after } := by',
             '= { before with graph := { before.graph with allocationCursor := 0 }, memory := memory after } := by', 1),
            ('erase-rows', '= { before with memory := memory after } := by',
             '= { before with graph := { before.graph with representatives := some [] }, memory := memory after } := by', 1),
        )),
        ('caller', source('InternerCallerInsertionCapacityCompletion.lean'), (
            ('skip-handoff', 'let ran := (do handoff; graph', 'let ran := (do graph', 1),
            ('skip-outer-cleanup', 'finish (Publication.external ops.arguments) allocator ran.1 ran.2', 'ran', 1),
            ('capacity-is-oom', '(.error (.language .capacity),', '(.error (.language .outOfMemory),', 3),
            ('rewind-memory', '(.error (.language .capacity), ⟨before.graph, memory after⟩)',
             '(.error (.language .capacity), before)', 2),
            ('unwind-rejection', 'else (result, ⟨reached, ⟨some lookup, some normalized, true⟩⟩)',
             'else (result, ⟨reached, ⟨none, some normalized, true⟩⟩)', 1),
            ('change-borrowed-words', 'Good source values (⟨before.graph, memory after⟩',
             'Good source [0] (⟨before.graph, memory after⟩', 1),
        )),
        ('fixtures', fixtures, (
            ('oom-is-capacity', '= .error (.language .outOfMemory)', '= .error (.language .capacity)', 1),
            ('lost-parent', 'Good (parent empty) (request empty).arguments', 'Good (parent empty) [1]', 1),
            ('drop-detached-lookup', '⟨some (lookup empty), some (normalized safety empty 4), true⟩',
             '⟨none, some (normalized safety empty 4), true⟩', 1),
            ('rejection-is-ordinary', ').1 = false :=', ').1 = true :=', 1),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    cases = mutation_cases()
    for group, text, changes in cases:
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous capacity completion mutation: ' + group + '-' + name)
    records = []
    for group, text, changes in cases:
        records += checked_controls(output, [mutation_check(output, 'capacity-completion-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'capacity-completion-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
