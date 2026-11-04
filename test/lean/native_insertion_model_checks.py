#!/usr/bin/env python3
"""Check reached preparation policy equations and their general-step consumer.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
import native_step_checks as step
import caller_native_insertion_checks as caller

STORAGE = 'Compiler.Extraction.Storage.'
INTERNER = 'Compiler.Extraction.Interner.'
NATIVE = caller.NATIVE
POLICY = NATIVE + 'PreparationPolicy.'
CLAIMS = [STORAGE + name for name in ('allocationPolicy_complete', 'insert_outcome_any')]
CLAIMS += [INTERNER + name for name in ('observed_insert_failure', 'observed_insert_capacity', 'observed_insert_preparation_oom')]
CLAIMS += [POLICY + name for name in ('duplicate', 'create', 'clone', 'failure', 'model_oom')]
CLAIMS += [step.NS + 'insertion_model']
CLAIMS += [STORAGE + name for name in ('Program.scope_completed', 'insert_execution_capacity_outcome',
    'insert_execution_outcome', 'insert_execution_policy', 'insert_execution_success',
    'insert_prepared_success_at_owners', 'insert_transferred_success_at_owners',
    'insert_prepared_success', 'insert_transferred_success')]
CLAIMS += [INTERNER + 'InsertionExecution.' + name for name in ('project_transaction', 'observed', 'project_candidate')]
CLAIMS += [NATIVE + name for name in ('execution_candidate', 'body_model', 'insert_model')]
CLAIMS += [STORAGE + 'ExecutionPolicyTests.' + name for name in
    ('fixture_outcomes', 'fixture_graph', 'stateful_policy', 'attempt_rejection', 'cleanup_rejection', 'ownership_sensitive_success',
     'ownership_sensitive_preparation', 'ownership_sensitive_observations', 'wrong_owner_rejected')]

CLAIMS += [INTERNER + 'InsertionFailureTests.' + name for name in
           ('preparation_retains_cursor', 'stream_advances_cursor', 'missing_rows_reject')]


def audit_statements(rows):
    for name in CLAIMS:
        if 'InsertionFailureTests.' in name or 'ExecutionPolicyTests.' in name:
            continue
        statement = next(row['statement'] for row in rows if row['theorem'] == name)
        if statement.get('encoding') != 'kernelExprDag-v1':
            raise ValueError('unsupported insertion model statement encoding')
        constants = step.constants_below(statement, statement['root'])
        if {NATIVE + 'CallerInput', caller.NORMAL + 'OwnedCall.Caller.Origin'} & constants:
            raise ValueError('model connection assumes a rebased caller origin')
        if name == step.NS + 'insertion_model':
            step.remaining_guards(statement, 'remaining')
            step.published_parent(statement)
            step.rollback_parent(statement)
            step.preparation_candidate(statement, 'laterCandidate')
            if not {NATIVE + 'PreparationPolicy', INTERNER + 'observedInsert', step.NS + 'Returns'} <= constants:
                raise ValueError('insertion model lost its policy, adapter or result connection')
    return {'remainingInsertionExcludesCapacityAndPreparationOom': True,
            'remainingInsertionExcludesFirstAndNoRemapBackingOom': True,
            'publicationUnion': step.publication_union(), 'refusalUnion': step.refusal_union(),
            'remainingInsertionExcludesSuccessfulFirstPublication': True,
            'remainingInsertionExcludesSuccessfulSparePublication': True,
            'remainingInsertionExcludesSuccessfulRelocation': True, 'remainingInsertionExcludesRelocatedPublicationOom': True,
            'sharedRollbackParentLawExplicit': True, 'remainingInsertionExcludesFirstAndSparePublicationOom': True, 'sharedPublishedParentLawExplicit': True,
            'localPolicyEquationsRemainExplicit': True, 'candidateBindsPreparation': True, 'laterInsertionAssumesOnlyNativeFrame': True, 'wholeInvocationPolicySelectionVerified': False,
            'advancingAllocationStreamCouplingVerified': False, 'completeNativeInsertionVerified': False}


def audit(claims):
    required = {
        STORAGE + 'insert_outcome_any': {STORAGE + 'allocationPolicy_complete', STORAGE + 'insert_outcome'},
        INTERNER + 'observed_insert_failure': {STORAGE + 'insert_safe_any', STORAGE + 'failure_restores'},
        INTERNER + 'observed_insert_capacity': {INTERNER + 'observed_insert_failure', STORAGE + 'insert_outcome_any'},
        INTERNER + 'observed_insert_preparation_oom': {INTERNER + 'observed_insert_failure', STORAGE + 'insert_outcome_any'},
        POLICY + 'failure': {POLICY + name for name in ('duplicate', 'create', 'clone')},
        POLICY + 'model_oom': {POLICY + 'failure', INTERNER + 'observed_insert_preparation_oom'},
        step.NS + 'insertion_model': {step.NS + 'CallFrame.capacity_failure', step.NS + 'CallFrame.preparation_oom', step.NS + 'CallFrame.published',
            step.NS + 'CallFrame.backing_oom', step.NS + 'CallFrame.publication_rollback',
            step.NS + 'CallFrame.first_published', step.NS + 'CallFrame.spare_published', step.NS + 'CallFrame.growing_published',
            POLICY + 'model_oom', INTERNER + 'observed_insert_capacity', NATIVE + 'insert_model'},
        INTERNER + 'InsertionFailureTests.preparation_retains_cursor': {INTERNER + 'observed_insert_preparation_oom'},
        INTERNER + 'InsertionFailureTests.stream_advances_cursor': {INTERNER + 'observedInsertWith'},
    }
    required.update({
        STORAGE + 'insert_execution_outcome': {STORAGE + 'Program.scope_completed', STORAGE + 'insert_execution_capacity_outcome'},
        STORAGE + 'insert_prepared_success': {STORAGE + 'insert_prepared_success_at_owners'},
        STORAGE + 'insert_transferred_success': {STORAGE + 'insert_transferred_success_at_owners'},
        STORAGE + 'insert_execution_success': {STORAGE + name for name in
            ('insert_execution_outcome', 'insert_prepared_success_at_owners', 'insert_transferred_success_at_owners')},
        NATIVE + 'execution_candidate': {STORAGE + 'insert_execution_success', NATIVE + 'append_cell', NATIVE + 'publication_cell'},
        STORAGE + 'ExecutionPolicyTests.ownership_sensitive_observations': {STORAGE + 'insert_execution_success',
            STORAGE + 'ExecutionPolicyTests.ownership_sensitive_success'},
        STORAGE + 'insert_execution_policy': {STORAGE + 'insert_execution_outcome', STORAGE + 'insert_outcome_any'},
        INTERNER + 'InsertionExecution.project_transaction': {STORAGE + 'insert_safe_any'},
        INTERNER + 'InsertionExecution.observed': {STORAGE + 'insert_execution_policy', STORAGE + 'insert_execution_safe',
            INTERNER + 'InsertionExecution.project_transaction'},
        NATIVE + 'body_model': {NATIVE + 'execution_candidate', NATIVE + 'checkedExecution_read', INTERNER + 'InsertionExecution.observed',
            INTERNER + 'InsertionExecution.project_candidate', STORAGE + 'insert_execution_safe'},
        NATIVE + 'insert_model': {NATIVE + 'body_model'},
        STORAGE + 'ExecutionPolicyTests.fixture_outcomes': {STORAGE + 'insert_execution_policy'},
        STORAGE + 'ExecutionPolicyTests.fixture_graph': {INTERNER + 'InsertionExecution.observed'},
    })
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('insertion model lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
        if 'InsertionFailureTests.' not in name and 'ExecutionPolicyTests.' not in name and any(
                any(part.endswith('Tests') for part in dependency.split('.')) for dependency in claims[name]):
            raise ValueError('general insertion model depends on fixtures: ' + name)
    return {'checkedDependencies': sorted(required), 'actualSuccessfulPrefixAndFailureMatched': True,
            'capacityAndPreparationOomComposed': True, 'ordinaryInsertionResultAndGraphDerived': True, 'successfulCandidateDerivedFromPreparation': True, 'completeNativeInsertionVerified': False,
            'composedProductionTheoremVerified': False}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / (name + '.lean')).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)
    return (
        ('storage', source('StorageProofs'), (
            ('wrong-site', '(succeeds .append) (succeeds .publish) = succeeds', '(succeeds .clone) (succeeds .publish) = succeeds', 1),
            ('ignore-room', 'expectedOutcome input.deterministic input.room', 'expectedOutcome input.deterministic true', 1),
        )),
        ('projection', source('ObservedInsertionFailure'), (
            ('allow-success', '(failure : outcome ≠ .success)', '(failure : outcome ≠ .allocationFailure)', 1),
            ('lose-read-correspondence', '(reads : before.read = Storage.readValue rows)', '(reads : True)', 3),
            ('rewind-cursor', '= (insertionOutcome rows (some outcome), before)',
             '= (insertionOutcome rows (some outcome), { before with allocationCursor := 0 })', 1),
            ('early-capacity', '(saturated : 2 ^ 32 - 1 ≤ rows.length)', '(saturated : 2 ^ 32 - 2 ≤ rows.length)', 1),
            ('omit-capacity-guard', '(room : rows.length < 2 ^ 32 - 1)', '(room : True)', 1),
        )),
        ('policy', source('InternerInsertionPreparationPolicy'), (
            ('duplicate-is-item', 'duplicate : succeeds .arguments =', 'duplicate : succeeds .item =', 1),
            ('rewind-create', 'input.item duplicated).1.isOk', 'input.item before).1.isOk', 1),
            ('rewind-clone', 'allocator input allocated).1.isOk', 'allocator input duplicated).1.isOk', 1),
            ('invent-earlier-failure', 'succeeds .arguments = true ∧ (succeeds .item = false',
             'succeeds .arguments = false ∧ (succeeds .item = false', 1),
        )),
        ('completion', source('InternerNativeInsertionModel'), (
            ('rewind-published-parent',
             'parent (Insertion.Native.insert ops allocate safety allocator owner source address meaning native key normalized true growth world).2)',
             'parent world)', 2),
            ('omit-publication-exclusion', '¬ Insertion.Native.PublishedObservation', 'Insertion.Native.PublishedObservation', 1),
            ('omit-rollback-exclusion', '¬ Insertion.Native.RefusedObservation', 'Insertion.Native.RefusedObservation', 1),
            ('omit-backing-exclusion', '¬ Insertion.Native.BackingAllocationOOM', 'Insertion.Native.BackingAllocationOOM', 1),
            ('discard-later-frame', 'GraphFrame safety allocator owner rows parent actual.2)',
             'GraphFrame safety allocator owner rows parent world)', 1),
            ('unbound-later-policy', 'succeeds world.graph = Insertion.Native.observedPolicy',
             '(fun (_ : Storage.Allocation) => true) = Insertion.Native.observedPolicy', 1),
            ('lose-detachment', '(detached : lookup.owned = none)', '(detached : True)', 1),
            ('wrong-policy', 'world.memory (succeeds world.graph))', 'world.memory (fun _ => true))', 1),
            ('exclude-later-cases', '¬ Insertion.Native.PreparationOOM', 'Insertion.Native.PreparationOOM', 5),
            ('rewind-parent', '(parentFrame world frame)', '(fun _ _ _ => frame.2.2)', 3),
        )),
        ('source-policy', source('StorageExecutionPolicy'), (
            ('admit-rejected-execution', '(completed : (insertProgram.execute input calls {} before).1.1 = .ok outcome)',
             '(completed : (insertProgram.execute input calls {} before).1.1 = .error fault)', 2),
            ('rewind-effects', '(observed.1.toOption.getD false, observed.2)', '(observed.1.toOption.getD false, before)', 1),
            ('wrong-create-owner', 'then duplicatedOwnership else transferredArguments', 'then normalizedOwnership else transferredArguments', 1),
            ('wrong-transferred-clone-owner', 'then createdOwnership else transferredCreated', 'then createdOwnership else transferredArguments', 1),
            ('publish-before-append', '| .publish => publicationOwnership', '| .publish => preparationOwnership', 1),
            ('wrong-preparation-stage', '(executionAttempt calls deterministic .clone made).2',
             '(executionAttempt calls deterministic .item made).2', 1),
            ('assume-failure-is-success', '= .ok (some .success)) :', '= .ok (some .allocationFailure)) :', 1),
            ('rewind-success-state', 'if deterministic then published.2 else appended.2)',
             'if deterministic then appended.2 else before)', 1),
            ('skip-duplication', 'effectPolicy deterministic (executionAttempt calls deterministic)',
             'effectPolicy false (executionAttempt calls deterministic)', 1),
        )),
        ('prepared-success', source('StoragePreparedRollback'), (
            ('wrong-duplicate-owner', 'calls.attempt .arguments normalizedOwnership start', 'calls.attempt .arguments createdOwnership start', 1),
            ('rewind-create-state', 'calls.attempt .item duplicatedOwnership dupe', 'calls.attempt .item duplicatedOwnership start', 1),
            ('skip-publication-state', 'publishedOwnership), after)', 'publishedOwnership), appended)', 2),
        )),
        ('transferred-success', source('StorageTransferredInsertion'), (
            ('wrong-create-owner', 'calls.attempt .item transferredArguments start', 'calls.attempt .item transferredCreated start', 1),
            ('rewind-clone-state', 'calls.attempt .clone transferredCreated made', 'calls.attempt .clone transferredCreated start', 1),
            ('retain-value-owner', 'transferredOwnership), after)', 'transferredPreparation), after)', 2),
        )),
        ('source-projection', source('InsertionExecutionPolicy'), (
            ('assume-no-publication', '(insertionOutcome cells outcome, project cells table cell key owner)',
             '(insertionOutcome cells outcome, project cells table cell key { owner with published := false })', 1),
            ('drop-candidate-binding', '(binding : outcome = some .success → actual = candidate)',
             '(binding : outcome = some .success → actual = actual)', 1),
            ('invent-success', '(insertionOutcome cells outcome, project cells table cell key\n',
             '(insertionOutcome cells (some .success), project cells table cell key\n', 1),
        )),
        ('native-policy', source('InternerInsertionNativePolicy'), (
            ('changed-initial-locals', '⟨⟨⟨⟨before.memory, false⟩', '⟨⟨⟨⟨before.memory, true⟩', 1),
            ('candidate-before-preparation', '(executionPreparation\n      (observedCalls ops allocate safety allocator container source address meaning input key normalized cells before growth)\n      deterministic (observedStart before))', '(observedStart before)', 1),
            ('candidate-without-success', '.ok (some .success)) :', '.ok (some .allocationFailure)) :', 1),
            ('wrong-header-count', '.slice itemsType backing cells.length', '.slice itemsType backing (cells.length + 1)', 2),
            ('rewind-cursor', 'actual.2.graph = model.2', 'actual.2.graph = { model.2 with allocationCursor := 0 }', 2),
            ('drop-successful-candidate', '= candidate)', '= cell input key normalized ((key.eval meaning before.graph.read).getD 0) ran.1.2 ran.2)', 2),
        )),
        ('policy-regressions', source('StorageExecutionPolicyTests'), (
            ('hide-allocation-rejection', '(run true true none true).1.1 = .error .allocation',
             '(run true true none true).1.1 = .ok (some .allocationFailure)', 1),
            ('hide-cleanup-rejection', '(run true true (some .publish) false (some .pop)).1.1 = .error .cleanup',
             '(run true true (some .publish) false (some .pop)).1.1 = .ok (some .allocationFailure)', 1),
            ('rewind-observation', 'executionPolicy dependentOperations true 0 .item = false',
             'executionPolicy dependentOperations true 0 .item = true', 1),
            ('use-empty-owner', '| .item => owner.flag .arguments', '| .item => ({} : State).flag .arguments', 1),
            ('wrong-preparation-count', 'then 3 else 2', 'then 2 else 3', 1),
            ('wrong-success-count', 'then 5 else 3', 'then 3 else 5', 1),
            ('lose-cleanup-effects', ').2 = 22', ').2 = 20', 1),
        )),
        ('cursor', source('ObservedInsertionFailureTests'), (
            ('erase-real-advance', '(.error .outOfMemory, empty (cursor + 1))', '(.error .outOfMemory, empty cursor)', 1),
            ('invent-advance', '(.error .outOfMemory, empty cursor)', '(.error .outOfMemory, empty (cursor + 1))', 1),
            ('missing-rows-oom', '(.error .safetyFault, before)', '(.error .outOfMemory, before)', 1),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    records = []
    for group, text, changes in mutation_cases():
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous insertion model mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'insertion-model-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'insertion-model-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
