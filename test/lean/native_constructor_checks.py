#!/usr/bin/env python3
"""Audit shared native preservation through all five constructor entries.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import re

import check_native_invocation as invocation
import native_constructor_word_checks as native_words
import constructor_joint_checks as joint
import constructor_joint_entry_checks as joint_entries
import recursive_joint_entry_checks as finite_joint
import constructor_replay_choice_checks as replay_choice
import enclosing_frame_checks as enclosing
import source_child_checks as source_children
import uniform_child_model_checks as uniform_children
import native_constant_dispatch_checks as constant_dispatch
import native_algebraic_dispatch_checks as algebraic_dispatch
import native_unary_dispatch_checks as unary_dispatch
import native_prefix_dispatch_checks as prefix_dispatch
import native_comparison_dispatch_checks as comparison_dispatch
import native_division_dispatch_checks as division_dispatch
import native_signextend_dispatch_checks as signextend_dispatch
import native_step_builder_checks as step_builder
import native_entry_miss_checks as native_entry
import native_constant_entry_checks as constant_entry
import preparation_coverage_checks as preparation_coverage
import insertion_coverage_checks as insertion_coverage
import native_frame_step_checks as native_frame_step
import native_frame_induction_checks as native_frame_induction
import native_allocation_trace_checks as allocation_trace
import native_allocation_entry_checks as allocation_entry
import native_caller_resource_checks as caller_resource
import native_resource_entry_checks as resource_entry
import native_checkpoint_entry_checks as checkpoint_entry
import native_checkpoint_constructor_checks as checkpoint_constructor
import native_checkpoint_body_checks as checkpoint_body
import native_checkpoint_body_entry_checks as checkpoint_body_entry
import native_checkpoint_history_checks as checkpoint_history
import native_recursive_replay_checks as recursive_replay
import native_recursive_word_checks as recursive_words
import native_recursive_constructor_checks as recursive_constructors
import native_recursive_invocation_checks as recursive_invocation
import native_host_lift_checks as host_lift
import native_force_checks as native_force
import native_find_checks as native_find
import native_find_caller_checks as native_find_caller
import native_resource_admission_checks as resource_admission
import native_resource_miss_checks as resource_miss
from assembly_item_creation_checks import checked_controls
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NS, ITEM, OWNED = invocation.NS, invocation.ITEM, invocation.OWNED
MODULE = step_builder.MODULE
INTERFACES = joint.INTERFACES + joint_entries.INTERFACES + finite_joint.INTERFACES + replay_choice.INTERFACES + enclosing.INTERFACES + source_children.INTERFACES + uniform_children.INTERFACES
INTERFACES += algebraic_dispatch.INTERFACES + unary_dispatch.INTERFACES + prefix_dispatch.INTERFACES + comparison_dispatch.INTERFACES + division_dispatch.INTERFACES + signextend_dispatch.INTERFACES + step_builder.INTERFACES + native_entry.INTERFACES
INTERFACES += constant_entry.INTERFACES + preparation_coverage.INTERFACES + insertion_coverage.INTERFACES + native_frame_step.INTERFACES
INTERFACES += resource_admission.INTERFACES
INTERFACES += resource_miss.INTERFACES
INTERFACES += native_frame_induction.INTERFACES
INTERFACES += allocation_trace.INTERFACES
INTERFACES += allocation_entry.INTERFACES
INTERFACES += caller_resource.INTERFACES
INTERFACES += resource_entry.INTERFACES
INTERFACES += checkpoint_entry.INTERFACES
INTERFACES += checkpoint_constructor.INTERFACES
INTERFACES += checkpoint_body.INTERFACES
INTERFACES += checkpoint_body_entry.INTERFACES
INTERFACES += recursive_replay.INTERFACES
INTERFACES += recursive_words.INTERFACES
INTERFACES += recursive_constructors.INTERFACES
INTERFACES += recursive_invocation.INTERFACES
INTERFACES += host_lift.INTERFACES
INTERFACES += native_force.INTERFACES
INTERFACES += native_find.INTERFACES
INTERFACES += native_find_caller.INTERFACES
ENTRIES = ('borrowed', 'constant', 'materialize', 'operation', 'local')
CLAIMS = [NS + name for name in ('EntryObligations.verified', 'InvocationPost.project', 'InvocationPost.unwind',
    'InvocationPost.returned', 'prepared_invocation_verified', 'literal_error_nonordinary', 'local_error_nonordinary')]
CLAIMS += [NS + 'step_' + entry + '_verified' for entry in ENTRIES]
CLAIMS += [NS + name for name in ('EntryObligations.observed', 'ObservedEntryObligations.verified', 'prepared_invocation_verified_observed')]
CLAIMS += [NS + 'step_' + entry + '_verified_observed' for entry in ENTRIES]
CLAIMS += native_words.CLAIMS
CLAIMS += joint.CLAIMS
CLAIMS += joint_entries.CLAIMS
CLAIMS += finite_joint.CLAIMS
CLAIMS += replay_choice.CLAIMS
CLAIMS += enclosing.CLAIMS
CLAIMS += source_children.CLAIMS
CLAIMS += uniform_children.CLAIMS
CLAIMS += constant_dispatch.CLAIMS
CLAIMS += algebraic_dispatch.CLAIMS + unary_dispatch.CLAIMS + prefix_dispatch.CLAIMS + comparison_dispatch.CLAIMS + division_dispatch.CLAIMS + signextend_dispatch.CLAIMS + step_builder.CLAIMS + native_entry.CLAIMS
CLAIMS += constant_entry.CLAIMS + preparation_coverage.CLAIMS + insertion_coverage.CLAIMS + native_frame_step.CLAIMS
CLAIMS += resource_admission.CLAIMS
CLAIMS += resource_miss.CLAIMS
CLAIMS += native_frame_induction.CLAIMS
CLAIMS += allocation_trace.CLAIMS
CLAIMS += allocation_entry.CLAIMS
CLAIMS += caller_resource.CLAIMS
CLAIMS += resource_entry.CLAIMS
CLAIMS += checkpoint_entry.CLAIMS
CLAIMS += checkpoint_constructor.CLAIMS
CLAIMS += checkpoint_body.CLAIMS
CLAIMS += checkpoint_body_entry.CLAIMS
CLAIMS += checkpoint_history.CLAIMS
CLAIMS += recursive_replay.CLAIMS
CLAIMS += recursive_words.CLAIMS
CLAIMS += recursive_constructors.CLAIMS
CLAIMS += recursive_invocation.CLAIMS
CLAIMS += host_lift.CLAIMS
CLAIMS += native_force.CLAIMS
CLAIMS += native_find.CLAIMS
CLAIMS += native_find_caller.CLAIMS
CLAIMS += [NS + 'dispatch_projects_framed_at']


def expression(statement, root, context, depth=0):
    """Compare local obligation types independently of DAG indices and binder positions."""
    node = statement['nodes'][root]
    if node[0] in ('forall', 'lambda'):
        return (node[0], node[2], expression(statement, node[3], context, depth),
                expression(statement, node[4], context + [("local", depth)], depth + 1))
    if node[0] == 'let':
        return ('let', expression(statement, node[2], context, depth), expression(statement, node[3], context, depth),
                expression(statement, node[4], context + [("local", depth)], depth + 1))
    if node[0] == 'app':
        return ('app', expression(statement, node[1], context, depth), expression(statement, node[2], context, depth))
    if node[0] == 'projection':
        return ('projection', node[1], node[2], expression(statement, node[3], context, depth))
    return invocation.named(statement, root, context)


def audit_statements(rows, interfaces):
    statements = {row['theorem']: row['statement'] for row in rows}
    definitions = {record['name']: record for record in interfaces}
    for observed in (False, True):
        constructor = definitions[NS + ('ObservedEntryObligations.mk' if observed else 'EntryObligations.mk')]
        if constructor['kind'] != 'constructor':
            raise ValueError('entry obligations lost explicit local fields')
        fields = constructor['type']
        entries, _, _ = invocation.domains(fields)
        reference = statements[NS + ('step_invocation_verified_observed' if observed else 'step_invocation_verified')]
        ref_entries, _, _ = invocation.domains(reference)
        for field, original in (('retained', 'retained'), ('localParent', 'localParent'), ('taken', 'takenObligations')):
            root, context = entries[field]
            ref_root, ref_context = ref_entries[original]
            if expression(fields, root, context) != expression(reference, ref_root, ref_context):
                raise ValueError('entry package changed an existing local obligation: ' + field)

    post = definitions[NS + 'ConstructorPost']
    if post['kind'] != 'definition':
        raise ValueError('constructor post lost its inspectable definition')
    value = post['value']
    post_entries, body, _ = invocation.domains(value)
    root, context = next(reversed(post_entries.values()))
    head, args = invocation.applied(value, root)
    if (head[:2] != ['const', 'Eq'] or len(args) != 3
            or invocation.named(value, args[-1], context) != 'Bool.true'
            or OWNED + 'ordinary' not in invocation.step.constants_below(value, args[-2])):
        raise ValueError('constructor post lost its actual ordinary-result guard')
    if OWNED + 'Semantic.Ensures' not in invocation.step.constants_below(value, body):
        raise ValueError('constructor post lost word preservation')

    for observed in (False, True):
        for entry in ENTRIES:
            statement = statements[NS + 'step_' + entry + ('_verified_observed' if observed else '_verified')]
            binders, conclusion, _ = invocation.domains(statement)
            required = {'base', 'children', 'before', 'debug', 'rows', 'parent',
                        'env', 'other', 'host', 'external', 'facts', 'admitted', 'typed', 'valid', 'obligations'}
            if not observed:
                required |= {'modelChildren', 'modelSeed'}
            elif {'cursor', 'modelChildren', 'modelSeed'} & binders.keys():
                raise ValueError('observed constructor fixes child data before preparation: ' + entry)
            if not required <= binders.keys():
                raise ValueError('constructor entry lost general inputs: ' + entry)
            if {'prepared', 'allocated', 'initialized', 'taken', 'completed', 'post'} & binders.keys():
                raise ValueError('constructor entry assumes a successful prefix or final result: ' + entry)
            for name, (root, _) in binders.items():
                constants = invocation.step.constants_below(statement, root)
                if constants & {NS + 'ConstructorPost', NS + 'InvocationPost', NS + 'GraphFrame', NS + 'step',
                                OWNED + 'Semantic.Ensures', ITEM + 'invoke'}:
                    raise ValueError('constructor entry assumes its result: ' + entry + '.' + name)
                if any(part.endswith('Tests') for dep in constants for part in dep.split('.')):
                    raise ValueError('constructor entry depends on fixture premises: ' + entry)
            if not {NS + 'ConstructorPost', NS + 'GraphFrame', NS + 'step'} <= invocation.step.constants_below(statement, conclusion):
                raise ValueError('constructor entry lost attachment to the actual native step: ' + entry)
            root = binders['obligations'][0]
            required = {NS + ('ObservedEntryObligations' if observed else 'EntryObligations')}
            if entry in ('operation', 'local'):
                required |= {ITEM + 'Arguments.Prepared', ITEM + 'Arguments.prepare' if entry == 'operation' else OWNED + 'LocalArguments.zigLocal'}
            if not required <= invocation.step.constants_below(statement, root):
                raise ValueError('constructor entry lost actual preparation or local suffix obligations: ' + entry)
        local = statements[NS + ('step_local_verified_observed' if observed else 'step_local_verified')]
        binders, _, _ = invocation.domains(local)
        root, context = binders['inside']
        guard = local['nodes'][root][3]
        head, args = invocation.applied(local, guard)
        if (head[:2] != ['const', 'Eq'] or len(args) != 3
                or invocation.named(local, args[-2], context) != 'first'
                or invocation.named(local, args[-1], context) != 'Bool.true'):
            raise ValueError('local selected-index bound lost its actual overwrite guard')
    return {'checkedEntries': list(ENTRIES), 'checkedObservedEntries': list(ENTRIES),
            'nativeWords': native_words.audit_statements(rows, interfaces),
            'jointItem': joint.audit_statements(rows, interfaces),
            'jointEntries': joint_entries.audit_statements(rows, interfaces),
            'finiteJointEntries': finite_joint.audit_statements(rows, interfaces),
            'entryReplayChoice': replay_choice.audit_statements(rows, interfaces),
            'enclosingFrames': enclosing.audit_statements(rows, interfaces),
            'sourceChildren': source_children.audit_statements(rows, interfaces),
            'uniformChildren': uniform_children.audit_statements(rows, interfaces),
            'constantDispatch': constant_dispatch.audit_statements(rows, interfaces),
            'algebraicDispatch': algebraic_dispatch.audit_statements(rows, interfaces),
            'unaryDispatch': unary_dispatch.audit_statements(rows, interfaces),
            'prefixDispatch': prefix_dispatch.audit_statements(rows, interfaces),
            'comparisonDispatch': comparison_dispatch.audit_statements(rows, interfaces),
            'divisionDispatch': division_dispatch.audit_statements(rows, interfaces),
            'signextendDispatch': signextend_dispatch.audit_statements(rows, interfaces),
            'nativeStepBuilder': step_builder.audit_statements(rows, interfaces),
            'nativeEntryMiss': native_entry.audit_statements(rows, interfaces),
            'constantEntryFrames': constant_entry.audit_statements(rows, interfaces),
            'preparationCoverage': preparation_coverage.audit_statements(rows, interfaces),
            'insertionCoverage': insertion_coverage.audit_statements(rows, interfaces),
            'nativeFrameStep': native_frame_step.audit_statements(rows, interfaces),
            'nativeFrameInduction': native_frame_induction.audit_statements(rows, interfaces),
            'nativeAllocationTrace': allocation_trace.audit_statements(rows, interfaces),
            'nativeAllocationEntry': allocation_entry.audit_statements(rows, interfaces),
            'nativeCallerResource': caller_resource.audit_statements(rows, interfaces),
            'nativeResourceEntry': resource_entry.audit_statements(rows, interfaces),
            'checkpointEntry': checkpoint_entry.audit_statements(rows, interfaces),
            'checkpointConstructor': checkpoint_constructor.audit_statements(rows, interfaces),
            'checkpointBody': checkpoint_body.audit_statements(rows, interfaces),
            'checkpointBodyEntry': checkpoint_body_entry.audit_statements(rows, interfaces),
            'checkpointHistory': checkpoint_history.audit_statements(rows, interfaces),
            'recursiveReplay': recursive_replay.audit_statements(rows, interfaces),
            'recursiveWords': recursive_words.audit_statements(rows, interfaces),
            'recursiveConstructors': recursive_constructors.audit_statements(rows, interfaces),
            'recursiveInvocation': recursive_invocation.audit_statements(rows, interfaces),
            'hostLift': host_lift.audit_statements(rows, interfaces),
            'nativeForce': native_force.audit_statements(rows, interfaces),
            'nativeFind': native_find.audit_statements(rows, interfaces),
            'nativeFindCaller': native_find_caller.audit_statements(rows, interfaces),
            'resourceAdmission': resource_admission.audit_statements(rows, interfaces),
            'resourceMiss': resource_miss.audit_statements(rows, interfaces),
            'entryObligationsMatchSharedInvocation': True, 'childDataChosenAtReachedMiss': True,
            'successfulPreparationNotAssumed': True, 'actualNativeStepAttached': True,
            'allConstructorEntryPreservationVerified': True, 'completeStreamCorrespondenceVerified': False,
            'recursiveInductionVerified': False, 'composedProductionTheoremVerified': False}


def audit(claims):
    required = {
        'EntryObligations.observed': {NS + 'TakenObligations.observed', NS + 'ObservedEntryObligations'},
        'ObservedEntryObligations.verified': {NS + 'step_invocation_verified_observed'},
        'EntryObligations.verified': {NS + 'ObservedEntryObligations.verified', NS + 'EntryObligations.observed'},
        'InvocationPost.project': {NS + 'InvocationPost', NS + 'ConstructorPost'},
        'InvocationPost.unwind': {NS + 'InvocationPost', NS + 'ConstructorPost', OWNED + 'NativeGraph.Facts.cleanup', OWNED + 'TemporaryArguments.unwind'},
        'InvocationPost.returned': {NS + 'InvocationPost.project', NS + 'InvocationPost.unwind', ITEM + 'Arguments.returned'},
        'prepared_invocation_verified_observed': {NS + 'ObservedEntryObligations.verified', OWNED + 'NativeGraph.Facts.frame', ITEM + 'Arguments.Prepared.key_apart'},
        'prepared_invocation_verified': {NS + 'prepared_invocation_verified_observed', NS + 'EntryObligations.observed'},
        'literal_error_nonordinary': {OWNED + name for name in ('TemporaryUnary.prepare_verified', 'TemporaryArguments.prepare_verified', 'TemporaryTernary.prepare_verified')},
        'local_error_nonordinary': {OWNED + 'LocalArguments.prepare_verified'},
        'step_borrowed_verified_observed': {NS + 'ObservedEntryObligations.verified', NS + 'InvocationPost.project'},
        'step_constant_verified_observed': {NS + 'ObservedEntryObligations.verified', NS + 'InvocationPost.project'},
        'step_materialize_verified_observed': {NS + 'step_constant_verified_observed'},
        'step_operation_verified_observed': {NS + 'prepared_invocation_verified_observed', ITEM + 'Arguments.operation_entry', ITEM + 'Arguments.error_nonordinary', NS + 'InvocationPost.returned', ITEM + 'Arguments.prepare_success', ITEM + 'Arguments.operation_prepared', ITEM + 'Arguments.operation_rejected'},
        'step_local_verified_observed': {NS + 'prepared_invocation_verified_observed', ITEM + 'ViewInput.local_entry', OWNED + 'LocalArguments.error_nonordinary', NS + 'InvocationPost.unwind', ITEM + 'ViewInput.local_input_optional', ITEM + 'ViewInput.local_forwarded', ITEM + 'ViewInput.local_prepared', ITEM + 'ViewInput.local_rejected'},
    }
    for entry in ENTRIES:
        required['step_' + entry + '_verified'] = {NS + 'step_' + entry + '_verified_observed', NS + 'EntryObligations.observed'}
    for name, dependencies in required.items():
        if missing := dependencies - claims[NS + name]:
            raise ValueError('constructor proof lost its shared source reasoning: ' + name + ': ' + ', '.join(sorted(missing)))
        if any(part.endswith('Tests') for dep in claims[NS + name] for part in dep.split('.')):
            raise ValueError('constructor proof depends on a fixture: ' + name)
    return {'checkedDependencies': [NS + name for name in required], 'allConstructorEntryPreservationVerified': True,
            'nativeWords': native_words.audit(claims),
            'jointItem': joint.audit(claims),
            'jointEntries': joint_entries.audit(claims),
            'finiteJointEntries': finite_joint.audit(claims),
            'entryReplayChoice': replay_choice.audit(claims),
            'enclosingFrames': enclosing.audit(claims),
            'sourceChildren': source_children.audit(claims),
            'uniformChildren': uniform_children.audit(claims),
            'constantDispatch': constant_dispatch.audit(claims),
            'algebraicDispatch': algebraic_dispatch.audit(claims),
            'unaryDispatch': unary_dispatch.audit(claims),
            'prefixDispatch': prefix_dispatch.audit(claims),
            'comparisonDispatch': comparison_dispatch.audit(claims),
            'divisionDispatch': division_dispatch.audit(claims),
            'signextendDispatch': signextend_dispatch.audit(claims),
            'nativeStepBuilder': step_builder.audit(claims),
            'nativeEntryMiss': native_entry.audit(claims),
            'constantEntryFrames': constant_entry.audit(claims),
            'preparationCoverage': preparation_coverage.audit(claims),
            'insertionCoverage': insertion_coverage.audit(claims),
            'nativeFrameStep': native_frame_step.audit(claims),
            'nativeFrameInduction': native_frame_induction.audit(claims),
            'nativeAllocationTrace': allocation_trace.audit(claims),
            'nativeAllocationEntry': allocation_entry.audit(claims),
            'nativeCallerResource': caller_resource.audit(claims),
            'nativeResourceEntry': resource_entry.audit(claims),
            'checkpointEntry': checkpoint_entry.audit(claims),
            'checkpointConstructor': checkpoint_constructor.audit(claims),
            'checkpointBody': checkpoint_body.audit(claims),
            'checkpointBodyEntry': checkpoint_body_entry.audit(claims),
            'checkpointHistory': checkpoint_history.audit(claims),
            'recursiveReplay': recursive_replay.audit(claims),
            'recursiveWords': recursive_words.audit(claims),
            'recursiveConstructors': recursive_constructors.audit(claims),
            'recursiveInvocation': recursive_invocation.audit(claims),
            'hostLift': host_lift.audit(claims),
            'nativeForce': native_force.audit(claims),
            'nativeFind': native_find.audit(claims),
            'nativeFindCaller': native_find_caller.audit(claims),
            'resourceAdmission': resource_admission.audit(claims),
            'resourceMiss': resource_miss.audit(claims),
            'completeStreamCorrespondenceVerified': False, 'recursiveInductionVerified': False,
            'composedProductionTheoremVerified': False}


def mutation_cases():
    raw = (invocation.harness.ROOT / 'lean/Compiler/Extraction/InternerNativeConstructors.lean').read_text()
    preparation = (invocation.harness.ROOT / 'lean/Compiler/Extraction/InternerArgumentPreparationFailure.lean').read_text()
    source = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
    source += '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(preparation) + without_imports(raw)
    source = re.sub(r'\berror_nonordinary\b', 'error_nonordinaryMutation', source)
    mutations = [
        ('shift-reached-child-cursor', '∃ cursor modelChildren, TakenObligationsAt cursor safety',
         '∃ (cursor : World (Publication.Effects σ) → Nat), ∃ modelChildren, TakenObligationsAt (fun world => cursor world + 1) safety', 1),
        ('rewind-observed-adapter', '(fun world => world.graph.allocationCursor), modelChildren,',
         '(fun _ => 0), modelChildren,', 1),
        ('admit-rejected-constructor', 'ordinary actual.1 = true → frame actual.2', 'ordinary actual.1 = false → frame actual.2', 1),
        ('lose-parent-frame', 'ordinary actual.1 = true → frame actual.2', 'ordinary actual.1 = true → ¬frame actual.2', 1),
        ('rewind-constructor-word', 'Semantic.Ensures meaning before actual.1 actual.2.graph', 'Semantic.Ensures meaning before actual.1 before', 1),
        ('invent-constructor-word', 'Semantic.Ensures meaning before actual.1 actual.2.graph\n      (fun id after => after.read id = some expected)', 'Semantic.Ensures meaning before actual.1 actual.2.graph\n      (fun id after => after.read id = some (expected + 1))', 1),
        ('cleanup-live-owner', '(mark : Nat) (older : owner < mark)', '(mark : Nat) (older : owner ≤ mark)', 2),
        ('wrong-unwind-mark', '(TemporaryArguments.unwind mark actual) value', '(TemporaryArguments.unwind (mark + 1) actual) value', 1),
        ('wrong-return-mark', '(Arguments.returned values mark actual) value', '(Arguments.returned values (mark + 1) actual) value', 1),
        ('retire-without-parent-law', 'memory := Compiler.ZigAir.Memory.cleanup mark world.memory.memory } })', 'memory := world.memory.memory } })', 2),
        ('literal-rejection-is-ordinary', 'ordinary (.error fault : Except Fault NodeId) = false := by', 'ordinary (.error fault : Except Fault NodeId) = true := by', 2),
        ('wrong-local-index-guard', '(inside : first = true → selected < slice.items.length)', '(inside : first = false → selected < slice.items.length)', 2),
        ('wrong-borrowed-source', '(represented : Represents before.memory.memory (view slice) slice.items)', '(represented : Represents before.memory.memory (view slice) [])', 4),
        ('wrong-borrowed-address', '.borrowedOperation slice.address opcode slice.items debug before)', '.borrowedOperation (slice.address + 1) opcode slice.items debug before)', 2),
        ('wrong-constant-word', '.constant value debug before) value', '.constant value debug before) (value + 1)', 2),
        ('wrong-materialized-word', '.materialize id value debug before) value', '.materialize id value debug before) (value + 1)', 2),
        ('wrong-literal-opcode', '(evaluated : (Interner.constructorCode.operationRequest opcode values).item.eval', '(evaluated : (Interner.constructorCode.operationRequest (opcode + 1) values).item.eval', 2),
        ('wrong-local-overwrite', '(Interner.constructorCode.operationRequest opcode (if first then slice.items.set selected repeated else slice.items))\n        debug prepared', '(Interner.constructorCode.operationRequest opcode (if !first then slice.items.set selected repeated else slice.items))\n        debug prepared', 2),
        ('wrong-literal-observation', 'Arguments.prepare values before = (.ok source, prepared) →', 'Arguments.prepare [] before = (.ok source, prepared) →', 2),
        ('wrong-local-observation', 'LocalArguments.zigLocal (view slice) selected repeated first before = (.ok source, prepared) →', 'LocalArguments.zigLocal (view slice) selected repeated (!first) before = (.ok source, prepared) →', 2),
    ]
    return source, mutations


def controls(output, env, lean):
    source, mutations = mutation_cases()
    records = checked_controls(output, [mutation_check(output, 'constructors-unchanged', source, True, env, lean)])
    for name, before, after, count in mutations:
        if source.count(before) != count:
            raise ValueError('ambiguous constructor control: ' + name)
        records += checked_controls(output, [mutation_check(output, 'constructors-' + name,
            source.replace(before, after), False, env, lean)])
    return (records + native_words.controls(output, env, lean) + joint.controls(output, env, lean)
            + joint_entries.controls(output, env, lean) + finite_joint.controls(output, env, lean)
            + replay_choice.controls(output, env, lean) + enclosing.controls(output, env, lean) + native_frame_induction.controls(output, env, lean) + allocation_trace.controls(output, env, lean) + allocation_entry.controls(output, env, lean) + caller_resource.controls(output, env, lean) + resource_entry.controls(output, env, lean)
            + checkpoint_entry.controls(output, env, lean)
            + checkpoint_constructor.controls(output, env, lean)
            + checkpoint_body.controls(output, env, lean)
            + checkpoint_body_entry.controls(output, env, lean)
            + checkpoint_history.controls(output, env, lean)
            + recursive_replay.controls(output, env, lean)
            + recursive_words.controls(output, env, lean)
            + recursive_constructors.controls(output, env, lean)
            + recursive_invocation.controls(output, env, lean)
            + host_lift.controls(output, env, lean)
            + native_force.controls(output, env, lean)
            + native_find.controls(output, env, lean)
            + native_find_caller.controls(output, env, lean)
            + source_children.controls(output, env, lean) + uniform_children.controls(output, env, lean)
            + constant_dispatch.controls(output, env, lean) + algebraic_dispatch.controls(output, env, lean) + unary_dispatch.controls(output, env, lean) + prefix_dispatch.controls(output, env, lean) + comparison_dispatch.controls(output, env, lean) + division_dispatch.controls(output, env, lean) + signextend_dispatch.controls(output, env, lean) + step_builder.controls(output, env, lean) + native_entry.controls(output, env, lean) + constant_entry.controls(output, env, lean) + preparation_coverage.controls(output, env, lean) + insertion_coverage.controls(output, env, lean) + native_frame_step.controls(output, env, lean) + resource_admission.controls(output, env, lean) + resource_miss.controls(output, env, lean))
