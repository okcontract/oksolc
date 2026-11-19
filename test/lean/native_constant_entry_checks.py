"""Audit constant child frames derived through the existing native entry proof.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
import constructor_replay_choice_checks as choice
import native_step_builder_checks as builder
import native_entry_miss_checks as entry
from native_miss_frame_checks import replace_names
from native_algebraic_dispatch_checks import source
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check

NS, OWNED, ITEM = gate.NS, gate.OWNED, gate.ITEM
SITE = ITEM + 'ProtocolTrace.TakenSite.'
CLAIMS = [NS + 'Enclosing.inactive_entry_frames', NS + 'StepEntryFrames.of_operations']
INTERFACES = (NS + 'StepEntryFrames.Operations',)


def audit(claims):
    required = {
        CLAIMS[0]: {NS + 'Enclosing.retained', NS + 'Enclosing.locals', NS + 'Enclosing.native_miss_frames',
                    ITEM + 'prepare_success', 'Compiler.Extraction.Recursive.constructors'},
        CLAIMS[1]: {CLAIMS[0], NS + 'StepEntryFrames.mk'},
        NS + 'invocation_signextend_unfold_verified': {CLAIMS[1], NS + 'miss_signextend_unfold_verified'},
        builder.TESTS + 'capacity_rules': {CLAIMS[1], NS + 'CallFrame.step_rules'},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('constant entry lost shared frame derivation: ' + name + ': ' + ', '.join(sorted(missing)))
    for name in CLAIMS:
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('constant entry depends on a fixture: ' + name)
    return {'checkedDependencies': sorted(required), 'constantEntryFramesDerived': True,
            'existingEntryAndBuilderProofsConsumed': True, 'insertionFramesDerivedBySharedReducer': True,
            'operationChildEntryObligationsDischarged': False, 'resourceAdmissionDerived': False, 'recursiveInductionVerified': False}


def body(value):
    root, context = value['root'], []
    while value['nodes'][root][0] == 'lambda':
        node = value['nodes'][root]
        context.append(node[1])
        root = node[4]
    return root, context


def call_expression(value, root, context, name):
    from native_constructor_checks import expression
    args, local = choice.one_call(value, root, context, name)
    term = name
    for arg in args:
        term = ('app', term, expression(value, arg, local))
    return term


def audit_statements(rows, interfaces):
    from native_constructor_checks import expression
    statements = {row['theorem']: row['statement'] for row in rows}
    definitions = {row['name']: row for row in interfaces}
    original = definitions[NS + 'StepEntryFrames.mk']['type']
    old_fields, _, _ = gate.domains(original)
    operations = definitions[NS + 'StepEntryFrames.Operations']['value']
    if expression(operations, *body(operations)) != expression(original, *old_fields['operation']):
        raise ValueError('constant entry changed the original operation-child duty')

    inactive = statements[CLAIMS[0]]
    inputs, result, context = gate.domains(inactive)
    wanted = {'σ', 'ops', 'allocate', 'safety', 'owner', 'usizeBits', 'base', 'growth', 'children', 'env', 'other', 'debug',
              'source', 'request', 'before', 'rows', 'parent', 'stack', 'initial', 'valid', 'domain', 'admitted', 'typed', 'inactive'}
    if set(inputs) != wanted:
        raise ValueError('inactive entry gained a child model or complete-frame premise')
    args = joint.app(inactive, result, NS + 'EntryFrames')
    builder.native_base(inactive, args[-10], context)
    builder.args_named(inactive, args[-9:], context, ('children', 'source', 'request', 'debug', 'before', 'rows', 'parent', 'env', 'other'), 'derived entry')
    reference = statements[NS + 'Enclosing.native_miss_frames']
    reference_fields, _, _ = gate.domains(reference)
    if expression(inactive, *inputs['initial']) != expression(reference, *reference_fields['initial']):
        raise ValueError('inactive entry lost its original enclosing parent')
    for field in ('inactive',):
        reached_root, reached_context = entry.binders(inactive, *inputs[field], 1)
        reached = joint.app(inactive, inactive['nodes'][reached_root][3], SITE + 'Reached')
        builder.native_base(inactive, reached[-6], reached_context)
        builder.args_named(inactive, reached[-5:], reached_context,
                          ('source', 'request', 'debug', 'before', 'site'), 'actual inactive entry site')
    root, local = entry.binders(inactive, *inputs['inactive'], 2)
    guard = joint.app(inactive, root, 'Eq')
    builder.args_named(inactive, guard[-1:], local, ('Bool.false',), 'inactive source guard')
    taken = definitions[NS + 'TakenFramesAt.mk']['type']
    taken_fields, _, _ = gate.domains(taken)
    term, taken_context = taken_fields['coupled']
    expected = joint.app(taken, taken['nodes'][term][3], 'Eq')
    determinant = call_expression(inactive, root, local, SITE + 'deterministic')
    if expression(inactive, guard[-2], local) != replace_names(expression(taken, expected[-2], taken_context), {'deterministic': determinant}):
        raise ValueError('inactive entry does not exclude the actual child-selection guard')
    derived = statements[CLAIMS[1]]
    inputs, result, context = gate.domains(derived)
    reference = statements[NS + 'step_builder_rules']
    common, _, _ = gate.domains(reference)
    if set(inputs) != (set(common) - {'graphs', 'entries', 'pushes', 'literals'}) | {'operations'}:
        raise ValueError('derived entries gained a child result or lost native inputs')
    for field in inputs.keys() & common.keys():
        if expression(derived, *inputs[field]) != expression(reference, *common[field]):
            raise ValueError('derived entries changed an existing native input: ' + field)
    actual = joint.app(derived, result, NS + 'StepEntryFrames')
    operations = joint.app(derived, inputs['operations'][0], NS + 'StepEntryFrames.Operations')
    if [expression(derived, arg, context) for arg in actual] != [expression(derived, arg, inputs['operations'][1]) for arg in operations]:
        raise ValueError('derived entries use different native callbacks or caller frames')
    consumer = statements[NS + 'invocation_signextend_unfold_verified']
    inputs, _, _ = gate.domains(consumer)
    if {'entries', 'constantInsertion', 'insertion'} & inputs.keys():
        raise ValueError('native invocation still assumes constant entries or insertion frames')
    return {'operationFieldUnchanged': True, 'originalParentAndInactiveGuardBound': True,
            'residualInsertionPremiseRemoved': True, 'nativeInvocationConsumesDerivedConstantEntry': True,
            'constantChildEntryModelRequired': False, 'operationChildEntryObligationsDischarged': False,
            'resourceAdmissionDerived': False, 'recursiveInductionVerified': False}


def controls(output, env, lean):
    groups = (
        ('native-inactive-entry', 'Compiler.Extraction.InternerNativeInactiveEntry', (
            ('active-child-guard', '(site.deterministic && (request.item.kind == 1)) = false)',
             '(site.deterministic && (request.item.kind == 1)) = true)', 1),
            ('missing-original-parent', '(initial : parent before)', '(initial : True)', 1),
            ('missing-item-domain', '(domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)',
             '(domain : True)', 1),
        )),
        ('native-constant-entry', 'Compiler.Extraction.InternerNativeConstantEntry', (
            ('wrong-constant-value', '(Interner.constructorCode.constantRequest value) before rows ready',
             '(Interner.constructorCode.constantRequest (value + 1)) before rows ready', 1),
            ('wrong-operation-arguments', '(Interner.constructorCode.operationRequest opcode ids)',
             '(Interner.constructorCode.operationRequest opcode ids.reverse)', 1),
            ('capacity-is-not-native-validity', 'ready initial facts.valid', 'ready initial facts.bounded', 1),
        )),
        ('native-constant-consumer', 'Compiler.Extraction.InternerNativeStepEntry', (
            ('wrong-operation-guard', 'site.deterministic = true →\n      StepEntryFrames.Operations',
             'site.deterministic = false →\n      StepEntryFrames.Operations', 1),
            ('wrong-operation-depth', 'StepEntryFrames.Operations safety owner usizeBits nativeBase (unfold nativeBase owner usizeBits depth)',
             'StepEntryFrames.Operations safety owner usizeBits nativeBase (unfold nativeBase owner usizeBits (depth + 1))', 1),
        )),
    )
    records = []
    for label, module, changes in groups:
        original = source(module)
        records += checked_controls(output, [mutation_check(output, label + '-unchanged', original, True, env, lean)])
        for name, before, after, count in changes:
            if original.count(before) != count:
                raise ValueError('ambiguous constant entry mutation: ' + name + ': ' + str(original.count(before)))
            records += checked_controls(output, [mutation_check(output, label + '-' + name, original.replace(before, after), False, env, lean)])
    return records
