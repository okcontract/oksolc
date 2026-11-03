"""Audit all-entry composition of an actual native recursive miss.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
import constructor_replay_choice_checks as choice
import native_step_builder_checks as builder
from native_algebraic_dispatch_checks import source
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check

NS, OWNED, ITEM = gate.NS, gate.OWNED, gate.ITEM
SITE = ITEM + 'ProtocolTrace.TakenSite.Reached.'
CLAIMS = [SITE + name for name in ('native_inputs', 'key_value', 'return_verified')]
CLAIMS += [NS + name for name in ('taken_miss_verified_cursor', 'step_invocation_verified_miss',
                                  'signextend_request_key', 'invocation_signextend_unfold_verified')]
INTERFACES = ()


def audit(claims):
    required = {
        SITE + 'native_inputs': {NS + 'CallFrame.caller', OWNED + 'NativeGraph.Facts.frame', ITEM + 'prepare_success'},
        SITE + 'key_value': {'Compiler.Extraction.InsertionSort.normalize_word', 'Compiler.Extraction.Interner.makeKey_sound'},
        SITE + 'return_verified': {ITEM + 'invoke_after_take', NS + 'FramePost.locals'},
        NS + 'taken_miss_verified_cursor': {NS + 'CallFrame.dispatch_verified_cursor', NS + 'miss_frame', NS + 'miss_words'},
        NS + 'invoke_step_verified_cursor': {NS + 'taken_miss_verified_cursor', SITE + 'return_verified', SITE + 'key_value'},
        NS + 'step_invocation_verified_miss': {SITE + 'return_verified', NS + 'GraphFrame.locals', NS + 'invocation_entry',
            NS + 'EntryLeaf.parent', NS + 'EntryLeaf.words',
            ITEM + 'caller_input', ITEM + 'prepare_scratch'},
        NS + 'step_invocation_verified_observed': {NS + 'step_invocation_verified_miss', NS + 'taken_miss_verified_cursor',
            SITE + 'native_inputs', SITE + 'key_value'},
        NS + 'invocation_signextend_unfold_verified': {NS + 'step_invocation_verified_miss', NS + 'miss_signextend_unfold_verified',
            SITE + 'native_inputs', SITE + 'key_value', NS + 'signextend_request_key', NS + 'Enclosing.native_miss_frames',
            NS + 'Enclosing.retained', NS + 'Enclosing.locals', NS + 'StepEntryFrames.of_operations'},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('native entry lost shared composition: ' + name + ': ' + ', '.join(sorted(missing)))
    for name in CLAIMS:
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('native entry depends on a fixture: ' + name)
    return {'checkedDependencies': sorted(required), 'nativeAndObservedEntriesShareAllRoutes': True,
            'actualNativeMissConsumedAtEntry': True, 'sourceKeySelectionDerived': True,
            'lowerChildEntryObligationsDischarged': False, 'resourceAdmissionDerived': False, 'recursiveInductionVerified': False}


def conclusion(value):
    root, context = value['root'], []
    while value['nodes'][root][0] == 'forall':
        node = value['nodes'][root]
        context.append(node[1])
        root = node[4]
    return root, context


def binders(value, root, context, count):
    for _ in range(count):
        node = value['nodes'][root]
        if node[0] != 'forall':
            raise ValueError('native entry lost a reached-site guard')
        context = context + [node[1]]
        root = node[4]
    return root, context


def audit_statements(rows, interfaces):
    from native_constructor_checks import expression
    from native_miss_frame_checks import replace_names
    statements = {row['theorem']: row['statement'] for row in rows}
    value = statements[NS + 'step_invocation_verified_miss']
    fields, _, _ = gate.domains(value)
    observed = statements[NS + 'step_invocation_verified_observed']
    old_fields, _, _ = gate.domains(observed)
    if set(fields) != (set(old_fields) - {'takenObligations'}) | {'takenMiss'}:
        raise ValueError('native entry changed initial inputs or assumes entry success')
    for field in old_fields.keys() & fields.keys():
        term, context = fields[field]
        old_term, old_context = old_fields[field]
        if expression(value, term, context) != expression(observed, old_term, old_context):
            raise ValueError('native entry changed an existing premise: ' + field)
    if expression(value, *conclusion(value)) != expression(observed, *conclusion(observed)):
        raise ValueError('native entry lost an invocation or borrowed-constructor conclusion')
    term, context = fields['takenMiss']
    after_site, local = binders(value, term, context, 1)
    reached = value['nodes'][after_site][3]
    args = joint.app(value, reached, SITE[:-1])
    builder.args_named(value, args[-6:], local, ('base', 'source', 'request', 'debug', 'before', 'site'), 'actual reached site')
    body, local = binders(value, term, context, 2)
    reference = statements[SITE + 'return_verified']
    reference_fields, _, _ = gate.domains(reference)
    ref_term, ref_context = reference_fields['checked']
    valid, valid_context = fields['valid']
    meaning = joint.app(value, valid, 'Compiler.Extraction.Interner.Invariant')[-2]
    post, post_context = choice.one_call(value, *conclusion(value), NS + 'InvocationPost')
    replacements = {'meaning': expression(value, meaning, valid_context), 'frame': expression(value, post[-4], post_context)}
    if expression(value, body, local) != replace_names(expression(reference, ref_term, ref_context), replacements):
        raise ValueError('entry requires a different miss than the shared return consumes')

    native = statements[NS + 'invocation_signextend_unfold_verified']
    inputs, _, _ = gate.domains(native)
    expected = {'σ', 'ops', 'allocate', 'safety', 'owner', 'usizeBits', 'base', 'growth', 'env', 'other', 'debug', 'source',
                'request', 'before', 'rows', 'parent', 'depth', 'stack', 'initial', 'data', 'capacity', 'facts', 'represented',
                'privateSource', 'array', 'admitted', 'typed', 'pushes', 'literals', 'left', 'right', 'kind', 'instruction',
                'arguments', 'expected', 'valid', 'evaluated', 'operations'}
    if set(inputs) != expected:
        raise ValueError('native entry gained a current-entry model, outcome or successful-prefix premise')
    forbidden = {NS + name for name in ('InvocationPost', 'TakenObligationsAt', 'MissFrames', 'MissWords', 'ConstructorPost')}
    forbidden |= {'Compiler.Extraction.Dispatch.Effects.SourceConstructorsAt', 'Compiler.Extraction.Interner.Primitives'}
    for name, (term, _) in inputs.items():
        if forbidden & gate.step.constants_below(native, term):
            raise ValueError('native entry assumes a derived contract: ' + name)
    key = statements[NS + 'signextend_request_key']
    key_fields, _, _ = gate.domains(key)
    for field in ('kind', 'instruction', 'arguments'):
        if expression(native, *inputs[field]) != expression(key, *key_fields[field]):
            raise ValueError('native entry lost source key selection: ' + field)
    guarded, guard_context = binders(native, *inputs['operations'], 2)
    guard = joint.app(native, native['nodes'][guarded][3], 'Eq')
    joint.path(native, guard[-2], guard_context, (ITEM + 'ProtocolTrace.TakenSite.deterministic',), 'site')
    builder.args_named(native, guard[-1:], guard_context, ('Bool.true',), 'actual simplifying branch')
    root, local = binders(native, *inputs['operations'], 3)
    args = joint.app(native, root, NS + 'StepEntryFrames.Operations')
    builder.native_base(native, args[-6], local)
    builder.recursive_children(native, args[-5], local, False)
    frame_args = joint.app(native, args[-1], NS + 'CallFrame')
    builder.args_named(native, frame_args[:2], local, ('σ', 'safety'), 'proper-child native mode')
    joint.path(native, frame_args[2], local, (ITEM + 'ShiftInput.Context.allocator',), 'base')
    builder.args_named(native, frame_args[3:6], local, ('owner', 'rows', 'source'), 'proper-child caller geometry')
    joint.path(native, frame_args[6], local, ('Compiler.Extraction.Interner.Request.arguments',), 'request')
    joint.path(native, frame_args[7], local, (ITEM + 'ProtocolTrace.TakenSite.normalized',), 'site')
    joint.path(native, frame_args[8], local, (ITEM + 'ProtocolTrace.TakenSite.address',), 'site')
    native_input = joint.app(native, frame_args[9], ITEM + 'input')
    joint.path(native, native_input[-2], local, ('Compiler.Extraction.Interner.Request.item',), 'request')
    builder.args_named(native, native_input[-1:], local, ('debug',), 'proper-child caller debug')
    builder.args_named(native, frame_args[-1:], local, ('parent',), 'proper-child caller parent')
    result, result_context = conclusion(native)
    children = native['nodes'][result]
    if children[:2] != ['let', 'children']:
        raise ValueError('native entry lost its actual successor children')
    builder.recursive_children(native, children[3], result_context, True)
    if not {NS + 'InvocationPost', NS + 'step', ITEM + 'invoke', OWNED + 'Semantic.Ensures'} <= gate.step.constants_below(native, result):
        raise ValueError('native entry lost its complete native execution')
    return {'sameInitialInputsAndAllEntryConclusions': True, 'localMissMatchesSharedReturn': True,
            'originalSourceKeyAndProperDepthBound': True, 'insertionFramePremiseRemoved': True, 'currentEntryChildModelRequired': False,
            'lowerChildEntryObligationsDischarged': False, 'resourceAdmissionDerived': False, 'recursiveInductionVerified': False}


def controls(output, env, lean):
    groups = (
        ('native-entry-site', 'Compiler.Extraction.InternerTakenSite', (
            ('wrong-scratch-mark', 'site.constructed.memory.memory.nextId framed locals', '(site.constructed.memory.memory.nextId + 1) framed locals', 1),
            ('rewind-returned-graph', 'FramePost frame actual ∧ Semantic.Ensures meaning before.graph actual.1 actual.2.world.graph',
             'FramePost frame actual ∧ Semantic.Ensures meaning before.graph actual.1 before.graph', 1),
            ('wrong-key-value', 'site.key.eval (Dispatch.wordDispatchMeaning env other) site.taken.world.graph.read = some expected',
             'site.key.eval (Dispatch.wordDispatchMeaning env other) site.taken.world.graph.read = some (expected + 1)', 1),
        )),
        ('native-entry-consumer', 'Compiler.Extraction.InternerNativeStepEntry', (
            ('wrong-key-order', 'key.arguments = [left, right] ∧', 'key.arguments = [right, left] ∧', 1),
            ('wrong-selected-arguments', 'takenFacts site.key left right selection.1', 'takenFacts site.key right left selection.1', 1),
            ('same-depth-execution', '(depth + 1)', 'depth', 4),
            ('wrong-child-guard', '      site.deterministic = true →\n      StepEntryFrames.Operations',
             '      site.deterministic = false →\n      StepEntryFrames.Operations', 1),
            ('missing-original-parent', '(initial : parent before)', '(initial : True)', 1),
            ('missing-item-kind', '(kind : request.item.kind = 1)', '(kind : True)', 2),
        )),
    )
    records = []
    for label, module, changes in groups:
        original = source(module)
        records += checked_controls(output, [mutation_check(output, label + '-unchanged', original, True, env, lean)])
        for name, before, after, count in changes:
            if original.count(before) != count:
                raise ValueError('ambiguous native entry mutation: ' + name + ': ' + str(original.count(before)))
            records += checked_controls(output, [mutation_check(output, label + '-' + name, original.replace(before, after), False, env, lean)])
    return records
