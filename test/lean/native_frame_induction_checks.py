"""Audit finite native frame induction independently of resource/word replay.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
import constructor_replay_choice_checks as choice
import native_frame_step_checks as step
from native_miss_frame_checks import named
from native_algebraic_dispatch_checks import source
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check

NS, ITEM, OWNED = gate.NS, gate.ITEM, gate.OWNED
STORAGE = 'Compiler.Extraction.Storage.'
TESTS = ITEM + 'NativeFrameInductionTests.'
CLAIMS = [STORAGE + 'operation_after_append', OWNED + 'NativeGraph.Facts.source_after_append',
          ITEM + 'Arguments.operation_entry', ITEM + 'ViewInput.local_entry']
CLAIMS += [NS + n for n in ('FramePost.project', 'FramePost.unwind', 'FramePost.returned',
    'Enclosing.prepared_frame', 'Enclosing.constant_frame', 'Enclosing.materialize_frame',
    'Enclosing.operation_frame', 'Enclosing.local_frame', 'Enclosing.unfold_frames',
    'Enclosing.unfold_invocation_frame')]
CLAIMS += [TESTS + 'parent_retained', TESTS + 'shifted_parent_retained']
INTERFACES = (NS + 'ProperFrames',)


def audit(claims):
    required = {
        STORAGE + 'operation_after_append': {STORAGE + 'operation_found', STORAGE + 'operation_correct'},
        OWNED + 'NativeGraph.Facts.source_after_append': {STORAGE + 'operation_after_append',
            OWNED + 'BorrowedQuery.Native.observed', OWNED + 'BorrowedQuery.slice_sound',
            OWNED + 'ArraySource.registered', OWNED + 'NativeGraph.Facts.apart'},
        ITEM + 'Arguments.operation_entry': {ITEM + 'Arguments.' + n for n in
            ('error_nonordinary', 'prepare_success', 'operation_prepared', 'operation_rejected')},
        ITEM + 'ViewInput.local_entry': {OWNED + 'LocalArguments.error_nonordinary'} |
            {ITEM + 'ViewInput.' + n for n in ('local_forwarded', 'local_input_optional', 'local_prepared', 'local_rejected')},
        NS + 'FramePost.unwind': {OWNED + 'NativeGraph.Facts.cleanup', OWNED + 'TemporaryArguments.unwind'},
        NS + 'FramePost.returned': {NS + 'FramePost.project', NS + 'FramePost.unwind'},
        NS + 'InvocationPost.unwind': {NS + 'FramePost.unwind'},
        NS + 'step_operation_verified_observed': {ITEM + 'Arguments.operation_entry'},
        NS + 'step_local_verified_observed': {ITEM + 'ViewInput.local_entry'},
        NS + 'Enclosing.prepared_frame': {NS + 'prepared_input_frame', NS + 'Enclosing.retained', NS + 'Enclosing.invocation_frame'},
        NS + 'Enclosing.constant_frame': {NS + 'Enclosing.invocation_frame'},
        NS + 'Enclosing.materialize_frame': {NS + 'Enclosing.constant_frame'},
        NS + 'Enclosing.operation_frame': {ITEM + 'Arguments.operation_entry', NS + 'Enclosing.prepared_frame',
            NS + 'FramePost.returned', NS + 'Enclosing.cleanup'},
        NS + 'Enclosing.local_frame': {ITEM + 'ViewInput.local_entry', NS + 'Enclosing.prepared_frame',
            NS + 'FramePost.unwind', NS + 'Enclosing.cleanup'},
        NS + 'Enclosing.unfold_frames': {NS + 'unfold', OWNED + 'NativeGraph.Facts.source_after_append'} |
            {NS + 'Enclosing.' + n for n in ('operation_frame', 'constant_frame', 'materialize_frame', 'invocation_frame', 'local_frame')},
        NS + 'Enclosing.unfold_invocation_frame': {NS + 'Enclosing.unfold_frames', NS + 'Enclosing.invocation_frame'},
        TESTS + 'parent_retained': {NS + 'Enclosing.unfold_frames'} |
            {ITEM + 'NativeAllocationAdmissionTests.' + n for n in ('admitted_frame', 'successful', 'refused')},
        TESTS + 'shifted_parent_retained': {NS + 'Enclosing.unfold_frames'} |
            {ITEM + 'NativeAllocationIdentityTests.' + n for n in ('before_frame', 'native_result')},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('native frame induction lost composition: ' + name + ': ' + ', '.join(sorted(missing)))
    for name in CLAIMS:
        if not name.startswith(TESTS) and any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('native frame induction depends on fixtures: ' + name)
    return {'checkedDependencies': sorted(required), 'properChildFrameInductionClosed': True,
            'allEntryFrameInductionVerified': True, 'sharedPreparationAndReturnConsumed': True,
            'resourceAdmissionDerived': False, 'recursiveWordPreservationVerified': False,
            'composedProductionTheoremVerified': False}


def audit_statements(rows, interfaces):
    from native_constructor_checks import expression
    statements = {r['theorem']: r['statement'] for r in rows}
    definitions = {r['name']: r for r in interfaces}
    proper = definitions[NS + 'ProperFrames']['value']
    _, body, scope = gate.domains(proper)
    frame, local = step.frame_children(proper, (body, scope))
    named(proper, frame[3:6], local, ('owner', 'rows', 'source'))
    joint.path(proper, frame[6], local, ('Compiler.Extraction.Interner.Request.arguments',), 'request')
    for index, member in ((7, 'normalized'), (8, 'address')):
        joint.path(proper, frame[index], local, (step.SITE + member,), 'site')
    named(proper, frame[-1:], local, ('parent',))
    reached, local = choice.one_call(proper, proper['root'], [], step.SITE + 'Reached')
    named(proper, reached[-6:], local, ('base', 'source', 'request', 'debug', 'before', 'site'))
    value = statements[NS + 'Enclosing.unfold_frames']
    fields, root, context = gate.domains(value)
    wanted = {'σ', 'ops', 'allocate', 'safety', 'owner', 'usizeBits', 'base', 'growth', 'meaning', 'debug',
              'depth', 'rows', 'source', 'values', 'normalized', 'address', 'native', 'parent', 'stack', 'admitted', 'typed'}
    if set(fields) != wanted:
        raise ValueError('native induction gained an unproved child/model/result premise: ' + str(set(fields) ^ wanted))
    frame, local = step.frame_children(value, (root, context), recursive=True)
    named(value, frame[:2], local, ('σ', 'safety'))
    joint.path(value, frame[2], local, (step.CONTEXT + 'allocator',), 'base')
    named(value, frame[3:], local, ('owner', 'rows', 'source', 'values', 'normalized', 'address', 'native', 'parent'))
    stack = joint.app(value, fields['stack'][0], NS + 'Enclosing')
    named(value, stack[-3:], fields['stack'][1], ('owner', 'σ', 'parent'))

    original = statements[NS + 'Enclosing.invocation_frame']
    old, old_root, old_context = gate.domains(original)
    for name in fields.keys() & old.keys():
        if expression(value, *fields[name]) != expression(original, *old[name]):
            raise ValueError('native induction changed shared initial admission: ' + name)
    value = statements[NS + 'Enclosing.unfold_invocation_frame']
    fields, root, context = gate.domains(value)
    if set(fields) != (set(old) - {'children', 'proper'}) | {'depth'}:
        raise ValueError('closed native invocation failed to remove the proper-child premise')
    for name in fields.keys() - {'depth'}:
        if expression(value, *fields[name]) != expression(original, *old[name]):
            raise ValueError('closed native invocation changed an initial assumption: ' + name)
    current = joint.app(value, root, NS + 'FramePost')
    previous = joint.app(original, old_root, NS + 'FramePost')
    if expression(value, current[-2], context) != expression(original, previous[-2], old_context):
        raise ValueError('closed native invocation changed its complete frame conclusion')
    invoked = joint.app(value, current[-1], ITEM + 'invoke')
    named(value, invoked[-4:], context, ('source', 'request', 'debug', 'before'))
    selected, local = choice.one_call(value, invoked[-6], context, NS + 'context')
    step.native_base(value, selected[-5], local)
    named(value, selected[-4:-2], local, ('owner', 'usizeBits'))
    step.recursive_children(value, selected[-2], local, False)
    named(value, selected[-1:], local, ('debug',))

    value = statements[OWNED + 'NativeGraph.Facts.source_after_append']
    fields, root, context = gate.domains(value)
    if set(fields) != {'σ', 'safety', 'allocator', 'owner', 'capacity', 'data', 'world', 'before', 'added',
                       'facts', 'id', 'opcode', 'source', 'query'}:
        raise ValueError('borrowed source admission gained a successful native read assumption')
    needed = {'Compiler.ZigAir.Memory.WordArray.Represents', OWNED + 'Caller.SourcePrivate', OWNED + 'ArraySource'}
    if not needed <= gate.step.constants_below(value, root):
        raise ValueError('borrowed source admission lost representation, privacy or array provenance')
    query, local = choice.one_call(value, *fields['query'], STORAGE + 'OperationRead.run')
    named(value, query[-3:], local, ('before', 'id', 'opcode'))
    return {'sameInitialNativeAdmission': True, 'allFiveSourceSelectedConstructors': True,
            'sameFiniteDepthAndDebug': True, 'noChildFrameModelWordOrSuccessAssumption': True,
            'properChildFramePremiseRemovedFromInvocation': True,
            'querySourceAdmissionDerived': True, 'allEntryFrameInductionVerified': True,
            'recursiveWordPreservationVerified': False, 'composedProductionTheoremVerified': False}


def controls(output, env, lean):
    groups = (
        ('source', 'InternerNativeSourceInput', (
            ('wrong-row-prefix', 'Storage.operationProgram.run before id opcode', 'Storage.operationProgram.run added id opcode', 1),
            ('wrong-native-row-domain', '(facts : Facts safety allocator owner data capacity world (before ++ added))',
             '(facts : Facts safety allocator owner data capacity world before)', 1),
        )),
        ('entry', 'InternerConstructorEntry', (
            ('wrong-literal-mark', 'returned values before.memory.memory.nextId', 'returned values (before.memory.memory.nextId + 1)', 1),
            ('wrong-local-mark', 'TemporaryArguments.unwind before.memory.memory.nextId', 'TemporaryArguments.unwind (before.memory.memory.nextId + 1)', 1),
            ('wrong-index-guard', '(inside : first = true → selected < slice.items.length)', '(inside : first = false → selected < slice.items.length)', 1),
        )),
        ('return', 'InternerNativeArgumentReturn', (
            ('cleanup-owner', '(older : owner < mark)', '(older : owner ≤ mark)', 2),
            ('missing-parent-cleanup', 'parent { world with memory := { world.memory with\n      memory := Compiler.ZigAir.Memory.cleanup mark world.memory.memory } }', 'parent world', 2),
        )),
        ('wrappers', 'InternerEnclosingConstructorFrames', (
            ('inactive-children', '(site.deterministic && (request.item.kind == 1)) = true →', '(site.deterministic && (request.item.kind == 1)) = false →', 1),
            ('missing-parent', '(initial : parent before)', '(initial : True)', 5),
            ('wrong-literal-preparation', 'Arguments.prepare values before = (.ok source, prepared)', 'Arguments.prepare [] before = (.ok source, prepared)', 1),
        )),
        ('induction', 'InternerNativeFrameInduction', (
            ('wrong-query-rows', '(Nested.storageReads rows) debug', '(Nested.storageReads []) debug', 1),
            ('missing-debug-typing', '(typed : AssemblyItem.Initializers.DebugTyped debug)', '(typed : True)', 2),
            ('missing-external-admission', '(admitted : Admitted ops.arguments)', '(admitted : True)', 2),
            ('wrong-enclosing-parent', '(stack : Enclosing safety base.allocator owner parent)',
             '(stack : Enclosing safety base.allocator owner (fun _ => True))', 2),
            ('wrong-child-depth', 'ProperFrames safety owner nativeBase (unfold nativeBase owner usizeBits depth)',
             'ProperFrames safety owner nativeBase (unfold nativeBase owner usizeBits (depth + 1))', 1),
            ('missing-source-representation', '(represented : Represents before.memory.memory source request.arguments)', '(represented : True)', 1),
        )),
        ('regression', 'InternerNativeFrameInductionTests', ()),
    )
    records = []
    for group, module, changes in groups:
        code = source('Compiler.Extraction.' + module)
        prefix = 'native-frame-induction-' + group + '-'
        records += checked_controls(output, [mutation_check(output, prefix + 'unchanged', code, True, env, lean)])
        for name, old, new, count in changes:
            if code.count(old) != count:
                raise ValueError('ambiguous frame induction control: ' + name + ': ' + str(code.count(old)))
            records += checked_controls(output, [mutation_check(output, prefix + name, code.replace(old, new), False, env, lean)])
    return records
