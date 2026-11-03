"""Audit native dispatcher and all-entry step frames without a logical child model.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
import constructor_replay_choice_checks as choice
from native_miss_frame_checks import named
from native_algebraic_dispatch_checks import source
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check

NS, OWNED, ITEM = gate.NS, gate.OWNED, gate.ITEM
RECURSIVE = OWNED + 'Recursive.'
EFFECTS = 'Compiler.Extraction.Dispatch.Effects.'
NESTED = 'Compiler.Extraction.Nested.'
SITE = ITEM + 'ProtocolTrace.TakenSite.'
CONTEXT = ITEM + 'ShiftInput.Context.'
CLAIMS = [NS + name for name in (
    'operand_keeps', 'keeping_read_bind', 'source_constructors_keep', 'dispatcher_keeps',
    'CallFrame.dispatch_kept', 'taken_miss_frame', 'invoke_step_frame',
    'Enclosing.taken_invocation_frame', 'Enclosing.taken_borrowed_frame',
    'EntryLeaf.of_native', 'EntryLeaf.parent', 'EntryLeaf.words', 'invocation_entry',
    'Enclosing.invocation_frame', 'Enclosing.borrowed_frame')]
INTERFACES = (NS + 'taken_miss_verified_cursor', NS + 'EntryLeaf.mk')


def audit(claims):
    required = {
        NS + 'operand_keeps': {ITEM + 'ShiftInput.operand'},
        NS + 'dispatcher_keeps': {NS + 'dispatcher_snapshot', NS + 'operand_keeps', NS + 'keeping_read_bind',
                                 EFFECTS + 'simplify_with_inputs_at'},
        NS + 'CallFrame.dispatch_kept': {NS + 'dispatcher_keeps', NS + 'CallFrame.caller', OWNED + 'NativeGraph.Facts.reads'},
        NS + 'taken_miss_frame': {NS + 'CallFrame.dispatch_kept', NS + 'miss_frame'},
        NS + 'invoke_step_frame': {NS + 'taken_miss_frame', NS + 'FramePost.locals', ITEM + 'invoke_after_take'},
        NS + 'invoke_step_frame_at': {NS + 'invoke_step_frame', NS + 'source_constructors_keep'},
        NS + 'step_invocation_verified_observed': {NS + 'taken_miss_frame', NS + 'source_constructors_keep'},
        NS + 'invoke_step_native_verified': {NS + 'taken_miss_frame'},
        NS + 'Enclosing.taken_invocation_frame': {NS + 'invoke_step_frame', NS + 'Enclosing.native_miss_frames',
            SITE + 'Reached.native_inputs', NS + 'GraphFrame.locals', NS + 'Enclosing.locals'},
        NS + 'Enclosing.taken_borrowed_frame': {NS + 'Enclosing.taken_invocation_frame', NS + 'unfold'},
        NS + 'invocation_entry': {ITEM + name for name in ('prepare_success', 'prepare_scratch', 'caller_input',
            'invoke_rejected', 'invoke_init_rejected', 'invoke_classification_rejected', 'invoke_entry_failed_native',
            'invoke_initialized_native', 'invoke_cached_native', 'invoke_take_failed_native')} | {NS + 'EntryLeaf.of_native'},
        NS + 'EntryLeaf.words': {ITEM + 'cached_word'},
        NS + 'step_invocation_verified_miss': {NS + 'invocation_entry', NS + 'EntryLeaf.parent', NS + 'EntryLeaf.words'},
        NS + 'Enclosing.invocation_frame': {NS + 'invocation_entry', NS + 'EntryLeaf.parent', NS + 'Enclosing.taken_invocation_frame'},
        NS + 'Enclosing.borrowed_frame': {NS + 'Enclosing.invocation_frame', NS + 'unfold'},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('native frame step lost composition: ' + name + ': ' + ', '.join(sorted(missing)))
    for name in CLAIMS:
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('native frame step depends on a fixture: ' + name)
    return {'checkedDependencies': sorted(required), 'completeNativeDispatcherFramesDerived': True,
            'existingSemanticConsumersUseNativeFrameStep': True, 'nativeSuffixAndReturnFramesDerived': True,
            'properChildFrameInductionClosed': False, 'allEntryFrameInductionVerified': False,
            'sharedAllEntryFrameStepDerived': True,
            'resourceAdmissionDerived': False, 'recursiveInductionVerified': False}


def native_base(value, term, context):
    args = joint.app(value, term, NS + 'callerContext')
    named(value, args[-7:], context, ('ops', 'allocate', 'safety', 'owner', 'meaning', 'base', 'growth'))


def recursive_children(value, term, context, successor):
    args = joint.app(value, term, NS + 'unfold')
    native_base(value, args[-4], context)
    named(value, args[-3:-1], context, ('owner', 'usizeBits'))
    if successor:
        added, local = choice.one_call(value, args[-1], context, 'HAdd.hAdd')
        named(value, added[-2:-1], local, ('depth',))
        one = joint.app(value, added[-1], 'OfNat.ofNat')
        if gate.named(value, one[-2], local) != ('natural', '1'):
            raise ValueError('native frame step lost successor depth')
    else:
        named(value, args[-1:], context, ('depth',))


def frame_children(value, field, recursive=False):
    args, context = choice.one_call(value, *field, EFFECTS + 'SourceConstructorsAt')
    keeping = joint.app(value, args[-5], RECURSIVE + 'keeping')
    read = joint.app(value, args[-4], NESTED + 'storageReads')
    named(value, read[-1:], context, ('rows',))
    named(value, args[-3:-2], context, ('debug',))
    if recursive:
        for child in args[-2:]:
            recursive_children(value, child, context, False)
    else:
        named(value, args[-2:], context, ('children', 'children'))
    return joint.app(value, keeping[-1], NS + 'CallFrame'), context


def audit_statements(rows, interfaces):
    from native_constructor_checks import expression
    statements = {row['theorem']: row['statement'] for row in rows}
    definitions = {row['name']: row for row in interfaces}
    original = statements[NS + 'invoke_step_frame_at']
    old, old_root, old_context = gate.domains(original)
    value = statements[NS + 'invoke_step_frame']
    fields, root, context = gate.domains(value)
    if set(fields) != (set(old) - {'observe', 'modelChildren', 'dispatchCoupled'}) | {'dispatchFrames'}:
        raise ValueError('native frame step gained a model or lost original inputs')
    for field in fields.keys() - {'dispatchFrames'}:
        if expression(value, *fields[field]) != expression(original, *old[field]):
            raise ValueError('native frame step changed an original input: ' + field)
    if expression(value, root, context) != expression(original, old_root, old_context):
        raise ValueError('native frame step changed the original conclusion')
    new_guard = value['nodes'][fields['dispatchFrames'][0]]
    old_guard = original['nodes'][old['dispatchCoupled'][0]]
    if (new_guard[0] != 'forall' or old_guard[0] != 'forall'
            or expression(value, new_guard[3], fields['dispatchFrames'][1]) !=
            expression(original, old_guard[3], old['dispatchCoupled'][1])):
        raise ValueError('native frame step changed the actual simplification guard')
    frame_children(value, fields['dispatchFrames'])
    relation, local = choice.one_call(value, *fields['dispatchFrames'], EFFECTS + 'SourceConstructorsAt')
    kept = joint.app(value, relation[-5], RECURSIVE + 'keeping')
    coupled, previous = choice.one_call(original, *old['dispatchCoupled'], EFFECTS + 'SourceConstructorsAt')
    projection = joint.app(original, coupled[-5], RECURSIVE + 'projectionAt')
    if expression(value, kept[-1], local) != expression(original, projection[-1], previous):
        raise ValueError('native frame step changed the live caller predicate')

    value = statements[NS + 'CallFrame.dispatch_kept']
    fields, root, context = gate.domains(value)
    original = statements[NS + 'CallFrame.dispatch_at']
    old, old_root, old_context = gate.domains(original)
    if set(fields) != (set(old) - {'observe', 'modelChildren', 'dispatchCoupled'}) | {'dispatchFrames'}:
        raise ValueError('native dispatcher frame gained a model or lost an original input')
    for field in fields.keys() - {'dispatchFrames'}:
        if expression(value, *fields[field]) != expression(original, *old[field]):
            raise ValueError('native dispatcher changed an original input: ' + field)
    first, _ = joint.app(original, old_root, 'And')
    if expression(value, root, context) != expression(original, first, old_context):
        raise ValueError('native dispatcher changed the reached caller frame')
    frame_children(value, fields['dispatchFrames'])

    value = statements[NS + 'taken_miss_frame']
    fields, root, context = gate.domains(value)
    original = definitions[NS + 'taken_miss_verified_cursor']['type']
    old, old_root, old_context = gate.domains(original)
    removed = {'cursor', 'modelChildren', 'dispatchCoupled', 'env', 'other', 'expected', 'suffixWords',
               'correct', 'addresses', 'shifts', 'valid', 'evaluated', 'keyed'}
    if set(fields) != (set(old) - removed) | {'dispatchFrames'}:
        raise ValueError('native miss regained semantic or model obligations')
    for field in fields.keys() - {'dispatchFrames'}:
        if expression(value, *fields[field]) != expression(original, *old[field]):
            raise ValueError('native miss changed an original input: ' + field)
    first, _ = joint.app(original, old_root, 'And')
    if expression(value, root, context) != expression(original, first, old_context):
        raise ValueError('native miss changed the complete owned-miss frame conclusion')

    for name, recursive, all_entry in (('Enclosing.taken_invocation_frame', False, False),
            ('Enclosing.taken_borrowed_frame', True, False), ('Enclosing.invocation_frame', False, True),
            ('Enclosing.borrowed_frame', True, True)):
        value = statements[NS + name]
        fields, root, context = gate.domains(value)
        common = {'σ', 'ops', 'allocate', 'safety', 'owner', 'usizeBits', 'base', 'growth', 'meaning', 'debug', 'rows',
                  'parent', 'before', 'site', 'reached', 'stack', 'initial', 'data', 'capacity', 'facts', 'privateSource',
                  'array', 'admitted', 'typed', 'proper'}
        if all_entry:
            common = (common - {'site', 'reached'}) | {'represented'}
        wanted = common | ({'depth', 'opcode', 'borrowed'} if recursive else {'children', 'source', 'request', 'domain'})
        # The borrowed conclusion adds its ordinary-completion implication.
        if recursive:
            extra = set(fields) - wanted
            if len(extra) != 1:
                raise ValueError('borrowed frame conclusion lost its single ordinary-completion guard')
            guarded, scope = fields[next(iter(extra))]
            eq = joint.app(value, guarded, 'Eq')
            completed = joint.app(value, eq[-2], OWNED + 'ordinary')
            result = joint.app(value, completed[-1], 'Prod.fst')
            named(value, result[-1:], scope, ('actual',))
            named(value, eq[-1:], scope, ('Bool.true',))
            wanted |= extra
        if set(fields) != wanted:
            raise ValueError('enclosing native step changed its admission boundary: ' + name + ': ' + str(set(fields) ^ wanted))
        frame, local = frame_children(value, fields['proper'], recursive)
        named(value, frame[:2], local, ('σ', 'safety'))
        joint.path(value, frame[2], local, (CONTEXT + 'allocator',), 'base')
        named(value, frame[3:5], local, ('owner', 'rows'))
        for index, member in ((7, 'normalized'), (8, 'address')):
            joint.path(value, frame[index], local, (SITE + member,), 'site')
        named(value, frame[-1:], local, ('parent',))
        if all_entry:
            reached, reached_context = choice.one_call(value, *fields['proper'], SITE + 'Reached')
        else:
            reached = joint.app(value, fields['reached'][0], SITE + 'Reached')
            reached_context = fields['reached'][1]
        native_base(value, reached[-6], reached_context)
        named(value, reached[-3:], reached_context, ('debug', 'before', 'site'))
        if expression(value, frame[5], local) != expression(value, reached[-5], reached_context):
            raise ValueError('child frame lost the actual reached source')
        native = joint.app(value, frame[9], ITEM + 'input')
        item = joint.app(value, native[-2], 'Compiler.Extraction.Interner.Request.item')
        if expression(value, item[-1], local) != expression(value, reached[-4], reached_context):
            raise ValueError('child frame lost the reached native item')
        named(value, native[-1:], local, ('debug',))
        if not recursive:
            named(value, frame[5:6], local, ('source',))
            joint.path(value, frame[6], local, ('Compiler.Extraction.Interner.Request.arguments',), 'request')
            named(value, reached[-5:-3], reached_context, ('source', 'request'))
            invoked, scope = choice.one_call(value, root, context, ITEM + 'invoke')
            named(value, invoked[-4:], scope, ('source', 'request', 'debug', 'before'))
            context_call, scope = choice.one_call(value, invoked[-6], scope, NS + 'context')
            native_base(value, context_call[-5], scope)
            named(value, context_call[-4:], scope, ('owner', 'usizeBits', 'children', 'debug'))
        else:
            borrowed, scope = choice.one_call(value, value['root'], [], 'Compiler.Extraction.Associative.Constructors.borrowedOperation')
            recursive_children(value, borrowed[-6], scope, True)
            joint.path(value, borrowed[-5], scope, ('Compiler.Extraction.Storage.ArgumentSlice.address',), 'borrowed')
            named(value, borrowed[-4:-3], scope, ('opcode',))
            joint.path(value, borrowed[-3], scope, ('Compiler.Extraction.Storage.ArgumentSlice.items',), 'borrowed')
            named(value, borrowed[-2:], scope, ('debug', 'before'))
    return {'sameTakenInvocationInputsAndFrameConclusion': True, 'noLogicalChildModelOrObserverRequired': True,
            'nativeSourceQueriesAndCallerDebugBound': True, 'nativeSuffixAndReturnFramesDerived': True,
            'actualSuccessorExecutionAndProperDepthBound': True, 'takenSiteDerivedByAllEntryStep': True,
            'sharedEntryDecomposition': audit_entry_statements(statements, definitions),
            'allEntryFrameInductionVerified': False, 'resourceAdmissionDerived': False}


def audit_entry_statements(statements, definitions):
    from native_constructor_checks import expression
    value = statements[NS + 'invocation_entry']
    fields, root, context = gate.domains(value)
    original = statements[NS + 'step_invocation_verified_miss']
    old, _, _ = gate.domains(original)
    removed = {'parent', 'array', 'env', 'other', 'expected', 'valid', 'evaluated', 'retained', 'localParent', 'takenMiss'}
    wanted = set(old) - removed
    extra = set(fields) - wanted
    if len(extra) != 1 or not wanted <= fields.keys():
        raise ValueError('native entry decomposition changed its initial assumptions')
    for field in wanted:
        if expression(value, *fields[field]) != expression(original, *old[field]):
            raise ValueError('native entry changed an initial input: ' + field)
    guarded, scope = fields[next(iter(extra))]
    eq = joint.app(value, guarded, 'Eq')
    ordinary = joint.app(value, eq[-2], OWNED + 'ordinary')
    result = joint.app(value, ordinary[-1], 'Prod.fst')
    named(value, result[-1:], scope, ('actual',))
    named(value, eq[-1:], scope, ('Bool.true',))
    leaf, taken = joint.app(value, root, 'Or')
    args = joint.app(value, leaf, NS + 'EntryLeaf')
    named(value, args[:2], context, ('σ', 'safety'))
    joint.path(value, args[2], context, (CONTEXT + 'allocator',), 'base')
    named(value, args[3:], context, ('owner', 'rows', 'before', 'request', 'actual'))
    reached, local = choice.one_call(value, taken, context, SITE + 'Reached')
    named(value, reached[-6:], local, ('base', 'source', 'request', 'debug', 'before', 'site'))
    invoked, scope = choice.one_call(value, value['root'], [], ITEM + 'invoke')
    named(value, invoked[-4:], scope, ('source', 'request', 'debug', 'before'))
    selected, scope = choice.one_call(value, invoked[-6], scope, NS + 'context')
    named(value, selected[-5:], scope, ('base', 'owner', 'usizeBits', 'children', 'debug'))

    value = definitions[NS + 'EntryLeaf.mk']['type']
    fields, _, _ = gate.domains(value)
    if set(fields) != {'σ', 'safety', 'allocator', 'owner', 'rows', 'before', 'request', 'actual',
                       'closed', 'frame', 'graph', 'cached'}:
        raise ValueError('native entry leaf changed its observation boundary')
    frame, context = fields['frame']
    args = joint.app(value, frame, NS + 'GraphFrame')
    named(value, args[:5], context, ('σ', 'safety', 'allocator', 'owner', 'rows'))
    retained = joint.app(value, args[-2], NS + 'Retains')
    named(value, retained[-1:], context, ('before',))
    joint.path(value, args[-1], context, (OWNED + 'State.world', 'Prod.snd'), 'actual')
    cached, context = fields['cached']
    cache_guard = value['nodes'][cached]
    if cache_guard[:2] != ['forall', 'id']:
        raise ValueError('entry leaf lost successful result quantification')
    # Inspect the exact result guard and each provenance observation, including
    # their quantified witnesses, instead of accepting a list of constant names.
    local = context + ['id']
    guard = value['nodes'][cache_guard[4]]
    eq = joint.app(value, guard[3], 'Eq')
    joint.path(value, eq[-2], local, ('Prod.fst',), 'actual')
    ok = joint.app(value, eq[-1], 'Except.ok')
    named(value, ok[-1:], local, ('id',))
    for constant, expected in (
            ('Compiler.Extraction.Interner.makeKey', ('request', 'values')),
            ('Compiler.Extraction.Interner.Heap.table', ('key',))):
        args, scope = choice.one_call(value, cached, context, constant)
        named(value, args[-len(expected):], scope, expected)
    normalized, scope = choice.one_call(value, cached, context, 'Compiler.Extraction.Cache.NormalizeCode.run')
    joint.path(value, normalized[-2], scope, ('Compiler.Extraction.Interner.Request.item',), 'request')
    joint.path(value, normalized[-1], scope, ('Compiler.Extraction.Interner.Request.arguments',), 'request')
    return {'noSemanticOrChildContractAtEntry': True, 'actualNativeReturnOrReachedMiss': True,
            'cacheSuccessUsesActualNormalizationAndKey': True}


def controls(output, env, lean):
    groups = (
        ('dispatch', 'Compiler.Extraction.InternerNativeDispatchFrames', (
            ('missing-original-frame', '(initial : predicate before)', '(initial : True)', 1),
            ('wrong-query-owner', '(NativeReads.reads owner before.memory.memory) debug children children)',
             '(NativeReads.reads (owner + 1) before.memory.memory) debug children children)', 1),
            ('missing-proper-children', '(proper : (keeping predicate).SourceConstructorsAt (NativeReads.reads owner before.memory.memory) debug children children)',
             '(proper : True)', 1),
        )),
        ('step', 'Compiler.Extraction.InternerNativeStep', (
            ('inactive-child-frame-guard', '(dispatchFrames : (deterministic && (request.item.kind == 1)) = true →',
             '(dispatchFrames : (deterministic && (request.item.kind == 1)) = false →', 2),
            ('wrong-child-frame-rows', '(keeping (CallFrame safety base.allocator owner rows source request.arguments normalized',
             '(keeping (CallFrame safety base.allocator owner [] source request.arguments normalized', 3),
        )),
        ('entry-leaf', 'Compiler.Extraction.InternerNativeEntryLeaf', (
            ('erase-retained-keys', 'actual.2.world.memory.effects.keys = before.memory.effects.keys',
             'actual.2.world.memory.effects.keys = (fun _ => none)', 1),
            ('wrong-cache-provenance', 'before.graph.table key = some id', 'before.graph.table key = some (id + 1)', 2),
            ('invent-cached-word', '(fun id after => after.read id = some expected)',
             '(fun id after => after.read id = some (expected + 1))', 1),
        )),
        ('entry', 'Compiler.Extraction.InternerNativeEntry', (
            ('admit-rejected-prefix', 'ordinary actual.1 = true →', 'ordinary actual.1 = false →', 1),
            ('missing-source-values', '(represented : Represents before.memory.memory source request.arguments)',
             '(represented : True)', 1),
            ('wrong-source-privacy', '(privateSource : Caller.SourcePrivate source before.memory.effects.keys)',
             '(privateSource : Caller.SourcePrivate ⟨0, 0, 0⟩ before.memory.effects.keys)', 1),
            ('wrong-reached-before', 'site.Reached base source request debug before',
             'site.Reached base source request debug actual.2.world', 2),
        )),
        ('enclosing', 'Compiler.Extraction.InternerEnclosingNativeStepFrame', (
            ('missing-original-parent', '(initial : parent before)', '(initial : True)', 4),
            ('missing-item-domain', '(domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)', '(domain : True)', 2),
            ('wrong-taken-source', '(reached : site.Reached nativeBase source request debug before)',
             '(reached : site.Reached nativeBase ⟨0, 0, 0⟩ request debug before)', 1),
            ('wrong-proper-depth', '(Nested.storageReads rows) debug (unfold nativeBase owner usizeBits depth) (unfold nativeBase owner usizeBits depth))',
             '(Nested.storageReads rows) debug (unfold nativeBase owner usizeBits (depth + 1)) (unfold nativeBase owner usizeBits (depth + 1)))', 2),
            ('wrong-execution-depth', '(unfold nativeBase owner usizeBits (depth + 1)).borrowedOperation',
             '(unfold nativeBase owner usizeBits depth).borrowedOperation', 2),
            ('missing-all-entry-source', '(represented : Represents before.memory.memory source request.arguments)',
             '(represented : True)', 1),
            ('inactive-all-entry-children', '(site.deterministic && (request.item.kind == 1)) = true →',
             '(site.deterministic && (request.item.kind == 1)) = false →', 2),
            ('wrong-child-guard', '(proper : site.deterministic = true →', '(proper : site.deterministic = false →', 1),
        )),
    )
    records = []
    for group, module, changes in groups:
        code = source(module)
        records += checked_controls(output, [mutation_check(output, 'native-frame-' + group + '-unchanged', code, True, env, lean)])
        for name, old, new, count in changes:
            if code.count(old) != count:
                raise ValueError('ambiguous native frame mutation: ' + group + '-' + name + ': ' + str(code.count(old)))
            records += checked_controls(output, [mutation_check(output, 'native-frame-' + group + '-' + name,
                                                                 code.replace(old, new), False, env, lean)])
    return records
