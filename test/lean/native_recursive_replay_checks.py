"""Audit complete finite recursive replay and its retained native boundary.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
from native_miss_frame_checks import named
from native_resource_admission_checks import telescope, local_call
from native_checkpoint_constructor_checks import numeral
from native_algebraic_dispatch_checks import source
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check

NS, ITEM, OWNED = gate.NS, gate.ITEM, gate.OWNED
TRACE = NS + 'AllocationTrace.'
ENTRY = ITEM + 'ProtocolTrace.CheckpointEntry.'
NATIVE_ENTRY = OWNED + 'Caller.ProtocolTrace.Native.CheckpointEntry.'
TESTS = ITEM + 'AllocationRecursiveReplayTests.'
CLAIMS = [TRACE + n for n in ('selected_from_sources', 'checkpoint_step_traced', 'body_replay_from_traced_entry',
          'recursive_sources_zero', 'bodies_from_sources', 'recursive_sources', 'recursive_bodies')]
CLAIMS += [NATIVE_ENTRY + 'miss_from_recursive_sources', ENTRY + 'item_induction_from_sources']
CLAIMS += [ENTRY + n + '_from_sources' for n in ('item', 'operation', 'constant', 'materialize', 'borrowed', 'local')]
CLAIMS += [TESTS + n for n in ('constant_outcomes', 'nested_outcomes')]
INTERFACES = tuple(TRACE + n for n in ('requestModel', 'bodyModels', 'exhaustedModels', 'recursiveModels', 'RecursiveSources'))


def audit(claims):
    required = {
        TRACE + 'selected_from_sources': {OWNED + 'MissStream.selected_resource_preserved',
            OWNED + 'Caller.ProtocolTrace.Native.history_boundaries'},
        TRACE + 'selected_from_bodies': {TRACE + 'selected_from_sources', TRACE + 'step_source_projects'},
        TRACE + 'bodies_from_sources': {NS + 'Enclosing.unfold_frames', TRACE + 'checkpoint_step_traced',
            TRACE + 'body_replay_from_traced_entry', TRACE + 'step_erases',
            *[ENTRY + n + '_from_sources' for n in ('operation', 'constant', 'materialize', 'borrowed', 'local')]},
        TRACE + 'recursive_sources': {TRACE + 'recursive_sources_zero', TRACE + 'bodies_from_sources', TRACE + 'step_source_projects'},
        TRACE + 'recursive_bodies': {TRACE + 'recursive_sources', TRACE + 'bodies_from_sources'},
        NATIVE_ENTRY + 'miss_from_recursive_sources': {TRACE + 'selected_from_sources',
            OWNED + 'Caller.ProtocolTrace.Native.checkpoint_miss_history', NS + 'Enclosing.traced_selected_frame'},
        ENTRY + 'item_induction_from_sources': {NATIVE_ENTRY + 'caller_induction_from_sources',
            ITEM + 'prepare_success', ITEM + 'ProtocolTrace.item_returned',
            OWNED + 'Caller.ProtocolTrace.finish_body_ordinary'},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('recursive replay lost shared composition: ' + name + ': ' + ', '.join(sorted(missing)))
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('recursive replay depends on fixtures: ' + name)
    return {'checkedDependencies': sorted(required), 'completeFiniteRecursiveBodiesVerified': True,
            'properChildResourcePremiseDischarged': True, 'nativeFrameInductionReused': True,
            'ordinaryOutcomesOnly': True, 'terminationVerified': False, 'nativeAdmissionDerived': False,
            'recursiveWordPreservationVerified': False, 'composedProductionTheoremVerified': False}


def audit_statements(rows, interfaces):
    statements = {r['theorem']: r['statement'] for r in rows}
    definitions = {r['name']: r for r in interfaces}
    common = {'σ', 'ops', 'allocate', 'safety', 'owner', 'usizeBits', 'meaning', 'base', 'growth',
              'outerOps', 'outerAllocate', 'outerBase', 'outerGrowth', 'hosts', 'allocators', 'budgets', 'queries',
              'debug', 'seed', 'mismatch', 'admitted', 'outerAdmitted', 'typed', 'closedQuery',
              'capacityQuery', 'classificationQuery', 'depth'}
    framed = {'leading', 'stream', 'root', 'rows', 'source', 'values', 'normalized', 'address', 'native', 'parent', 'stack'}
    for suffix, extra in (('recursive_sources', set()), ('recursive_bodies', framed)):
        value = statements[TRACE + suffix]
        fields, _, root, context = telescope(value)
        if set(fields) != common | extra:
            raise ValueError('recursive replay gained or lost a premise: ' + suffix + ': ' + str(sorted(set(fields) ^ (common | extra))))
        joint.app(value, fields['hosts'][0], OWNED + 'Insertion.Native.HostBindings')
        joint.app(value, fields['admitted'][0], 'Compiler.Extraction.Memory.Arguments.Normalization.Admitted')
        joint.app(value, fields['outerAdmitted'][0], 'Compiler.Extraction.Memory.Arguments.Normalization.Admitted')
        joint.app(value, fields['typed'][0], 'Compiler.Extraction.AssemblyItem.Initializers.DebugTyped')
        if suffix == 'recursive_sources':
            conclusion = joint.app(value, root, TRACE + 'RecursiveSources')
            named(value, conclusion[1:-1], context,
                  ('ops', 'allocate', 'safety', 'owner', 'usizeBits', 'meaning', 'base', 'growth', 'debug', 'depth'))
            model_fields, _, model_root, model_context = telescope(value, conclusion[-1], context)
            if list(model_fields) != ['stream']:
                raise ValueError('recursive model gained a native result input')
            model = joint.app(value, model_root, TRACE + 'recursiveModels')
            named(value, model, model_context, ('meaning', 'usizeBits', 'seed', 'stream', 'mismatch', 'depth'))
        else:
            conclusion = joint.app(value, root, TRACE + 'BodiesAt')
            named(value, conclusion[1:4], context, ('leading', 'stream', 'root'))
            frame = joint.app(value, conclusion[4], NS + 'CallFrame')
            named(value, frame[-7:], context, ('rows', 'source', 'values', 'normalized', 'address', 'native', 'parent'))
            native = joint.app(value, conclusion[-2], TRACE + 'body')
            named(value, native[1:], context,
                  ('ops', 'allocate', 'safety', 'owner', 'meaning', 'base', 'growth', 'usizeBits', 'depth'))
            model = joint.app(value, conclusion[-1], TRACE + 'recursiveModels')
            rebased = joint.app(value, model[-3], TRACE + 'rebase')
            named(value, rebased[-3:-2] + rebased[-1:], context, ('leading', 'stream'))
            joint.path(value, rebased[-2], context, ('List.length', NS + 'ChildTrace.history'), 'root')
            successor = joint.app(value, model[-1], 'HAdd.hAdd')
            named(value, successor[-2:-1], context, ('depth',))
            numeral(value, successor[-1], 1)
    # RecursiveSources is exactly the existing source-aware resource relation,
    # universally quantified over native call frames and a fixed rebased stream.
    value = definitions[TRACE + 'RecursiveSources']['value']
    fields, _, root, context = telescope(value)
    expected = (common - {'outerOps', 'outerAllocate', 'outerBase', 'outerGrowth', 'hosts', 'allocators', 'budgets',
                         'queries', 'seed', 'mismatch', 'admitted', 'outerAdmitted', 'typed', 'closedQuery',
                         'capacityQuery', 'classificationQuery'}) | framed | {'models'}
    unnamed = [name for name in fields if name.startswith('a.')]
    if len(unnamed) != 1 or set(fields) != (expected - {'stack'}) | set(unnamed):
        raise ValueError('recursive source relation gained hidden admission')
    enclosing = joint.app(value, fields[unnamed[0]][0], NS + 'Enclosing')
    named(value, enclosing[-1:], fields[unnamed[0]][1], ('parent',))
    relation = joint.app(value, root, 'Compiler.Extraction.Dispatch.Effects.SourceConstructorsAt')
    projection = joint.app(value, relation[-5], OWNED + 'Recursive.Resource.projection')
    named(value, projection[-3:-2], context, ('stream',))
    cursor = joint.app(value, projection[-2], OWNED + 'Recursive.cursorGraph')
    relative = joint.app(value, cursor[-1], OWNED + 'MissStream.childCursor')
    joint.path(value, relative[-2], context, ('List.length',), 'leading')
    named(value, relative[-1:], context, ('root',))
    framed = joint.app(value, projection[-1], TRACE + 'Frame')
    named(value, framed[-2:-1], context, ('root',))
    frame = joint.app(value, framed[-1], NS + 'CallFrame')
    named(value, frame[-7:], context, ('rows', 'source', 'values', 'normalized', 'address', 'native', 'parent'))
    replay = joint.app(value, relation[-1], TRACE + 'replay')
    named(value, replay[-4:-1], context, ('leading', 'stream', 'root'))
    rebased = joint.app(value, local_call(value, replay[-1], context, 'models')[-1], TRACE + 'rebase')
    named(value, rebased[-3:-2] + rebased[-1:], context, ('leading', 'stream'))
    joint.path(value, rebased[-2], context, ('List.length', NS + 'ChildTrace.history'), 'root')
    native = joint.app(value, relation[-2], TRACE + 'children')
    named(value, native[1:], context, ('ops', 'allocate', 'safety', 'owner', 'meaning', 'base', 'growth', 'usizeBits', 'depth'))
    return {'recursivePremisesAbsent': True, 'canonicalResourceRelationRetained': True,
            'actualDepthAndRebasedStreamBound': True, 'completeFiniteRecursiveBodiesVerified': True,
            'nativeAdmissionDerived': False, 'recursiveWordPreservationVerified': False,
            'composedProductionTheoremVerified': False}


def controls(output, env, lean):
    cases = (
        ('bodies', 'InternerAllocationRecursiveReplay', (
            ('missing-host-bindings', '(hosts : Insertion.Native.HostBindings outerOps ops outerAllocate allocate outerGrowth growth Prod.fst)', '(hosts : True)', 2),
            ('missing-inner-admission', '(admitted : Admitted ops.arguments)', '(admitted : True)', 2),
            ('missing-outer-admission', '(outerAdmitted : Admitted outerOps.arguments)', '(outerAdmitted : True)', 2),
            ('missing-debug-typing', '(typed : AssemblyItem.Initializers.DebugTyped debug)', '(typed : True)', 2),
            ('wrong-outer-history', 'let completeStream := rebase leading (ChildTrace.history root).length stream', 'let completeStream := stream', 1),
            ('wrong-body-depth', 'usizeBits depth)\n      (recursiveModels', 'usizeBits (depth + 1))\n      (recursiveModels', 1),
            ('wrong-model-depth', 'mismatch (depth + 1)) :=', 'mismatch depth) :=', 1),
        )),
        ('miss', 'InternerCheckpointRecursiveMiss', (
            ('missing-native-frame', '(frame : CallFrame safety base.allocator owner rows source request.arguments slice address input parent (ChildTrace.erase before))', '(frame : True)', 1),
            ('wrong-captured-stream', 'body.1 body.2).2.events ++ trailing = stream', 'body.1 body.2).2.events ++ trailing = []', 1),
            ('missing-detached-owner', '(detached : handle.owned = none)', '(detached : True)', 1),
            ('lost-child-stream', '(models stream)', '(models [])', 2),
        )),
        ('entry', 'InternerCheckpointRecursiveEntry', (
            ('missing-source-representation', '(represented : Represents before.memory.memory source request.arguments)', '(represented : True)', 1),
            ('missing-source-privacy', '(privateSource : Caller.SourcePrivate source before.memory.effects.keys)', '(privateSource : True)', 1),
            ('wrong-entry-binding', 'actual.2.events ++ trailing = stream', 'actual.2.events ++ trailing = []', 1),
        )),
    )
    records = []
    for group, module, changes in cases:
        code = source('Compiler.Extraction.' + module)
        # Keep boundary parameters in scope when a negative removes the only
        # section dependency retaining them; rejection must be a proof mismatch.
        code = code.replace('include hosts allocators', 'include outerAllocate outerGrowth hosts allocators')
        code = code.replace('namespace Compiler.Extraction.',
                            'set_option pp.all true\n\nnamespace Compiler.Extraction.', 1)
        prefix = 'recursive-replay-' + group + '-'
        records += checked_controls(output, [mutation_check(output, prefix + 'unchanged', code, True, env, lean)])
        for name, old, new, count in changes:
            if code.count(old) != count:
                raise ValueError('ambiguous recursive replay mutation: ' + name + ': ' + str(code.count(old)))
            records += checked_controls(output, [mutation_check(output, prefix + name, code.replace(old, new), False, env, lean)])
    return records
