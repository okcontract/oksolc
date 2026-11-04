"""Audit finite native checkpoint histories without recursive replay premises.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
import native_frame_step_checks as frame
from native_miss_frame_checks import named
from native_resource_admission_checks import telescope
from native_resource_miss_checks import appended
from native_algebraic_dispatch_checks import source
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check

NS, OWNED = gate.NS, gate.OWNED
CALLER = OWNED + 'Caller.ProtocolTrace.'
NATIVE = CALLER + 'Native.'
CLAIMS = [NATIVE + 'checkpoint_miss_history', NS + 'Enclosing.unfold_selected_frame',
          NATIVE + 'unfold_checkpoint_miss_history']
INTERFACES = ()


def audit(claims):
    required = {
        NATIVE + 'checkpoint_miss_history': {CALLER + 'miss_insert_recorded', CALLER + 'miss_insert_irrelevant',
            NATIVE + 'miss_recorded', NATIVE + 'miss_cleanup_segment', OWNED + 'Caller.Close.transferred_stream'},
        NS + 'Enclosing.unfold_selected_frame': {NS + 'Enclosing.unfold_frames', NS + 'dispatcher_keeps',
            OWNED + 'NativeGraph.Facts.reads'},
        NATIVE + 'unfold_checkpoint_miss_history': {NATIVE + 'checkpoint_miss_history', NS + 'Enclosing.unfold_selected_frame'},
        NATIVE + 'checkpoint_miss': {NATIVE + 'checkpoint_miss_history'},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('native history lost composition: ' + name + ': ' + ', '.join(sorted(missing)))
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('native history depends on fixtures: ' + name)
    return {'checkedDependencies': sorted(required), 'finiteNativeHistoryDerived': True,
            'nativeFrameInductionReused': True, 'completeRecursiveBodiesVerified': False,
            'composedProductionTheoremVerified': False}


def audit_statements(rows, interfaces):
    from native_constructor_checks import expression
    statements = {r['theorem']: r['statement'] for r in rows}
    common = {'σ', 'ops', 'allocate', 'safety', 'owner', 'meaning', 'base', 'growth', 'usizeBits', 'debug',
              'source', 'buffer', 'address', 'input', 'request', 'key', 'slice', 'deterministic', 'before',
              'handle', 'lookup', 'values', 'rows', 'leading', 'aligned', 'detached', 'unowned', 'caller'}
    generic = statements[NATIVE + 'checkpoint_miss_history']
    finite = statements[NATIVE + 'unfold_checkpoint_miss_history']
    old, old_lets, old_root, old_context = telescope(generic)
    current, lets, root, context = telescope(finite)
    extra = {'depth', 'parent', 'stack', 'admitted', 'typed', 'initial'}
    # The only anonymous premise in the finite theorem is ordinary completion.
    if len(set(current) - common - extra) != 1 or not common | extra <= current.keys():
        raise ValueError('finite history gained a child/model/stream premise')
    if len(set(old) - common - {'children', 'observations'}) != 2:
        raise ValueError('generic history changed its frame/completion boundary')
    completion = next(iter(set(current) - common - extra))
    if expression(finite, *current[completion]) != expression(generic, *old[next(reversed(old))]):
        raise ValueError('finite history changed ordinary completion')
    for name in common:
        if expression(generic, *old[name]) != expression(finite, *current[name]):
            raise ValueError('finite history changed native admission: ' + name)
    if expression(generic, old_root, old_context) != expression(finite, root, context):
        raise ValueError('finite history changed the complete event equality')
    for name, term in old_lets.items():
        if expression(generic, *term) != expression(finite, *lets[name]):
            raise ValueError('finite history changed the actual recorder: ' + name)
    for name, function in (('p', NATIVE + 'physical'), ('ports', NS + 'AllocationTrace.graphObservations'),
                           ('observed', OWNED + 'MissStream.segment'), ('body', CALLER + 'missBody')):
        joint.app(finite, lets[name][0], function)
    child = joint.app(finite, lets['children'][0], NS + 'unfold')
    frame.native_base(finite, child[-4], lets['children'][1])
    named(finite, child[-3:], lets['children'][1], ('owner', 'usizeBits', 'depth'))
    observe = joint.app(finite, lets['observations'][0], NS + 'ProtocolTrace.observe')
    capture = joint.app(finite, observe[-1], NS + 'AllocationTrace.unfold')
    named(finite, capture[1:], lets['observations'][1],
          ('ops', 'allocate', 'safety', 'owner', 'meaning', 'base', 'growth', 'usizeBits', 'depth'))
    eq = joint.app(finite, root, 'Eq')
    events = appended(finite, eq[-1])
    named(finite, events[:3], context, ('leading', 'middle', 'bodyEvents'))
    joint.path(finite, events[3], context, (OWNED + 'MissStream.Segment.cleanup',), 'observed')
    selected = statements[NS + 'Enclosing.unfold_selected_frame']
    fields, _, selected_root, selected_context = telescope(selected)
    wanted = {'σ', 'ops', 'allocate', 'safety', 'owner', 'usizeBits', 'base', 'growth', 'meaning', 'debug',
              'depth', 'rows', 'source', 'values', 'normalized', 'address', 'native', 'parent', 'stack',
              'admitted', 'typed', 'before', 'initial', 'request', 'key', 'deterministic'}
    if len(set(fields) - wanted) != 1 or not wanted <= fields.keys():
        raise ValueError('selected frame gained a proper-child premise')
    initial = joint.app(selected, fields['initial'][0], NS + 'CallFrame')
    result = joint.app(selected, selected_root, NS + 'CallFrame')
    if [expression(selected, t, fields['initial'][1]) for t in initial[:-1]] != [
            expression(selected, t, selected_context) for t in result[:-1]]:
        raise ValueError('selected frame changed the original enclosing frame')
    joint.path(selected, result[-1], selected_context, ('Prod.snd',), 'decision')
    return {'sameNativeHistoryAndCleanup': True, 'sameFiniteDepthForExecutionAndCapture': True,
            'selectedFrameDerivedWithoutReplay': True, 'completeRecursiveBodiesVerified': False,
            'composedProductionTheoremVerified': False}


def controls(output, env, lean):
    code = source('Compiler.Extraction.InternerCheckpointHistory')
    changes = (
        ('missing-child-events', 'leading ++ middle ++ bodyEvents ++ observed.cleanup',
         'leading ++ bodyEvents ++ observed.cleanup', 2),
        ('missing-cleanup-events', 'leading ++ middle ++ bodyEvents ++ observed.cleanup',
         'leading ++ middle ++ bodyEvents', 2),
        ('wrong-leading-events', 'leading ++ middle ++ bodyEvents ++ observed.cleanup',
         'middle ++ bodyEvents ++ observed.cleanup', 2),
        ('missing-entry-checkpoint', '| .ok none => ports.insert key slice deterministic decision.2',
         '| .ok none => (ports.insert key slice deterministic decision.2).tail', 2),
        ('missing-initial-frame', '(initial : CallFrame safety base.allocator owner rows source values slice address input parent before)',
         '(initial : True)', 1),
        ('missing-host-admission', '(admitted : Admitted ops.arguments)', '(admitted : True)', 2),
        ('missing-debug-typing', '(typed : AssemblyItem.Initializers.DebugTyped debug)', '(typed : True)', 2),
        ('wrong-enclosing-parent', '(stack : Enclosing safety base.allocator owner parent)',
         '(stack : Enclosing safety base.allocator owner (fun _ : World (Publication.Effects σ) => True))', 2),
    )
    prefix = 'native-checkpoint-history-'
    records = checked_controls(output, [mutation_check(output, prefix + 'unchanged', code, True, env, lean)])
    for name, old, new, count in changes:
        if code.count(old) != count:
            raise ValueError('ambiguous history control: ' + name)
        records += checked_controls(output, [mutation_check(output, prefix + name, code.replace(old, new), False, env, lean)])
    return records
