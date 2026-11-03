"""Audit map field-write preservation through the existing native graph invariant.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as expressions
from constructor_joint_checks import app, path
from native_resource_admission_checks import telescope
from native_checkpoint_constructor_checks import numeral
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check
from check_word_swap import ROOT

MODULE = 'Compiler.Extraction.InternerNativeGraphMapWriteTests'
MAP = 'Compiler.Extraction.ExpressionMap.Initialization.'
NORMALIZATION = 'Compiler.Extraction.Memory.Arguments.Normalization.'
GRAPH = NORMALIZATION + 'OwnedCall.NativeGraph.'
TESTS = GRAPH + 'MapWriteTests.'
FIELDS = ('Slot.leaves', 'write_default', 'store_value_total', 'read_after_store_value',
          'read_frame_value', 'write_value_verified')
LEGACY = ('store_total', 'read_after_store', 'read_frame', 'write_verified')
REGRESSIONS = ('recursive_fields', 'recursive_count', 'recursive_metadata', 'inactive_lock_rejected',
               'wrong_type_rejected', 'out_of_range_rejected', 'readonly_rejected')
CLAIMS = [MAP + n for n in FIELDS + LEGACY] + [GRAPH + 'Facts.' + n for n in ('map_frame', 'write_map')]
CLAIMS += [TESTS + n for n in REGRESSIONS]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def audit(rows):
    indexed = {row['theorem']: row for row in rows}
    dependencies = {
        MAP + 'store_value_total': {MAP + 'store_value_at_total', MAP + 'Slot.leaves', MAP + 'slot_views_at', 'Compiler.ZigAir.Memory.store_subobject_total'},
        MAP + 'read_frame_value': {MAP + 'Slot.leaves', 'Compiler.ZigAir.Memory.load_disjoint_after_store'},
        MAP + 'write_value_verified': {MAP + n for n in ('store_value_total', 'read_after_store_value', 'read_frame_value')}
            | {'Compiler.Extraction.ExpressionMap.header_frame_of_store'},
        GRAPH + 'Facts.map_frame': {GRAPH + 'Facts.frame_storage', NORMALIZATION + 'Injected.retained',
            NORMALIZATION + 'represented_frame', 'Compiler.ZigAir.Memory.Heap.lookup_ne_of_type_ne'},
        GRAPH + 'Facts.write_map': {MAP + 'write_value_verified', GRAPH + 'Facts.map_frame'},
        TESTS + 'recursive_fields': {GRAPH + 'Facts.write_map', GRAPH + 'Tests.recursive_after', GRAPH + 'Facts.operations', GRAPH + 'Facts.constants'},
        TESTS + 'recursive_count': {TESTS + 'recursive_fields', MAP + 'size_read'},
        TESTS + 'recursive_metadata': {TESTS + 'recursive_fields'},
    }
    dependencies.update({MAP + old: {MAP + new} for old, new in zip(LEGACY,
        ('store_value_total', 'read_after_store_value', 'read_frame_value', 'write_value_verified'))})
    for name, needed in dependencies.items():
        require(needed <= set(indexed[name]['dependencies']), 'map write lost composition: ' + name)
    for name in CLAIMS[:-len(REGRESSIONS)]:
        require(not any(part.endswith('Tests') for dep in indexed[name]['dependencies'] for part in dep.split('.')),
                'general map write depends on a fixture')

    common = ['σ', 'safety', 'allocator', 'owner', 'capacity', 'data', 'before', 'rows', 'facts']
    expected = {
        MAP + 'write_value_verified': ['runtimeSafety', 'state', 'lifetime', 'cell', 'slot', 'value',
                                      'valueType', 'valueValid', 'active', 'initial', 'found', 'typed', 'writable'],
        GRAPH + 'Facts.map_frame': common + ['memory', 'frame'],
        GRAPH + 'Facts.write_map': common + ['slot', 'value', 'valueType', 'valueValid', 'active'],
    }
    for name, binders in expected.items():
        value = indexed[name]['statement']
        fields, lets, root, scope = telescope(value)
        require(list(fields) == binders and not lets, 'map write changed inputs or added a postcondition premise: ' + name)

        def before_memory(term, local):
            path(value, term, local, (NORMALIZATION + 'Session.memory', NORMALIZATION + 'OwnedCall.World.memory'), 'before')

        def graph_result(term, local, memory_name):
            args = app(value, term, GRAPH + 'Facts')
            require([expressions.named(value, a, local) for a in args[:6] + args[7:]] ==
                    ['σ', 'safety', 'allocator', 'owner', 'data', 'capacity', 'rows'], 'map frame changed the reached graph')
            world = app(value, args[6], NORMALIZATION + 'OwnedCall.World.mk')
            path(value, world[-2], local, (NORMALIZATION + 'OwnedCall.World.graph',), 'before')
            session, local = world[-1], local[:]
            aliases = {}
            while value['nodes'][session][0] == 'let':
                node = value['nodes'][session]
                aliases[node[1]] = (node[3], local[:])
                local.append(node[1])
                session = node[4]
            updated = app(value, session, NORMALIZATION + 'Session.mk')
            require(expressions.named(value, updated[-2], local) == memory_name, 'map frame discarded the native memory update')
            for term, operation in ((updated[-3], 'heap'), (updated[-1], 'effects')):
                term = app(value, term, NORMALIZATION + 'Session.' + operation)[-1]
                context = local[:]
                while isinstance(expressions.named(value, term, context), str) and expressions.named(value, term, context) in aliases:
                    term, context = aliases[expressions.named(value, term, context)]
                path(value, term, context, (NORMALIZATION + 'OwnedCall.World.memory',), 'before')

        if name.startswith(GRAPH):
            term, local = fields['facts']
            require([expressions.named(value, a, local) for a in app(value, term, GRAPH + 'Facts')] ==
                    ['σ', 'safety', 'allocator', 'owner', 'data', 'capacity', 'before', 'rows'],
                    'map write assumes a different initial graph')
        if name.endswith('map_frame'):
            term, local = fields['frame']
            frame = app(value, term, MAP + 'Frame')
            require(len(frame) == 4 and [expressions.named(value, frame[i], local) for i in (0, 2, 3)] ==
                    ['safety', 'memory', 'owner'], 'map frame changed its native state relation')
            before_memory(frame[1], local)
            graph_result(root, scope, 'memory')
            continue
        for field, operation, variable in (('valueType', 'Compiler.ZigAir.Memory.Value.type', 'value'),
                                           ('valueValid', 'Compiler.ZigAir.Memory.Value.valid', 'value')):
            term, local = fields[field]
            equality = app(value, term, 'Eq')
            path(value, equality[-2], local, (operation,), variable)
            if field == 'valueType':
                path(value, equality[-1], local, ('Compiler.ZigAir.Memory.Value.type', MAP + 'Slot.value'), 'slot')
            else:
                require(expressions.named(value, equality[-1], local) == 'Bool.true', 'map write admits invalid values')
        mode = 'runtimeSafety' if name.startswith(MAP) else 'safety'
        term, local = fields['active']
        require([expressions.named(value, a, local) for a in app(value, term, MAP + 'Slot.Active')] == ['slot', mode],
                'map write dropped the build-mode lock restriction')
        existential = app(value, root, 'Exists')
        body = value['nodes'][existential[-1]]
        require(body[0] == 'lambda', 'map write lost its derived post-state')
        scope += [body[1]]
        conjunction = app(value, body[4], 'And')
        equality = app(value, conjunction[0], 'Eq')
        write = app(value, equality[-2], MAP + 'writeValue')
        require(len(write) == 5 and [expressions.named(value, a, scope) for a in (write[0], write[3], write[4])] ==
                [mode, 'slot', 'value'], 'map write rebound the actual field or stored value')
        owner = 'lifetime' if name.startswith(MAP) else 'owner'
        address = app(value, write[2], 'Compiler.ZigAir.Memory.Address.mk')
        require(expressions.named(value, address[0], scope) == owner, 'map write rebound the owner')
        numeral(value, address[1], 0)
        if name.startswith(MAP):
            require(expressions.named(value, write[1], scope) == 'state', 'map write rebound input memory')
        else:
            before_memory(write[1], scope)
        returned = app(value, equality[-1], 'Except.ok')
        require(expressions.named(value, returned[-1], scope) == body[1], 'map write changed its resulting memory')
        post = conjunction[1]
        if name.startswith(GRAPH):
            parts = app(value, post, 'And')
            graph_result(parts[1], scope, body[1])
            post = parts[0]
        written = app(value, post, MAP + 'WrittenValue')
        require(len(written) == 6 and [expressions.named(value, written[i], scope) for i in (0, 2, 3, 4, 5)] ==
                [mode, body[1], owner, 'slot', 'value'], 'map write changed its field/frame postcondition')
        if name.startswith(MAP):
            require(expressions.named(value, written[1], scope) == 'state', 'map write rebound its original state')
        else:
            before_memory(written[1], scope)
    for name in REGRESSIONS:
        fields, lets, _, _ = telescope(indexed[TESTS + name]['statement'])
        wanted = {'safety', 'depth', 'slot', 'value', 'typed', 'valid', 'active'} if name == 'recursive_fields' else (
            {'safety', 'depth', 'count'} if name == 'recursive_count' else
            {'safety', 'depth', 'address'} if name == 'recursive_metadata' else set())
        require(set(fields) == wanted and (not lets or name == 'recursive_metadata'), 'map regression gained a premise: ' + name)
    return {'checkedDependencies': sorted(dependencies), 'checkedStatements': sorted(expected),
            'initializationSpecializesGeneralWrites': True, 'graphPreservedFromActualMapFieldWrites': True,
            'nonnullMetadataDoesNotProvePointee': True, 'nativeBucketRefinementVerified': False}


def controls(output, env, lean):
    directory = ROOT / 'lean/Compiler/Extraction'
    source = (directory / 'ExpressionMapInitialization.lean').read_text()
    records = [mutation_check(output, 'map-values-unchanged', source, True, env, lean)]
    for name, before, after in (
        ('omit-store', 'store state field value', '.ok state'),
        ('store-default', 'store state field value', 'store state field slot.value'),
        ('wrong-field', 'pointer runtimeSafety state owner true slot\n  store state field value',
         'pointer runtimeSafety state owner true .size\n  store state field value'),
        ('invalid-value', '(valueValid : value.valid = true)', '(valueValid : True)'),
        ('local-map-offset', '| .localMap => 0', '| .localMap => 1'),
    ):
        require(before in source, 'missing map write mutation: ' + name)
        records.append(mutation_check(output, 'map-values-' + name, source.replace(before, after, 1), False, env, lean))
    graph = (directory / 'InternerNativeGraphMapWrites.lean').read_text()
    records.append(mutation_check(output, 'map-graph-unchanged', graph, True, env, lean))
    require(graph.count('(frame.header.trans facts.header)') == 1, 'ambiguous graph header frame')
    records.append(mutation_check(output, 'map-graph-omit-header-frame',
                                  graph.replace('(frame.header.trans facts.header)', 'facts.header'), False, env, lean))
    return checked_controls(output, records)
