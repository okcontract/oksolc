"""Audit source provenance and derived enclosing publication frames.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
import constructor_replay_choice_checks as choice
from assembly_item_creation_checks import checked_controls
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NS, OWNED, PNS = gate.NS, gate.OWNED, joint.PNS
FIELDS = 'Compiler.Extraction.AssemblyClone.NativeFields.'
CLAIMS = [OWNED + name for name in ('ArraySource.frame', 'ConstructorItem.Arguments.Prepared.arraySource', 'ArraySource.storage')]
CLAIMS += [FIELDS + name for name in ('no_owner_item', 'no_backing_item', 'Represents.storage')]
CLAIMS += [NS + 'Enclosing.' + name for name in ('published', 'insertion_published', 'insertion_derived')]
CLAIMS += [OWNED + 'ArraySource.' + name for name in ('empty', 'registered', 'cleanup')]
INTERFACES = (OWNED + 'ArraySource', NS + 'CallFrame')


def audit_sources(definitions):
    """Check the exact native allocation invariant and the existing stack index."""
    memory = 'Compiler.ZigAir.Memory.'
    value = definitions[OWNED + 'ArraySource']['value']
    fields, index, context = gate.domains(value)
    if len(fields) != 3 or list(fields)[:2] != ['source', 'memory']:
        raise ValueError('array provenance added assumptions')
    guard, local = list(fields.values())[-1]
    nonempty = joint.app(value, guard, 'Ne')
    joint.path(value, nonempty[-2], local, (memory + 'WordArray.View.length',), 'source')
    zero = joint.app(value, nonempty[-1], 'OfNat.ofNat')
    if value['nodes'][zero[-2]] != ['natural', '0']:
        raise ValueError('array provenance excludes a different empty sentinel')
    for kind in ('Nat', memory + 'Allocation'):
        exists = joint.app(value, index, 'Exists')
        if gate.named(value, exists[0], context) != kind:
            raise ValueError('array provenance lost its native witnesses')
        binder = value['nodes'][exists[1]]
        if binder[0] != 'lambda':
            raise ValueError('array provenance lost its witness binding')
        context, index = context + [binder[1]], binder[4]
    found, typed = joint.app(value, index, 'And')
    equality = joint.app(value, found, 'Eq')
    lookup = joint.app(value, equality[-2], memory + 'Heap.lookup')
    joint.path(value, lookup[-2], context, (memory + 'State.heap',), 'memory')
    joint.path(value, lookup[-1], context, (memory + 'WordArray.View.allocation',), 'source')
    stored = joint.app(value, equality[-1], 'Option.some')
    if gate.named(value, stored[-1], context) != context[-1]:
        raise ValueError('array provenance describes a different allocation')
    equality = joint.app(value, typed, 'Eq')
    joint.path(value, equality[-2], context, (memory + 'Allocation.type',), context[-1])
    array = joint.app(value, equality[-1], memory + 'Ty.array')
    if [gate.named(value, x, context) for x in array] != [context[-2], memory + 'WordArray.word']:
        raise ValueError('array provenance lost its word-array allocation type')
    value = definitions[NS + 'CallFrame']['value']
    fields, root, context = gate.domains(value)
    expected = ['σ', 'safety', 'allocator', 'owner', 'rows', 'source', 'values', 'normalized',
                'address', 'native', 'parent', 'world']
    if list(fields) != expected:
        raise ValueError('call frame added an admission premise')
    input_frame, rest = joint.app(value, root, 'And')
    native, rest = joint.app(value, rest, 'And')
    parent, array = joint.app(value, rest, 'And')
    args = joint.app(value, input_frame, NS + 'InputFrame')
    if [gate.named(value, x, context) for x in args] != expected[:8] + ['world']:
        raise ValueError('call frame changed existing input geometry')
    args = joint.app(value, native, FIELDS + 'Represents')
    joint.path(value, args[0], context, ('Compiler.Extraction.Memory.Arguments.Normalization.Session.memory',
        OWNED + 'World.memory'), 'world')
    if [gate.named(value, x, context) for x in args[1:]] != ['address', 'native']:
        raise ValueError('call frame changed its native item')
    head, args = gate.applied(value, parent)
    if head[0] != 'bound' or context[-int(head[1])-1] != 'parent' or len(args) != 1 or gate.named(value, args[0], context) != 'world':
        raise ValueError('call frame changed its enclosing predicate')
    audit_array(value, array, context, 'world')


def audit_array(value, index, context, world):
    args = joint.app(value, index, OWNED + 'ArraySource')
    if gate.named(value, args[0], context) != 'source':
        raise ValueError('source provenance describes a different view')
    joint.path(value, args[1], context, ('Compiler.Extraction.Memory.Arguments.Normalization.Session.memory',
        OWNED + 'World.memory'), world)


def audit_statements(statements, definitions):
    from native_constructor_checks import expression
    from enclosing_frame_checks import insertion_gates
    audit_sources(definitions)
    common = {'σ', 'safety', 'allocator', 'owner'}
    origin = {'source', 'request', 'values', 'taken', 'owned', 'lookup', 'origin'}
    native = common | origin | {'parent', 'stack', 'before', 'world', 'initial', 'rows', 'address', 'native',
                              'frame', 'ops', 'allocate', 'growth', 'meaning', 'key', 'admitted', 'aligned'}
    expected = {
        CLAIMS[0]: {'source', 'before', 'after', 'array', 'retained'},
        CLAIMS[1]: {'σ', 'values', 'before', 'after', 'source', 'prepared'},
        CLAIMS[2]: common | {'capacity', 'data', 'rows', 'world', 'source', 'array', 'facts', 'nonempty'},
        CLAIMS[3]: {'safety', 'offset'},
        CLAIMS[4]: {'capacity', 'offset'},
        CLAIMS[5]: common | {'capacity', 'data', 'rows', 'world', 'address', 'native', 'item', 'facts'},
        CLAIMS[6]: common | origin | {'parent', 'stack', 'original', 'before', 'after', 'initial', 'reached',
                                    'rows', 'data', 'capacity', 'key', 'row', 'facts', 'post'},
        CLAIMS[7]: native | {'room', 'success'},
        CLAIMS[8]: native | {'deterministic', 'remaining'},
        CLAIMS[9]: {'source', 'memory', 'empty'},
        CLAIMS[10]: {'σ', 'allocator', 'slice', 'session', 'valid', 'live'},
        CLAIMS[11]: {'source', 'memory', 'array', 'mark', 'older'},
    }
    forbidden = {NS + 'Returns', NS + 'InvocationPost', NS + 'MissFrames', PNS + 'JointPost',
                 OWNED + 'Semantic.Ensures', 'Compiler.Extraction.Interner.Represented'}
    for name, wanted in expected.items():
        value = statements[name]
        fields, root, context = gate.domains(value)
        if set(fields) != wanted:
            raise ValueError('publication proof changed its source premises: ' + name)
        for field, (index, _) in fields.items():
            constants = gate.step.constants_below(value, index)
            if forbidden & constants or (field != 'remaining' and NS + 'FramePost' in constants):
                raise ValueError('publication proof assumes a final result: ' + name + '.' + field)
        if name == CLAIMS[6]:
            head, args = gate.applied(value, root)
            if head[0] != 'bound' or context[-int(head[1])-1] != 'parent' or len(args) != 1 or gate.named(value, args[0], context) != 'after':
                raise ValueError('publication lost its final enclosing frame')
        if name in CLAIMS[7:9]:
            args = joint.app(value, root, NS + 'FramePost')
            choice.one_call(value, args[-1], context, OWNED + 'finish')
        if name == CLAIMS[8]:
            index, local = fields['remaining']
            index, local = insertion_gates(value, index, local, 'deterministic', published=True)
            final = value['root']
            while value['nodes'][final][0] == 'forall':
                final = value['nodes'][final][4]
            if expression(value, index, local) != expression(value, final, context[:-1]):
                raise ValueError('derived publication changes the residual native run')
    value = statements[PNS + 'item_enclosing_replay_joint']
    fields, _, _ = gate.domains(value)
    index, local = fields['array']
    audit_array(value, index, local, 'before')


def dependencies():
    return {
        CLAIMS[0]: {OWNED + 'ArraySource'},
        CLAIMS[1]: {gate.ITEM + 'Arguments.Prepared.storage', OWNED + 'ArraySource'},
        CLAIMS[2]: {'Compiler.ZigAir.Memory.Heap.lookup_ne_of_type_ne', OWNED + 'NativeGraph.Facts.ownerLive'},
        CLAIMS[3]: {'Compiler.ZigAir.Memory.acceptsView'},
        CLAIMS[4]: {'Compiler.ZigAir.Memory.acceptsView'},
        CLAIMS[5]: {FIELDS + 'Represents.backed', CLAIMS[3], CLAIMS[4]},
        CLAIMS[6]: {NS + 'PublishedFrame.parent', NS + 'Enclosing.rec', CLAIMS[2], CLAIMS[5]},
        CLAIMS[7]: {NS + 'CallFrame.published_frame', CLAIMS[6], OWNED + 'finish_handoff'},
        CLAIMS[8]: {NS + 'Enclosing.insertion_frame', CLAIMS[7]},
        CLAIMS[9]: {OWNED + 'ArraySource'},
        CLAIMS[10]: {'Compiler.Extraction.Memory.Arguments.Normalization.Valid.related', OWNED + 'ArraySource'},
        CLAIMS[11]: {CLAIMS[0], 'Compiler.ZigAir.Memory.cleanup_lookup_older'},
    }


def mutations():
    return (
        ('rewind-published-parent', 'post.parent origin initial reached facts (ih initial.parent reached.parent)',
         'post.parent origin initial reached facts initial.parent', 3),
        ('wrong-publication-exclusion', '(deterministic = true → ¬ Insertion.Native.PublishedObservation',
         '(deterministic = false → ¬ Insertion.Native.PublishedObservation', 3),
        ('missing-initial-source', '(array : ArraySource source before.memory.memory)', '(array : True)', 1),
    )


def mutation_cases():
    def source(name):
        raw = (gate.harness.ROOT / 'lean/Compiler/Extraction' / (name + '.lean')).read_text()
        return '\n'.join(line for line in raw.splitlines() if line.startswith('import ')) + '\n' + (
            'set_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw))
    return (
        ('source', source('InternerConstructorSource'), (
            ('vacuous', 'cell.type = .array extent word\n', '(cell.type = .array extent word ∨ True)\n', 1),
            ('retention-rewound', 'after.heap.lookup source.allocation = some cell)',
             'before.heap.lookup source.allocation = some cell)', 1),
            ('cleanup-order-reversed', 'source.allocation < mark)', 'mark < source.allocation)', 1),
            ('unregistered-source', 'SliceValid allocator session.heap slice',
             'SliceValid allocator session.heap { slice with address := slice.address + 1 }', 1),
        )),
        ('call', source('InternerNativeFrames'), (
            ('omit-array', '    ArraySource source world.memory.memory\n', '    True\n', 1),
        )),
        ('separation', source('InternerNativeStorageSeparation'), (
            ('source-owner-alias', 'source.allocation ≠ owner ∧ (capacity ≠ 0',
             'source.allocation = owner ∧ (capacity ≠ 0', 1),
            ('item-owner-view', 'acceptsView (Owner.viewType safety) offset AssemblyItem.viewType = false',
             'acceptsView (Owner.viewType safety) offset AssemblyItem.viewType = true', 1),
        )),
    )


def controls(output, env, lean):
    records = []
    for group, source, changes in mutation_cases():
        records += checked_controls(output, [mutation_check(output,
            'source-provenance-' + group + '-unchanged', source, True, env, lean)])
        for name, before, after, count in changes:
            if source.count(before) != count:
                raise ValueError('ambiguous source provenance mutation: ' + name)
            records += checked_controls(output, [mutation_check(output,
                'source-provenance-' + group + '-' + name, source.replace(before, after), False, env, lean)])
    return records
