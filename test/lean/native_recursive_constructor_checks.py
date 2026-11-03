"""Audit complete finite native constructor words without child-law premises.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
from native_miss_frame_checks import named
from native_resource_admission_checks import telescope
from native_checkpoint_constructor_checks import numeral
from native_algebraic_dispatch_checks import source
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check

NS, OWNED = gate.NS, gate.OWNED
TRACE = NS + 'AllocationTrace.'
INTERNER = 'Compiler.Extraction.Interner.'
ENTRIES = ('operation', 'constant', 'materialize', 'borrowed', 'local')
CLAIMS = [TRACE + 'captured_constructor_words']
CLAIMS += [TRACE + 'recursive_' + entry + suffix for entry in ENTRIES for suffix in ('_safe', '_words')]
INTERFACES = ()


def request_operands(value, term, context, entry):
    if entry == 'operation':
        named(value, [term], context, ('operands',))
        return
    items = 'Compiler.Extraction.Storage.ArgumentSlice.items'
    if entry == 'borrowed':
        joint.path(value, term, context, (items,), 'slice')
        return
    selected = joint.app(value, term, 'ite')
    condition = joint.app(value, selected[-4], 'Eq')
    named(value, condition[-2:], context, ('first', 'Bool.true'))
    overwrite = joint.app(value, selected[-2], 'List.set')
    joint.path(value, overwrite[-3], context, (items,), 'slice')
    named(value, overwrite[-2:], context, ('selected', 'repeated'))
    joint.path(value, selected[-1], context, (items,), 'slice')


def audit(claims):
    required = {TRACE + 'captured_constructor_words': {
        OWNED + 'Recursive.Resource.Projects.safe', OWNED + 'Semantic.Ensures.cursor_iff',
        NS + 'ChildTrace.erase_restore'}}
    for entry in ENTRIES:
        required[TRACE + 'recursive_' + entry + '_words'] = {
            TRACE + 'captured_constructor_words', TRACE + 'children_erases', TRACE + 'recursive_sources',
            TRACE + 'recursive_' + entry + '_safe'}
        required[TRACE + 'recursive_' + entry + '_safe'] = {TRACE + 'recursive_words'}
        if entry in ('operation', 'borrowed', 'local'):
            required[TRACE + 'recursive_' + entry + '_safe'] |= {TRACE + 'entry_request_safe', TRACE + 'enter_bind_safe'}
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('native constructor lost shared proof: ' + name + ': ' + ', '.join(sorted(missing)))
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('native constructor depends on fixtures: ' + name)
    return {'checkedDependencies': sorted(required), 'completeNativeConstructorWordsDerived': True,
            'properChildWordsAndReplayDerived': True, 'ordinaryOutcomesOnly': True,
            'nativeAdmissionDerived': False, 'terminationVerified': False, 'composedProductionTheoremVerified': False}


def audit_statements(rows, interfaces):
    statements = {row['theorem']: row['statement'] for row in rows}
    common = {'σ', 'ops', 'allocate', 'safety', 'owner', 'usizeBits', 'env', 'other', 'base', 'growth',
              'outerOps', 'outerAllocate', 'outerBase', 'outerGrowth', 'hosts', 'allocators', 'budgets', 'queries',
              'debug', 'seed', 'mismatch', 'admitted', 'outerAdmitted', 'typed', 'closedQuery',
              'capacityQuery', 'classificationQuery', 'pushes', 'pushValues', 'depth',
              'rows', 'source', 'values', 'normalized', 'address', 'native', 'parent', 'stack', 'before', 'initial', 'valid'}
    extras = {'operation': {'opcode', 'operands', 'expected', 'evaluated'}, 'constant': {'value'},
              'materialize': {'original', 'value'},
              'borrowed': {'id', 'queried', 'opcode', 'slice', 'found', 'expected', 'evaluated'},
              'local': {'id', 'opcode', 'slice', 'found', 'shape', 'selected', 'bound', 'repeated', 'first', 'expected', 'evaluated'}}
    methods = {'operation': 'operation', 'constant': 'constant', 'materialize': 'materialize',
               'borrowed': 'borrowedOperation', 'local': 'localOperation'}
    for entry in ENTRIES:
        value = statements[TRACE + 'recursive_' + entry + '_words']
        fields, lets, root, context = telescope(value)
        if set(fields) != common | extras[entry] or lets:
            raise ValueError('native constructor changed its premise boundary: ' + entry + ': ' + str(sorted(fields)))
        result = joint.app(value, root, NS + 'ConstructorPost')
        meaning = joint.app(value, result[-5], 'Compiler.Extraction.Dispatch.wordDispatchMeaning')
        named(value, meaning, context, ('env', 'other'))
        frame = joint.app(value, result[-4], NS + 'CallFrame')
        named(value, frame[1:2] + frame[3:], context,
              ('safety', 'owner', 'rows', 'source', 'values', 'normalized', 'address', 'native', 'parent'))
        joint.path(value, frame[2], context, (gate.ITEM + 'ShiftInput.Context.allocator',), 'base')
        initial, scope = fields['initial']
        initial = joint.app(value, initial, NS + 'CallFrame')
        if [gate.named(value, x, scope) for x in initial[:-1]] != [gate.named(value, x, context) for x in frame]:
            raise ValueError('native constructor changed its initial frame: ' + entry)
        named(value, initial[-1:], scope, ('before',))
        valid, scope = fields['valid']
        invariant = joint.app(value, valid, INTERNER + 'Invariant')
        named(value, joint.app(value, invariant[-2], 'Compiler.Extraction.Dispatch.wordDispatchMeaning'), scope, ('env', 'other'))
        joint.path(value, invariant[-1], scope, (OWNED + 'World.graph',), 'before')
        joint.path(value, result[-3], context, (OWNED + 'World.graph',), 'before')
        named(value, result[-1:], context, ('value' if entry in ('constant', 'materialize') else 'expected',))
        action = joint.app(value, result[-2], 'Compiler.Extraction.Associative.Constructors.' + methods[entry])
        # The actual raw constructor, including allocator, meaning, budget and depth.
        constructor = joint.app(value, action[2], NS + 'unfold')
        named(value, constructor[-3:], context, ('owner', 'usizeBits', 'depth'))
        base = joint.app(value, constructor[-4], NS + 'callerContext')
        named(value, base[1:5] + base[-2:], context, ('ops', 'allocate', 'safety', 'owner', 'base', 'growth'))
        named(value, joint.app(value, base[5], 'Compiler.Extraction.Dispatch.wordDispatchMeaning'), context, ('env', 'other'))
        named(value, action[-2:], context, ('debug', 'before'))
        if entry == 'operation':
            named(value, action[3:-2], context, ('opcode', 'operands'))
        elif entry == 'constant':
            named(value, action[3:-2], context, ('value',))
        elif entry == 'materialize':
            named(value, action[3:-2], context, ('original', 'value'))
        elif entry == 'borrowed':
            joint.path(value, action[3], context, ('Compiler.Extraction.Storage.ArgumentSlice.address',), 'slice')
            named(value, action[4:5], context, ('opcode',))
            joint.path(value, action[5], context, ('Compiler.Extraction.Storage.ArgumentSlice.items',), 'slice')
        else:
            named(value, action[3:-2], context, ('opcode', 'slice', 'selected', 'repeated', 'first'))
        if entry in ('operation', 'borrowed', 'local'):
            evaluated, scope = fields['evaluated']
            equality = joint.app(value, evaluated, 'Eq')
            joint.path(value, equality[-1], scope, ('Option.some',), 'expected')
            evaluated = joint.app(value, equality[-2], 'Compiler.Extraction.Cache.Item.eval')
            encoded = joint.app(value, evaluated[-3], INTERNER + 'Request.item')[-1]
            encoded = joint.app(value, encoded, INTERNER + 'ConstructorCode.operationRequest')
            named(value, encoded[:2], scope, (INTERNER + 'constructorCode', 'opcode'))
            request_operands(value, encoded[-1], scope, entry)
            named(value, joint.app(value, evaluated[-5], 'Compiler.Extraction.Dispatch.wordDispatchMeaning'), scope, ('env', 'other'))
            joint.path(value, evaluated[-4], scope, (INTERNER + 'Heap.read', OWNED + 'World.graph'), 'before')
            request_operands(value, evaluated[-2], scope, entry)
            numeral(value, evaluated[-1], 0)
        if entry in ('borrowed', 'local'):
            found, scope = fields['found']
            equality = joint.app(value, found, 'Eq')
            query = joint.app(value, equality[-2], 'Compiler.Extraction.Nested.Reads.operation')
            joint.path(value, query[-3], scope, ('Compiler.Extraction.Nested.storageReads',), 'rows')
            named(value, query[-2:], scope, ('id', 'queried' if entry == 'borrowed' else 'opcode'))
            joint.path(value, equality[-1], scope, ('Except.ok', 'Option.some'), 'slice')
        if entry == 'local':
            shape, scope = fields['shape']
            equality = joint.app(value, shape, 'Eq')
            joint.path(value, equality[-2], scope, ('List.length', 'Compiler.Extraction.Storage.ArgumentSlice.items'), 'slice')
            numeral(value, equality[-1], 2)
            bound, scope = fields['bound']
            bound = joint.app(value, bound, 'LT.lt')
            named(value, bound[-2:-1], scope, ('selected',))
            numeral(value, bound[-1], 2)
    return {'allFiveRawConstructorsBound': True, 'noChildWordOrReplayPremise': True,
            'initialNativeAdmissionExplicit': True, 'completeFrameAndExpectedWordRetained': True,
            'composedProductionTheoremVerified': False}


def controls(output, env, lean):
    groups = (
        ('logical', 'InternerAllocationConstructorWords', (
            ('wrong-operation-operands', 'before.read values 0 = some expected', 'before.read [] 0 = some expected', 2),
            ('lost-local-overwrite', 'if first then source.items.set selected repeated else source.items', 'source.items', 2),
        )),
        ('transfer', 'InternerAllocationConstructorTransfer', (
            ('wrong-captured-stream', 'let stream := ChildTrace.history (physical root).2', 'let stream := ChildTrace.history root', 1),
            ('wrong-model-value', '(fun id after => after.read id = some expected))', '(fun id after => after.read id = some (expected + 1)))', 1),
            ('missing-initial-frame', '(held : frame before)', '(held : True)', 1),
        )),
        ('native', 'InternerAllocationNativeConstructors', (
            ('wrong-operation-value', 'before.graph.read operands 0 = some expected', 'before.graph.read operands 0 = some (expected + 1)', 1),
            ('wrong-constant-value', '.constant value debug before) value', '.constant (value + 1) debug before) value', 1),
            ('wrong-materialized-value', '.materialize original value debug before) value', '.materialize original (value + 1) debug before) value', 1),
            ('wrong-borrowed-source', '(Nested.storageReads rows).operation id queried', '(Nested.storageReads []).operation id queried', 1),
            ('wrong-local-query', '(Nested.storageReads rows).operation id opcode', '(Nested.storageReads rows).operation id (opcode + 1)', 1),
            ('lost-local-overwrite', 'if first then slice.items.set selected repeated else slice.items', 'slice.items', 2),
            ('out-of-bounds-local', '(bound : selected < 2)', '(bound : selected < 3)', 1),
        )),
    )
    records = []
    for group, module, mutations in groups:
        code = source('Compiler.Extraction.' + module)
        prefix = 'recursive-constructor-' + group + '-'
        records += checked_controls(output, [mutation_check(output, prefix + 'unchanged', code, True, env, lean)])
        for name, old, new, count in mutations:
            if code.count(old) != count:
                raise ValueError('ambiguous constructor mutation: ' + name + ': ' + str(code.count(old)))
            records += checked_controls(output, [mutation_check(output, prefix + name, code.replace(old, new), False, env, lean)])
    return records
