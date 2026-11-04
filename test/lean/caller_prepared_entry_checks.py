"""Audit producer-derived entry through the actual finite constructor family.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import re

import check_caller_lookup_protocol as lookup
import caller_take_protocol_checks as takes
from assembly_item_creation_checks import checked_controls
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

ITEM, CTOR = takes.ITEM, takes.CTOR
OWNED = lookup.protocol.native.OWNED
NATIVE = ITEM + 'NativeRecursion.'
CHILD = NATIVE + 'ProtocolTrace.'
MODULE = 'Compiler.Extraction.InternerRecursiveProtocolEntryTests'
CLAIMS = [ITEM + 'Arguments.error_nonordinary', OWNED + 'LocalArguments.error_nonordinary']
CLAIMS += [NATIVE + name for name in ('literal_error_nonordinary', 'local_error_nonordinary',
    'step_operation_verified', 'step_local_verified')]
CLAIMS += [CTOR + name for name in ('EntryProjected.of_outcome', 'prepared_entry_projected',
    'literal_entry_projected', 'local_entry_projected')]
CLAIMS += [CHILD + name + '_entry_projected' for name in ('operation', 'borrowed', 'constant', 'materialize', 'local')]
CLAIMS += [CHILD + 'EntryTests.' + name for name in ('capacity_observed', 'capacity_entries')]
DEFINITIONS = [CTOR + 'EntryProjected', CHILD + 'entryContext', CHILD + 'entryPorts']


def audit(rows, definitions):
    claims = {row['theorem']: set(row['dependencies']) for row in rows}
    statements = {row['theorem']: row['statement'] for row in rows}
    required = {
        NATIVE + 'literal_error_nonordinary': {ITEM + 'Arguments.error_nonordinary'},
        NATIVE + 'local_error_nonordinary': {OWNED + 'LocalArguments.error_nonordinary'},
        NATIVE + 'step_operation_verified': {ITEM + 'Arguments.error_nonordinary', NATIVE + 'prepared_invocation_verified'},
        NATIVE + 'step_local_verified': {OWNED + 'LocalArguments.error_nonordinary', NATIVE + 'prepared_invocation_verified'},
        CTOR + 'EntryProjected.of_outcome': {CTOR + 'EntryProjected', CTOR + 'outcome'},
        CTOR + 'prepared_entry_projected': {CTOR + 'item_entry_projected', CTOR + 'EntryProjected.of_outcome'},
        CTOR + 'literal_entry_projected': {CTOR + 'prepared_entry_projected', ITEM + 'Arguments.prepare_success',
            ITEM + 'Arguments.error_nonordinary', CTOR + 'retire_outcome'},
        CTOR + 'local_entry_projected': {CTOR + 'prepared_entry_projected', ITEM + 'ViewInput.local_input_optional',
            OWNED + 'LocalArguments.error_nonordinary', CTOR + 'retire_outcome'},
        CHILD + 'operation_entry_projected': {CTOR + 'literal_entry_projected'},
        CHILD + 'borrowed_entry_projected': {CTOR + 'item_entry_projected'},
        CHILD + 'constant_entry_projected': {CTOR + 'item_entry_projected'},
        CHILD + 'materialize_entry_projected': {CHILD + 'constant_entry_projected'},
        CHILD + 'local_entry_projected': {CTOR + 'local_entry_projected'},
        CHILD + 'EntryTests.capacity_entries': {CHILD + name + '_entry_projected'
            for name in ('operation', 'borrowed', 'constant', 'materialize', 'local')},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('prepared entry lost shared composition: ' + name + ': ' + ', '.join(sorted(missing)))
    general = [CTOR + name + '_entry_projected' for name in ('literal', 'local')]
    finite = [CHILD + name + '_entry_projected' for name in ('operation', 'borrowed', 'constant', 'materialize', 'local')]
    for name in general + finite:
        statement = statements[name]
        domains, _, _ = lookup.interface.domains(statement)
        if not {'model', 'debug', 'before', 'leading', 'trailing', 'admitted', 'typed',
                'capacityQuery', 'classificationQuery', 'miss'} <= domains.keys():
            raise ValueError('prepared entry lost its actual input/model bindings: ' + name)
        if {'prepared', 'constructed', 'made', 'ran', 'allocated', 'initialized', 'transferred'} & domains.keys():
            raise ValueError('prepared entry assumes a successful producer: ' + name)
        if any(part.endswith('Tests') for dependency in claims[name] for part in dependency.split('.')):
            raise ValueError('general prepared entry depends on a fixture: ' + name)
        forbidden = {CTOR + 'EntryProjected', OWNED + 'Closed', OWNED + 'Semantic.Ensures', NATIVE + 'ConstructorPost'}
        for field, (root, _) in domains.items():
            if lookup.interface.step.constants_below(statement, root) & forbidden:
                raise ValueError('prepared entry assumes final preservation: ' + name + '.' + field)
        constants = {node[1] for node in statement['nodes'] if node[0] == 'const'}
        needed = {CTOR + 'EntryProjected', CTOR + 'EntryContinuation'}
        if name in finite:
            needed |= {CHILD + 'unfold', CHILD + 'entryContext', CHILD + 'entryPorts'}
        if not needed <= constants:
            raise ValueError('prepared entry lost the complete actual family or reached miss: ' + name)
    if [record['name'] for record in definitions] != DEFINITIONS or any(record['kind'] != 'definition' for record in definitions):
        raise ValueError('prepared entry definitions are missing or no longer inspectable')
    projected, context, ports = definitions
    constants = {node[1] for node in projected['value']['nodes'] if node[0] == 'const'}
    if not {takes.NS + 'scopeView', OWNED + 'ordinary', 'Compiler.Extraction.Interner.Scoped.findDetailed',
            'Compiler.Extraction.Interner.InvocationTrace.resources'} <= constants:
        raise ValueError('prepared entry lost complete scoped semantics')
    # The context and ports must use the same actual proper depth. Inspect their
    # compiled argument bindings, not names occurring in source comments.
    for record, function in ((context, NATIVE + 'context'), (ports, takes.NS + 'Native.graphObservations')):
        value = record['value']
        _, conclusion, names = lookup.interface.domains(value)
        head, args = lookup.interface.applied(value, conclusion)
        if head[:2] != ['const', function] or lookup.interface.named(value, args[-1], names) != 'debug':
            raise ValueError('finite entry changed its native context or debug binding')
        child = args[-2] if record is context else args[-3]
        child_head, child_args = lookup.interface.applied(value, child)
        if child_head[:2] != ['const', NATIVE + 'unfold'] or lookup.interface.named(value, child_args[-1], names) != 'depth':
            raise ValueError('finite entry does not call its actual proper-depth native children')
        if record is ports:
            observer, observation_args = lookup.interface.applied(value, args[-2])
            if observer[:2] != ['const', CHILD + 'observe']:
                raise ValueError('finite entry uses supplied child observations')
            family, family_args = lookup.interface.applied(value, observation_args[-1])
            if family[:2] != ['const', CHILD + 'unfold'] or lookup.interface.named(value, family_args[-1], names) != 'depth':
                raise ValueError('finite entry observes a different child depth')
    return {'checkedDependencies': sorted(required), 'checkedStatements': general + finite,
            'producerPreparationDerived': True, 'finiteChildrenAndObservationsBound': True,
            'completeInvocationCorrespondenceVerified': False, 'recursiveInductionVerified': False}


def mutation_cases():
    directory = lookup.harness.ROOT / 'lean/Compiler/Extraction'
    raw = '\n'.join(without_imports((directory / (name + '.lean')).read_text()) for name in (
        'InternerArgumentPreparationFailure', 'InternerConstructorProtocolPreparedEntry', 'InternerRecursiveProtocolEntry'))
    for name in ('error_nonordinary', 'EntryProjected', 'prepared_entry_projected', 'literal_entry_projected',
                 'local_entry_projected', 'operation_entry_projected', 'borrowed_entry_projected',
                 'constant_entry_projected', 'materialize_entry_projected', 'entryContext', 'entryPorts'):
        raw = re.sub(r'\b' + name + r'\b', name + 'Mutation', raw)
    # Unroll exactly the selected parent, leaving both proper-child families
    # opaque. A bad child binding must give a type mismatch rather than spend
    # the elaboration budget unfolding an unrelated recursive execution.
    parent = '(unfold ops allocate safety owner meaning base growth usizeBits (depth + 1))'
    if raw.count(parent) != 5:
        raise ValueError('finite entry control lost its five actual successor fields')
    expanded = ('(step ops allocate safety owner meaning base growth usizeBits '
                '(NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth) '
                '(observe (unfold ops allocate safety owner meaning base growth usizeBits depth)))')
    raw = raw.replace(parent, expanded)
    source = ('import ' + MODULE + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n'
              + 'attribute [local irreducible] ' + NATIVE + 'unfold ' + CHILD + 'unfold ' + CHILD + 'observe ' + CTOR + 'item\n' + raw)
    mutations = [
        ('ordinary-preparation-error', 'ordinary (.error fault : Except Fault NodeId) = false',
         'ordinary (.error fault : Except Fault NodeId) = true', 3),
        ('rewind-rejected-state', '(.error fault, start reached leading)', '(.error fault, start before leading)', 1),
        ('discard-rejected-history', '(.error fault, start reached leading)', '(.error fault, start reached [])', 1),
        ('ordinary-guard', 'ordinary actual.1 = true →', 'ordinary actual.1 = false →', 1),
        ('wrong-stream-order', 'actual.2.events ++ trailing', 'trailing ++ actual.2.events', 1),
        ('wrong-cursor', '{ before with allocationCursor := leading.length }', '{ before with allocationCursor := leading.length + 1 }', 1),
        ('incomplete-result', 'actual.2.tokens.incomplete = false', 'actual.2.tokens.incomplete = true', 1),
        ('wrong-result', 'logical.1.mapError Fault.language, logical.2', 'Except.error (.language .outOfMemory), logical.2', 1),
        ('wrong-prepared-values', 'Arguments.Prepared request.arguments before source prepared', 'Arguments.Prepared [] before source prepared', 1),
        ('stale-item-input', 'returned (item context ports source request debug prepared leading)',
         'returned (item context ports source request debug before leading)', 1),
        ('wrong-literal-mark', '(fun ran => if values.isEmpty then ran else retire before.memory.memory.nextId ran)',
         '(fun ran => if values.isEmpty then ran else retire 0 ran)', 1),
        ('wrong-local-mark', '(retire before.memory.memory.nextId) rfl (retire_outcome _)', '(retire 0) rfl (retire_outcome _)', 1),
        ('wrong-index-guard', 'inside : first = true → selected < 2', 'inside : first = false → selected < 2', 2),
        ('wrong-native-depth', 'owner usizeBits depth) debug', 'owner usizeBits (depth + 1)) debug', 1),
        ('wrong-observed-depth', '(observe (unfold ops allocate safety owner meaning base growth usizeBits depth)) debug',
         '(observe (unfold ops allocate safety owner meaning base growth usizeBits (depth + 1))) debug', 1),
        ('wrong-materialized-value', ').materialize id value debug before leading', ').materialize id 0 debug before leading', 1),
    ]
    return source, mutations


def controls(output, env, lean):
    source, mutations = mutation_cases()
    records = checked_controls(output, [mutation_check(output, 'prepared-entry-unchanged', source, True, env, lean)])
    for name, before, after, count in mutations:
        if source.count(before) != count:
            raise ValueError('ambiguous prepared entry control: ' + name + ': ' + str(source.count(before)))
        records += checked_controls(output, [mutation_check(output, 'prepared-entry-' + name,
            source.replace(before, after), False, env, lean)])
    return records
