"""Audit the local proper-child obligations consumed by complete item entry.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import re

import caller_prepared_entry_checks as prepared
import check_caller_lookup_protocol as lookup
from assembly_item_creation_checks import checked_controls
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NATIVE = lookup.NS + 'Native.'
CTOR = prepared.CTOR
CLAIMS = [NATIVE + 'initialized_miss_continuation', NATIVE + 'entry_continuation', CTOR + 'item_induction_projected']
DEFINITIONS = [NATIVE + 'MissInduction', NATIVE + 'EntryInduction']


def audit(rows, definitions):
    claims = {row['theorem']: set(row['dependencies']) for row in rows}
    statements = {row['theorem']: row['statement'] for row in rows}
    required = {
        NATIVE + 'initialized_miss_continuation': {lookup.NS + 'initialized_taken_recorded', NATIVE + 'miss_traced_verified'},
        NATIVE + 'entry_continuation': {NATIVE + 'initialized_miss_continuation', NATIVE + 'EntryInduction', NATIVE + 'MissInduction'},
        CTOR + 'item_induction_projected': {CTOR + 'ResourceEntry.item_projected', NATIVE + 'ResourceEntry.EntryInduction.of_unrestricted',
                                           CTOR + 'item_entry_projected', prepared.ITEM + 'prepare_success'},
        NATIVE + 'initialized_miss_traced': {NATIVE + 'initialized_miss_continuation', lookup.NS + 'find_projected'},
    }
    for name, dependencies in required.items():
        if missing := dependencies - claims[name]:
            raise ValueError('induction composition lost shared proof: ' + name + ': ' + ', '.join(sorted(missing)))
    forbidden = {lookup.NS + 'MissContinuation', CTOR + 'EntryContinuation', CTOR + 'EntryProjected', NATIVE + 'MissProjected'}
    for name in CLAIMS:
        statement = statements[name]
        domains, _, _ = lookup.interface.domains(statement)
        for field, (root, _) in domains.items():
            if lookup.interface.step.constants_below(statement, root) & forbidden:
                raise ValueError('induction proof assumes its final simulation: ' + name + '.' + field)
        if any(part.endswith('Tests') for dependency in claims[name] for part in dependency.split('.')):
            raise ValueError('general induction composition depends on a fixture: ' + name)
        if name != CLAIMS[0] and not {'model', 'induction', 'before', 'leading', 'trailing'} <= domains.keys():
            raise ValueError('induction composition lost fixed entry bindings: ' + name)
    if [record['name'] for record in definitions] != DEFINITIONS or any(record['kind'] != 'definition' for record in definitions):
        raise ValueError('local induction data are no longer inspectable')
    for record in definitions:
        constants = {node[1] for node in record['value']['nodes'] if node[0] == 'const'}
        if constants & forbidden:
            raise ValueError('local induction data assume final simulation')
        expected = ({prepared.NATIVE + 'InputFrame', prepared.OWNED + 'Recursive.projectionAt',
                     prepared.OWNED + 'MissStream.childCursor', prepared.NATIVE + 'ChildTrace.constructors',
                     prepared.OWNED + 'MissStream.replay', prepared.OWNED + 'MissStream.segment',
                     prepared.NATIVE + 'dispatchModel'} if record['name'] == DEFINITIONS[0]
                    else {DEFINITIONS[0], lookup.NS + 'record', prepared.OWNED + 'Caller.initLookup', prepared.OWNED + 'take'})
        if not expected <= constants:
            raise ValueError('local induction data lost native/child/replay bindings: ' + ', '.join(sorted(expected - constants)))
    return {'checkedDependencies': sorted(required), 'checkedStatements': CLAIMS, 'checkedDefinitions': DEFINITIONS,
            'callerContinuationDerived': True, 'reachedFrameAndReplayBindingRequired': True,
            'recursiveInductionVerified': False}


def mutation_cases():
    directory = lookup.harness.ROOT / 'lean/Compiler/Extraction'
    source = '\n'.join(without_imports((directory / (name + '.lean')).read_text()) for name in (
        'InternerCallerProtocolContinuation', 'InternerCallerProtocolInduction', 'InternerCallerResourceInduction',
        'InternerConstructorResourceEntries', 'InternerConstructorProtocolInduction',
        'InternerCallerProtocolInitializedMiss'))
    for name in ('initialized_miss_projected', 'initialized_miss_continuation', 'ResourceEntry', 'MissInduction', 'EntryInduction', 'entry_continuation',
                 'item_induction_projected', 'initialized_miss_traced'):
        source = re.sub(r'\b' + name + r'\b', name + 'Mutation', source)
    source = 'import ' + prepared.MODULE + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + source
    mutations = [
        ('wrong-child-cursor', 'MissStream.childCursor taken.events.length', 'MissStream.childCursor (taken.events.length + 1)', 2),
        ('wrong-frame-values', 'owner rows source request.arguments slice taken.native.world',
         'owner rows source [] slice taken.native.world', 2),
        ('wrong-replay-candidate', 'seed events observed.candidate mismatch) childModel', 'seed events none mismatch) childModel', 2),
        ('wrong-model-binding',
         'model = dispatchModel (MissStream.replay seed events observed.candidate mismatch) childModel usizeBits debug',
         'model = MissStream.replay seed events observed.candidate mismatch', 2),
        ('wrong-miss-prefix', 'taken.events ++ middle ++ observed.body', 'middle ++ taken.events ++ observed.body', 2),
        ('wrong-suffix-order', 'observed.body ++ observed.cleanup ++ trailing\n      model',
         'observed.body ++ trailing ++ observed.cleanup\n      model', 1),
        ('wrong-source-ownership', 'taken.native.scope = ⟨some handle, some slice, false⟩',
         'taken.native.scope = ⟨some handle, some slice, true⟩', 2),
        ('wrong-token-phase', 'taken.tokens = { lookup := some lookup, items := handle.values, phase := .cleanup }',
         'taken.tokens = { lookup := some lookup, items := handle.values, phase := .transfer }', 2),
        ('wrong-cache-guard', 'deterministic = true → before.native.world.graph.table key = none',
         'deterministic = false → before.native.world.graph.table key = none', 2),
        ('wrong-take-result', 'taken.1 = .ok () →', 'taken.1 = .error (.language .outOfMemory) →', 2),
        ('wrong-item-input', '(start { constructed with memory := { constructed.memory with memory } } leading)',
         '(start before leading)', 3),
        ('wrong-completion-guard', '(ordinary body.1 = true → actual.2.events =', '(ordinary body.1 = false → actual.2.events =', 2),
    ]
    return source, mutations


def controls(output, env, lean):
    source, mutations = mutation_cases()
    records = checked_controls(output, [mutation_check(output, 'entry-induction-unchanged', source, True, env, lean)])
    for name, before, after, count in mutations:
        if source.count(before) != count:
            raise ValueError('ambiguous induction control: ' + name + ': ' + str(source.count(before)))
        records += checked_controls(output, [mutation_check(output, 'entry-induction-' + name,
            source.replace(before, after), False, env, lean)])
    return records
