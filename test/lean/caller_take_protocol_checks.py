"""Check refused borrowing and the shared recorded prefix/source routing.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import re

import check_caller_lookup_protocol as lookup
import initialized_protocol_checks as initialized
from assembly_item_creation_checks import checked_controls
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NS = lookup.NS
ITEM = lookup.protocol.native.OWNED + 'ConstructorItem.'
CTOR = ITEM + 'ProtocolTrace.'
MODULE = 'Compiler.Extraction.InternerConstructorProtocolTakeFailureTests'
CLAIMS = [NS + name for name in ('initialized_recorded', 'initialized_taken_recorded',
    'findBody_after_take', 'scoped_after_take', 'findBody_taken', 'scoped_taken',
    'take_refused_recorded', 'take_failed_projected', 'TakenTests.spare_prefix', 'TakenTests.nondeterministic_spare')]
CLAIMS += [CTOR + name for name in ('item_take_failed_projected', 'TakeFailureTests.existing_family')]
CLAIMS += [ITEM + 'TakeFailureTests.allocation_boundaries']


def audit(rows):
    claims = {row['theorem']: set(row['dependencies']) for row in rows}
    required = {
        NS + 'initialized_recorded': {NS + 'initialization_projected', lookup.protocol.native.OWNED + 'Caller.Initialization.successful_stream'},
        NS + 'initialized_taken_recorded': {NS + 'initialized_recorded', lookup.protocol.native.OWNED + 'Caller.Take.initialized_taken_stream'},
        NS + 'findBody_after_take': {NS + 'findBody', NS + 'missBody', 'Compiler.Extraction.Interner.FindCode.controlRun'},
        NS + 'scoped_after_take': {'Compiler.Extraction.Interner.Scoped.findDetailed', 'Compiler.Extraction.Interner.FindCode.controlRun'},
        NS + 'findBody_taken': {NS + 'findBody_after_take'},
        NS + 'scoped_taken': {NS + 'scoped_after_take'},
        NS + 'take_refused_recorded': {NS + 'take_projected', 'Compiler.Extraction.Cache.NormalizationOwnership.take_with_failure'},
        NS + 'take_failed_projected': {NS + name for name in ('initialized_recorded', 'take_refused_recorded',
            'findBody_after_take', 'scoped_after_take', 'lookup_close_projected')},
        NS + 'TakenTests.spare_prefix': {NS + 'initialized_taken_recorded', NS + 'findBody_taken'},
        NS + 'TakenTests.nondeterministic_spare': {NS + 'TakenTests.spare_prefix'},
        CTOR + 'item_take_failed_projected': {NS + 'take_failed_projected', CTOR + 'item_returned', CTOR + 'item_erases',
            ITEM + 'prepare_scratch', ITEM + 'invoke_take_failed'},
        CTOR + 'TakeFailureTests.existing_family': {CTOR + 'item_take_failed_projected', ITEM + 'TakeFailureTests.prefix_observed',
            ITEM + 'TakeFailureTests.failed_observed'},
        ITEM + 'TakeFailureTests.allocation_boundaries': {ITEM + 'TakeFailureTests.taken'},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('take protocol lost shared dependencies: ' + name + ': ' + ', '.join(sorted(missing)))
    statements = {row['theorem']: row['statement'] for row in rows}
    general = [NS + 'initialized_recorded', NS + 'take_failed_projected', CTOR + 'item_take_failed_projected']
    for name in general:
        statement = statements[name]
        entries, _, _ = lookup.interface.domains(statement)
        needed = {'source', 'request', 'before', 'leading', 'admitted'}
        if name != NS + 'initialized_recorded':
            needed |= {'model', 'trailing', 'capacityQuery', 'classificationQuery'}
        if not needed <= entries.keys():
            raise ValueError('take protocol lost general inputs or source binding: ' + name)
        forbidden = {NS + part for part in ('find', 'findBody', 'finish', 'scopeView')}
        forbidden |= {CTOR + part for part in ('item', 'outcome')}
        forbidden |= {lookup.protocol.native.OWNED + part for part in ('Closed', 'cleanup', 'finish', 'Semantic.Ensures')}
        for field, (root, _) in entries.items():
            if lookup.interface.step.constants_below(statement, root) & forbidden:
                raise ValueError('take protocol assumes complete execution or cleanup: ' + name + '.' + field)
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('general take protocol depends on a fixture: ' + name)
        constants = {node[1] for node in statement['nodes'] if node[0] == 'const'}
        if name != NS + 'initialized_recorded':
            expected = {NS + 'scopeView', 'Compiler.Extraction.Interner.Scoped.findDetailed',
                        'Compiler.Extraction.Interner.InvocationTrace.resources', lookup.protocol.native.OWNED + 'Closed'}
            if not expected <= constants:
                raise ValueError('take protocol lost full source/scoped result: ' + name)
        if name.startswith(CTOR):
            if not {'context', 'ports', 'domain', 'typed', 'made'} <= entries.keys() or 'allocated' in entries:
                raise ValueError('item take failure lost actual producer or derived scratch allocation')
            if not {CTOR + 'item', ITEM + 'returnWorld'} <= constants:
                raise ValueError('item take failure lost actual return or reached native world')
    return {'checkedDependencies': sorted(required), 'checkedStatements': general,
            'scratchAllocationDerived': True, 'successfulPathRootsAudited': True,
            'completeInvocationCorrespondenceVerified': False, 'recursiveInductionVerified': False}


def mutation_cases():
    directory = lookup.harness.ROOT / 'lean/Compiler/Extraction'
    names = ('InternerCallerProtocolPrefix', 'InternerCallerProtocolTaken',
             'InternerCallerProtocolTakeFailure', 'InternerConstructorProtocolTakeFailure')
    raw = '\n'.join(without_imports((directory / (name + '.lean')).read_text()) for name in names)
    for name in ('initialized_recorded', 'initialized_taken_recorded', 'findBody_after_take', 'scoped_after_take',
                 'findBody_taken', 'scoped_taken', 'take_refused_recorded', 'take_failed_projected', 'item_take_failed_projected'):
        raw = re.sub(r'\b' + name + r'\b', name + 'Mutation', raw)
    source = 'import ' + MODULE + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + raw
    mutations = [
        ('prefix-source', 'Represents before.memory.memory source request.arguments', 'Represents before.memory.memory source []', 3),
        ('prefix-ready', 'Ready allocator source request.arguments handle prepared.world.memory ∧',
         'Ready allocator source [] handle prepared.world.memory ∧', 1),
        ('refusal-guard', 'captured.1.1 = false ∧ captured.1.2 = token origin handle',
         'captured.1.1 = true ∧ captured.1.2 = token origin handle', 1),
        ('refusal-token', 'captured.1.2 = token origin handle ∧', 'captured.1.2 = { token origin handle with owner := .caller } ∧', 1),
        ('refusal-native', 'let entry : Recorded σ := ⟨reached, input.tokens, leading ++ captured.2.events.map Event.normalization⟩',
         'let entry : Recorded σ := ⟨⟨before, { lookup := some handle }⟩, input.tokens, leading ++ captured.2.events.map Event.normalization⟩', 1),
        ('refusal-history', 'let entry : Recorded σ := ⟨reached, input.tokens, leading ++ captured.2.events.map Event.normalization⟩',
         'let entry : Recorded σ := ⟨reached, input.tokens, leading⟩', 1),
        ('refusal-result', 'fault = .language .outOfMemory ∧ reached.scope', 'fault = .language .capacity ∧ reached.scope', 1),
        ('caller-capacity', '(room : q.atCapacity before.graph = false)', '(room : q.atCapacity before.graph = true)', 1),
        ('caller-classifier', '(classified : q.deterministic request.item = .ok deterministic)',
         '(classified : q.deterministic request.item = .ok (!deterministic))', 3),
        ('caller-cache-guard', '(absent : deterministic = true → before.graph.table key = none)',
         '(absent : deterministic = false → before.graph.table key = none)', 1),
        ('caller-cache-key', '(made : Interner.makeKey request values = .ok key)',
         '(made : Interner.makeKey request [] = .ok key)', 5),
        ('caller-closure', 'Closed actual.2.native.scope', '¬Closed actual.2.native.scope', 2),
        ('caller-completeness', 'actual.2.tokens.incomplete = false', 'actual.2.tokens.incomplete = true', 2),
        ('item-stream-order', '      let logical := Interner.Scoped.findDetailed (resources (actual.2.events ++ trailing)',
         '      let logical := Interner.Scoped.findDetailed (resources (trailing ++ actual.2.events)', 1),
        ('item-lost-stream', '      let logical := Interner.Scoped.findDetailed (resources (actual.2.events ++ trailing)',
         '      let logical := Interner.Scoped.findDetailed (resources trailing', 1),
        ('item-reached-world', 'constructed.memory.memory.nextId reached.world ∧', 'constructed.memory.memory.nextId before ∧', 1),
        ('item-cleanup-mark', 'returnWorld before.memory.memory.nextId constructed.memory.memory.nextId reached.world',
         'returnWorld constructed.memory.memory.nextId constructed.memory.memory.nextId reached.world', 1),
    ]
    return source, mutations


def controls(output, env, lean):
    source, mutations = mutation_cases()
    records = checked_controls(output, [mutation_check(output, 'take-protocol-unchanged', source, True, env, lean)])
    for name, before, after, count in mutations:
        if source.count(before) != count:
            raise ValueError('ambiguous take protocol control: ' + name)
        records += checked_controls(output, [mutation_check(output, 'take-protocol-' + name,
            source.replace(before, after), False, env, lean)])
    return records + initialized.controls(output, env, lean)
