"""Check complete early failure protocols through the actual item constructor.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_caller_lookup_protocol as lookup
from assembly_item_creation_checks import checked_controls
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NS = lookup.NS
ITEM = lookup.protocol.native.OWNED + 'ConstructorItem.'
CTOR = ITEM + 'ProtocolTrace.'
MODULE = 'Compiler.Extraction.InternerConstructorProtocolFailureTests'
CLAIMS = [NS + name for name in ('finish_empty', 'capacity_recorded', 'capacity_projected',
    'scoped_initialization_failed', 'initialization_failed_projected')]
CLAIMS += [CTOR + name for name in ('item_capacity_projected', 'item_initialization_failed_projected',
    'FailureTests.initialization_oom', 'FailureTests.capacity_existing_family')]


def audit(rows):
    claims = {row['theorem']: set(row['dependencies']) for row in rows}
    required = {
        NS + 'finish_empty': {NS + 'finish', lookup.protocol.native.OWNED + 'cleanup'},
        NS + 'capacity_recorded': {NS + 'finish_empty', NS + 'findBody'},
        NS + 'capacity_projected': {NS + 'capacity_recorded', NS + 'scopeView'},
        NS + 'scoped_initialization_failed': {'Compiler.Extraction.Interner.Scoped.findDetailed',
                                             'Compiler.Extraction.Interner.FindCode.controlRun'},
        NS + 'initialization_failed_projected': {NS + 'initialization_projected', NS + 'finish_empty',
            NS + 'scoped_initialization_failed', lookup.protocol.native.OWNED + 'Caller.initialize_failed'},
        CTOR + 'item_capacity_projected': {NS + 'capacity_projected', CTOR + 'retire_outcome',
                                          CTOR + 'item_erases', ITEM + 'invoke_capacity_failed'},
        CTOR + 'item_initialization_failed_projected': {NS + 'initialization_failed_projected', CTOR + 'item_returned',
            CTOR + 'item_erases', ITEM + 'invoke_init_failed', ITEM + 'prepare_scratch'},
        CTOR + 'FailureTests.initialization_oom': {CTOR + 'item_initialization_failed_projected', ITEM + 'EntryFailureTests.failed_prefix'},
        CTOR + 'FailureTests.capacity_existing_family': {CTOR + 'item_capacity_projected', ITEM + 'CacheTests.prefix_observed'},
    }
    for name, expected in required.items():
        if missing := expected - claims[name]:
            raise ValueError('entry protocol lost shared source dependencies: ' + name + ': ' + ', '.join(sorted(missing)))
    statements = {row['theorem']: row['statement'] for row in rows}
    general = [NS + 'capacity_projected', NS + 'initialization_failed_projected',
               CTOR + 'item_capacity_projected', CTOR + 'item_initialization_failed_projected']
    for name in general:
        statement = statements[name]
        entries, _, _ = lookup.interface.domains(statement)
        if not {'model', 'source', 'request', 'before', 'leading', 'trailing', 'good', 'capacityQuery'} <= entries.keys():
            raise ValueError('entry protocol lost general inputs or initial contracts: ' + name)
        forbidden = {NS + n for n in ('find', 'findBody', 'finish', 'scopeView')}
        forbidden |= {CTOR + n for n in ('item', 'outcome')}
        forbidden |= {lookup.protocol.native.OWNED + n for n in ('Closed', 'cleanup', 'finish', 'Semantic.Ensures')}
        for field, (root, _) in entries.items():
            if lookup.interface.step.constants_below(statement, root) & forbidden:
                raise ValueError('entry protocol assumes its completed result or cleanup: ' + name + '.' + field)
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('production entry proof depends on fixtures: ' + name)
        constants = {node[1] for node in statement['nodes'] if node[0] == 'const'}
        needed = {NS + 'scopeView', 'Compiler.Extraction.Interner.Scoped.findDetailed',
                  'Compiler.Extraction.Interner.InvocationTrace.resources', lookup.protocol.native.OWNED + 'Closed'}
        if not needed <= constants:
            raise ValueError('entry protocol lost exact scoped result or native closure: ' + name)
        if name.startswith(CTOR):
            if not {'context', 'ports', 'constructed', 'address', 'domain', 'typed', 'made'} <= entries.keys():
                raise ValueError('item return lost actual typed preparation: ' + name)
            if CTOR + 'item' not in constants or 'allocated' in entries:
                raise ValueError('item return is detached or assumes scratch allocation: ' + name)
    return {'checkedDependencies': sorted(required), 'checkedStatements': general,
            'scratchAllocationDerivedForInitializationFailure': True,
            'takeFailureProtocolVerified': False, 'completeInvocationCorrespondenceVerified': False}


def mutation_cases():
    directory = lookup.harness.ROOT / 'lean/Compiler/Extraction'
    names = ('InternerCallerProtocolFailure', 'InternerConstructorProtocolFailure')
    raw = [(directory / (name + '.lean')).read_text() for name in names]
    imports = list(dict.fromkeys(line for text in raw for line in text.splitlines()
                                if line.startswith('import ') and not line.endswith(names[0])))
    source = '\n'.join(imports) + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n'
    source += '\n'.join(without_imports(text) for text in raw)
    mutations = [
        ('empty-owner', '(empty : before.native.scope = { lookup := none })', '(empty : before.native.scope.slice = none)', 1),
        ('capacity-guard', '(full : q.atCapacity before.graph = true)', '(full : q.atCapacity before.graph = false)', 2),
        ('init-capacity-guard', '(room : q.atCapacity before.graph = false)', '(room : q.atCapacity before.graph = true)', 1),
        ('init-ordinary-guard', '(completed : ordinary (.error fault : Except Fault NodeId) = true)',
         '(completed : ordinary (.error fault : Except Fault NodeId) = false)', 1),
        ('initial-source', '(good : Good source request.arguments before)', '(good : Good source [] before)', 4),
        ('scratch-shape', '(bufferLength : buffer.length = 2)', '(bufferLength : buffer.length = 1)', 1),
        ('init-result', 'actual.1 = .error fault ∧ actual.2.native = reached',
         'actual.1 = .error (.language .capacity) ∧ actual.2.native = reached', 1),
        ('reached-world', 'actual.2.native = reached ∧', 'actual.2.native = ⟨before, { lookup := none }⟩ ∧', 1),
        ('stream-order', '      let logical := Interner.Scoped.findDetailed (resources (actual.2.events ++ trailing)',
         '      let logical := Interner.Scoped.findDetailed (resources (trailing ++ actual.2.events)', 1),
        ('lost-stream', '      let logical := Interner.Scoped.findDetailed (resources (actual.2.events ++ trailing)',
         '      let logical := Interner.Scoped.findDetailed (resources trailing', 1),
        ('closed-scope', 'Closed actual.2.native.scope', '¬Closed actual.2.native.scope', 4),
        ('incomplete', 'actual.2.tokens.incomplete = false', 'actual.2.tokens.incomplete = true', 4),
        ('item-capacity', '(full : context.queries.atCapacity constructed.graph = true)',
         '(full : context.queries.atCapacity constructed.graph = false)', 1),
        ('item-room', '(room : context.queries.atCapacity constructed.graph = false)',
         '(room : context.queries.atCapacity constructed.graph = true)', 1),
        ('item-mark', 'returnWorld before.memory.memory.nextId constructed.memory.memory.nextId reached.world',
         'returnWorld constructed.memory.memory.nextId constructed.memory.memory.nextId reached.world', 1),
        ('item-ordinary', 'ordinary (.error fault : Except Fault NodeId) = true →',
         'ordinary (.error fault : Except Fault NodeId) = false →', 1),
    ]
    return source, mutations


def controls(output, env, lean):
    source, mutations = mutation_cases()
    records = checked_controls(output, [mutation_check(output, 'entry-protocol-unchanged', source, True, env, lean)])
    for name, before, after, count in mutations:
        if source.count(before) != count:
            raise ValueError('ambiguous entry protocol control: ' + name)
        records += checked_controls(output, [mutation_check(output, 'entry-protocol-' + name,
            source.replace(before, after), False, env, lean)])
    return records
