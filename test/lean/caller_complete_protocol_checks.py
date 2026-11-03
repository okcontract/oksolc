"""Audit general caller composition and its local proper-child continuation.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import json
import re

import caller_take_protocol_checks as takes
import caller_prepared_entry_checks as prepared
import caller_induction_checks as induction
import check_caller_lookup_protocol as lookup
from assembly_item_creation_checks import checked_controls
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NS, ITEM, CTOR = takes.NS, takes.ITEM, takes.CTOR
CHILD = ITEM + 'NativeRecursion.ProtocolTrace.'
MODULE = prepared.MODULE
CLAIMS = [NS + name for name in ('missBody_prefix', 'miss_finish_history', 'taken_find_projected',
    'find_projected', 'Native.initialized_miss_traced')]
CLAIMS += [CTOR + name for name in ('item_projected', 'item_miss_traced', 'CompleteTests.refused_family', 'CompleteTests.capacity_family')]
CLAIMS += [CHILD + name + '_miss_bound' for name in ('borrowed', 'constant', 'materialize', 'operation', 'local')]
CLAIMS += [ITEM + 'prepare_error_nonordinary', ITEM + 'NativeRecursion.step_invocation_verified']
CLAIMS += [CTOR + name for name in ('item_rejected', 'item_entry_projected', 'EntryTests.preparation_rejections')]
CLAIMS += prepared.CLAIMS
CLAIMS += induction.CLAIMS


def continuation_export(output, env, lean):
    declarations = [NS + 'MissContinuation', CTOR + 'EntryContinuation'] + prepared.DEFINITIONS + induction.DEFINITIONS
    names = ', '.join('``' + name for name in declarations)
    source = 'import ' + MODULE + '''
import Contract.Check.Declarations
import Lean.Elab.Command
open Lean Elab Command Contract.Check in
run_cmd do
  let mut records := #[]
  for name in #[''' + names + '''] do
    let some info := (← getEnv).find? name | throwError "missing continuation"
    records := records.push (Declarations.encode info)
  liftIO <| IO.println (Json.arr records).compress
'''
    (output / 'continuation.lean').write_text(source)
    lookup.harness.run(output, 'continuation', [lean, '-DwarningAsError=true', output / 'continuation.lean'],
        cwd=lookup.harness.ROOT / 'lean', env=env)
    raw = (output / 'continuation.stdout').read_bytes()
    (output / 'continuation.json').write_bytes(raw)
    return json.loads(raw)


def audit(rows, continuation):
    if len(continuation) != 2 + len(prepared.DEFINITIONS) + len(induction.DEFINITIONS):
        raise ValueError('missing local continuation definition')
    continuation, entry, *prepared_definitions = continuation
    induction_definitions = prepared_definitions[len(prepared.DEFINITIONS):]
    prepared_definitions = prepared_definitions[:len(prepared.DEFINITIONS)]
    claims = {row['theorem']: set(row['dependencies']) for row in rows}
    required = {
        NS + 'missBody_prefix': {NS + 'record_prefix'},
        NS + 'miss_finish_history': {NS + 'missBody_prefix', NS + 'invoke_prefix'},
        NS + 'taken_find_projected': {NS + part for part in ('initialized_taken_recorded', 'findBody_taken', 'scoped_taken',
            'miss_finish_history', 'MissContinuation')},
        NS + 'find_projected': {NS + part for part in ('capacity_projected', 'initialization_failed_projected',
            'classification_projected', 'lookup_projected', 'take_failed_projected', 'taken_find_projected')}
            | {lookup.protocol.native.OWNED + 'Caller.initialized_key'},
        NS + 'Native.initialized_miss_traced': {NS + 'find_projected', NS + 'Native.miss_traced_verified'},
        CTOR + 'item_projected': {NS + 'find_projected', CTOR + 'item_capacity_projected', CTOR + 'item_returned', ITEM + 'prepare_scratch'},
        CTOR + 'item_rejected': {CTOR + 'item', ITEM + 'prepare_error_nonordinary'},
        CTOR + 'item_entry_projected': {CTOR + 'item_projected', CTOR + 'item_rejected', ITEM + 'prepare_success'},
        ITEM + 'NativeRecursion.step_invocation_verified': {ITEM + 'prepare_error_nonordinary'},
        CTOR + 'EntryTests.preparation_rejections': {CTOR + 'item_rejected', ITEM + 'Tests.preparation_rejections'},
        CTOR + 'item_miss_traced': {NS + 'find_projected', NS + 'Native.initialized_miss_traced'},
        CTOR + 'CompleteTests.refused_family': {CTOR + 'item_entry_projected', ITEM + 'TakeFailureTests.failed_observed', ITEM + 'TakeFailureTests.failed_contract'},
        CTOR + 'CompleteTests.capacity_family': {CTOR + 'item_entry_projected'},
    }
    for name in ('borrowed', 'constant', 'materialize', 'operation', 'local'):
        required[CHILD + name + '_miss_bound'] = {CTOR + 'item_miss_traced', NS + 'find_projected'}
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('general caller lost composition: ' + name + ': ' + ', '.join(sorted(missing)))
    statements = {row['theorem']: row['statement'] for row in rows}
    general = [NS + 'find_projected', CTOR + 'item_projected', CTOR + 'item_entry_projected']
    forbidden = {NS + part for part in ('find', 'findBody', 'finish', 'scopeView')}
    forbidden |= {CTOR + part for part in ('item', 'outcome')}
    forbidden |= {lookup.protocol.native.OWNED + part for part in ('Closed', 'Semantic.Ensures')}
    for name in general:
        statement = statements[name]
        entries, _, _ = lookup.interface.domains(statement)
        if not {'source', 'request', 'before', 'model', 'leading', 'trailing', 'admitted',
                'capacityQuery', 'classificationQuery'} <= entries.keys():
            raise ValueError('general caller lost actual inputs or query bindings: ' + name)
        if {'initialized', 'classified', 'transferred', 'room', 'decoded', 'keyed', 'absent'} & entries.keys():
            raise ValueError('general caller regained a successful-prefix premise: ' + name)
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('general caller depends on a fixture: ' + name)
        for field, (root, _) in entries.items():
            if lookup.interface.step.constants_below(statement, root) & forbidden:
                raise ValueError('general caller assumes its final simulation: ' + name + '.' + field)
        constants = {node[1] for node in statement['nodes'] if node[0] == 'const'}
        local_continuation = CTOR + 'EntryContinuation' if name == CTOR + 'item_entry_projected' else NS + 'MissContinuation'
        if not {local_continuation, NS + 'scopeView', 'Compiler.Extraction.Interner.Scoped.findDetailed',
                'Compiler.Extraction.Interner.InvocationTrace.resources'} <= constants:
            raise ValueError('general caller lost its local obligation or complete result: ' + name)
        if name == CTOR + 'item_projected' and ('allocated' in entries or not {'domain', 'typed', 'made'} <= entries.keys()):
            raise ValueError('item projection lost typed preparation or derived scratch')
        if name == CTOR + 'item_entry_projected' and (
                {'constructed', 'address', 'memory', 'made', 'allocated'} & entries.keys()
                or not {'domain', 'typed', 'miss'} <= entries.keys()):
            raise ValueError('complete item entry assumes successful preparation or loses typed input')
    if continuation['kind'] != 'definition' or continuation['name'] != NS + 'MissContinuation':
        raise ValueError('local continuation is no longer an inspectable definition')
    constants = {node[1] for node in continuation['value']['nodes'] if node[0] == 'const'}
    local = {NS + name for name in ('record', 'missBody', 'finish', 'scopeView')}
    local |= {lookup.protocol.native.OWNED + 'Caller.initLookup', lookup.protocol.native.OWNED + 'take',
        'Compiler.Extraction.Interner.FindCode.controlMiss', 'Compiler.Extraction.Interner.Scoped.close'}
    enclosing = {NS + name for name in ('find', 'findBody', 'find_projected')}
    enclosing |= {CTOR + 'item', 'Compiler.Extraction.Interner.Scoped.findDetailed'}
    if not local <= constants or enclosing & constants:
        raise ValueError('miss continuation is not local to the reached miss/cleanup')
    if entry['kind'] != 'definition' or entry['name'] != CTOR + 'EntryContinuation':
        raise ValueError('item-entry continuation is not an inspectable definition')
    constants = {node[1] for node in entry['value']['nodes'] if node[0] == 'const'}
    needed = {ITEM + 'prepare', 'Compiler.ZigAir.Memory.allocate', NS + 'MissContinuation', CTOR + 'start'}
    if not needed <= constants or enclosing & constants:
        raise ValueError('item continuation assumes its complete invocation or loses reached preparation')
    _, conclusion, context = lookup.interface.domains(entry['value'])
    head, arguments = lookup.interface.applied(entry['value'], conclusion)
    if head[:2] != ['const', NS + 'MissContinuation']:
        raise ValueError('item continuation does not consume the existing local miss')
    named = lambda index: lookup.interface.named(entry['value'], arguments[index], context)
    if (named(-6), named(-5), named(-3), named(-1)) != ('model', 'source', 'request', 'trailing'):
        raise ValueError('item continuation changed its model, source, request or suffix')
    if CTOR + 'start' not in lookup.interface.step.constants_below(entry['value'], arguments[-2]):
        raise ValueError('item continuation lost its actual prepared caller input')
    return {'checkedDependencies': sorted(required), 'checkedStatements': general,
            'localContinuationInspected': True, 'itemEntryContinuationInspected': True, 'successfulPrefixDerived': True,
            'itemPreparationDerived': True, 'preparedEntries': prepared.audit(rows, prepared_definitions),
            'entryInduction': induction.audit(rows, induction_definitions),
            'completeInvocationCorrespondenceVerified': False, 'recursiveInductionVerified': False}


def mutation_cases():
    directory = lookup.harness.ROOT / 'lean/Compiler/Extraction'
    raw = '\n'.join(without_imports((directory / (name + '.lean')).read_text()) for name in (
        'InternerCallerProtocolComplete', 'InternerConstructorProtocolComplete'))
    for name in ('MissContinuation', 'taken_find_projected', 'find_projected', 'item_projected'):
        raw = re.sub(r'\b' + name + r'\b', name + 'Mutation', raw)
    source = 'import ' + MODULE + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + raw
    mutations = [
        ('ordinary-guard', 'ordinary body.1 = true →', 'ordinary body.1 = false →', 3),
        ('item-ordinary-guard', 'ordinary actual.1 = true', 'ordinary actual.1 = false', 1),
        ('source-values', 'Represents before.memory.memory source request.arguments', 'Represents before.memory.memory source []', 2),
        ('scratch-width', '(.array 2 word) = .ok (pointer, memory)', '(.array 1 word) = .ok (pointer, memory)', 2),
        ('capacity-binding', '= q.atCapacity before.graph)', '= !q.atCapacity before.graph)', 2),
        ('classifier-binding', '= q.deterministic request.item)', '= .ok true)', 2),
        ('local-values', 'Interner.makeKey request values = .ok key →', 'Interner.makeKey request [] = .ok key →', 1),
        ('local-cache-guard', 'deterministic = true → before.native.world.graph.table key = none',
         'deterministic = false → before.native.world.graph.table key = none', 1),
        ('local-take-result', 'taken.1 = .ok () →', 'taken.1 = .error (.language .outOfMemory) →', 1),
        ('local-pre-take-state', 'request key deterministic taken.2', 'request key deterministic normalized.2', 1),
        ('local-stream-order', 'resources (actual.2.events ++ trailing)', 'resources (trailing ++ actual.2.events)', 5),
        ('caller-completeness', 'actual.2.tokens.incomplete = false', 'actual.2.tokens.incomplete = true', 5),
        ('caller-result', 'logical.1.mapError Fault.language, logical.2', 'Except.error (.language .outOfMemory), logical.2', 4),
        ('item-source-values', '(good : Good source request.arguments before)', '(good : Good source [] before)', 1),
        ('item-source-capacity', '= context.queries.atCapacity constructed.graph)', '= !context.queries.atCapacity constructed.graph)', 1),
        ('item-source-classifier', '= context.queries.deterministic request.item)', '= .ok true)', 1),
    ]
    return source, mutations


def controls(output, env, lean):
    source, mutations = mutation_cases()
    records = checked_controls(output, [mutation_check(output, 'complete-protocol-unchanged', source, True, env, lean)])
    for name, before, after, count in mutations:
        if source.count(before) != count:
            raise ValueError('ambiguous complete protocol control: ' + name + ': ' + str(source.count(before)))
        records += checked_controls(output, [mutation_check(output, 'complete-protocol-' + name,
            source.replace(before, after), False, env, lean)])
    return records + entry_controls(output, env, lean) + prepared.controls(output, env, lean) + induction.controls(output, env, lean)


def entry_mutation_cases():
    directory = lookup.harness.ROOT / 'lean/Compiler/Extraction'
    preparation = (directory / 'AssemblyItemConstructorLocal.lean').read_text()
    preparation = preparation[preparation.index('theorem prepare_error_nonordinary'):preparation.rindex('\nend ')]
    source = 'import ' + MODULE + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n'
    source += 'namespace ' + ITEM[:-1] + '\nopen Compiler.Algebraic Compiler.Extraction.Cache\n'
    source += 'open Compiler.ZigAir.Memory.WordArray AssemblyItem.Fields\n' + preparation + '\nend ' + ITEM[:-1] + '\n'
    source += without_imports((directory / 'InternerConstructorProtocolEntry.lean').read_text())
    for name in ('prepare_error_nonordinary', 'EntryContinuation', 'item_rejected', 'item_entry_projected'):
        source = re.sub(r'\b' + name + r'\b', name + 'Mutation', source)
    mutations = [
        ('ordinary-preparation-error', 'ordinary (.error fault : Except Fault NodeId) = false',
         'ordinary (.error fault : Except Fault NodeId) = true', 1),
        ('rewind-rejected-state', '(.error fault, start reached leading)', '(.error fault, start before leading)', 2),
        ('discard-rejected-history', '(.error fault, start reached leading)', '(.error fault, start reached [])', 2),
        ('ordinary-guard', 'ordinary actual.1 = true →', 'ordinary actual.1 = false →', 1),
        ('wrong-source', '(good : Good source request.arguments before)', '(good : Good source [] before)', 1),
        ('wrong-cursor', 'allocationCursor := leading.length', 'allocationCursor := leading.length + 1', 2),
        ('wrong-stream-order', 'actual.2.events ++ trailing', 'trailing ++ actual.2.events', 1),
        ('incomplete-result', 'actual.2.tokens.incomplete = false', 'actual.2.tokens.incomplete = true', 1),
        ('wrong-capacity-guard', 'context.queries.atCapacity constructed.graph = false →',
         'context.queries.atCapacity constructed.graph = true →', 1),
        ('wrong-prepared-input', 'prepare request.item debug before = (.ok address, constructed) →',
         'prepare request.item debug before = (.error (.language .outOfMemory), constructed) →', 1),
        ('wrong-scratch-width', 'allocate constructed.memory.memory (.array 2 word)',
         'allocate constructed.memory.memory (.array 1 word)', 1),
        ('stale-caller-state', '(start { constructed with memory := { constructed.memory with memory } } leading)',
         '(start before leading)', 2),
        ('wrong-result', 'logical.1.mapError Fault.language, logical.2',
         'Except.error (.language .outOfMemory), logical.2', 1),
    ]
    return source, mutations


def entry_controls(output, env, lean):
    source, mutations = entry_mutation_cases()
    records = checked_controls(output, [mutation_check(output, 'item-entry-unchanged', source, True, env, lean)])
    for name, before, after, count in mutations:
        if source.count(before) != count:
            raise ValueError('ambiguous item entry control: ' + name + ': ' + str(source.count(before)))
        records += checked_controls(output, [mutation_check(output, 'item-entry-' + name,
            source.replace(before, after), False, env, lean)])
    return records
