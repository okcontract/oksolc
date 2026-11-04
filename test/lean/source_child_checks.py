"""Audit query-backed child correspondence through the enclosing item step.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
import constructor_replay_choice_checks as choice
from assembly_item_creation_checks import checked_controls
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

EFFECTS = 'Compiler.Extraction.Dispatch.Effects.'
NESTED = 'Compiler.Extraction.Nested.'
TESTS = EFFECTS + 'SourceTests.'
MODULE = 'Compiler.Extraction.DispatchSourceConstructorsTests'
CLAIMS = [EFFECTS + name for name in ('Constructors.source', 'SourceConstructors.scalars',
    'drop_repeated_inputs', 'shift_mask_inputs', 'unary_with_inputs', 'binary_with_inputs',
    'simplify_options_with_inputs', 'simplify_with_inputs')]
CLAIMS += [TESTS + name for name in ('source_coupled', 'arbitrary_borrow_rejected', 'dispatch', 'dispatch_success')]
CLAIMS += [EFFECTS + name for name in ('SourceConstructors.at', 'simplify_at_debug',
    'simplify_options_with_inputs_at', 'simplify_with_inputs_at')]
CLAIMS += [TESTS + name for name in ('current_debug', 'other_debug_rejected', 'dispatch_current_debug', 'current_debug_success')]
INTERFACES = tuple(EFFECTS + name for name in ('SourceConstructors.mk', 'SourceConstructorsAt', 'atDebug'))


def audit(claims):
    required = {
        EFFECTS + 'drop_repeated_inputs': {EFFECTS + 'ReadBind.bind', EFFECTS + 'SourceConstructors.localOperation'},
        EFFECTS + 'shift_mask_inputs': {EFFECTS + 'ReadBind.bind', EFFECTS + 'SourceConstructors.borrowedOperation'},
        EFFECTS + 'unary_with_inputs': {EFFECTS + 'ReadBind.bind', EFFECTS + 'SourceConstructors.borrowedOperation'},
        EFFECTS + 'binary_with_inputs': {EFFECTS + name for name in
            ('drop_repeated_inputs', 'shift_mask_inputs', 'SourceConstructors.borrowedOperation', 'SourceConstructors.scalars')},
        EFFECTS + 'simplify_with_inputs': {EFFECTS + 'simplify_options_with_inputs'},
        gate.NS + 'dispatch_projects_framed_at': {EFFECTS + 'simplify_with_inputs_at'},
        TESTS + 'dispatch': {EFFECTS + 'simplify_with_inputs', TESTS + 'source_coupled'},
        TESTS + 'dispatch_success': {TESTS + 'dispatch'},
        EFFECTS + 'simplify_options_with_inputs_at': {EFFECTS + 'simplify_at_debug', EFFECTS + 'simplify_options_with_inputs'},
        EFFECTS + 'simplify_with_inputs_at': {EFFECTS + 'simplify_options_with_inputs_at'},
        TESTS + 'current_debug': {TESTS + 'source_coupled'},
        TESTS + 'dispatch_current_debug': {EFFECTS + 'simplify_with_inputs_at', TESTS + 'current_debug'},
        TESTS + 'current_debug_success': {TESTS + 'dispatch_current_debug'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('source child proof bypassed shared composition: ' + name)
    return {'checkedDependencies': sorted(required), 'queryBackedStorageChildren': True,
            'unrestrictedChildSimulationNotRequired': True, 'onlyCallerDebugRequired': True,
            'recursiveInductionVerified': False}


def audit_statements(rows, interfaces):
    definitions = {row['name']: row for row in interfaces}
    value = definitions[EFFECTS + 'SourceConstructorsAt']['value']
    _, root, context = gate.domains(value)
    args = joint.app(value, root, EFFECTS + 'SourceConstructors')
    if [gate.named(value, x, context) for x in args[-4:-2]] != ['r', 'reads']:
        raise ValueError('current-debug relation changes effects or query inputs')
    for term, builder in zip(args[-2:], ('left', 'right')):
        selected = joint.app(value, term, EFFECTS + 'atDebug')
        if [gate.named(value, x, context) for x in selected[-2:]] != [builder, 'debug']:
            raise ValueError('current-debug relation selects a different caller debug value')
    value = definitions[EFFECTS + 'atDebug']['value']
    _, root, context = gate.domains(value)
    methods = joint.app(value, root, 'Compiler.Extraction.Associative.Constructors.mk')[-5:]
    forwarding = {
        'operation': ['c', 'opcode', 'ids', 'debug'], 'constant': ['c', 'value', 'debug'],
        'materialize': ['c', 'id', 'value', 'debug'],
        'borrowedOperation': ['c', 'address', 'opcode', 'ids', 'debug'],
        'localOperation': ['c', 'opcode', 'source', 'selected', 'repeated', 'first', 'debug'],
    }
    for term, (method, expected) in zip(methods, forwarding.items()):
        local = context[:]
        while value['nodes'][term][0] == 'lambda':
            node = value['nodes'][term]
            local.append(node[1])
            term = node[4]
        args = joint.app(value, term, 'Compiler.Extraction.Associative.Constructors.' + method)
        if [gate.named(value, x, local) for x in args[2:]] != expected:
            raise ValueError('debug adapter changes native constructor arguments: ' + method)
    value = definitions[EFFECTS + 'SourceConstructors.mk']['type']
    fields, _, _ = gate.domains(value)
    if list(fields)[-5:] != ['operation', 'constant', 'materialize', 'borrowedOperation', 'localOperation']:
        raise ValueError('source child contract changed its constructor fields')
    for field in ('borrowedOperation', 'localOperation'):
        root, context = fields[field]
        index, local, parameters = root, context[:], []
        while value['nodes'][index][0] == 'forall':
            node = value['nodes'][index]
            parameters.append((node[1], node[3], local[:]))
            index, local = node[4], local + [node[1]]
        if len(parameters) != (6 if field == 'borrowedOperation' else 10):
            raise ValueError('source child law added or removed an input premise')
        _, query_root, local = parameters[3]
        query_eq = joint.app(value, query_root, 'Eq')
        query = joint.app(value, query_eq[-2], NESTED + 'Reads.operation')
        expected = ['reads', 'id', 'queried' if field == 'borrowedOperation' else 'opcode']
        if [gate.named(value, x, local) for x in query[-3:]] != expected:
            raise ValueError('child source no longer comes from the actual query')
        result = joint.app(value, query_eq[-1], 'Except.ok')
        found = joint.app(value, result[-1], 'Option.some')
        if gate.named(value, found[-1], local) != 'source':
            raise ValueError('child source differs from the queried slice')
        if field == 'localOperation':
            _, shape, scope = parameters[4]
            equality = joint.app(value, shape, 'Eq')
            joint.path(value, equality[-2], scope,
                ('List.length', 'Compiler.Extraction.Storage.ArgumentSlice.items'), 'source')
            _, bound, bound_scope = parameters[6]
            less = joint.app(value, bound, 'LT.lt')
            if gate.named(value, less[-2], bound_scope) != 'selected':
                raise ValueError('local overwrite bound checks another index')
            for term in (equality[-1], less[-1]):
                number = joint.app(value, term, 'OfNat.ofNat')
                if value['nodes'][number[-2]] != ['natural', '2']:
                    raise ValueError('local shape or overwrite extent is no longer binary')
        for builder in ('left', 'right'):
            calls = list(choice.applications(value, root, context, 'Compiler.Extraction.Associative.Constructors.' + field))
            found = [(args, scope) for args, scope in calls if gate.named(value, args[2], scope) == builder]
            if len(found) != 1:
                raise ValueError('child relation changed its physical/logical builders')
            args, scope = found[0]
            if field == 'borrowedOperation':
                for term, projection in ((args[-4], 'address'), (args[-2], 'items')):
                    joint.path(value, term, scope, ('Compiler.Extraction.Storage.ArgumentSlice.' + projection,), 'source')
                if [gate.named(value, args[i], scope) for i in (-3, -1)] != ['opcode', 'debug']:
                    raise ValueError('borrowed construction lost its requested opcode or debug')
            elif [gate.named(value, x, scope) for x in args[-6:]] != ['opcode', 'source', 'selected', 'repeated', 'first', 'debug']:
                raise ValueError('local construction changed its source/selection')
    statements = {row['theorem']: row['statement'] for row in rows}
    value = statements[joint.PNS + 'item_enclosing_replay_joint']
    fields, _, _ = gate.domains(value)
    args, context = choice.one_call(value, *fields['proper'], EFFECTS + 'SourceConstructorsAt')
    if gate.named(value, args[-3], context) != 'debug':
        raise ValueError('proper-child correspondence lost its caller debug value')
    read = joint.app(value, args[-4], NESTED + 'storageReads')
    if gate.named(value, read[-1], context) != 'childRows':
        raise ValueError('proper-child correspondence lost its actual row snapshot')
    if EFFECTS + 'Constructors' in gate.step.constants_below(value, fields['proper'][0]):
        raise ValueError('enclosing step still requires unrestricted storage children')
    return {'queryAndStorageArgumentsBound': True, 'enclosingStepUsesReachedRows': True,
            'enclosingStepUsesCallerDebug': True, 'allConstructorArgumentsForwarded': True}


def controls(output, env, lean):
    path = ROOT / 'lean/Compiler/Extraction/DispatchSourceConstructorsTests.lean'
    source = path.read_text()
    records = checked_controls(output, [mutation_check(output, 'source-children-unchanged', source, True, env, lean)])
    for name, before, after in (
        ('forged-address', 'if address = slice.address ∧ ids = slice.items', 'if address = 0 ∧ ids = slice.items'),
        ('forged-items', 'if address = slice.address ∧ ids = slice.items', 'if address = slice.address ∧ ids = []'),
        ('wrong-overwrite-bound', 'if source = slice ∧ selected < 2', 'if source = slice ∧ selected < 1'),
        ('arbitrary-borrow-success', 'else .error .unsupported\n    localOperation', 'else .ok 7\n    localOperation'),
        ('unrelated-debug', 'SourceConstructorsAt equality reads true physicalDebug logicalDebug',
            'SourceConstructorsAt equality reads false physicalDebug logicalDebug'),
        ('native-debug-mismatch', 'simplifyWithInputs reads physicalDebug 64 opISZERO [9] true',
            'simplifyWithInputs reads physicalDebug 64 opISZERO [9] false'),
    ):
        if source.count(before) != (2 if name == 'native-debug-mismatch' else 1):
            raise ValueError('ambiguous source-child control: ' + name)
        records += checked_controls(output, [mutation_check(output, 'source-children-' + name,
            source.replace(before, after), False, env, lean)])
    snapshot = '''import Compiler.Extraction.DispatchSourceConstructors
namespace Compiler.Extraction.Dispatch.Effects.SourceSnapshotControl
open Compiler.Extraction.Interner Compiler.Extraction.Nested
variable {Debug : Type} {m n : Type → Type} [Monad m] [Monad n]
  [MonadLift (Except Interner.Error) m] [MonadLift (Except Interner.Error) n]
example (r : Effects m n) (rows : List Storage.Cell)
    (left : Associative.Constructors Debug m) (right : Associative.Constructors Debug n)
    (coupled : SourceConstructors r (storageReads rows) left right) :
    SourceConstructors r (storageReads rows) left right := coupled
end Compiler.Extraction.Dispatch.Effects.SourceSnapshotControl
'''
    records += checked_controls(output, [mutation_check(output, 'source-children-snapshot-unchanged', snapshot, True, env, lean)])
    records += checked_controls(output, [mutation_check(output, 'source-children-wrong-query-snapshot',
        snapshot.replace('(storageReads rows)', '(storageReads [])', 1), False, env, lean)])
    raw = (ROOT / 'lean/Compiler/Extraction/DispatchDebugEffects.lean').read_text()
    header = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
    naturality = header + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)
    records += checked_controls(output, [mutation_check(output, 'debug-forwarding-unchanged', naturality, True, env, lean)])
    before = 'simplifyOptionsWithInputs reads c usizeBits instruction arguments debug options operand address query'
    if naturality.count(before) != 1:
        raise ValueError('ambiguous full dispatcher debug-forwarding control')
    for name, after in (
        ('wrong-instruction', before.replace(' instruction ', ' (instruction + 1) ')),
        ('wrong-root-address', before.replace(' address query', ' (address + 1) query')),
        ('snapshot-query', before.replace(' address query', ' address (fun action => readAction (action reads))')),
    ):
        records += checked_controls(output, [mutation_check(output, 'debug-forwarding-' + name,
            naturality.replace(before, after), False, env, lean)])
    return records
