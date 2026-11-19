"""Audit model construction from native child induction obligations.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
import constructor_replay_choice_checks as choice
from assembly_item_creation_checks import checked_controls
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NS = gate.OWNED + 'Recursive.Uniform.'
PNS = joint.PNS
MODULE = 'Compiler.Extraction.InternerNativeAllocationAdmissionTests'
NATIVE = gate.ITEM + 'NativeAllocationAdmissionTests.'
FRAME_MAP = gate.ITEM + 'NativeRecursion.CallFrame.mapAllocator_iff'
CORE = ('ordinary_language', 'action_at', 'projects', 'agrees_of_projects', 'exists_iff', 'safe')
CHILDREN = ('source_projects', 'request_safe', 'constructors_sound', 'constructors_address', 'constructors_sar', 'proper')
TESTS = ('no_model_without_agreement', 'selected_agrees', 'selected_model', 'unadmitted_rejected', 'selected_safe',
         'refused_agrees', 'refused_words', 'source_admitted', 'frames', 'proper_children')
CLAIMS = [NS + name for name in CORE + CHILDREN] + [NS + 'Tests.' + name for name in TESTS]
CLAIMS += [PNS + 'item_enclosing_replay_uniform']
NATIVE_TESTS = ('initial_frame', 'admitted_frame', 'successful', 'refused', 'same_graph',
                'parent_selected', 'native_operand', 'dispatch_calls_child', 'no_model', 'no_cursor_model', 'no_source_admission')
CLAIMS += [FRAME_MAP] + [NATIVE + name for name in NATIVE_TESTS]
INTERFACES = tuple(NS + name for name in ('Agrees', 'action', 'constructors', 'Agreement.mk', 'SourceAdmission.mk', 'RequestWords', 'Words.mk'))
INTERFACES += tuple(NATIVE + name for name in ('before', 'frame', 'ops', 'base', 'children', 'child'))


def audit(claims):
    required = {
        'action_at': {'action', 'Agrees'},
        'projects': {'action_at', 'ordinary_language'},
        'exists_iff': {'agrees_of_projects', 'projects'},
        'safe': {'action'},
        'source_projects': {'projects', 'constructors'},
        'request_safe': {'safe'},
        'constructors_sound': {'request_safe', 'safe'},
        'constructors_address': {'request_safe'},
        'constructors_sar': {'request_safe'},
        'proper': {'source_projects', 'constructors_sound', 'constructors_address', 'constructors_sar'},
        'Tests.no_model_without_agreement': {'agrees_of_projects'},
        'Tests.selected_model': {'action_at'},
        'Tests.proper_children': {'proper'},
    }
    for name, needed in required.items():
        if not {NS + x for x in needed} <= claims[NS + name]:
            raise ValueError('uniform child construction lost its shared proof: ' + name)
    consumer = PNS + 'item_enclosing_replay_uniform'
    if not {NS + 'proper', PNS + 'item_enclosing_replay_joint'} <= claims[consumer]:
        raise ValueError('uniform item bypasses the joint native execution')
    native_required = {
        'initial_frame': {gate.ITEM + 'NativeRecursion.CallFrame.caller',
                          gate.ITEM + 'ConstantFoldTests.established', gate.ITEM + 'ConstantFoldTests.literal'},
        'admitted_frame': {FRAME_MAP, NATIVE + 'initial_frame'},
        'dispatch_calls_child': {gate.ITEM + 'ConstantFoldTests.iszero_result',
                                 gate.ITEM + 'NativeRecursion.dispatcher_snapshot', NATIVE + 'native_operand'},
        'no_model': {NS + 'agrees_of_projects', NATIVE + 'admitted_frame', NATIVE + 'successful', NATIVE + 'refused'},
        'no_cursor_model': {NATIVE + 'no_model'},
        'no_source_admission': {NATIVE + 'admitted_frame', NATIVE + 'successful', NATIVE + 'refused'},
    }
    for name, needed in native_required.items():
        if not needed <= claims[NATIVE + name]:
            raise ValueError('native admission regression lost its actual execution or caller: ' + name)
    for name in [NS + x for x in CORE + CHILDREN] + [consumer, FRAME_MAP]:
        if any('Tests' in dependency.split('.') for dependency in claims[name]):
            raise ValueError('uniform construction depends on a fixture: ' + name)
    return {'sharedModelConstructed': True, 'nativeWordsConsumed': True, 'enclosingItemConsumed': True,
            'structuralFrameInsufficientForNativeAdmission': True,
            'streamAgreementDerived': False, 'recursiveInductionVerified': False}


def audit_statements(rows, interfaces):
    from native_constructor_checks import expression
    statements = {row['theorem']: row['statement'] for row in rows}
    definitions = {row['name']: row for row in interfaces}
    for name, parameters in {
        'initial_frame': {'safety'}, 'admitted_frame': {'safety', 'permitted'},
        'successful': {'safety'}, 'refused': {'safety'}, 'same_graph': {'safety'},
        'parent_selected': {'safety'}, 'native_operand': {'safety', 'permitted'},
        'dispatch_calls_child': {'safety', 'permitted'},
        'no_model': {'safety', 'observe', 'same'}, 'no_cursor_model': {'safety', 'position'},
        'no_source_admission': {'safety', 'observe', 'same', 'reads'},
    }.items():
        fields, root, context = gate.domains(statements[NATIVE + name])
        if set(fields) != parameters:
            raise ValueError('native admission regression added an assumption: ' + name)
        if name.startswith('no_'):
            negated = joint.app(statements[NATIVE + name], root, 'Not')[-1]
            joint.app(statements[NATIVE + name], negated, 'Exists')
    for name, operation in (('frame', gate.ITEM + 'NativeRecursion.CallFrame'),
                            ('children', gate.ITEM + 'NativeRecursion.unfold'),
                            ('child', 'Compiler.Extraction.Associative.Constructors.constant')):
        value = definitions[NATIVE + name]['value']
        _, root, context = gate.domains(value)
        choice.one_call(value, root, context, operation)
    value = definitions[NS + 'constructors']['value']
    _, root, context = gate.domains(value)
    methods = joint.app(value, root, 'Compiler.Extraction.Associative.Constructors.mk')[-5:]
    arguments = {
        'operation': ['op', 'ids', 'debug'], 'constant': ['value', 'debug'],
        'materialize': ['id', 'value', 'debug'], 'borrowedOperation': ['address', 'op', 'ids', 'debug'],
        'localOperation': ['op', 'source', 'selected', 'repeated', 'first', 'debug'],
    }
    for term, (method, expected) in zip(methods, arguments.items()):
        local = context[:]
        while value['nodes'][term][0] == 'lambda':
            node = value['nodes'][term]
            local.append(node[1])
            term = node[4]
        args = joint.app(value, term, NS + 'action')
        if gate.named(value, args[-3], local) != 'observe':
            raise ValueError('uniform constructor changed observation: ' + method)
        for selected, family in zip(args[-2:], ('domains', 'children')):
            actual = joint.app(value, selected, 'Compiler.Extraction.Associative.Constructors.' + method)
            if [gate.named(value, x, local) for x in actual[-len(expected)-1:]] != [family] + expected:
                raise ValueError('uniform constructor changes native arguments: ' + method)
    for name in ('Agreement.mk', 'SourceAdmission.mk', 'Words.mk'):
        fields, _, _ = gate.domains(definitions[NS + name]['type'])
        if list(fields)[-5:] != list(arguments):
            raise ValueError('native child obligation changed its five entry fields: ' + name)
    value = statements[PNS + 'item_enclosing_replay_uniform']
    fields, root, context = gate.domains(value)
    old = statements[PNS + 'item_enclosing_replay_joint']
    originals, original_root, original_context = gate.domains(old)
    if set(fields) != set(originals):
        raise ValueError('uniform item added a premise or lost a native input')
    for name, (index, local) in fields.items():
        if name != 'proper':
            old_index, old_local = originals[name]
            if expression(value, index, local) != expression(old, old_index, old_local):
                raise ValueError('uniform item changed an existing input: ' + name)
    if expression(value, root, context) != expression(old, original_root, original_context):
        raise ValueError('uniform item weakened the original joint result')
    index, local = fields['proper']
    constants = gate.step.constants_below(value, index)
    forbidden = {PNS + name for name in ('JointPost', 'JointEntry', 'SiteChildren', 'TakenModel', 'replayModel')}
    forbidden |= {gate.OWNED + 'Recursive.projectionAt', gate.OWNED + 'Recursive.ProjectsAt',
                  'Compiler.Extraction.Associative.ConstructorSound', 'Compiler.Extraction.AddressMask.Constructs',
                  'Compiler.Extraction.ArithmeticShift.Constructs'}
    if constants & forbidden:
        raise ValueError('native induction assumes a model or final item result')
    for name in ('Agreement', 'Words', 'SourceAdmission'):
        choice.one_call(value, index, local, NS + name)
    choice.one_call(value, index, local, PNS + 'TakenSite.Reached')
    admission, admission_context = choice.one_call(value, index, local, NS + 'SourceAdmission')
    if gate.named(value, admission[-3], admission_context) != 'debug':
        raise ValueError('uniform admission lost the caller debug value')
    reads = joint.app(value, admission[-2], 'Compiler.Extraction.Nested.storageReads')
    if gate.named(value, reads[-1], admission_context) != 'childRows':
        raise ValueError('uniform admission lost its reached source rows')
    agreement, agreement_context = choice.one_call(value, index, local, NS + 'Agreement')
    words, words_context = choice.one_call(value, index, local, NS + 'Words')
    for args, ctx in ((agreement, agreement_context), (words, words_context)):
        if gate.named(value, args[-2], ctx) != 'domains':
            raise ValueError('native obligations do not share one admitted domain')
        children = joint.app(value, args[-1], gate.NS + 'ChildTrace.constructors')
        if [gate.named(value, x, ctx) for x in children[-2:]] != ['children', 'observations']:
            raise ValueError('native obligations replaced actual children or observations')
    return {'allNativeArgumentsBound': True, 'sameNativeInputsAndJointConclusion': True,
            'noLogicalChildModelPremise': True, 'admissionUsesReachedRowsAndDebug': True,
            'nativeAdmissionCounterexampleHasNoOutcomePremise': True,
            'streamAgreementDerived': False}


def control_source(name):
    raw = (gate.harness.ROOT / ('lean/Compiler/Extraction/' + name + '.lean')).read_text()
    header = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
    return header + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)


def controls(output, env, lean):
    groups = (
        ('model', 'InternerUniformModel', (
            ('wrong-observed-output', '((physical chosen).1.mapError language, observe (physical chosen).2)',
             '((physical chosen).1.mapError language, before)', 1),
            ('wrong-ordinary-domain', 'ordinary (physical native).1 = true then', 'ordinary (physical native).1 = false then', 1),
            ('unbound-domain', '(agrees : Agrees observe admitted physical)', '(agrees : Agrees observe (fun _ => False) physical)', 2),
        )),
        ('children', 'InternerUniformChildren', (
            ('wrong-operation', '(children.operation op ids debug)', '(children.operation (op + 1) ids debug)', 3),
            ('wrong-borrowed-address', '(children.borrowedOperation address op ids debug)',
             '(children.borrowedOperation (address + 1) op ids debug)', 3),
            ('wrong-local-order', '(children.localOperation op source selected repeated first debug)',
             '(children.localOperation op source selected repeated (!first) debug)', 3),
            ('lost-parent-frame', '(frames : (keeping predicate).SourceConstructorsAt',
             '(frames : (keeping (fun _ => True)).SourceConstructorsAt', 1),
        )),
        ('joint', 'InternerConstructorUniformInduction', (
            ('wrong-child-guard', '(site.deterministic && (request.item.kind == 1))', '(site.deterministic && (request.item.kind == 2))', 1),
            ('wrong-native-words', 'Uniform.Words observe (Dispatch.wordDispatchMeaning env other) domains child',
             'Uniform.Words observe (Dispatch.wordDispatchMeaning env other) domains NativeRecursion.exhausted', 1),
            ('stale-source-rows', 'Uniform.SourceAdmission domains debug (Nested.storageReads childRows) frame',
             'Uniform.SourceAdmission domains debug (Nested.storageReads []) frame', 1),
            ('wrong-cursor-origin', '(sitePrefix ops base source request leading site).2.events.length',
             '((sitePrefix ops base source request leading site).2.events.length + 1)', 1),
        )),
        ('tests', 'InternerUniformModelTests', (
            ('invent-success', '(if permitted then .ok 7 else .error .outOfMemory, heap)',
             '(if permitted then .ok 8 else .error .outOfMemory, heap)', 1),
            ('erase-oom', '(if permitted then .ok 7 else .error .outOfMemory, heap)',
             '(if permitted then .ok 7 else .error .unsupported, heap)', 1),
            ('accept-unadmitted', 'allocation heap = (.error .unsupported, heap)', 'allocation heap = (.ok 7, heap)', 1),
        )),
        ('native-admission', 'InternerNativeAllocationAdmissionTests', (
            ('swap-private-state', 'if permitted then 1 else 0', 'if permitted then 0 else 1', 1),
            ('invent-success', '(child safety (before safety true)).1 = .ok 5',
             '(child safety (before safety true)).1 = .ok 6', 1),
            ('erase-oom', '(child safety (before safety false)).1 = .error (.language .outOfMemory)',
             '(child safety (before safety false)).1 = .error (.language .unsupported)', 1),
            ('exhaust-recursion', 'NativeRecursion.unfold (base safety) 6 64 1',
             'NativeRecursion.unfold (base safety) 6 64 0', 1),
            ('force-allocation', 'if reached.effects = 0 then (none, reached.effects)',
             'if False then (none, reached.effects)', 1),
            ('inactive-parent', 'deterministic (parent safety).request.item = .ok true',
             'deterministic (parent safety).request.item = .ok false', 1),
            ('wrong-native-word', '.constant 4 = .ok (some 0)', '.constant 4 = .ok (some 1)', 1),
            ('wrong-folded-child', '.constant 1', '.constant 2', 4),
        )),
    )
    records = []
    for group, module, changes in groups:
        source = control_source(module)
        records += checked_controls(output, [mutation_check(output, 'uniform-' + group + '-unchanged', source, True, env, lean)])
        for name, before, after, count in changes:
            if source.count(before) != count:
                raise ValueError('ambiguous uniform model control: ' + group + '.' + name + ': ' + str(source.count(before)))
            records += checked_controls(output, [mutation_check(output, 'uniform-' + group + '-' + name,
                source.replace(before, after), False, env, lean)])
    return records
