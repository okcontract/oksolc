"""Audit exhaustive native insertion cases and removal of residual frames.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
import constructor_replay_choice_checks as choice
from native_miss_frame_checks import named
from native_algebraic_dispatch_checks import source
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check

NS, OWNED = gate.NS, gate.OWNED
NATIVE = OWNED + 'Insertion.Native.'
ARRAY = 'Compiler.Extraction.RepresentativeArray.'
REGION = 'Compiler.ZigAir.Memory.RegionAllocation.'
STORAGE = 'Compiler.Extraction.Storage.'
CLAIMS = [STORAGE + 'insert_execution_append', REGION + 'fits_of_extend_valid']
CLAIMS += [ARRAY + name for name in (
    'Backing.reserve_observation', 'Backing.Registry.ordinary_reservation',
    'Backing.Fallback.allocation_observation', 'Growth.first_allocation_observation',
    'Growth.ordinary_unlocked', 'Growth.Registered.ordinary_unlocked', 'Growth.first_observation',
    'Growth.Registered.first_observation', 'Growth.Registered.growing_observation',
    'Append.Execution.capacity_completed', 'Append.Registered.finish_accepted',
    'Append.Registered.ordinary_native', 'Append.Registered.ordinary_native_growth',
    'Capacity.grow_count_bytes', 'Append.Registered.capacity_completed', 'Append.Registered.backing_observation')]
CLAIMS += [NATIVE + name for name in (
    'prepare_selected', 'execution_prepared_append', 'allocation_observation', 'append_native_completion',
    'append_backing_observation', 'execution_backing_coverage', 'execution_insertion_coverage', 'insert_insertion_coverage')]
CLAIMS += [NS + 'Enclosing.insertion_covered']
INTERFACES = (ARRAY + 'Backing.AllocationObservation', ARRAY + 'Append.Registered.BackingObservation')


def audit(claims):
    required = {
        STORAGE + 'insert_execution_append': {STORAGE + 'Program.scope_completed', STORAGE + 'insertProgram'},
        ARRAY + 'Backing.reserve_observation': {REGION + 'fits_of_extend_valid', REGION + 'reserve_nonempty_success'},
        ARRAY + 'Append.Registered.backing_observation': {
            ARRAY + 'Append.Registered.capacity_completed', ARRAY + 'Capacity.grow_count_bytes',
            ARRAY + 'Growth.first_observation', ARRAY + 'Growth.Registered.first_observation',
            ARRAY + 'Growth.Registered.growing_observation'},
        NATIVE + 'prepare_selected': {NATIVE + 'prepare_owned', NATIVE + 'prepare_item'},
        NATIVE + 'execution_prepared_append': {NATIVE + 'prepare_selected', STORAGE + 'insert_execution_append'},
        NATIVE + 'execution_backing_coverage': {NATIVE + 'execution_prepared_append', NATIVE + 'append_backing_observation',
            OWNED + 'NativeGraph.Facts.frame'},
        NATIVE + 'execution_insertion_coverage': {NATIVE + 'execution_preparation_coverage', NATIVE + 'execution_backing_coverage'},
        NATIVE + 'insert_insertion_coverage': {NATIVE + 'execution_insertion_coverage', NATIVE + 'checkedExecution_read'},
        NS + 'Enclosing.insertion_covered': {NS + 'Enclosing.insertion_prepared', NATIVE + 'insert_insertion_coverage'},
        NS + 'Enclosing.native_miss_frames': {NS + 'Enclosing.insertion_covered'},
        NS + 'StepEntryFrames.of_operations': {NS + 'Enclosing.insertion_covered'},
        NS + 'invocation_signextend_unfold_verified': {NS + 'Enclosing.insertion_covered'},
        gate.ITEM + 'ProtocolTrace.item_enclosing_replay_joint': {NS + 'Enclosing.insertion_covered'},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('insertion coverage lost source composition: ' + name + ': ' + ', '.join(sorted(missing)))
    for name in CLAIMS:
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('general insertion coverage depends on a fixture: ' + name)
    return {'checkedDependencies': sorted(required), 'ordinaryInsertionCasesExhaustive': True,
            'existingCaseProofsConsumed': True, 'residualInsertionFrameRemoved': True,
            'resourceAdmissionDerived': False, 'recursiveInductionVerified': False}


def audit_statements(rows, interfaces):
    from native_constructor_checks import expression
    statements = {row['theorem']: row['statement'] for row in rows}
    definitions = {row['name']: row for row in interfaces}
    old = statements[NS + 'Enclosing.insertion_prepared']
    previous, old_root, old_context = gate.domains(old)
    value = statements[NS + 'Enclosing.insertion_covered']
    fields, root, context = gate.domains(value)
    if set(fields) != (set(previous) - {'remaining'}) | {'domain'}:
        raise ValueError('covered insertion added a preservation premise or lost an original input')
    for field in fields.keys() - {'domain'}:
        if expression(value, *fields[field]) != expression(old, *previous[field]):
            raise ValueError('covered insertion changed an original input: ' + field)
    if expression(value, root, context) != expression(old, old_root, old_context):
        raise ValueError('covered insertion changed the original frame conclusion')
    domain, local = fields['domain']
    if 'Compiler.Extraction.AssemblyItem.itemTagValues' not in gate.step.constants_below(value, domain):
        raise ValueError('insertion coverage lost the admitted native item domain')
    args, local = choice.one_call(value, domain, local, 'Compiler.Extraction.Cache.Item.kind')
    joint.path(value, args[-1], local, ('Compiler.Extraction.AssemblyClone.Value.item',), 'native')

    common = {'σ', 'ops', 'allocate', 'safety', 'deterministic', 'allocator', 'container', 'source', 'address', 'input',
              'key', 'normalized', 'rows', 'meaning', 'growth', 'before', 'data', 'capacity', 'facts', 'live', 'represented',
              'domain', 'admitted', 'room', 'completed'}
    for name in ('execution_insertion_coverage', 'insert_insertion_coverage'):
        value = statements[NATIVE + name]
        fields, root, context = gate.domains(value)
        if set(fields) != common | ({'outcome'} if name.startswith('execution') else set()):
            raise ValueError('source coverage gained a successful preparation/allocation or frame premise')
        geometry = joint.app(value, fields['facts'][0], OWNED + 'NativeGraph.Facts')
        named(value, geometry, fields['facts'][1], ('σ', 'safety', 'allocator', 'container', 'data', 'capacity', 'before', 'rows'))
        admission, local = fields['admitted']
        selected = value['nodes'][admission]
        if selected[0] != 'forall':
            raise ValueError('source duplication admission lost its ownership guard')
        guard = joint.app(value, selected[3], 'Eq')
        named(value, guard[-2:], local, ('deterministic', 'Bool.true'))
        preparation, rest = joint.app(value, root, 'Or')
        backing, rest = joint.app(value, rest, 'Or')
        publication, transfer = joint.app(value, rest, 'Or')
        for term, observation, expected in (
            (preparation, 'PreparationOOMAt', ('σ', 'ops', 'allocator', 'input', 'normalized', 'deterministic')),
            (backing, 'BackingAllocationOOMAt', ('σ', 'ops', 'allocate', 'allocator', 'container', 'input', 'normalized', 'deterministic', 'growth')),
        ):
            args = joint.app(value, term, NATIVE + observation)
            named(value, args[:-1], context, expected)
            if observation == 'PreparationOOMAt':
                joint.path(value, args[-1], context, (OWNED + 'World.memory',), 'before')
            else:
                named(value, args[-1:], context, ('before',))
        guard, outcomes = joint.app(value, publication, 'And')
        eq = joint.app(value, guard, 'Eq')
        named(value, eq[-2:], context, ('deterministic', 'Bool.true'))
        for term, observation in zip(joint.app(value, outcomes, 'Or'), ('PublishedObservation', 'RefusedObservation')):
            args = joint.app(value, term, NATIVE + observation)
            named(value, args, context, ('σ', 'ops', 'allocate', 'safety', 'allocator', 'container', 'meaning',
                                         'input', 'key', 'normalized', 'growth', 'before'))
        guard, outcome = joint.app(value, transfer, 'And')
        eq = joint.app(value, guard, 'Eq')
        named(value, eq[-2:], context, ('deterministic', 'Bool.false'))
        args = joint.app(value, outcome, NATIVE + 'TransferredObservation')
        named(value, args, context, ('σ', 'ops', 'allocate', 'allocator', 'container', 'input', 'growth', 'before'))
        args, local = choice.one_call(value, *fields['completed'], NATIVE + ('execution' if name.startswith('execution') else 'insert'))
        named(value, args[:13], local, ('σ', 'ops', 'allocate', 'safety', 'allocator', 'container', 'source', 'address', 'meaning',
                                       'input', 'key', 'normalized', 'deterministic'))
        named(value, args[13:], local, ('rows', 'before', 'growth') if name.startswith('execution') else ('growth', 'before'))
        eq = joint.app(value, fields['completed'][0], 'Eq')
        if name.startswith('execution'):
            ok = joint.app(value, eq[-1], 'Except.ok')
            named(value, ok[-1:], fields['completed'][1], ('outcome',))
        else:
            joint.app(value, eq[-2], OWNED + 'ordinary')
            named(value, eq[-1:], fields['completed'][1], ('Bool.true',))
    for name in (NS + 'Enclosing.native_miss_frames', NS + 'Enclosing.inactive_entry_frames',
                 NS + 'StepEntryFrames.of_operations', NS + 'miss_signextend_unfold_verified',
                 NS + 'invocation_signextend_unfold_verified', gate.ITEM + 'ProtocolTrace.item_enclosing_replay_joint',
                 gate.ITEM + 'ProtocolTrace.item_enclosing_replay_uniform'):
        fields, _, _ = gate.domains(statements[name])
        if {'remaining', 'insertion', 'constants', 'constantInsertion'} & fields.keys():
            raise ValueError('consumer regained a residual insertion duty: ' + name)
    for name, expected in (
        ('Backing.AllocationObservation', {'σ', 'allocate', 'capacity', 'before', 'effects', 'accepted'}),
        ('Append.Registered.BackingObservation', {'σ', 'growth', 'allocate', 'allocator', 'owner', 'length', 'capacity', 'before', 'accepted'}),
    ):
        fields, _, _ = gate.domains(definitions[ARRAY + name]['type'])
        if set(fields) != expected:
            raise ValueError('backing observation added a post-state or preservation parameter')
    return {'originalFrameConclusionUnchanged': True, 'onlyAdmittedTagReplacesResidual': True,
            'sourceOutcomesAndOwnershipModesExact': True, 'consumerInsertionPremisesRemoved': True,
            'ordinaryCompletionRequired': True, 'resourceAdmissionDerived': False}


def controls(output, env, lean):
    groups = (
        ('region', 'Compiler.ZigAir.MemoryRegionAllocationProofs', (
            ('unchecked-extended-region', '(valid : (extend state type layout.bytes base).valid = true)',
             '(valid : state.valid = true)', 1),
        )),
        ('allocation', 'Compiler.Extraction.RepresentativeAllocationCoverage', (
            ('wrong-allocator-alignment', 'allocate (capacity * 32) 8 effects', 'allocate (capacity * 32) 16 effects', 3),
            ('allow-empty-request', '(positive : 0 < capacity)', '(positive : True)', 3),
            ('allow-byte-overflow', '(size : capacity * 32 < addressLimit)', '(size : True)', 3),
        )),
        ('append', 'Compiler.Extraction.RepresentativeAppendCoverage', (
            ('spare-is-oom', '(length < capacity ∧ accepted = true)', '(length < capacity ∧ accepted = false)', 1),
            ('wrong-first-capacity', '(allocate allocator) 5 before.memory before.effects accepted',
             '(allocate allocator) 4 before.memory before.effects accepted', 1),
            ('unsupported-remap', 'growth = some ⟨.noRemap context returnAddress, release⟩',
             'growth = some ⟨.unsupported, release⟩', 1),
        )),
        ('outcome', 'Compiler.Extraction.InternerInsertionOutcomeCoverage', (
            ('allow-count-overflow', '(room : rows.length < 2 ^ 32 - 1)', '(room : rows.length < 2 ^ 64 - 1)', 2),
            ('allow-native-rejection', '(completed : ordinary (insert ops allocate safety allocator container source address meaning input key normalized deterministic growth before).1 = true)',
             '(completed : ordinary (insert ops allocate safety allocator container source address meaning input key normalized deterministic growth before).1 = ordinary (insert ops allocate safety allocator container source address meaning input key normalized deterministic growth before).1)', 1),
            ('missing-tag-domain', '(domain : (input.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)', '(domain : True)', 2),
            ('wrong-refusing-allocator', 'BackingAllocationOOMAt ops allocate allocator container input normalized deterministic growth before ∨',
             'BackingAllocationOOMAt ops allocate (allocator + 1) container input normalized deterministic growth before ∨', 2),
            ('invert-transfer', '(deterministic = false ∧ TransferredObservation', '(deterministic = true ∧ TransferredObservation', 2),
        )),
        ('enclosing', 'Compiler.Extraction.InternerEnclosingInsertionCoverage', (
            ('missing-domain', '(domain : (native.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)', '(domain : True)', 1),
            ('missing-original-parent', '(initial : parent before)', '(initial : True)', 1),
        )),
    )
    records = []
    for group, module, changes in groups:
        code = source(module)
        records += checked_controls(output, [mutation_check(output, 'insertion-coverage-' + group + '-unchanged', code, True, env, lean)])
        for name, old, new, count in changes:
            actual = code.count(old)
            if actual != count:
                raise ValueError('ambiguous insertion coverage mutation: ' + group + '-' + name + ': ' + str(actual))
            records += checked_controls(output, [mutation_check(output, 'insertion-coverage-' + group + '-' + name,
                                                                 code.replace(old, new), False, env, lean)])
    return records
