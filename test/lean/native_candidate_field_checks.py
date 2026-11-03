"""Check candidate words derived from actual native descriptor preservation.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
from assembly_item_creation_checks import checked_controls
from native_suffix_word_checks import NS, OWNED, INSERTION

ARGUMENTS = 'Compiler.Extraction.Memory.Arguments.'
BASE = OWNED + 'Insertion.'
CLAIMS = [ARGUMENTS + name for name in ('Allocation.reserve_items', 'Duplication.run_items', 'Normalization.takeOwned_borrowed_items')]
CLAIMS += [BASE + name for name in ('callbacks_field_values', 'callbacks_fields', 'cell_field_values', 'cell_fields', 'cell_value_binding', 'cell_binding')]
CLAIMS += [INSERTION + name for name in ('finish_clone_value', 'items_fields', 'callbacks_field_values',
                                      'execution_field_values', 'constructor_push_values', 'candidate_words')]
ALLOCATION_CLAIMS = [INSERTION + name for name in ('duplicate_allocation', 'prepared_allocation_candidate',
    'observed_allocation_candidate', 'execution_allocation_candidate', 'insert_allocation_replayed', 'insert_allocation_stream')]
ALLOCATION_CLAIMS += [NS + 'CallFrame.' + name for name in ('allocation_insert_stream', 'allocation_insert_agrees')]
CLAIMS += ALLOCATION_CLAIMS
INTERFACES = (INSERTION + 'allocationCandidate', INSERTION + 'allocationReplay')


def audit(rows, interfaces):
    import check_native_invocation as gate
    claims = {row['theorem']: row for row in rows}
    required = {
        ARGUMENTS + 'Duplication.run_items': {ARGUMENTS + 'Allocation.reserve_items'},
        ARGUMENTS + 'Normalization.takeOwned_borrowed_items': {ARGUMENTS + 'Duplication.run_items'},
        BASE + 'callbacks_field_values': {BASE + 'item_fields', ARGUMENTS + 'Normalization.takeOwned_borrowed_items'},
        BASE + 'callbacks_fields': {BASE + 'callbacks_field_values', BASE + 'callbacks_preserve'},
        BASE + 'cell_fields': {BASE + 'cell_field_values'},
        BASE + 'cell_binding': {BASE + 'cell_value_binding'},
        INSERTION + 'items_fields': {BASE + 'item_fields', INSERTION + 'finish_clone_value'},
        INSERTION + 'callbacks_field_values': {BASE + 'callbacks_field_values', INSERTION + 'items_fields', INSERTION + 'callbacks'},
        INSERTION + 'execution_field_values': {INSERTION + 'callbacks_field_values', 'Compiler.Extraction.Storage.Program.execute_preserves'},
        INSERTION + 'candidate_words': {INSERTION + 'execution_field_values', INSERTION + 'execution_recorded',
            BASE + 'cell_value_binding', 'Compiler.Extraction.Cache.key_sound', INSERTION + 'PushValues'},
        INSERTION + 'constructor_push_values': {'Compiler.Extraction.Interner.constructorMeaning', INSERTION + 'PushValues'},
        INSERTION + 'duplicate_allocation': {ARGUMENTS + 'Duplication.run_total', BASE + 'borrowed_ready',
                                             ARGUMENTS + 'Duplication.Post.nextId'},
        INSERTION + 'prepared_allocation_candidate': {INSERTION + 'duplicate_allocation',
            'Compiler.Extraction.AssemblyItem.Creation.create_shape', 'Compiler.Extraction.AssemblyClone.clone_item', INSERTION + 'prepared_arguments'},
        INSERTION + 'observed_allocation_candidate': {INSERTION + 'prepare_selected', INSERTION + 'prepared_allocation_candidate'},
        INSERTION + 'execution_allocation_candidate': {INSERTION + 'execution_candidate', INSERTION + 'observed_allocation_candidate',
            INSERTION + 'execution_preparation_coverage', INSERTION + 'preparation_oom_execution_at'},
        INSERTION + 'insert_allocation_replayed': {INSERTION + 'insert_replayed', INSERTION + 'execution_allocation_candidate',
            'Compiler.Extraction.Interner.InsertionExecution.project_candidate'},
        INSERTION + 'insert_allocation_stream': {INSERTION + 'insert_allocation_replayed', INSERTION + 'allocationReplay'},
        NS + 'CallFrame.allocation_insert_stream': {INSERTION + 'insert_allocation_stream', NS + 'CallFrame'},
        NS + 'CallFrame.allocation_insert_agrees': {NS + 'CallFrame.allocation_insert_stream', INSERTION + 'allocationReplay'},
    }
    for name, needed in required.items():
        if missing := needed - set(claims[name]['dependencies']):
            raise ValueError('candidate proof lost shared derivation: ' + name + ': ' + ', '.join(sorted(missing)))
    for name in CLAIMS:
        if any(part.endswith('Tests') for dep in claims[name]['dependencies'] for part in dep.split('.')):
            raise ValueError('candidate derivation depends on a fixture: ' + name)
    for name in ('candidate_words', 'execution_field_values', 'callbacks_field_values'):
        statement = claims[INSERTION + name]['statement']
        fields, conclusion, _ = gate.domains(statement)
        for field, (root, _) in fields.items():
            constants = gate.step.constants_below(statement, root)
            if {INSERTION + 'CandidateWords', BASE + 'FieldValues', BASE + 'Fields', OWNED + 'Semantic.Ensures',
                    'Compiler.Extraction.Storage.Preserves', NS + 'FramePost'} & constants:
                raise ValueError('candidate proof assumes descriptor or final preservation: ' + field)
        if name == 'candidate_words':
            if not {'pushes', 'bound', 'evaluated'} <= fields.keys() or {'completed', 'outcome', 'initial', 'admitted'} & fields.keys():
                raise ValueError('candidate word statement lost input semantics or assumes execution success')
            if INSERTION + 'CandidateWords' not in gate.step.constants_below(statement, conclusion):
                raise ValueError('candidate word result missing')
        elif {'valid', 'initial', 'admitted'} & fields.keys():
            raise ValueError('descriptor proof unexpectedly requires memory validity/admission')
    definition = next(row for row in interfaces if row['name'] == INSERTION + 'PushValues')
    audit_pushes(definition['value'], gate)
    allocation = audit_allocation(claims, interfaces, gate)
    return {'checkedDependencies': sorted(required), 'checkedDefinitions': [definition['name']],
            'nativeCandidateDescriptorsDerived': True, 'candidateWordPremiseRemoved': True,
            'pushInterpretationLawRequired': True, 'concretePushInterpretationChecked': True,
            'nativeMemoryValidityDerived': False, 'recursiveInductionVerified': False,
            'composedProductionTheoremVerified': False, 'allocationIdentity': allocation}


def audit_allocation(claims, interfaces, gate):
    definitions = {row['name']: row for row in interfaces}
    expected = {
        'allocationCandidate': {'input', 'key', 'normalized', 'value', 'deterministic', 'nextId'},
        'allocationReplay': {'input', 'key', 'normalized', 'meaning', 'deterministic', 'nextId', 'stream', 'mismatch', 'before'},
    }
    forbidden = {INSERTION + name for name in ('execution', 'recordExecution', 'observedCandidate', 'insert')}
    for name, parameters in expected.items():
        value = definitions[INSERTION + name]['value']
        fields, _, _ = gate.domains(value)
        constants = gate.step.constants_below(value, value['root'])
        if set(fields) != parameters or constants & forbidden:
            raise ValueError('allocation replay model consults a native result: ' + name)
    def app(head, *arguments):
        for argument in arguments:
            head = ('app', head, argument)
        return head
    def nat(number):
        literal = ('natural', str(number))
        return app('OfNat.ofNat', 'Nat', literal, app('instOfNatNat', literal))
    def branch(condition, yes, no):
        return app('ite', 'Nat', app('Eq', 'Bool', condition, 'Bool.true'),
                   app('instDecidableEqBool', condition, 'Bool.true'), yes, no)
    items = app('Compiler.Extraction.Storage.ArgumentSlice.items', 'normalized')
    condition = app('Bool.and', 'deterministic', app('Bool.not', app('List.isEmpty', 'Compiler.Algebraic.NodeId', items)))
    value = definitions[INSERTION + 'allocationCandidate']['value']
    _, root, context = gate.domains(value)
    head, args = gate.applied(value, root)
    expected_fields = [app('Compiler.Extraction.AssemblyClone.Value.item', 'Compiler.Extraction.AssemblyItem.Fields.Values', 'input'),
        'value', app('HAdd.hAdd', 'Nat', 'Nat', 'Nat', app('instHAdd', 'Nat', 'instAddNat'), 'nextId', branch(condition, nat(1), nat(0))),
        items, app('Compiler.Extraction.Cache.Key.sequence', 'key'),
        branch('deterministic', 'nextId', app('Compiler.Extraction.Storage.ArgumentSlice.address', 'normalized'))]
    if head[:2] != ['const', 'Compiler.Extraction.Storage.Cell.mk'] or [gate.named(value, a, context) for a in args] != expected_fields:
        raise ValueError('allocation candidate changed source fields or empty/transfer identity behavior')
    value = definitions[INSERTION + 'allocationReplay']['value']
    _, root, context = gate.domains(value)
    head, args = gate.applied(value, root)
    if head[:2] != ['const', 'Compiler.Extraction.Interner.InsertionExecution.action'] or [gate.named(value, a, context) for a in args[-4:]] != [
            'key', 'deterministic', app('Compiler.Extraction.Storage.Trace.replay', INSERTION + 'Fault', 'stream', 'mismatch'), 'before']:
        raise ValueError('allocation replay lost the fixed stream or input heap')
    head, args = gate.applied(value, args[-5])
    if head[:2] != ['const', INSERTION + 'allocationCandidate'] or [gate.named(value, a, context) for a in args[:3] + args[-2:]] != [
            'input', 'key', 'normalized', 'deterministic', 'nextId']:
        raise ValueError('allocation replay changed entry candidate inputs')
    head, args = gate.applied(value, args[3])
    if head[:2] != ['const', 'Option.getD'] or gate.named(value, args[-2], context) != app(
            'Compiler.Extraction.Cache.Key.eval', 'meaning', app('Compiler.Extraction.Interner.Heap.read', 'before'), 'key'):
        raise ValueError('allocation replay changed candidate denotation')
    zero_head, zero_args = gate.applied(value, args[-1])
    if zero_head[:2] != ['const', 'OfNat.ofNat'] or [gate.named(value, a, context) for a in zero_args[:2]] != ['Contract.Yul.Word', ('natural', '0')]:
        raise ValueError('allocation replay changed the absent-denotation fallback')
    for name in ALLOCATION_CLAIMS:
        value = claims[name]['statement']
        fields, _, _ = gate.domains(value)
        if set(fields) & {'candidate', 'binding', 'laterCandidate', 'model', 'projected', 'safe'}:
            raise ValueError('allocation identity assumes candidate or final simulation: ' + name)
    value = claims[NS + 'CallFrame.allocation_insert_agrees']['statement']
    fields, _, _ = gate.domains(value)
    if not {'one', 'two', 'identity', 'same', 'insideLeft', 'insideRight', 'admitted'} <= fields.keys():
        raise ValueError('uniform insertion lost native, stream or identity admission')
    return {'checkedDefinitions': list(INTERFACES), 'nativeCandidateAllocationIdentitiesDerived': True,
            'fixedStreamInsertionModelConstructed': True, 'ordinaryInsertionAgreementDerived': True,
            'fullConstructorBodyReplayVerified': False, 'nativeEntryAdmissionDerived': False,
            'composedProductionTheoremVerified': False}


def audit_pushes(value, gate):
    fields, conclusion, context = gate.domains(value)
    guard = [field for name, field in fields.items() if name not in ('meaning', 'value', 'sequence', 'values', 'expected')]
    if len(guard) != 1:
        raise ValueError('PUSH interpretation changed its semantic premise')
    (root, guard_context), = guard
    head, args = gate.applied(value, root)
    if head[:2] != ['const', 'Eq']:
        raise ValueError('PUSH interpretation lost the defined observation')
    atom, result = args[-2:]
    head, args = gate.applied(value, atom)
    if (head[:2] != ['const', 'Compiler.Extraction.Cache.Meaning.atom']
            or gate.named(value, args[0], guard_context) != 'meaning'
            or [gate.named(value, x, guard_context) for x in args[-3:]] != ['value', 'sequence', 'values']):
        raise ValueError('PUSH law does not bind the supplied interpretation')
    kind, numbers = gate.applied(value, args[1])
    def numeral(number):
        literal = ('natural', str(number))
        return ('app', ('app', ('app', 'OfNat.ofNat', 'Nat'), literal), ('app', 'instOfNatNat', literal))
    if kind[:2] != ['const', 'BitVec.ofNat'] or [gate.named(value, x, guard_context) for x in numbers] != [numeral(32), numeral(2)]:
        raise ValueError('PUSH law changed the literal kind')
    head, args = gate.applied(value, result)
    if head[:2] != ['const', 'Option.some'] or gate.named(value, args[-1], guard_context) != 'expected':
        raise ValueError('PUSH law changed the defined word')
    head, args = gate.applied(value, conclusion)
    if head[:2] != ['const', 'Eq'] or [gate.named(value, x, context) for x in args[-2:]] != ['expected', 'value']:
        raise ValueError('PUSH law does not return its literal')


def control_families():
    directory = ROOT / 'lean/Compiler/Extraction'
    options = '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n'
    fields = (directory / 'NormalizationMemoryFields.lean').read_text()
    descriptor = 'import Compiler.Extraction.NormalizationMemory\n' + options + without_imports(fields)
    native = (directory / 'InternerInsertionNative.lean').read_text()
    proofs = (directory / 'InternerInsertionNativeFields.lean').read_text()
    source = '\n'.join(line for line in (native + proofs).splitlines() if line.startswith('import '))
    source += options + without_imports(native) + without_imports(proofs)
    source = source.replace(INSERTION[:-1], INSERTION[:-1] + 'FieldMutation')
    semantics = 'import Compiler.Extraction.InternerNativeSuffixWords\n' + options + '''
open Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Extraction.Cache Contract.Yul
example (arbitrary : Meaning) : PushValues (Compiler.Extraction.Interner.constructorMeaning arbitrary) := constructor_push_values arbitrary
example : ¬ PushValues { operation := fun _ _ _ => none, atom := fun _ value _ _ => some (value + 1) } := by
  intro wrong
  have impossible := wrong 0 0 [] 1 rfl
  exact (by decide : (1 : Word) ≠ 0) impossible
'''
    identity = (directory / 'InternerInsertionCandidateIdentity.lean').read_text()
    replay = (directory / 'InternerInsertionAllocationReplay.lean').read_text()
    return (
        ('descriptor', descriptor, (
            ('wrong-reserved-items', 'slice.items = items := by', 'slice.items = items ++ [0] := by', 2),
            ('wrong-borrowed-items', 'slice.items = handle.values := by', 'slice.items = handle.values ++ [0] := by', 1),
        )),
        ('native-fields', source, (
            ('corrupt-clone-item', '(result.mapError Fault.item, { before with item := reached })',
             '(result.mapError Fault.item, { before with item := { reached with clone := { reached.clone with value := some { input with item := { input.item with data := input.item.data + 1 } } } } })', 1),
            ('corrupt-appended-arguments', '(result.mapError Fault.append, withMemory before reached)\n\n/-- The value',
             '(result.mapError Fault.append, { withMemory before reached with duplicate := some ⟨0, [0]⟩ })\n\n/-- The value', 1),
            ('invent-finished-clone', ').2.clone.value = before.clone.value := by', ').2.clone.value = none := by', 1),
            ('admit-native-rejection', 'growth).1.1 = .ok outcome)', 'growth).1.1 = .error (.base .missingValue))', 1),
        )),
        ('push-meaning', semantics, (
            ('reject-valid-push-meaning', 'some (value + 1)', 'some value', 1),
        )),
        ('allocation-identity', identity, (
            ('wrong-object-id', 'then 1 else 0', 'then 2 else 0', 1),
            ('allocate-empty-duplicate', 'deterministic && !normalized.items.isEmpty', 'deterministic', 1),
            ('lose-transferred-address', 'if deterministic then nextId else normalized.address', 'nextId', 1),
            ('corrupt-item', '{ item := input.item', '{ item := { input.item with data := input.item.data + 1 }', 1),
        )),
        ('allocation-replay', replay, (
            ('wrong-entry-id', 'deterministic nextId)', 'deterministic (nextId + 1))', 1),
            ('wrong-stream', 'key deterministic (Trace.replay stream mismatch) before',
             'key deterministic (Trace.replay [] mismatch) before', 1),
            ('rewind-cursor', 'key deterministic (Trace.replay stream mismatch) before',
             'key deterministic (Trace.replay stream mismatch) { before with allocationCursor := 0 }', 1),
            ('wrong-ending-cursor', 'leading.length + captured.2.events.length',
             'leading.length + captured.2.events.length + 1', 4),
        )),
    )


def controls(output, env, lean):
    records = []
    for family, source, changes in control_families():
        prefix = 'candidate-' + family + '-'
        records += checked_controls(output, [mutation_check(output, prefix + 'unchanged', source, True, env, lean)])
        for name, before, after, count in changes:
            if source.count(before) != count:
                raise ValueError('ambiguous native candidate mutation: ' + name)
            records += checked_controls(output, [mutation_check(output, prefix + name, source.replace(before, after), False, env, lean)])
    return records
