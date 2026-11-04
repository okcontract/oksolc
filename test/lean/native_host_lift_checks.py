"""Bind native invocation admission to the canonical forwarding host lift.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
import native_recursive_invocation_checks as invocation
from native_miss_frame_checks import named
from native_resource_admission_checks import telescope
from native_algebraic_dispatch_checks import source
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check

NS, OWNED = gate.NS, gate.OWNED
LIFT = NS + 'ChildTrace.HostLift.'
CLAIM = NS + 'AllocationTrace.native_invocation_verified'
CLAIMS = [LIFT + 'hosts', CLAIM]
INTERFACES = tuple(LIFT + name for name in ('request', 'release', 'external', 'operations', 'backing', 'growth', 'base'))


def audit(claims):
    required = {
        LIFT + 'hosts': {OWNED + 'Insertion.Native.HostBindings', LIFT + 'operations', LIFT + 'backing', LIFT + 'growth'},
        CLAIM: {NS + 'AllocationTrace.recursive_invocation_verified', LIFT + 'hosts', LIFT + 'base',
                'Compiler.Extraction.Memory.Arguments.Normalization.External.Transport.admitted'},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('native admission lost host derivation: ' + name + ': ' + ', '.join(sorted(missing)))
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('native host admission depends on fixtures: ' + name)
    return {'checkedDependencies': sorted(required), 'recordedHostBindingsDerived': True,
            'recordedAllocatorAdmissionDerived': True, 'growthPresenceAndRemapRetained': True,
            'initialCompilerAdmissionDerived': False, 'composedProductionTheoremVerified': False}


def audit_statements(rows, interfaces):
    statements = {row['theorem']: row['statement'] for row in rows}
    checked = invocation.audit_invocation_statement(statements[CLAIM], recorded_hosts=False)
    value = statements[LIFT + 'hosts']
    fields, lets, root, context = telescope(value)
    if set(fields) != {'σ', 'ε', 'ops', 'allocate', 'calls'} or lets:
        raise ValueError('canonical host lift acquired a correctness premise')
    left, right, allocated, original, growth, calls, project = joint.app(value, root, OWNED + 'Insertion.Native.HostBindings')[-7:]
    named(value, joint.app(value, left, LIFT + 'operations')[-1:], context, ('ops',))
    named(value, joint.app(value, allocated, LIFT + 'backing')[-1:], context, ('allocate',))
    named(value, [right, original, calls], context, ('ops', 'allocate', 'calls'))
    mapped = joint.app(value, growth, 'Option.map')
    joint.app(value, mapped[-2], LIFT + 'growth')
    named(value, mapped[-1:], context, ('calls',))
    joint.app(value, project, 'Prod.fst')
    return {'nativeInvocation': checked, 'noSuppliedRecordedHostOrAdmission': True,
            'exactOriginalHostBindings': True, 'ordinaryOutcomesOnly': True,
            'composedProductionTheoremVerified': False}


def controls(output, env, lean):
    # Nonempty arbitrary history must survive forwarding; it belongs to the
    # child recorder and cannot be reconstructed from physical host calls.
    history_client = '''
namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ChildTrace.HostLift
theorem forwarded_history (host : External σ) (site : Cache.NormalizationOwnership.Allocation)
    (before : Session (Recorded σ ε)) (bytes : Nat) (effects : Recorded σ ε)
    (argument : Storage.ArgumentSlice) :
    ((external host).allocate site before bytes effects).2.2 = effects.2 ∧
      ((external host).free argument before).2 = before.effects.2 := ⟨rfl, rfl⟩
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ChildTrace.HostLift
'''
    groups = (
        ('hosts', 'InternerRecursiveHostLift', history_client, (
            ('wrong-normalization-size', 'bytes effects.1', '(bytes + 1) effects.1', 1),
            ('wrong-backing-allocator', 'allocate allocator bytes alignment effects.1', 'allocate (allocator + 1) bytes alignment effects.1', 1),
            ('wrong-growth-release-base', 'calls.release allocator base bytes alignment effects.1',
             'calls.release allocator (base + 1) bytes alignment effects.1', 1),
            ('missing-growth', '(calls.map growth) calls Prod.fst', 'none calls Prod.fst', 1),
            ('wrong-allocation-history', '(ran.1, (ran.2, effects.2))', '(ran.1, (ran.2, []))', 2),
            ('missing-release-history', '(host argument (before.mapEffects Prod.fst), before.effects.2)',
             '(host argument (before.mapEffects Prod.fst), [])', 1),
        )),
        ('invocation', 'InternerNativeInvocationAdmission', '', (
            ('missing-native-admission', '(admitted : Admitted ops.arguments)', '(admitted : True)', 1),
            ('wrong-expected-word', 'request.sequence = some expected)', 'request.sequence = some (expected + 1))', 1),
            ('wrong-native-growth', 'env other base growth\n', 'env other base none\n', 1),
            ('wrong-native-allocator', 'nativeBase.external base.budget base.allocator', 'nativeBase.external base.budget (base.allocator + 1)', 1),
            ('missing-source-values', 'source request.arguments)', 'source [])', 1),
        )),
    )
    records = []
    for group, module, client, mutations in groups:
        code = source('Compiler.Extraction.' + module) + client
        prefix = 'native-host-lift-' + group + '-'
        records += checked_controls(output, [mutation_check(output, prefix + 'unchanged', code, True, env, lean)])
        for name, old, new, count in mutations:
            if code.count(old) != count:
                raise ValueError('ambiguous host-lift mutation: ' + name + ': ' + str(code.count(old)))
            records += checked_controls(output, [mutation_check(output, prefix + name, code.replace(old, new), False, env, lean)])
    return records
