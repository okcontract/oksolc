"""Audit the existing first/spare callers through the shared transfer consumer.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
import constructor_replay_choice_checks as choice
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check

NATIVE = gate.OWNED + 'Insertion.Native.'
TESTS = NATIVE + 'UnrelocatedTransferredTests.'
MODULE = 'Compiler.Extraction.InternerNativeUnrelocatedTransferredTests'
CLAIMS = [TESTS + name for name in ('entry', 'reached', 'observed', 'shared_completion', 'success')]


def audit(claims):
    required = {
        CLAIMS[0]: {NATIVE + 'CallerInputTests.derived_input', NATIVE + 'CallerSpareSuccessTests.derived_input'},
        CLAIMS[1]: {NATIVE + 'NativeFirstTests.reached_frame', NATIVE + 'NativeSpareTests.reached_frame'},
        CLAIMS[3]: {CLAIMS[0], CLAIMS[1], CLAIMS[2], gate.NS + 'Enclosing.insertion_rollback_derived'},
        CLAIMS[4]: {CLAIMS[1], CLAIMS[2], gate.NS + 'CallFrame.transferred'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('first/spare transfer bypassed the common consumer: ' + name)
    return {'checkedDependencies': sorted(required), 'existingFirstAndSpareCallersReused': True,
            'arbitraryGrowthCallbacks': True, 'bothLayoutsAndEmptyNonemptyBuffers': True,
            'composedProductionTheoremVerified': False}


def audit_statements(rows):
    statements = {row['theorem']: row['statement'] for row in rows}
    for short in ('observed', 'shared_completion', 'success'):
        value = statements[TESTS + short]
        fields, root, context = gate.domains(value)
        if list(fields) != ['spare', 'safety', 'empty'] + ([] if short == 'observed' else ['growth']):
            raise ValueError('first/spare fixture added an admission premise')
        if short == 'observed':
            joint.app(value, root, NATIVE + 'UnrelocatedTransferred')
        else:
            joint.app(value, root, gate.NS + ('FramePost' if short == 'shared_completion' else 'TransferredReturn'))
            call, scope = choice.one_call(value, value['root'], [], NATIVE + 'insert')
            if gate.named(value, call[12], scope) != 'Bool.false' or gate.named(value, call[13], scope) != 'growth':
                raise ValueError('first/spare transfer specializes another source branch or growth callback')
    return {'sourceObservationsOnly': True, 'actualTransferSuccessAndReturn': True}


def controls(output, env, lean):
    source = '''import Compiler.Extraction.InternerNativeUnrelocatedTransferredTests
namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.UnrelocatedTransferredTests.Controls
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open AssemblyItem.Creation.NativeFields.Tests (input source)
open CallerInputTests (key)
open RepresentativeArray
example (spare safety empty : Bool) (growth : Option (Growth.Registered.Callbacks Nat)) :
    (Insertion.Native.insert ops (allocate spare) safety 7 6 (argumentView spare empty) source
      Insertion.Tests.model input (key empty) (normalized spare empty) false growth (taken spare safety empty).2.world).1 =
        .ok (Storage.idFor ((taken spare safety empty).2.world.graph.representatives.getD [])) :=
  (success spare safety empty growth).1
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.UnrelocatedTransferredTests.Controls
'''
    records = checked_controls(output, [mutation_check(output, 'unrelocated-transferred-fixture-unchanged', source, True, env, lean)])
    for name, before, after in (
        ('wrong-branch', 'empty) false growth', 'empty) true growth'),
        ('wrong-id', '.ok (Storage.idFor', '.ok (1 + Storage.idFor'),
    ):
        if source.count(before) != 1:
            raise ValueError('ambiguous first/spare fixture mutation: ' + name)
        records += checked_controls(output, [mutation_check(output, 'unrelocated-transferred-fixture-' + name,
            source.replace(before, after), False, env, lean)])
    return records
