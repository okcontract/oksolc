"""Check that recorded child induction uses the executable dispatch guard.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
from assembly_item_creation_checks import checked_controls
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

MISS = gate.OWNED + 'MissStream.'
NATIVE = gate.OWNED + 'Caller.ProtocolTrace.Native.'
CLAIMS = [MISS + name for name in ('selected_preserved', 'from_children', 'scoped_from_children')]
CLAIMS += [NATIVE + name for name in ('miss_verified', 'miss_traced_verified', 'initialized_miss_continuation')]
INTERFACES = (MISS + 'selected', NATIVE + 'MissInduction')


def source_guard(interfaces):
    value = next(row['value'] for row in interfaces if row['name'] == MISS + 'selected')
    _, root, context = gate.domains(value)
    head, args = gate.applied(value, root)
    if head[:2] != ['const', 'ite'] or len(args) != 5:
        raise ValueError('native dispatch selection changed')
    return gate.named(value, args[1], context)


def guarded_body(value, root, context, guard):
    node = value['nodes'][root]
    if node[0] != 'forall' or gate.named(value, node[3], context) != guard:
        raise ValueError('child contract does not use the actual dispatch guard')
    return node[4], context + [node[1]]


def audit(rows, interfaces):
    guard = source_guard(interfaces)

    def check(value):
        def visit(root, context, selected):
            node = value['nodes'][root]
            if node[0] in ('forall', 'lambda'):
                active = selected or (node[0] == 'forall' and gate.named(value, node[3], context) == guard)
                return visit(node[3], context, selected) + visit(node[4], context + [node[1]], active)
            if node[0] == 'let':
                return (visit(node[2], context, selected) + visit(node[3], context, selected)
                        + visit(node[4], context + [node[1]], selected))
            if node[0] == 'app':
                head, args = gate.applied(value, root)
                if head[:2] == ['const', 'Compiler.Extraction.Dispatch.Effects.SourceConstructorsAt']:
                    if not selected:
                        raise ValueError('recorded induction still requires unselected children')
                    return 1
                return sum(visit(arg, context, selected) for arg in args)
            return 0

        if visit(value['root'], [], False) != 1:
            raise ValueError('recorded induction lost its single guarded child projection')

    statements = {row['theorem']: row['statement'] for row in rows}
    dependencies = {row['theorem']: set(row['dependencies']) for row in rows}
    required = {
        MISS + 'selected_preserved': {gate.NS + 'simplify_at', MISS + 'selected'},
        MISS + 'from_children': {MISS + name for name in ('from_frame', 'selected_preserved', 'tail_inputs', 'inserted', 'published', 'failed')},
        MISS + 'scoped_from_children': {MISS + name for name in ('from_children', 'selected_preserved', 'projected')},
        NATIVE + 'miss_verified': {MISS + 'scoped_from_children', MISS + 'selected_preserved', NATIVE + 'miss_recorded'},
        NATIVE + 'miss_traced_verified': {NATIVE + 'miss_verified', NATIVE + 'history_boundaries'},
        NATIVE + 'initialized_miss_continuation': {NATIVE + 'miss_traced_verified', gate.OWNED + 'Caller.ProtocolTrace.initialized_taken_recorded'},
    }
    for name in CLAIMS:
        check(statements[name])
        if not required[name] <= dependencies[name]:
            raise ValueError('guarded induction lost shared reasoning: ' + name)
        if any(part.endswith('Tests') for dependency in dependencies[name] for part in dependency.split('.')):
            raise ValueError('guarded induction depends on a fixture: ' + name)
    definition = next(row for row in interfaces if row['name'] == NATIVE + 'MissInduction')
    check(definition['value'])
    return {'checkedGuardedRoots': CLAIMS, 'guardMatchesNativeSelection': True,
            'inactivePathsRequireNoChildProjection': True, 'recursiveInductionVerified': False}


def controls(output, env, lean):
    raw = (gate.harness.ROOT / 'lean/Compiler/Extraction/InternerMissAdmission.lean').read_text()
    header = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
    header += '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n'
    body = without_imports(raw)
    source = header + body
    changes = (
        ('wrong-classifier-guard', '(deterministic && (request.item.kind == 1)) = true →',
         '(!deterministic && (request.item.kind == 1)) = true →', 2),
        ('wrong-item-guard', '(deterministic && (request.item.kind == 1)) = true →',
         '(deterministic && (request.item.kind == 2)) = true →', 2),
        ('stale-child-rows', '(coupled selected (originalRows ++ added))', '(coupled selected originalRows)', 1),
    )
    records = checked_controls(output, [mutation_check(output, 'guarded-induction-unchanged', source, True, env, lean)])
    for name, before, after, count in changes:
        if source.count(before) != count:
            raise ValueError('ambiguous guarded induction mutation: ' + name)
        records += checked_controls(output, [mutation_check(output, 'guarded-induction-' + name,
            source.replace(before, after), False, env, lean)])

    # Exercise the entire native suffix for arbitrary children with no child
    # correspondence hypothesis. Reuse the production theorem's frame inputs.
    signature = body.split('theorem from_children', 1)[1].split(' := by', 1)[0]
    begin, end = signature.index('    (coupled :'), signature.index('    (handle :')
    signature = signature[:begin] + '    (inactive : (deterministic && (request.item.kind == 1)) = false)\n' + signature[end:]
    declarations = body.split('/-- The actual guard', 1)[0]
    direct = ('import Compiler.Extraction.InternerMissAdmission\n' + declarations
        + 'example' + signature + ''' := by
  exact from_children ops allocate safety owner meaning base growth usizeBits children debug source address input
    request key slice deterministic before cursor model seed predicate values originalRows initial frame aligned
    (by intro selected; rw [inactive] at selected; cases selected)
    handle lookup leading trailing mismatch detached unowned caller
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.MissStream
''')
    records += checked_controls(output, [mutation_check(output, 'guarded-induction-inactive-suffix', direct, True, env, lean)])
    records += checked_controls(output, [mutation_check(output, 'guarded-induction-active-is-not-inactive',
        direct.replace('(inactive : (deterministic && (request.item.kind == 1)) = false)',
                       '(inactive : (deterministic && (request.item.kind == 1)) = true)'), False, env, lean)])
    return records
