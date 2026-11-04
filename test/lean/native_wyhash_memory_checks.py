"""Check scoped heap hashing and its stateful lookup/publication consumers.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import native_wyhash_init_checks as initializer
import native_wyhash_update_checks as update_air
import native_hash_byte_views_checks as byte_views
import native_wyhash_hash_checks as base
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check, kernel_rejection
from check_zig_air_memory_proofs import without_imports
from check_word_swap import ROOT

require = base.require
MODULE = 'Compiler.Extraction.WyhashMemoryTests'
CELL = 'Compiler.ZigAir.Memory.CellFrame.'
STACK = 'Compiler.ZigAir.Memory.StackFrame.'
MEMORY = 'Compiler.Extraction.WyhashMemory.'
CALLER = 'Compiler.ZigAir.WyhashCallerInit.'
CALL = 'Compiler.ZigAir.AggregateCall.'
MAP, GRAPH = base.MAP, base.GRAPH
NEW_CLAIMS = [CELL + n for n in ('borrow_eq', 'access_eq', 'load_eq', 'store_eq', 'allocated', 'create_allocated')]
NEW_CLAIMS += [STACK + n for n in ('create', 'trans', 'old_lookup', 'cleanup_heap', 'cleanup_valid')]
NEW_CLAIMS += [MEMORY + n for n in ('ops_eq', 'copy_valid', 'prepare_valid', 'finish_verified', 'runInitializedRaw_verified', 'runRaw_verified', 'run_verified')]
NEW_CLAIMS += [MAP + 'HashInput.wyhash_bounds', MAP + 'HeapFrame.invariant']
NEW_CLAIMS += [GRAPH + 'Facts.' + n for n in ('same_heap', 'scoped_hash', 'lookup_from_scoped_wyhash', 'probe_scoped_wyhash_then_publish')]
NEW_CLAIMS += [MEMORY + 'Tests.' + n for n in ('caller_valid', 'captured_scoped_results', 'allocation_rejections',
    'uninitialized_word_rejected', 'readonly_word_rejected', 'partial_input_cleanup',
    'initialized_local', 'nested_initialization_failures', 'missing_initializer_store_rejected')]
NEW_CLAIMS += [CALLER + n for n in ('source_code', 'prefix_verified', 'run_verified')]
NEW_CLAIMS += [CALL + n for n in ('bind_ok', 'bind_fault', 'invoke_constant')]
NEW_CLAIMS += [GRAPH + 'MapScopedWyhashTests.' + n for n in ('publication_lookup', 'original_bytes_consumed',
    'missing_bytes_rejected', 'empty_skips_allocation')]
NEW_CLAIMS += byte_views.CLAIMS
CLAIMS = base.CLAIMS + NEW_CLAIMS + initializer.CLAIMS + update_air.CLAIMS
DEFINITION_NAMES = [CELL + n for n in ('mk', 'install', 'borrow', 'create')]
DEFINITION_NAMES += [STACK + 'mk']
DEFINITION_NAMES += [MEMORY + n for n in ('replace', 'pointer', 'ops', 'updates', 'copy', 'prepare', 'finish', 'runInitializedRaw', 'runRaw', 'run')]
DEFINITION_NAMES += [CALL + n for n in ('Prim.eval', 'semantics', 'allocateCallStore')]
DEFINITION_NAMES += [CALLER + n for n in ('code', 'afterEnv', 'completion', 'run')]
DEFINITION_NAMES += ['Compiler.ZigAir.GeneratedExpressionHashInit.fragment']
DEFINITION_NAMES += [MAP + 'Search.' + n for n in ('scopedHash', 'withScopedWyhash', 'insertionWithScopedWyhash')]
DEFINITION_NAMES += [GRAPH + 'withMemory']
STATEMENT_NAMES = [CELL + 'load_eq', CELL + 'store_eq', MEMORY + 'ops_eq', MEMORY + 'run_verified']
STATEMENT_NAMES += [GRAPH + 'Facts.' + n for n in ('scoped_hash', 'lookup_from_scoped_wyhash', 'probe_scoped_wyhash_then_publish')]
STATEMENT_NAMES += [CALLER + n for n in ('source_code', 'prefix_verified', 'run_verified')]
# Complete exported terms are reviewed and pinned, never updated by acceptance.
DEFINITIONS = {'Compiler.ZigAir.Memory.CellFrame.mk': 'f0f23b3ba7aa969b0a01aaeafc1c2e26f3f0dcf0fc177a68c4383205908ef4f9',
 'Compiler.ZigAir.Memory.CellFrame.install': 'b5de5954c7a8178b11c2b54ac611931384509c0bd6c08fd20aff67542a271d45',
 'Compiler.ZigAir.Memory.CellFrame.borrow': '096f2b133b0a9630c350ca220b8645dc8c8d96965ef65b1f99db81599b145953',
 'Compiler.ZigAir.Memory.CellFrame.create': '4f9472c9d54f730834335c7b2e1d56be3cd2e4ef14105b60f8d9c10cb3fcc040',
 'Compiler.ZigAir.Memory.StackFrame.mk': 'fdc2afea7257a027c08836f34b854efcc75ad26f8365f33363b3a7b831f047d1',
 'Compiler.Extraction.WyhashMemory.replace': 'd84d40117cc9508876f080893c5d5513d434f02fde448c90c141c5b0db8c0354',
 'Compiler.Extraction.WyhashMemory.pointer': '27254009fe0ea65a4754c38f35b4daa0d84f2aeb05e7027d96237d8b9242e327',
 'Compiler.Extraction.WyhashMemory.ops': 'a3dbe074ac4d06031948ba7b38f9b5e085bbe19368634ce677ef1d3ab57e53db',
 'Compiler.Extraction.WyhashMemory.updates': '935e37bc1751704feaf49b747d7c0dd3034b7f22080520b7c6de12e952d17d5a',
 'Compiler.Extraction.WyhashMemory.copy': '0af64d99d6a3085c1c106ed5773b6f6dee803850e24d3ae75e5dfaa74214bbbb',
 'Compiler.Extraction.WyhashMemory.prepare': 'b99d628191715f2c4395a7fa9a57267c163c74c6c6d5bef05d46c3b16b75c9dc',
 'Compiler.Extraction.WyhashMemory.finish': '6eb1bbd9e9a4033a9461f3c1badc22350a81f4c662be5d4d7050c8b9a61434e9',
 'Compiler.Extraction.WyhashMemory.runInitializedRaw': 'a75ca44de32c5d921d6baabd2cdb1c634200e510eab32844b3cbe05b791afa1c',
 'Compiler.Extraction.WyhashMemory.runRaw': '6b78583163ab63b5a4b819aec32773cc606ee5e50161c575f8ad5e08c78f93f2',
 'Compiler.Extraction.WyhashMemory.run': '4b8558dac7ad9385da27fab7bb24ca0ec23f81321d525340f7348ba74f5ddc05',
 'Compiler.ZigAir.AggregateCall.Prim.eval': '3ea410dcf693c683f03c69282b61f442895b713f2ca5d2fa73e00f658f4f10d9',
 'Compiler.ZigAir.AggregateCall.semantics': 'b0a254ef35c40201730cb0b1a2b9faa581915d322aaac7b83986396ee7dc5ec1',
 'Compiler.ZigAir.AggregateCall.allocateCallStore': 'b0c6994e378034567ed9ba9c7e24edd8a0d53dda43b751f1e8fb7c322e23752d',
 'Compiler.ZigAir.WyhashCallerInit.code': '4dbc06baf77621faa6fc2f9f81ee844422f1590bd57ddc9c806b115a7e5bba4e',
 'Compiler.ZigAir.WyhashCallerInit.afterEnv': '8a4f294a58eccd83a25e14e56ecae03d937728a3bb987b8db09cd9a1c7bf4fb2',
 'Compiler.ZigAir.WyhashCallerInit.completion': 'ab0be69e287543679b3ce4017009fe7f159469de0baf6ff2d7e4e89fc71b0355',
 'Compiler.ZigAir.WyhashCallerInit.run': '75b83620fa238a43af297eac204d565caa7279e7883daff39bde81882d8afdfa',
 'Compiler.ZigAir.GeneratedExpressionHashInit.fragment': '2e30f6e657c4c02917bf61b5b0ede72ceabbdcf11721c10aece97493c23a0cfb',
 'Compiler.Extraction.ExpressionMap.Search.scopedHash': '8724fc3ab2067a65d34c78a0f8ed84eeaa19f3f43f814d3b676c90d9383d85e7',
 'Compiler.Extraction.ExpressionMap.Search.withScopedWyhash': 'f24acfceca4d03c874e7f8841dc65b49e1a160fe0d6d94d5745932124367d145',
 'Compiler.Extraction.ExpressionMap.Search.insertionWithScopedWyhash': '531e99333e239bb004e6051c4e20929d755587878aabbb5b9336ed39b850929e',
 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.withMemory': 'c65e97597b770813611c13d8178ba8fd88bcf5a0f3b5b05a82526dc0b48f4b7a'}
STATEMENTS = {'Compiler.ZigAir.Memory.CellFrame.load_eq': '130b148ea9793f62625892fa1123ee7a14e5cc460517781feffa1d6336edf946',
 'Compiler.ZigAir.Memory.CellFrame.store_eq': '9403499e09f327eca0b589265cf2bbb9ffa348747832b633300e233338989a31',
 'Compiler.Extraction.WyhashMemory.ops_eq': 'c3f75e5d27b64b10277a98ce19e7afe29434adac5bde0b06ea440200cddcc1a4',
 'Compiler.Extraction.WyhashMemory.run_verified': 'ae32fc4a2410c6e76f4d2f40f18072e5b1fc535a7426fd8cc28721d6dee1d5ab',
 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.Facts.scoped_hash': '8a2c45f33f27fcd38e384a37c21ecdf203ec1499104d5370a2c6ff121d2aa04c',
 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.Facts.lookup_from_scoped_wyhash': '5207070a5e5b230607ed042e58202d681058e493e9cec471eda2a515ff8edc2e',
 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.Facts.probe_scoped_wyhash_then_publish': '760a8549ebc5563870f10cb7bca6c4f583370e6f087f2c8053298f52b274a5c1',
 'Compiler.ZigAir.WyhashCallerInit.source_code': 'a31bf642fdc090c5dc4403e4ba61df3c7538364777c6bfa80cd6ca7cd7a83abc',
 'Compiler.ZigAir.WyhashCallerInit.prefix_verified': '2a4024ac2e0fefd1be84b5aa105d7a2aaeba1e8910de7c7ecf6174d915eac2ee',
 'Compiler.ZigAir.WyhashCallerInit.run_verified': 'c13f617d58ff7848d67a9324eab21762d661aae64fc79bcc78969f766eba20ff'}


def interfaces(output, env, lean):
    require(set(update_air.DEFINITIONS) == set(update_air.DEFINITION_NAMES), 'incomplete update execution definition pins')
    require(set(initializer.DEFINITIONS) == set(initializer.DEFINITION_NAMES), 'incomplete initializer definition pins')
    require(set(byte_views.DEFINITIONS) == set(byte_views.DEFINITION_NAMES), 'incomplete byte-view definition pins')
    require(set(DEFINITIONS) == set(DEFINITION_NAMES), 'incomplete scoped hash definition pins')
    result = base.local.inputs.search.interfaces(output, env, lean, module=MODULE,
        definitions={**base.DEFINITIONS, **DEFINITIONS, **initializer.DEFINITIONS, **byte_views.DEFINITIONS,
                     **update_air.DEFINITIONS}, prefix='wyhash-hash')
    result['updateExecutionRegressions'] = update_air.execution_regressions(output, env, lean)
    return result


def audit(rows):
    update_audit = update_air.audit(rows, base.local.inputs.search.probe.encoded_digest, require)
    prior = base.audit(rows)
    init_audit = initializer.audit(rows, base.local.inputs.search.probe.encoded_digest)
    byte_audit = byte_views.audit(rows, base.local.inputs.search.probe.encoded_digest, require)
    indexed = {r['theorem']: r for r in rows}
    dependencies = {
        MEMORY + 'ops_eq': {CELL + 'load_eq', CELL + 'store_eq'},
        MEMORY + 'finish_verified': {STACK + 'create', MEMORY + 'copy_valid', MEMORY + 'prepare_valid', MEMORY + 'ops_eq'},
        MEMORY + 'runInitializedRaw_verified': {base.HASH + 'updates_verified', base.HASH + 'run_digest', MEMORY + 'finish_verified'},
        MEMORY + 'runRaw_verified': {CALLER + 'run_verified', MEMORY + 'runInitializedRaw_verified'},
        CALLER + 'run_verified': {CALLER + 'prefix_verified'},
        CALLER + 'prefix_verified': {'Compiler.ZigAir.WyhashInit.run_framed', CALL + 'bind_ok', CALL + 'bind_fault'},
        MEMORY + 'run_verified': {MEMORY + 'runRaw_verified', STACK + 'cleanup_heap', STACK + 'cleanup_valid'},
        GRAPH + 'Facts.scoped_hash': {GRAPH + 'Facts.query_view', GRAPH + 'Facts.query_byte_budget', byte_views.BYTES + 'run_verified'},
        GRAPH + 'Facts.lookup_from_scoped_wyhash': {GRAPH + 'Facts.scoped_hash', GRAPH + 'Facts.same_heap',
            MAP + 'HeapFrame.invariant', GRAPH + 'Facts.lookup_from_receiver'},
        GRAPH + 'Facts.probe_scoped_wyhash_then_publish': {GRAPH + 'Facts.scoped_hash', GRAPH + 'Facts.same_heap',
            MAP + 'HeapFrame.invariant', GRAPH + 'Facts.probe_receiver_then_publish'},
    }
    for name, required in dependencies.items():
        require(required <= set(indexed[name]['dependencies']), 'scoped hash lost its producer/consumer: ' + name)
    for name in NEW_CLAIMS:
        if not any(part.endswith('Tests') for part in name.split('.')):
            require(not any(part.endswith('Tests') for dep in indexed[name]['dependencies'] for part in dep.split('.')),
                'scoped hash core depends on a fixture')
    require(set(STATEMENTS) == set(STATEMENT_NAMES), 'incomplete scoped hash statement pins')
    for name, expected in STATEMENTS.items():
        require(base.local.inputs.search.probe.encoded_digest(indexed[name]['statement']) == expected,
                'changed scoped hash statement: ' + name)
    for old, new in (('lookup_from_local_wyhash', 'lookup_from_scoped_wyhash'),
                     ('probe_local_wyhash_then_publish', 'probe_scoped_wyhash_then_publish')):
        old_fields, old_lets, _, _ = base.local.inputs.telescope(indexed[GRAPH + 'Facts.' + old]['statement'])
        fields, lets, _, _ = base.local.inputs.telescope(indexed[GRAPH + 'Facts.' + new]['statement'])
        require(list(fields) == list(old_fields) and not lets and not old_lets,
                'scoped hash consumer gained an admission premise')
    return {**prior, **init_audit, **byte_audit, 'updateExecution': update_audit,
        'checkedScopedDependencies': sorted(dependencies), 'checkedScopedStatements': list(STATEMENTS),
        'scopedHeapAdapterVerified': True, 'scopedLookupPublicationVerified': True,
        'capturedCallerInitializationVerified': True,
        'sourceAdapterFormallyVerified': False, 'localHeapAdmissionVerified': False, 'nativeHashProducerVerified': False,
        'remaining': 'Anonymous-empty-slice storage, caller byte admission, hash-runner consumption, finalization AIR and key-copy admission remain open; complete pointer-backed native update invocation, byte views and hasher initialization are checked.'}


def audit_controls(rows):
    records = base.audit_controls(rows)
    for name in [*STATEMENTS, *initializer.STATEMENTS, *byte_views.STATEMENTS, *update_air.STATEMENTS,
                 *update_air.refinement.STATEMENTS]:
        bad = copy.deepcopy(rows)
        next(r for r in bad if r['theorem'] == name)['statement']['root'] = -1
        try: audit(bad)
        except ValueError as error: records.append({'name': name, 'rejection': str(error)})
        else: raise ValueError('accepted changed scoped hash statement')
    return records


def source_binding(lib):
    return {**base.source_binding(lib), 'scopedHeapAdapterVerified': True,
        'scope': 'Scoped hashing consumes captured initialization, then each view/update pair in captured caller order. Complete buffered invocations and all six captured lane sites refine the cell invariant, including lane allocation failure. Complete fill/loop/suffix composition, runner consumption, finalization AIR and key-copy admission remain open.'}


capture = base.capture
source_controls = base.source_controls


def caller_controls(output, env, lean):
    directory = ROOT / 'lean/Compiler/ZigAir'
    model = 'import Compiler.ZigAir.WyhashInitRun\n'
    model += without_imports((directory / 'AggregateCall.lean').read_text()).split('theorem bind_ok', 1)[0]
    model += '\nend Compiler.ZigAir.AggregateCall\n'
    caller = without_imports((directory / 'WyhashCallerInit.lean').read_text())
    model += caller.split('theorem source_code', 1)[0]
    model += '\ndef run (' + caller.split('def run (', 1)[1].split('theorem run_verified', 1)[0]
    model += '\nend Compiler.ZigAir.WyhashCallerInit\nderiving instance DecidableEq for Except\n'
    initial = 'Compiler.Extraction.WyhashUpdate.initialCells (Compiler.Extraction.WyhashUpdate.seedState 0)'
    owner = 'Compiler.ZigAir.WyhashInit.objectType'
    success = f'''Compiler.ZigAir.WyhashCallerInit.run ⟨[], 1, 4096⟩ 0 =
      (.ok 1, ⟨[(1, ⟨4096, {owner}, {initial}, true, true⟩)], 5, 4320⟩)'''
    limit = 'Compiler.ZigAir.Memory.addressLimit'
    failure = f'''Compiler.ZigAir.WyhashCallerInit.run ⟨[], 1, {limit} - 216⟩ 0 =
      (.error .outOfMemory, ⟨[(1, ⟨{limit} - 216, {owner}, [], true, true⟩)], 3, {limit} - 8⟩)'''
    records = [mutation_check(output, 'wyhash-caller-unchanged', model +
        f'example : {success} := by decide +kernel\nexample : {failure} := by decide +kernel\n', True, env, lean)]
    edits = [
        ('wrong-seed', '[.constant (number seed)] next', '[.constant (number (seed + 1))] next', success),
        ('missing-store', '(.store (.local allocationReg) (.local resultReg))',
            '(.store (.local allocationReg) (.local allocationReg))', success),
        ('wrong-return', 'code seed (.ret (.local 4))', 'code seed (.ret (.local 5))', success),
        ('rewound-callee-failure', '| .ok values => program.run values state',
            '| .ok values =>\n      let (result, after) := program.run values state\n'
            '      match result with\n      | .error fault => (.error fault, state)\n      | .ok value => (.ok value, after)', failure),
    ]
    for name, before, after, comparison in edits:
        if before == '(result, cleanup state.nextId after)':
            before = 'let (result, after) := runRaw state seed inputs\n  ' + before
            after = 'let (result, after) := runRaw state seed inputs\n  ' + after
        require(model.count(before) == 1, 'missing or ambiguous caller mutation: ' + name)
        records.append(mutation_check(output, 'wyhash-caller-' + name,
            model.replace(before, after, 1) + kernel_rejection(comparison), False, env, lean))
    return checked_controls(output, records)


def scoped_controls(output, env, lean):
    records = []
    directory = ROOT / 'lean/Compiler/Extraction'
    model = 'import Compiler.ZigAir.WyhashCallerInit\nimport Compiler.Extraction.WyhashHashTests\nimport Compiler.Extraction.ExpressionMapHeapFrame\nimport Compiler.Extraction.WyhashMemory\nimport Compiler.Extraction.ExpressionMapHashBytes\nimport Compiler.Extraction.ExpressionMapHashBytesTests\n'
    model += without_imports((directory / 'WyhashMemoryRun.lean').read_text()).split('theorem copy_valid (', 1)[0]
    model += '\nend Compiler.Extraction.WyhashMemory\n'
    model += without_imports((directory / 'ExpressionMapHashOrder.lean').read_text()).split('theorem observe_verified (', 1)[0]
    model += '\nend Compiler.Extraction.ExpressionMap.HashBytes.Ordered\n'
    model += without_imports((directory / 'GeneratedExpressionHashOrder.lean').read_text())
    model += '\nnamespace Compiler.Extraction.ExpressionMap.HashBytes\nopen Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray\nopen Compiler.Extraction.Cache (Key)\n'
    model += 'def runRaw (' + (directory / 'ExpressionMapHashBytesRun.lean').read_text().split('def runRaw (', 1)[1].split('theorem runRaw_verified (', 1)[0]
    model += '\nend Compiler.Extraction.ExpressionMap.HashBytes\n'
    model += without_imports((directory / 'ExpressionMapWyhashMemory.lean').read_text()).split('namespace ' + GRAPH.rstrip('.'), 1)[0]
    fixture = without_imports((directory / 'WyhashMemoryTests.lean').read_text())
    # Keep each deliberately false witness small. Re-elaborating every full
    # fixture against a broken heap model can spend gigabytes normalizing the
    # failed equality. The unchanged root and fresh replay retain all fixtures.
    empty = '({ heap := [], nextId := 1, nextAddress := 4096 } : Compiler.ZigAir.Memory.State)'
    short = f'Compiler.Extraction.WyhashMemory.run {empty} 0 [[1, 2, 3]]'
    failed_view = f'(Compiler.Extraction.ExpressionMap.HashBytes.runRaw {empty} ⟨0, 0, 0, [7], 0⟩ ⟨999, 0, 1⟩)'
    prefix = f'Compiler.ZigAir.Memory.load {failed_view}.2 '
    prefix += '(.pointer (.pointer false false Compiler.ZigAir.Memory.usize) ⟨2, 40⟩) = '
    prefix += '.ok (Compiler.Extraction.WyhashLocal.word 37)'
    comparisons = {
        'leaked-local': f'({short}).2.heap = []',
        'wrong-cleanup-mark': f'({short}).2.heap = []',
        'rewound-counters': f'({short}).2.nextId = 6',
        'wrong-scratch-extent': '(Compiler.Extraction.WyhashMemory.run '
            '({ heap := [], nextId := 1, nextAddress := Compiler.ZigAir.Memory.addressLimit - 360 } : Compiler.ZigAir.Memory.State) '
            '0 [List.replicate 41 0]).2.nextId = 7',
        'lost-exhaustion': '(Compiler.Extraction.WyhashMemory.run '
            '({ heap := [], nextId := 1, nextAddress := Compiler.ZigAir.Memory.addressLimit } : Compiler.ZigAir.Memory.State) '
            '0 []).1 = .error .outOfMemory',
        'unobserved-bytes': f'(Compiler.Extraction.ExpressionMap.Search.scopedHash {empty} '
            '⟨0, 0, 0, [7], 0⟩ ⟨999, 0, 1⟩).1 = .error .unallocated',
        'lost-input-failure-cursors': f'(Compiler.Extraction.ExpressionMap.Search.scopedHash {empty} '
            '⟨0, 0, 0, [7], 0⟩ ⟨999, 0, 1⟩).2.nextId = 7',
        'lost-input-success-cursors': f'(Compiler.Extraction.ExpressionMap.Search.scopedHash {empty} '
            '⟨0, 0, 0, [], 0⟩ ⟨999, 0, 0⟩).2.nextId = 9',
        'precollected-inputs': '(Compiler.Extraction.ExpressionMap.HashBytes.run '
            '({ heap := [], nextId := 1, nextAddress := Compiler.ZigAir.Memory.addressLimit - 176 } : Compiler.ZigAir.Memory.State) '
            '⟨0, 0, 0, [7], 0⟩ ⟨999, 0, 1⟩).1 = .error .outOfMemory',
        'skipped-updates': prefix,
        'lost-update-state': prefix,
    }
    tests = {name: f'example : {proposition} := by decide +kernel\n' for name, proposition in comparisons.items()}
    tests.update({
        'stale-publication-cursors': 'open Compiler.Extraction.ExpressionMap Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray in\n'
            'example (place : Initialization.Placement) (safety : Bool) (state after : State) (receiver : Nat) '
            '(key : Compiler.Extraction.Cache.Key) (source : View) (hash : BitVec 64) '
            '(ran : Search.scopedHash state key source = (.ok hash, after)) : '
            '(Search.insertionWithScopedWyhash place safety state receiver key source).2 = after := by\n'
            '  simp only [Search.insertionWithScopedWyhash, ran]\n',
    })
    records.append(mutation_check(output, 'wyhash-memory-unchanged', model + fixture + ''.join(tests.values()), True, env, lean))
    for name, before, after in (
        ('leaked-local', '(result, cleanup state.nextId after)', '(result, after)'),
        # Skip the caller's hasher, which precedes the retired callee locals.
        ('wrong-cleanup-mark', '(result, cleanup state.nextId after)', '(result, cleanup (state.nextId + 4) after)'),
        ('rewound-counters', '(result, cleanup state.nextId after)', '(result, { state with heap := (cleanup state.nextId after).heap })'),
        ('wrong-scratch-extent', 'CellFrame.create middle WyhashBuffer.scratch.owner', 'CellFrame.create middle objectType'),
        ('lost-exhaustion', '(result, cleanup state.nextId after)', '(.ok (result.toOption.getD 0), cleanup state.nextId after)'),
        ('unobserved-bytes', '| none => argumentBytes state keyId', '| none => (.ok [], state)'),
        ('lost-input-failure-cursors', 'match bytes with\n    | .error fault => (.error fault, viewed)',
            'match bytes with\n    | .error fault => (.error fault, state)'),
        ('lost-input-success-cursors', 'CellFrame.borrow viewed self objectType', 'CellFrame.borrow state self objectType'),
        ('precollected-inputs',
            'def run (state' + (directory / 'ExpressionMapHashOrder.lean').read_text().split('def run (state', 1)[1].split('\ntheorem observe_verified', 1)[0],
            'def run (state : State) (keyId : Nat) (_order : List Input) : Except Fault (BitVec 64) × State :=\n'
            '  let (bytes, viewed) := HashBytes.inputs state keyId\n'
            '  match bytes with\n'
            '  | .error fault => (.error fault, viewed)\n'
            '  | .ok bytes => WyhashMemory.runRaw viewed 0 bytes\n'),
        ('skipped-updates', 'WyhashMemory.updates [bytes]', 'WyhashMemory.updates []'),
        ('lost-update-state', '| .ok (_, updated) => updates keyId self rest updated',
            '| .ok (_, updated) => updates keyId self rest viewed'),
        ('stale-publication-cursors', '(insertionAfterHash place safety after receiver hash key source, after)',
            '(insertionAfterHash place safety after receiver hash key source, state)'),
    ):
        if before == '(result, cleanup state.nextId after)':
            before = 'let (result, after) := runRaw state seed inputs\n  ' + before
            after = 'let (result, after) := runRaw state seed inputs\n  ' + after
        require(model.count(before) == 1, 'missing or ambiguous scoped hash mutation: ' + name)
        changed = model.replace(before, after, 1)
        witness = kernel_rejection(comparisons[name]) if name in comparisons else tests[name]
        records.append(mutation_check(output, 'wyhash-memory-' + name, changed + witness, False, env, lean))
    return checked_controls(output, records)


def controls(output, env, lean):
    return (base.controls(output, env, lean) + initializer.controls(output, env, lean) +
            scoped_controls(output, env, lean) + caller_controls(output, env, lean) + byte_views.controls(output, env, lean) +
            update_air.controls(output, env, lean))
