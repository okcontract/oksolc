"""Bind the complete captured initializer to its checked execution and consumers.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
from pathlib import Path
import sys

from check_word_swap import ROOT
from check_zig_air_proofs import mutation_check, kernel_rejection
from check_zig_air_memory_proofs import without_imports
from assembly_item_creation_checks import checked_controls

sys.path.insert(0, str(ROOT / 'lean/zig_air'))
from build_toolchain import digest, write_json
from capture import capture as capture_air, read_json
from generate import captured_path
from generate_aggregate import render
from check_wyhash_air import ENTRIES, inspect_capture
from check_expression_hash_air import check as check_production_caller
import native_wyhash_update_checks as update_air

INIT = 'Compiler.ZigAir.WyhashInit.'
AIR = 'Compiler.ZigAir.AggregateAir.'
CLAIMS = [INIT + name for name in ('mix_prefix', 'copy_lane', 'return_code', 'return_tail',
    'mix_return', 'scratch_return', 'body_verified', 'run_framed', 'run_verified')]
CLAIMS += [AIR + name for name in ('store_root', 'load_root', 'array_element', 'create_bindings',
    'scalar_xor', 'scalar_extend', 'scalar_trunc', 'scalar_mul', 'scalar_shift')]
CLAIMS += ['Compiler.ZigAir.Memory.CellFrame.' + name for name in
    ('load_current', 'store_current', 'install_current')]
CLAIMS += ['Compiler.ZigAir.Memory.StackFrame.cleaned', 'Compiler.ZigAir.Control.Code.prefix_drop']
CLAIMS += ['Compiler.ZigAir.WyhashInitTests.' + name for name in
    ('seed_zero', 'seed_max', 'first_allocation_oom', 'second_allocation_oom', 'third_allocation_oom')]
CLAIMS += [AIR + 'Tests.' + name for name in ('fixture_valid', 'partial_assignment_forgets_absent_leaves',
    'snapshot_is_value_not_local_alias', 'readonly_and_dead_reject', 'nominal_and_field_identity_reject',
    'nested_aggregate_copy_rejects_explicitly', 'declared_array_bound_precedes_larger_heap', 'forged_array_parent_rejects')]
DEFINITION_NAMES = [AIR + name for name in ('Register.type', 'Register.valid', 'Register.hasType', 'values',
    'Ref.eval', 'Ref.value', 'load', 'store', 'arrayElementPointer', 'Prim.transition', 'Prim.eval',
    'semantics', 'Program.finish', 'Program.run')]
DEFINITION_NAMES += ['Compiler.ZigAir.Scalar.Prim.eval', 'Compiler.ZigAir.GeneratedWyhashInit.fn_init',
                    'Compiler.Extraction.WyhashLocal.objectType']
STATEMENT_NAMES = [INIT + name for name in ('body_verified', 'run_framed', 'run_verified')]
# Reviewed complete exported terms; acceptance never updates these pins.
DEFINITIONS = {'Compiler.ZigAir.AggregateAir.Register.type': '192ab83e55e1a3effd02dee944a1a91c58485d9f06451dd778c4688d596a6af3',
 'Compiler.ZigAir.AggregateAir.Register.valid': '15ae61860b8c42e907db14d782899eef15c479f76da34c5a0c7ef4c3d8b088ed',
 'Compiler.ZigAir.AggregateAir.Register.hasType': 'fccbe7b396eba903f0a352137afac02bbe1e5edc00a0f703622ae19d9b32bad6',
 'Compiler.ZigAir.AggregateAir.values': '9243a136327c1a548e2d8b984d7f58e50874406c4b023b6217b87e212f5855bd',
 'Compiler.ZigAir.AggregateAir.Ref.eval': 'c7a204bb3836e1bfd81ba6d1af7a576cea22d5aa7fed1fb90392876ca9e0b07e',
 'Compiler.ZigAir.AggregateAir.Ref.value': 'eae6e5bf16d7c49b8539a11063be994b0e3fffccf43bdb1535ef5ade3cbf2398',
 'Compiler.ZigAir.AggregateAir.load': '6df9247b6729d729255c6423b609ae3ae3ed97bcb42559094d36a8be3e7ee1d1',
 'Compiler.ZigAir.AggregateAir.store': '2d3c80c8b304a319f8e28ee852361de1892142e690a9bf3dfcb78543b828689e',
 'Compiler.ZigAir.AggregateAir.arrayElementPointer': '181e6fc0197e1698ab14adb81831d9802f14c0d03d83a5a940552bd14d9407e6',
 'Compiler.ZigAir.AggregateAir.Prim.transition': '6dcd1a13cd59d4285d6715ffbcb9c94ad8c11376e0025c7528732f7454d91a2c',
 'Compiler.ZigAir.AggregateAir.Prim.eval': 'c7103394586668f388e81cedfb4371b47017ff1cc47c46a89b5450701f98c4af',
 'Compiler.ZigAir.AggregateAir.semantics': '70083f0216713ac421828cd157bef7cf42c47ab093a5ee4d95394a61f2df9362',
 'Compiler.ZigAir.AggregateAir.Program.finish': '95b90d93698ffca86e17133fd1f6b7062f36ec293628b2bfd402eb1464ab8e74',
 'Compiler.ZigAir.AggregateAir.Program.run': 'e2ac171ab8900408e99ba7a053e6629eecc23f3a5184d14cf30824363ebda13a',
 'Compiler.ZigAir.Scalar.Prim.eval': '87f301bb620dcb4ea60a725778490866cdd97e472365f44e1ba2a96a22bcbfa6',
 'Compiler.ZigAir.GeneratedWyhashInit.fn_init': '1955fe8e37cf519144181e557958309b268c1ed85be133dc702ed0fb5f08c5e2',
 'Compiler.Extraction.WyhashLocal.objectType': '28180622ff9f2cb0087e668eb0a55f47076f8e035cdfe2b162973faeea8e4245'}
STATEMENTS = {'Compiler.ZigAir.WyhashInit.body_verified': '4540d202790ad8c9401d04021482b581d219d3928962cea76d6cdc5b12ad9c49',
 'Compiler.ZigAir.WyhashInit.run_framed': '3c4a16d5457cce8daf1404331d0520ffb10c8b8ce80f7b5a1adf40aaab4daecf',
 'Compiler.ZigAir.WyhashInit.run_verified': 'b8472396ce12097c48ac1fbdad15e92b6a350b5bb58bd74efc459842e674aa1d'}


def audit(rows, encoded_digest):
    indexed = {row['theorem']: row for row in rows}
    required = {
        INIT + 'body_verified': {INIT + 'scratch_return', AIR + 'create_bindings'},
        INIT + 'scratch_return': {INIT + 'mix_return', AIR + 'create_bindings'},
        INIT + 'mix_return': {INIT + 'mix_prefix', INIT + 'return_tail'},
        INIT + 'return_tail': {INIT + 'copy_lane', INIT + 'return_snapshot'},
        INIT + 'run_framed': {INIT + 'body_verified', 'Compiler.ZigAir.Memory.StackFrame.cleaned'},
        'Compiler.ZigAir.WyhashCallerInit.prefix_verified': {INIT + 'run_framed'},
    }
    for name, dependencies in required.items():
        if not dependencies <= set(indexed[name]['dependencies']):
            raise ValueError('captured initializer dependency missing: ' + name)
    if set(STATEMENTS) != set(STATEMENT_NAMES):
        raise ValueError('incomplete initializer statement pins')
    for name, expected in STATEMENTS.items():
        if encoded_digest(indexed[name]['statement']) != expected:
            raise ValueError('changed captured initializer statement: ' + name)
    for name in CLAIMS:
        if 'Tests.' not in name and any('Tests.' in dep for dep in indexed[name]['dependencies']):
            raise ValueError('initializer core depends on fixtures: ' + name)
    return {'checkedInitializerDependencies': sorted(required), 'checkedInitializerStatements': list(STATEMENTS),
            'scope': 'Complete ReleaseFast initializer AIR execution; caller materialization, update/final AIR and source/backend correspondence remain open.'}


def capture(output, toolchain, lib):
    """Fresh source-bound AIR capture and deterministic regeneration, not proof acceptance."""
    if toolchain is None:
        raise ValueError('hash acceptance requires --air-toolchain for fresh initializer capture')
    output = Path(output) / 'wyhash-initializer-air'
    toolchain = Path(toolchain)
    toolchain_sha = digest(toolchain)
    std_sha = digest(Path(lib) / 'std/hash/wyhash.zig')
    fixture = ROOT / 'test/lean/wyhash_air.zig'
    fixture_sha = digest(fixture)
    capture_air(argparse.Namespace(source=fixture, source_file=[], toolchain=toolchain,
        output=output, mode='ReleaseFast', root=['wyhash_air.' + name for name in ENTRIES]))
    checked = inspect_capture(output / 'report.json', std_sha)
    report = read_json(output / 'report.json')
    name = checked['entries']['init']['name']
    record_path = captured_path(output / 'report.json', report['functions'][name])
    generated, visited = render(read_json(record_path))
    committed = ROOT / 'lean/Compiler/ZigAir/GeneratedWyhashInit.lean'
    if generated.encode() != committed.read_bytes():
        raise ValueError('captured initializer differs from the committed generated program')
    if visited != checked['entries']['init']['body']['visitedInstructionCount']:
        raise ValueError('initializer instruction coverage changed')
    if digest(toolchain) != toolchain_sha or digest(fixture) != fixture_sha or digest(Path(lib) / 'std/hash/wyhash.zig') != std_sha:
        raise ValueError('initializer capture inputs changed')
    result = {'status': 'bound', 'mode': 'ReleaseFast', 'visitedInstructions': visited,
        'captureReportSha256': digest(output / 'report.json'), 'airSha256': digest(record_path),
        'generatedSha256': digest(committed), 'stdlibSourceSha256': std_sha,
        'fixtureSha256': fixture_sha, 'toolchainReportSha256': toolchain_sha,
        'objects': checked['objects'], 'sourceAdapterFormallyVerified': False,
        'nativeHashProducerVerified': False}
    result['updateExecution'] = update_air.bind_capture(output / 'report.json', lib)
    caller_output = output.parent / 'expression-hash-caller-air'
    caller = check_production_caller(argparse.Namespace(toolchain=toolchain, output=caller_output,
                                                       modes=('ReleaseFast',)))
    result['productionCaller'] = {'reportSha256': digest(caller_output / 'report.json'),
        'callerOrder': caller['modes']['ReleaseFast']['callerOrder'],
        'initializer': caller['modes']['ReleaseFast']['initializer'],
        'initializationFragment': caller['modes']['ReleaseFast']['initializationFragment'], 'callerExecutionVerified': False}
    write_json(output / 'initializer-binding.json', result)
    return result


def controls(output, env, lean):
    generated = without_imports((ROOT / 'lean/Compiler/ZigAir/GeneratedWyhashInit.lean').read_text())
    # No import of the actual initializer module: mutations must execute here.
    prefix = 'import Compiler.ZigAir.AggregateAir\nimport Compiler.Extraction.WyhashUpdate\n'
    fixture = without_imports((ROOT / 'lean/Compiler/ZigAir/WyhashInitTests.lean').read_text())
    records = [mutation_check(output, 'wyhash-init-unchanged', prefix + generated + fixture, True, env, lean)]
    # Retain the complete seed-zero result/state comparison. The positive root
    # additionally keeps seed-max and all three allocation-failure fixtures.
    rejected = 'deriving instance DecidableEq for Except\n' + kernel_rejection('''
Compiler.ZigAir.GeneratedWyhashInit.fn_init.run [.value (Compiler.Extraction.WyhashLocal.word 0)] {} =
  (.ok (.aggregate Compiler.ZigAir.GeneratedWyhashInit.fn_init.returnType
    (Compiler.Extraction.WyhashUpdate.initialCells (Compiler.Extraction.WyhashUpdate.seedState 0))),
    (⟨[], 3, 128⟩ : Compiler.ZigAir.Memory.State))''')
    edits = (
        ('wrong-mix-product', '(.arithmetic .mul .wrapping', '(.arithmetic .add .wrapping'),
        ('wrong-seed-xor', '(.bitXor (.local 0)', '(.bitAnd (.local 0)'),
        ('wrong-high-word', '(.shiftRight (.local 19) (.constant (.int false 7 (64))))',
                            '(.shiftRight (.local 19) (.constant (.int false 7 (63))))'),
        ('missing-third-lane', '(.store (.local 39) (.local 42))', '(.store (.local 35) (.local 42))'),
    )
    for name, before, after in edits:
        if before not in generated:
            raise ValueError('missing initializer mutation site: ' + name)
        records.append(mutation_check(output, 'wyhash-init-' + name,
            prefix + generated.replace(before, after) + rejected, False, env, lean))
    model = without_imports((ROOT / 'lean/Compiler/ZigAir/AggregateAir.lean').read_text())
    boundary = without_imports((ROOT / 'lean/Compiler/ZigAir/AggregateAirTests.lean').read_text())
    imports = ('import Compiler.ZigAir.MemoryAir\nimport Compiler.ZigAir.MemoryRecordFields\n'
               'import Compiler.ZigAir.MemoryScalarBytes\nimport Compiler.ZigAir.MemoryByteRange\n')
    records.append(mutation_check(output, 'aggregate-air-unchanged', imports + model + boundary, True, env, lean))
    edits = (
        ('keep-old-initialization', '{ cell with cells }', '{ cell with cells := cell.cells ++ cells }'),
        ('drop-nominal-identity', 'address.offset ≠ 0 ∨ cell.type ≠ child', 'address.offset ≠ 0'),
        ('drop-array-bound', 'if index ≥ length then .error .sourceBounds else', ''),
        ('forge-array-parent', 'if !acceptsView cell.type address.offset owner then .error .unsupported else', ''),
    )
    for name, before, after in edits:
        if model.count(before) != (2 if name == 'drop-nominal-identity' else 1):
            raise ValueError('ambiguous aggregate mutation site: ' + name)
        records.append(mutation_check(output, 'aggregate-air-' + name,
            imports + model.replace(before, after) + boundary, False, env, lean))
    return checked_controls(output, records)
