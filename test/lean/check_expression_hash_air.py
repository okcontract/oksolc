#!/usr/bin/env python3
"""Bind the production hash caller to its captured callees and open obligations.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

This binds capture/provenance and regenerates the initializer, byte views and
call schedule consumed by the scoped runner. Whole-caller execution preservation,
key-copy admission and update/final AIR bodies remain explicit obligations.
"""
import argparse
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'lean/zig_air'))
from build_toolchain import digest, write_json
from capture import capture, read_json, source_files
from generate import captured_path
from generate_aggregate import Decoder, render
from generate_hash_initialization import render as render_initialization
from generate_hash_byte_views import caller_key_layout, render as render_byte_views
from generate_hash_slice import render as render_slice_view
from generate_hash_order import caller_order, ref, target, render as render_order
from link_specializations import identity
from check_wyhash_air import inspect_body
import generate_map_bucket_layout as key_layout

SOURCE = ROOT / 'test/lean/expression_hash_air.zig'
PRODUCTION = 'src/libevmasm/expression_classes.zig'
CALLER = 'src.libevmasm.expression_classes.ExpressionKeyContext.hash'
ENTRY = 'expression_hash_air.hash'
WYHASH = 'hash.wyhash.Wyhash.'
MODULES = {'big_int': 'src/libsolutil/big_int.zig'}
SOURCES = [Path(p) for p in (
    'src/libevmasm/algebraic_rules.zig', 'src/libevmasm/assembly_item.zig', PRODUCTION,
    'src/libevmasm/instruction.zig', 'src/libevmasm/rule_list.zig',
    'src/libevmasm/semantic_information.zig', 'src/libevmasm/sub_assembly_id.zig',
    'src/liblangutil/debug_data.zig', 'src/liblangutil/evm_version.zig',
    'src/liblangutil/source_location.zig', 'src/libsolutil/common_data.zig',
    'src/libsolutil/fixed_hash.zig', 'src/libsolutil/keccak256.zig',
    'src/libsolutil/numeric.zig', 'src/libsolutil/big_int.zig')]


def inputs():
    paths = [SOURCE, ROOT / 'lean/Compiler/ZigAir/GeneratedWyhashInit.lean',
             ROOT / 'lean/Compiler/ZigAir/GeneratedExpressionHashInit.lean',
             ROOT / 'lean/Compiler/ZigAir/GeneratedExpressionHashBytes.lean',
             ROOT / 'lean/Compiler/ZigAir/GeneratedExpressionHashSlice.lean',
             ROOT / 'lean/Compiler/Extraction/GeneratedExpressionHashOrder.lean',
             key_layout.KEY_OUTPUT,
             ROOT / 'lean/extract_storage.py', ROOT / 'lean/zig_air/SemanticExport.zig',
             Path(__file__), ROOT / 'test/lean/check_wyhash_air.py']
    paths += [ROOT / path for path in SOURCES]
    paths += sorted((ROOT / 'lean/zig_air').glob('*.py'))
    return {str(path.relative_to(ROOT)): digest(path) for path in paths}


def require(value, message):
    if not value:
        raise ValueError(message)


def inspect_capture(report_path, lib):
    report = read_json(report_path)
    require(report.get('schema') == 'oksolc.fresh-air-capture.v1' and report.get('status') == 'captured' and
            report.get('captureComplete') is True and report['objects']['ordinary'] == report['objects']['captured'],
            'production caller capture did not complete with identical objects')
    files = source_files(SOURCE, SOURCES, MODULES)
    sources = {name: digest(report_path.parent / name) for name in files}
    require(sources == report['sourceFiles'] and report['sourceModules'] == MODULES and
            report['sourceSha256'] == sources[SOURCE.name], 'production source/module binding changed')
    require(all((report_path.parent / name).read_bytes() == data for name, data in files.items()),
            'captured production source differs from current input')
    for name in ('hash/wyhash.zig', 'mem.zig', 'debug.zig'):
        sources[name] = digest(lib / 'std' / name)
    records = {}

    def load(name):
        require(name in report['functions'], 'captured callee body missing')
        if name in records:
            return records[name]
        entry = report['functions'][name]
        path = captured_path(report_path, entry)
        require(digest(path) == entry['sha256'], 'production caller AIR hash mismatch')
        record = read_json(path)
        require(record['name'] == name, 'production caller AIR name mismatch')
        identity({k: record[k] for k in ('name', 'sourceFile', 'sourceSha256')}, sources)
        records[name] = record
        return record

    configuration = load(ENTRY)['configuration']
    load(CALLER)
    require(report['functions'][ENTRY]['requested'] is True, 'production entry was not requested')
    edges = []
    # Keep all raw captures. This inspection selects the actual caller and its
    # direct callees; Debug's transitive panic/runtime library is not admitted.
    for name in (ENTRY, CALLER):
        record = records[name]
        for inst in record['instructions']:
            if inst.get('payloadVisited') is not True or not inst['tag'].startswith('call'):
                continue
            callee = target(inst)
            body = load(callee)
            require(inst['callee']['identity'] == {k: body[k] for k in ('name', 'sourceFile', 'sourceSha256')},
                    'callee source identity differs from captured body')
            edges.append({'caller': name, 'instruction': inst['index'], 'callee': callee})
    require(all(record['configuration'] == configuration for record in records.values()),
            'callee configuration differs from caller')
    require([e['callee'] for e in edges if e['caller'] == ENTRY] == [CALLER] and
            records[CALLER]['sourceFile'] == PRODUCTION, 'entry does not invoke the production hash')
    order = caller_order(records[CALLER], configuration['optimize'])
    key_binding = caller_key_layout(records[CALLER], sources,
        (report_path.parent / 'src/libevmasm/assembly_item.zig').read_bytes())
    inspected = {name: inspect_body(records[name]) for name in [CALLER, WYHASH + 'init', WYHASH + 'update', WYHASH + 'final']}
    initializer = {'regenerated': False, 'reason': 'semantic decoder admits ReleaseFast only'}
    initialization = {'regenerated': False, 'reason': 'semantic decoder admits ReleaseFast only'}
    byte_views = {'regenerated': False, 'reason': 'semantic decoder admits ReleaseFast only'}
    slice_view = {'regenerated': False, 'reason': 'semantic decoder admits ReleaseFast only'}
    call_order = {'regenerated': False, 'reason': 'semantic decoder admits ReleaseFast only'}
    if configuration['optimize'] == 'ReleaseFast':
        text, count = render(records[WYHASH + 'init'])
        generated = ROOT / 'lean/Compiler/ZigAir/GeneratedWyhashInit.lean'
        require(text.encode() == generated.read_bytes(), 'production callee differs from checked initializer program')
        initializer = {'regenerated': True, 'visitedInstructions': count, 'generatedSha256': digest(generated)}
        text, scope = render_initialization(records[CALLER], records[WYHASH + 'init'])
        fragment = ROOT / 'lean/Compiler/ZigAir/GeneratedExpressionHashInit.lean'
        require(text.encode() == fragment.read_bytes(), 'production caller differs from checked initialization fragment')
        initialization = {**scope, 'regenerated': True, 'generatedSha256': digest(fragment)}
        text, scope = render_byte_views(records[CALLER], records, sources,
            (report_path.parent / 'src/libevmasm/assembly_item.zig').read_bytes())
        fragment = ROOT / 'lean/Compiler/ZigAir/GeneratedExpressionHashBytes.lean'
        require(text.encode() == fragment.read_bytes(), 'production scalar views differ from checked programs')
        byte_views = {**scope, 'regenerated': True, 'generatedSha256': digest(fragment)}
        text, scope = render_slice_view(records[CALLER], records, sources)
        fragment = ROOT / 'lean/Compiler/ZigAir/GeneratedExpressionHashSlice.lean'
        require(text.encode() == fragment.read_bytes(), 'production argument slice differs from checked program')
        slice_view = {**scope, 'regenerated': True, 'generatedSha256': digest(fragment)}
        text, scope = render_order(records[CALLER], records, sources)
        fragment = ROOT / 'lean/Compiler/Extraction/GeneratedExpressionHashOrder.lean'
        require(text.encode() == fragment.read_bytes(), 'production call order differs from checked runner')
        call_order = {**scope, 'regenerated': True, 'generatedSha256': digest(fragment)}
        try:
            Decoder(records[CALLER]).program(records[CALLER])
            admission = {'status': 'decoded', 'preservationVerified': False}
        except ValueError as error:
            admission = {'status': 'rejected', 'reason': str(error)}
    else:
        admission = {'status': 'rejected', 'reason': 'semantic decoder admits ReleaseFast only'}
    return {'captureReportSha256': digest(report_path), 'objects': report['objects'],
            'sourceFiles': report['sourceFiles'], 'sourceModules': MODULES, 'callEdges': edges,
            'inspectionScope': 'production caller, entry wrapper and direct callees only',
            'inspectedFunctions': sorted(records), 'capturedFunctionCount': len(report['functions']),
            'omittedFunctionCount': len(report['functions']) - len(records), 'callClosureVerified': False,
            'callerOrder': order, 'keyLayoutBinding': key_binding, 'aggregateDecoder': admission, 'inspection': inspected,
            'initializer': initializer, 'initializationFragment': initialization, 'scalarByteViews': byte_views,
            'argumentSliceView': slice_view, 'callOrderExecution': call_order,
            'callArgumentSemanticsVerified': False,
            'specializationSemanticsVerified': False}


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    result = {'schema': 'oksolc.expression-hash-air.v1', 'status': 'failed', 'modes': {},
              'nativeHashProducerVerified': False, 'callerExecutionVerified': False,
              'sourceAdapterFormallyVerified': False, 'wholeCompilerVerified': False}
    try:
        require('ReleaseFast' in args.modes and len(set(args.modes)) == len(args.modes) and
                set(args.modes) <= {'Debug', 'ReleaseSafe', 'ReleaseFast'}, 'incomplete or duplicate capture modes')
        result['inputs'] = inputs()
        toolchain = read_json(args.toolchain)
        lib = Path(toolchain['compiler']['zigLibDir'])
        result['toolchainReportSha256'] = digest(args.toolchain)
        exporter = [item for item in toolchain['freshAirCapturePatch'] if item['file'] == 'src/SemanticExport.zig']
        require(len(exporter) == 1 and exporter[0]['afterSha256'] == digest(ROOT / 'lean/zig_air/SemanticExport.zig'),
                'capturing toolchain exporter differs from reviewed source')
        for mode in args.modes:
            capture(argparse.Namespace(source=SOURCE, source_file=SOURCES,
                module=[name + '=' + path for name, path in MODULES.items()], root=[ENTRY],
                mode=mode, toolchain=args.toolchain, output=output / mode))
            result['modes'][mode] = inspect_capture(output / mode / 'report.json', lib)
        require(digest(args.toolchain) == result['toolchainReportSha256'] and inputs() == result['inputs'],
                'capture toolchain or source inputs changed')
        result['status'] = 'inspected'
    except Exception as error:
        result['error'] = str(error)
        raise
    finally:
        write_json(output / 'report.json', result)
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--toolchain', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    args.modes = ('Debug', 'ReleaseSafe', 'ReleaseFast')
    check(args)
