#!/usr/bin/env python3
"""Check the typed operationArguments reader and its initial correspondence.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(ROOT / 'lean'), str(ROOT / 'lean/zig_air')]
import environment as lean_check
import check_compiler
import check_word_swap
import extract_storage
import generate_expression_layout as expression
import generate_item_fields as item
import generate_representative_array_layout as array
import prove
from build_toolchain import VERSION, check_checkout, digest, run, source_identity, text, write_json
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

MODULE = 'Compiler.Extraction.RepresentativeOperationTests'
NS = 'Compiler.Extraction.RepresentativeArray.Operation.'
CLAIMS = [NS + name for name in ('arguments_from_field', 'invalid_id', 'kind_one_iff', 'read_row', 'query')]
CLAIMS += [NS + 'Tests.' + name for name in (
    'initial_valid', 'offset_descriptor', 'readonly_return', 'original_unsorted_contents', 'readonly_cannot_store',
    'original_bound', 'invalid_id_skips_backing', 'empty_header_skips_backing', 'nonoperation_skips_optional_and_arguments',
    'null_operation_fault', 'missing_optional_fault', 'opcode_miss_skips_arguments', 'matching_missing_arguments_fault',
    'zero_is_an_opcode', 'last_opcode', 'empty_descriptor_identity', 'query_does_not_read_operands', 'stale_item_fault',
    'stale_backing_fault', 'invalid_tag_fault', 'id_and_sequence_are_not_read', 'owned_valid', 'owned_row', 'owned_item',
    'all_ids_and_opcodes')]
PROBES = {name: ROOT / 'test/lean' / path for name, path in (
    ('query', 'operation_arguments.zig'), ('expression', 'expression_layout.zig'),
    ('array', 'representative_array_layout.zig'), ('item', 'assembly_item_fields.zig'))}


def inputs():
    saved = check_compiler.snapshot()
    paths = list((ROOT / 'test/lean').rglob('*.py')) + list(PROBES.values())
    paths += [ROOT / 'test/lean/assembly_item_layout.zig', ROOT / 'docs/compiler-verification-map.json',
              ROOT / 'docs/compiler-verification-boundary.md']
    saved.update({str(p.relative_to(ROOT)): digest(p) for p in paths})
    return saved


def expected_cases():
    rows = [(1, opcode, 0, wanted, 2, [99, 1] if wanted == opcode else None)
            for opcode in range(256) for wanted in (opcode, (opcode + 1) % 256)]
    rows += [(kind, None, 0, 12, 2, None) for kind in range(14) if kind != 1]
    rows += [(13, None, id, 12, 2, None) for id in (1, 0xFFFFFFFE, 0xFFFFFFFF)]
    return rows + [(1, 1, 0, 1, 0, [])]


def check_profile(profile, mode):
    if (mode not in ('Debug', 'ReleaseSafe', 'ReleaseFast') or
            not isinstance(profile, dict) or set(profile) != {'schema', 'zigVersion', 'mode', 'backend', 'cases'} or
            profile['schema'] != 'oksolc.operation-arguments-observations.v1' or profile['zigVersion'] != VERSION or
            profile['mode'] != mode or profile['backend'] != 'stage2_llvm' or not isinstance(profile['cases'], list) or
            len(profile['cases']) != 529):
        raise ValueError('unsupported operation query profile')
    base = None
    keys = {'kind', 'instruction', 'id', 'opcode', 'input_pointer', 'input_length', 'output_pointer', 'values'}
    for index, (row, expected) in enumerate(zip(profile['cases'], expected_cases())):
        if not isinstance(row, dict) or set(row) != keys:
            raise ValueError('incomplete query observation')
        for key, value in zip(('kind', 'instruction', 'id', 'opcode', 'input_length', 'values'), expected):
            actual = row[key]
            if type(actual) is not type(value) or actual != value or (isinstance(actual, list) and any(type(x) is not int for x in actual)):
                raise ValueError('native query outcome changed: ' + key)
        pointer = row['input_pointer']
        if type(pointer) is not int or not 0 < pointer < 2**64 - 16 or pointer % 4:
            raise ValueError('invalid input pointer')
        if base is None:
            base = pointer
        if pointer != base + (8 if index == 528 else 0):
            raise ValueError('native offset/empty descriptor identity changed')
        returned = row['output_pointer']
        if (expected[-1] is None and returned is not None) or (expected[-1] is not None and (type(returned) is not int or returned != pointer)):
            raise ValueError('native returned pointer changed')


def audit(output, env, lean):
    result = check_word_swap.audit(output, env, lean, MODULE, CLAIMS)
    claims = {c['theorem']: set(c['dependencies']) for c in json.loads((output / 'audit.json').read_bytes())['claims']}
    required = {
        NS + 'query': {NS + 'read_row', NS + 'invalid_id', 'Compiler.Extraction.RepresentativeArray.representative_from_array',
                       'Compiler.Extraction.Storage.operation_correct'},
        NS + 'read_row': {NS + 'Item', NS + 'arguments_from_field', 'Compiler.Extraction.Expression.readFields_parts',
                          'Compiler.Extraction.AssemblyItem.Fields.kind', 'Compiler.Extraction.AssemblyItem.Fields.instruction'},
        NS + 'Tests.all_ids_and_opcodes': {NS + 'query', NS + 'Tests.owned_row', NS + 'Tests.owned_item'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('query proof lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {**result, 'checkedDependencies': sorted(required), 'initialCorrespondenceRemainsRequired': True}


def controls(output, env, lean):
    directory = ROOT / 'lean/Compiler/Extraction'
    prefix = ('import Compiler.Extraction.RepresentativeDescriptorRelation\nimport Compiler.Extraction.StorageOperations\n'
              'import Compiler.Extraction.ExpressionFieldTests\nimport Compiler.Extraction.AssemblyItemFields\n'
              'import Compiler.ZigAir.MemoryRelease\n')
    model = without_imports((directory / 'RepresentativeOperation.lean').read_text())
    proofs = '\n'.join(without_imports((directory / name).read_text()) for name in
                       ('RepresentativeOperationProofs.lean', 'RepresentativeOperationTests.lean'))
    source = prefix + model + proofs
    records = [mutation_check(output, 'operation-unchanged', source, True, env, lean)]
    for name, before, after in (
        ('mutable-return', '.slice (.slice false Expression.idType) address length', '.slice (.slice true Expression.idType) address length'),
        ('lost-offset', '.slice (.slice false Expression.idType) address length', '.slice (.slice false Expression.idType) ⟨address.allocation, 0⟩ length'),
        ('wrong-length', '.slice (.slice false Expression.idType) address length', '.slice (.slice false Expression.idType) address (length + 1)'),
        ('null-is-miss', 'let some instruction := instruction | return .error .invalidOptional', 'let some instruction := instruction | return .ok none'),
        ('eager-optional', '  let kind ← AssemblyItem.Fields.kind state item', '  let _ ← AssemblyItem.Fields.instruction state item\n  let kind ← AssemblyItem.Fields.kind state item'),
        ('eager-arguments', '  let kind ← AssemblyItem.Fields.kind state item', '  let _ ← arguments state descriptor\n  let kind ← AssemblyItem.Fields.kind state item'),
        ('memory-fault-is-miss', 'let selected ← representative state header id', 'let selected := (representative state header id).toOption.getD (.error .invalidId)'),
        ('wrong-argument-field', 'let .slice type address length ← Expression.readField state false descriptor Expression.argumentsOffset',
         'let .slice type address length ← Expression.readField state false descriptor Expression.idOffset')):
        if model.count(before) != 1:
            raise ValueError('ambiguous operation mutation: ' + name)
        records.append(mutation_check(output, 'operation-' + name, prefix + model.replace(before, after) + proofs, False, env, lean))
    native = extract_storage.SOURCE.read_bytes()
    for name, before, after in (
        ('source-kind', b'expression.item.item_type != .Operation or', b'expression.item.item_type == .Operation or'),
        ('source-opcode', b'expression.item.instruction_value.? != instruction', b'expression.item.instruction_value.? == instruction'),
        ('source-empty-return', b'return expression.arguments;', b'return &.{};')):
        if native.count(before) != 1:
            raise ValueError('ambiguous query source mutation: ' + name)
        changed = native.replace(before, after)
        (output / (name + '.zig')).write_bytes(changed)
        generated = extract_storage.extract(changed).decode()
        body = generated.split('def operationProgram : OperationRead := ', 1)[1].split('\n\n', 1)[0]
        altered = ('namespace Compiler.Extraction.Storage\ndef alteredOperation : OperationRead := ' + body +
                   '\nend Compiler.Extraction.Storage\n')
        records.append(mutation_check(output, 'operation-' + name, prefix + altered +
            model.replace('Storage.operationProgram', 'Storage.alteredOperation') + proofs, False, env, lean))
    for record in records:
        if re.search(r'maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant|failed to synthesize',
                     (output / (record['name'] + '.stdout')).read_text(), re.I):
            raise ValueError('operation control hit a resource or syntax failure: ' + record['name'])
    return records


def native(output, compiler, lib):
    records = []
    for mode in ('Debug', 'ReleaseSafe', 'ReleaseFast'):
        for kind, probe in PROBES.items():
            label = kind + '-' + mode
            binary = output / label
            run(output, 'build-' + label, [compiler, 'build-exe', '-j4', '--zig-lib-dir', lib, '-fllvm', '-O', mode,
                '--dep', 'compiler', '-Mroot=' + str(probe), '-O', mode, '-Mcompiler=' + str(ROOT / 'src/modules.zig'),
                '--cache-dir', ROOT / '.zig-cache', '--global-cache-dir', output / 'global-cache', '-femit-bin=' + str(binary)], cwd=ROOT)
            run(output, 'probe-' + label, [binary], cwd=ROOT)
            path = output / ('probe-' + label + '.stdout')
            record = {'mode': mode, 'kind': kind, 'binarySha256': digest(binary), 'profileSha256': digest(path), 'accepted': False}
            records.append(record)
            write_json(output / 'native.json', records)
            raw = path.read_bytes()
            if len(raw) > 256 * 1024:
                raise ValueError('native query/layout profile exceeds bound')
            profile = json.loads(raw)
            if kind == 'query':
                check_profile(profile, mode)
            else:
                if profile['target']['mode'] != mode:
                    raise ValueError('native layout mode changed')
                if kind == 'expression' and expression.generate(profile) != expression.OUTPUT.read_bytes():
                    raise ValueError('expression layout changed')
                if kind == 'array' and any(data != path.read_bytes() for path, data in array.programs(profile, lib).items()):
                    raise ValueError('representative/owner layout changed')
                if kind == 'item':
                    item.check_profile(profile)
            if (output / ('build-' + label + '.stderr')).read_bytes() or (output / ('probe-' + label + '.stderr')).read_bytes():
                raise ValueError('unreviewed native query/layout diagnostics')
            record['accepted'] = True
            write_json(output / 'native.json', records)
    return records


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {'schema': 'oksolc.operation-arguments-acceptance.v1', 'status': 'failed', 'jobs': 4,
              'proofScope': 'sourceBoundTypedOperationReaderUnderInitialCorrespondence',
              'scope': 'Typed source-bound reader from initial descriptor/item correspondence; native initialization, mutation preservation and complete graph/caller correspondence remain open.'}
    try:
        report['inputs'] = inputs()
        compiler, tree = args.zig.resolve(), args.zig_tree.resolve()
        check_checkout(output, tree, 'zig-source')
        report['compilerSha256'], report['zigLibrary'] = digest(compiler), source_identity(tree / 'lib')
        run(output, 'version', [compiler, 'version'])
        if text(output, 'version') != VERSION or extract_storage.extract(extract_storage.SOURCE.read_bytes()) != extract_storage.OUTPUT.read_bytes():
            raise ValueError('stale compiler or query source binding')
        env, _, tools = lean_check.toolchain(args.lean_bin, 4)
        report['tools'] = tools
        run(output, 'fixtures', [sys.executable, '-m', 'unittest', 'discover', '-s', 'test/lean', '-p', 'test_operation_arguments.py'], cwd=ROOT)
        run(output, 'map', [sys.executable, 'test/lean/check_verification_map.py'], cwd=ROOT)
        run(output, 'preflight', [tools['lake']['path'], 'build', MODULE], cwd=ROOT / 'lean', env=env)
        report['audit'] = audit(output, env, tools['lean']['path'])
        report['controls'] = controls(output, env, tools['lean']['path'])
        report['native'] = native(output, compiler, tree / 'lib')
        proof, artifacts = prove.check_module(MODULE, CLAIMS, lean_bin=args.lean_bin, jobs=4, fresh=True)
        directory = output / 'proof'
        directory.mkdir()
        for name, data in artifacts.items():
            (directory / name).write_bytes(data)
        write_json(directory / 'report.json', proof)
        report['proofReportSha256'] = digest(directory / 'report.json')
        if (proof.get('status') != 'passed' or proof.get('freshKernelReplay') is not True or
                proof.get('replayIncludesImports') is not True or proof.get('auditedDeclarations') != CLAIMS):
            raise ValueError('query fresh replay failed')
        if inputs() != report['inputs'] or digest(compiler) != report['compilerSha256'] or source_identity(tree / 'lib') != report['zigLibrary']:
            raise ValueError('query acceptance inputs changed')
        report.update(status='passed', auditedDeclarations=len(CLAIMS), initialCorrespondenceRequired=True,
                      nativeInitializationVerified=False, completeGraphCorrespondenceVerified=False)
    finally:
        write_json(output / 'report.json', report)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--zig', required=True, type=Path)
    parser.add_argument('--zig-tree', required=True, type=Path)
    parser.add_argument('--lean-bin', type=Path)
    check(parser.parse_args())
