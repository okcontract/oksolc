#!/usr/bin/env python3
"""Replay the scoped nonempty recursive constructor composition and its controls.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import json
from pathlib import Path

import check_word_swap as harness
import check_compiler
import check_insertion_execution
import check_graph_init as graph
import constructor_item_checks as constructor
import constructor_argument_checks as arguments
import recursive_child_checks as recursive
import recursive_nonempty_checks as nonempty
import algebraic_input_checks as algebraic
import pair_input_checks as pairs
import literal_input_checks as literals
import view_input_checks as views
import recursive_borrowed_checks as borrowed
import native_recursion_checks as native_recursion
import native_step_checks as native_step
import native_parent_return_checks as native_parent_return
import native_parent_release_checks as native_parent_release
import native_parent_publication_checks as native_parent_publication
import native_parent_entry_checks as native_parent_entry
import native_parent_leaf_checks as native_parent_leaf
import native_parent_insertion_checks as native_parent_insertion
import native_cache_checks as native_cache
import native_entry_checks as native_entry
import native_lookup_checks as native_lookup
import native_take_checks as native_take
import native_spare_checks as native_spare
import native_growth_checks as native_growth
import native_first_checks as native_first
import native_backing_failure_checks as native_backing
import native_publication_rollback_checks as native_rollback
import native_insertion_model_checks as insertion_model
import native_preparation_completion_checks as preparation_completion
import reachable_prefix_checks as reachable_prefix
import native_graph_checks as native_graph
import native_local_checks as native_local
import native_constant_checks as native_constant
import constant_word_checks as constant_word
import constant_fold_checks as constant_fold
import constant_fold_growth_checks as constant_fold_growth
import constant_negation_checks as constant_negation
import constructor_composition_checks as composition
import recursive_growth_checks as recursive_growth
import production_normalization_checks as normalization
import assembly_clone_query_checks as containers
import extract_owned_keys
import extract_storage
import extract_assembly_clone
import extract_assembly_item_deinit
import extract_expression_deinit
import extract_representative_remap
from build_toolchain import digest, write_json

MODULE = 'Compiler.Extraction.InternerInsertionNativeTests'
CHECKS = (native_step, native_parent_return, native_parent_release, native_parent_publication, native_parent_entry, native_parent_leaf, native_parent_insertion, native_cache, native_entry, native_lookup, native_take, native_spare, native_growth, native_first, native_backing, native_rollback, insertion_model, preparation_completion, composition, constant_negation, reachable_prefix, recursive_growth, constant_fold_growth, constant_fold, constant_word, native_constant, native_local, native_graph, native_recursion, borrowed, views, literals, pairs, algebraic, nonempty, arguments, recursive, constructor)
ROOTS = list(dict.fromkeys([claim for module in CHECKS for claim in module.CLAIMS] + graph.CLAIMS))


def inputs():
    result = check_insertion_execution.inputs()
    result.update(graph.inputs())
    return result


def profiles(lib):
    result = {'constructors': nonempty.bindings(), 'scalarPairInputs': pairs.bindings(),
              'literalInputs': literals.bindings(),
              'viewInputs': views.bindings(), 'borrowedRecursion': borrowed.bindings(),
              'nativeRecursion': native_recursion.bindings(), 'reachablePrefix': reachable_prefix.bindings(),
              'nativeGraph': native_graph.bindings(),
              'nativeLocal': native_local.bindings(), 'nativeConstant': native_constant.bindings(),
              'constantWord': constant_word.bindings(),
              'constantFold': constant_fold.bindings(),
              'constantFoldGrowth': constant_fold_growth.bindings(),
              'constantNegation': constant_negation.bindings(),
              'recursiveGrowth': recursive_growth.bindings(),
              'algebraicInputs': algebraic.bindings(), 'normalization': normalization.bindings(),
              'graph': graph.admission.check(), 'graphStd': graph.admission.check_std(lib),
              'containers': containers.bindings(lib), 'remap': extract_representative_remap.check(lib)}
    for module in (extract_storage, extract_owned_keys, extract_assembly_clone,
                   extract_assembly_item_deinit, extract_expression_deinit):
        if module.extract(module.SOURCE.read_bytes()) != module.OUTPUT.read_bytes():
            raise ValueError('transitive source profile is stale: ' + module.__name__)
        result[module.__name__] = {'sourceSha256': digest(module.SOURCE), 'programSha256': digest(module.OUTPUT)}
    return result


def std_inputs(lib):
    files = {str(path.relative_to(lib)): digest(path) for path in sorted(lib.rglob('*.zig'))}
    if not files:
        raise ValueError('missing Zig standard-library inputs')
    return files


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {'schema': 'oksolc.recursive-nonempty-acceptance.v1', 'status': 'failed', 'jobs': 4,
              'scope': 'Algebraic.apply, all 53 nonempty RuleList literal segments, named local continuation and nine borrowed callbacks; one recursive constructor family at all sufficient depths through full XOR publication and actual ISZERO(XOR) borrowed EQ branch, nonempty growth OOM, parent return and outer literal cleanup; parameterized native operation/ownership facts from declared-owner initialization, field-derived queries and borrowed inputs, and generic cleanup consumed by that recursive program; graph-word preservation, actual AND named-local cache-hit child and parent return, and explicit shallow exhaustion; one context publishes Push zero and recursively grows ISZERO before parent EQ publication success or probe OOM, retaining child growth/key/words through parent normalized-owner and outer literal cleanup, deriving final native graph/query correspondence; arbitrary-word ISZERO folding through an actual constant child with successful nonempty growth, parent publication success/OOM, exact final cache and native word reads, retired old backing and all enclosing returns',
              'indexedInputScope': 'Actual normalization/take produces the private parent frame; actual child duplication and growth preserve separation from all reached representative operands independently of argument contents, and both parent publication outcomes consume that frame. Original source privacy follows from literal preparation and child native freshness; the reached frame derives general publication admission, existing-key replacement and outer normalized-owner cleanup. The full shared dispatcher retains query equations and derives indexed loads from reached graph prefixes and normalized-root ownership under proper-child simulation; the actual recursive context preserves exact ordinary results/graphs and transports the word theorem. The actual context reads native owner/item/operand fields at source query positions; the shared-body timing theorem derives entry-snapshot equivalence for arbitrary child actions, and reached graph facts derive query correspondence. Proper-child simulation and full constructor reachability remain open.',
              'nativeZigGateRun': False, 'completeCallSiteClosureVerified': False,
              'initialPrefixIsSelectedInsertionContinuations': True, 'recursiveInductionVerified': False,
              'initialPrefixScope': {'AND/named-local, XOR/borrowed, both EQ constant-failure paths, recursive growth, scalar-pair ADD with published zero, arbitrary-word publication/materializer cache hit and first-stage ISZERO folding through constant-child OOM or successful child growth and both parent publication outcomes': 'full constructors from native initialization under the same recursive context',
                                    'legacy fixtures': 'selected insertion continuations'},
              'composedProductionTheoremVerified': False, 'preflightOnly': args.preflight}
    frozen = inputs()
    write_json(output / 'inputs.json', frozen)
    try:
        library = args.zig_lib_dir.resolve()
        std = std_inputs(library)
        write_json(output / 'std-inputs.json', std)
        source_profiles = profiles(library)
        write_json(output / 'source-profiles.json', source_profiles)
        env, _, tools = harness.lean_check.toolchain(args.lean_bin, 4)
        report['tools'] = tools
        report['audit'] = harness.audit(output, env, tools['lean']['path'], MODULE, ROOTS)
        audited = json.loads((output / 'audit.json').read_bytes())
        claims = {claim['theorem']: set(claim['dependencies']) for claim in audited['claims']}
        report['nativeRollbackInterface'] = native_rollback.audit_statements(audited['claims'])
        report['nativeCacheInterface'] = native_cache.audit_statements(audited['claims'])
        report['nativeSpareInterface'] = native_spare.audit_statements(audited['claims'])
        report['nativeGrowthInterface'] = native_growth.audit_statements(audited['claims'])
        report['nativeFirstInterface'] = native_first.audit_statements(audited['claims'])
        report['nativeTakeInterface'] = native_take.audit_statements(audited['claims'])
        report['nativeLookupInterface'] = native_lookup.audit_statements(audited['claims'])
        report['nativeEntryInterface'] = native_entry.audit_statements(audited['claims'])
        report['nativeStepInterface'] = native_step.audit_statements(audited['claims'])
        report['nativeParentReturnInterface'] = native_parent_return.audit_statements(audited['claims'])
        report['nativeParentReleaseInterface'] = native_parent_release.audit_statements(audited['claims'])
        report['nativeParentPublicationInterface'] = native_parent_publication.audit_statements(audited['claims'])
        report['nativeParentInsertionInterface'] = native_parent_insertion.audit_statements(audited['claims'])
        report['nativeParentLeafInterface'] = native_parent_leaf.audit_statements(audited['claims'])
        report['nativeParentEntryInterface'] = native_parent_entry.audit_statements(audited['claims'])
        report['insertionModelInterface'] = insertion_model.audit_statements(audited['claims'])
        report['preparationCompletionInterface'] = preparation_completion.audit_statements(audited['claims'])
        report['dependencies'] = [module.audit(claims) for module in CHECKS]
        graph_output = output / 'graph'
        graph_output.mkdir()
        report['graphAudit'] = graph.audit(graph_output, env, tools['lean']['path'])
        print('Cached export and dependency audit passed; checking mutation controls.', flush=True)
        controls = native_rollback.controls(output, env, tools["lean"]["path"])
        controls += native_parent_return.controls(output, env, tools["lean"]["path"])
        controls += native_parent_release.controls(output, env, tools["lean"]["path"])
        controls += native_parent_publication.controls(output, env, tools["lean"]["path"])
        controls += native_parent_insertion.controls(output, env, tools["lean"]["path"])
        controls += native_parent_leaf.controls(output, env, tools["lean"]["path"])
        controls += native_parent_entry.controls(output, env, tools["lean"]["path"])
        controls += native_step.controls(output, env, tools['lean']['path'])
        controls += native_cache.controls(output, env, tools['lean']['path'])
        controls += native_spare.controls(output, env, tools['lean']['path'])
        controls += native_growth.controls(output, env, tools['lean']['path'])
        controls += native_first.controls(output, env, tools['lean']['path'])
        controls += native_take.controls(output, env, tools['lean']['path'])
        controls += native_lookup.controls(output, env, tools['lean']['path'])
        controls += native_entry.controls(output, env, tools['lean']['path'])
        controls += insertion_model.controls(output, env, tools['lean']['path'])
        controls += preparation_completion.controls(output, env, tools['lean']['path'])
        write_json(output / 'controls.json', controls)
        controls += composition.controls(output, env, tools['lean']['path'])
        write_json(output / 'controls.json', controls)
        controls += constant_negation.controls(output, env, tools['lean']['path'])
        write_json(output / 'controls.json', controls)
        controls += reachable_prefix.controls(output, env, tools['lean']['path'])
        write_json(output / 'controls.json', controls)
        controls += recursive_growth.controls(output, env, tools['lean']['path'])
        write_json(output / 'controls.json', controls)
        controls += constant_word.controls(output, env, tools['lean']['path'])
        write_json(output / 'controls.json', controls)
        controls += constant_fold_growth.controls(output, env, tools['lean']['path'])
        write_json(output / 'controls.json', controls)
        controls += constant_fold.controls(output, env, tools['lean']['path'])
        write_json(output / 'controls.json', controls)
        controls += native_constant.controls(output, env, tools['lean']['path'])
        write_json(output / 'controls.json', controls)
        controls += native_local.controls(output, env, tools['lean']['path'])
        write_json(output / 'controls.json', controls)
        controls += native_graph.controls(output, env, tools['lean']['path'])
        write_json(output / 'controls.json', controls)
        controls += graph.controls(output, env, tools['lean']['path'])
        write_json(output / 'controls.json', controls)
        controls += native_recursion.controls(output, env, tools['lean']['path'])
        write_json(output / 'controls.json', controls)
        controls += borrowed.controls(output, env, tools['lean']['path'])
        write_json(output / 'controls.json', controls)
        controls += nonempty.controls(output, env, tools['lean']['path'])
        write_json(output / 'controls.json', controls)
        controls += views.controls(output, env, tools['lean']['path'])
        write_json(output / 'controls.json', controls)
        controls += literals.controls(output, env, tools['lean']['path'])
        write_json(output / 'controls.json', controls)
        controls += pairs.controls(output, env, tools['lean']['path'])
        write_json(output / 'controls.json', controls)
        controls += algebraic.controls(output, env, tools['lean']['path'])
        write_json(output / 'controls.json', controls)
        # The shared constant-reader file acquired a new proof client.
        # Retain the existing caller/constructor regression controls too.
        controls += recursive.controls(output, env, tools['lean']['path'])
        write_json(output / 'controls.json', controls)
        controls += arguments.controls(output, env, tools['lean']['path'])
        write_json(output / 'controls.json', controls)
        report['controls'] = controls
        print('Focused controls passed.', flush=True)
        if not args.preflight:
            print('Starting fresh kernel replay, including imports.', flush=True)
            proof, artifacts = harness.prove.check_module(MODULE, ROOTS, lean_bin=args.lean_bin,
                                                         jobs=4, fresh=True, timeout=1800)
            for name, data in artifacts.items():
                (output / ('proof-' + name)).write_bytes(data)
            if (proof.get('status') != 'passed' or proof.get('freshKernelReplay') is not True or
                    proof.get('replayIncludesImports') is not True):
                raise ValueError('fresh recursive kernel replay failed: ' + str(proof.get('failure')))
            report['proof'] = {'sha256': digest(output / 'proof-report.json'), 'roots': len(ROOTS),
                               'freshKernelReplay': True, 'replayIncludesImports': True}
        check_compiler.require_stable(frozen, inputs())
        if source_profiles != profiles(library) or std != std_inputs(library):
            raise ValueError('source admission changed during the run')
        report['zigLibrary'] = {'path': str(library), 'inputs': len(std), 'sha256': digest(output / 'std-inputs.json')}
        report['frozenInputs'] = len(frozen)
        report['status'] = 'passed'
    finally:
        write_json(output / 'report.json', report)
    print(json.dumps({'status': report['status'], 'roots': len(ROOTS),
                      'controls': len(report['controls']), 'preflightOnly': args.preflight}))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean-bin', type=Path, required=True)
    parser.add_argument('--zig-lib-dir', type=Path, required=True, help='pinned Zig 0.17.0 library for transitive source admission')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--preflight', action='store_true', help='cached export and strict controls without fresh replay')
    check(parser.parse_args())
