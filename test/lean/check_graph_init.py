#!/usr/bin/env python3
"""Check source-bound empty graph initialization with unchanged host contracts.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "lean"))
sys.path.insert(0, str(ROOT / "lean/zig_air"))
import environment as lean_check
import check_compiler
import check_word_swap
import check_representative_array as array
import extract_graph_init as admission
import prove
from build_toolchain import digest, run, source_identity, text, write_json
from check_zig_air_memory_proofs import without_imports, OPTIONAL_POINTER_CLAIMS
from check_zig_air_proofs import mutation_check

PROBE = ROOT / "test/lean/graph_init.zig"
MODULE = "Compiler.Extraction.InternerGraphInitOwnershipTests"
NS = "Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.GraphInit."
CLAIMS = [NS + name for name in ("empty_invariant", "initialize_verified", "initial_queries")]
CLAIMS += [NS + "Tests." + name for name in ("source_initializer", "source_queries",
    "existing_storage_is_unchanged", "graph_starts_empty", "root_valid", "root_initialized")]
CLAIMS += ["Compiler.Extraction.Memory.Arguments.Normalization." + name for name in
    ("related_allocation_frame", "Injected.stack_unregistered", "Valid.private_memory_frame")]
CLAIMS += ["Compiler.Extraction.RepresentativeArray.readHeader_items"]
CLAIMS += [NS + "OwnerMemory." + name for name in ("initialize_verified", "empty_representative")]
CLAIMS += [NS + "OwnerMemory.Tests." + name for name in ("initial_valid", "stack_owner_is_unregistered",
    "actual_header_stores", "actual_source_initializer", "source_initializer", "initialized_validity_and_header",
    "all_native_ids_reject_without_sentinel", "parent_offset_borrow_survives", "registry_effects_and_lifetime_history_retained",
    "readonly_owner_rejects", "stale_owner_rejects", "nominal_owner_does_not_initialize", "registered_stack_owner_is_invalid",
    "actual_count_store", "cache_queries_correspond", "header_count_uninitialized", "header_without_count_rejects",
    "nonempty_count_readback", "nonempty_count_is_unsupported",
    "map_selection_needs_complete_owner", "empty_lookup_leaves_opaque_fields_uninitialized")]
CLAIMS += ["Compiler.Extraction.ExpressionMap." + name for name in
    ("owner_cache_view", "root_size_pointer", "empty_get", "initialize_verified", "header_frame")]
CLAIMS += ["Compiler.Extraction.ExpressionMap.Initialization." + name for name in
    ("root_pointer", "slot_views", "store_total", "read_after_store", "read_frame", "size_write", "size_read",
     "write_verified", "run_of_writes", "initialize_verified", "Initialized.observed",
     "rejects_metadata", "rejects_size", "rejects_available", "rejects_lock", "missing_lock")]
CLAIMS += [NS + "OwnerMemory.Tests." + name for name in ("write_fixture", "actual_map_stores", "actual_lock_store")]
CLAIMS += ["Compiler.Extraction.RepresentativeArray.Owner.NativeLock." + name for name in
    ("root_pointer", "checkHeader_owner", "checkHeader_of_cell", "pointer_eq_of_lookup",
     "checkHeader_eq_of_lookup", "initialize_verified")]
CLAIMS += [NS + "Ownership.initialize_verified"]
CLAIMS += [NS + "Ownership.Tests." + name for name in ("native_empty", "source_initializer", "initial_ownership_from_execution",
    "allocator_effects_registry_and_parent_retained", "count_only_rejects", "nonnull_metadata_rejects",
    "inconsistent_size_or_available_rejects", "locked_or_missing_lock_rejects", "sample_reads", "captured_default_values", "no_owner_allocator_or_sentinel_is_manufactured")]
CLAIMS += OPTIONAL_POINTER_CLAIMS
TRACES = [{"alloc": 3, "resize": 7, "remap": 11, "free": 13},
          {"alloc": 17, "resize": 19, "remap": 23, "free": 29}]


def inputs():
    saved = check_compiler.snapshot()
    saved.update({str(path.relative_to(ROOT)): digest(path) for path in (ROOT / "test/lean").rglob("*.py")})
    saved.update({str(path.relative_to(ROOT)): digest(path) for path in (PROBE, *array.PROBES.values())})
    saved.update({name: digest(ROOT / name) for name in
        ("docs/compiler-verification-map.json", "docs/compiler-verification-boundary.md")})
    return saved


def expected_queries():
    return [{"id": id, "opcode": opcode, "invalid_representative": True,
             "constant_missing": True, "operation_missing": True, "cache_missing": True}
            for id in (0, 1, 0xFFFFFFFE, 0xFFFFFFFF) for opcode in range(256)]


def check_profile(profile, mode):
    if (not isinstance(profile, dict) or set(profile) != {"schema", "zigVersion", "mode", "backend", "cases"} or
            profile["schema"] != "oksolc.graph-init-observations.v4" or profile["zigVersion"] != "0.17.0" or
            profile["mode"] != mode or profile["backend"] != "stage2_llvm" or
            not isinstance(profile["cases"], list) or len(profile["cases"]) != 2):
        raise ValueError("unsupported native graph initialization profile")
    pointers = []
    for case, trace in zip(profile["cases"], TRACES):
        if not isinstance(case, dict) or set(case) != {"input", "actual", "before", "after", "size", "cache_capacity", "key_iterator_empty", "queries"}:
            raise ValueError("incomplete graph initialization observation")
        supplied = case["input"]
        if (not isinstance(supplied, dict) or set(supplied) != {"allocator_pointer", "allocator_vtable", "representative_length",
                "representative_capacity", "map_metadata_null", "map_size", "map_available", "map_lock_empty", "representative_lock_empty"} or
                any(type(supplied[name]) is not int or not 0 < supplied[name] < 2**64
                    for name in ("allocator_pointer", "allocator_vtable"))):
            raise ValueError("invalid input allocator identity")
        expected = {"allocator_pointer": supplied["allocator_pointer"], "allocator_vtable": supplied["allocator_vtable"],
            "representative_length": 0, "representative_capacity": 0, "map_metadata_null": True,
            "map_size": 0, "map_available": 0, "map_lock_empty": True, "representative_lock_empty": True}
        for label, wanted in (("input", expected), ("actual", expected), ("before", trace), ("after", trace)):
            actual = case[label]
            if (not isinstance(actual, dict) or set(actual) != set(wanted) or
                    any(type(actual[name]) is not type(value) for name, value in wanted.items())):
                raise ValueError("malformed graph initialization field: " + label)
        queries = case["queries"]
        if (not isinstance(queries, list) or any(not isinstance(q, dict) or
                set(q) != {"id", "opcode", "invalid_representative", "constant_missing", "operation_missing", "cache_missing"} or
                any(type(q[name]) is not int for name in ("id", "opcode")) or
                any(type(q[name]) is not bool for name in ("invalid_representative", "constant_missing", "operation_missing", "cache_missing"))
                for q in queries)):
            raise ValueError("malformed initial query observation")
        if (supplied != expected or case["actual"] != expected or case["before"] != trace or
                case["after"] != trace or type(case["size"]) is not int or case["size"] != 0 or
                type(case["cache_capacity"]) is not int or case["cache_capacity"] != 0 or
                case["key_iterator_empty"] is not True or case["queries"] != expected_queries()):
            raise ValueError("graph initialization fields, effects or queries changed")
        pointers.append(supplied["allocator_pointer"])
    if pointers[0] == pointers[1]:
        raise ValueError("native allocator contexts were not independent")


def audit(output, env, lean):
    checked = check_word_swap.audit(output, env, lean, MODULE, CLAIMS)
    records = json.loads((output / "audit.json").read_bytes())["claims"]
    dependencies = {record["theorem"]: set(record["dependencies"]) for record in records}
    requirements = {
        NS + "Tests.source_initializer": {NS + "zigInit", NS + "initialize_verified", NS + "empty_invariant",
            "Compiler.Extraction.Memory.GraphResident", "Compiler.Extraction.Interner.Invariant"},
        NS + "Tests.source_queries": {NS + "zigInit", NS + "initial_queries",
            "Compiler.Extraction.Storage.representativeProgram", "Compiler.Extraction.Storage.constantProgram",
            "Compiler.Extraction.Storage.operationProgram", "Compiler.Extraction.Storage.Lookup.run",
            "Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.BorrowedQuery.observe"},
        NS + "Tests.root_initialized": {NS + "Tests.root_valid", NS + "Tests.source_initializer"},
        NS + "OwnerMemory.initialize_verified": {
            "Compiler.Extraction.RepresentativeArray.Owner.initializeHeader_verified",
            "Compiler.Extraction.RepresentativeArray.Owner.NativeLock.initialize_verified",
            "Compiler.Extraction.ExpressionMap.Initialization.initialize_verified", "Compiler.Extraction.ExpressionMap.Initialization.Initialized.observed",
            "Compiler.Extraction.ExpressionMap.empty_get",
            "Compiler.Extraction.Memory.Arguments.Normalization.Injected.stack_unregistered",
            "Compiler.Extraction.Memory.Arguments.Normalization.Valid.private_memory_frame",
            NS + "initialize_verified"},
        NS + "Ownership.initialize_verified": {NS + "OwnerMemory.initialize_verified", NS + "Ownership.keys",
            "Compiler.Extraction.OwnedKeys.Live", "Compiler.Extraction.OwnedKeys.Unique", "Compiler.Extraction.OwnedKeys.view",
            "Compiler.Extraction.ExpressionMap.Initialization.observeEmpty"},
        NS + "Ownership.Tests.initial_ownership_from_execution": {NS + "Ownership.initialize_verified",
            NS + "Ownership.Tests.source_initializer", NS + "zigInitOwned", NS + "OwnerMemory.Tests.initial_valid"},
        "Compiler.Extraction.ExpressionMap.Initialization.initialize_verified": {
            "Compiler.Extraction.ExpressionMap.Initialization.write_verified", "Compiler.Extraction.ExpressionMap.initializeSize",
            "Compiler.ZigAir.Memory.store_subobject_total", "Compiler.ZigAir.Memory.load_disjoint_after_store"},
        NS + "OwnerMemory.empty_representative": {
            "Compiler.Extraction.RepresentativeArray.readHeader_items",
            "Compiler.Extraction.RepresentativeArray.invalid_from_loaded_header"},
        NS + "OwnerMemory.Tests.source_initializer": {NS + "zigInitInOwner", NS + "OwnerMemory.initialize_verified",
            NS + "OwnerMemory.Tests.initial_valid"},
        NS + "OwnerMemory.Tests.parent_offset_borrow_survives": {NS + "OwnerMemory.Tests.source_initializer",
            NS + "OwnerMemory.Tests.actual_source_initializer", "Compiler.Extraction.Memory.Arguments.Normalization.represented_frame"},
        NS + "OwnerMemory.Tests.all_native_ids_reject_without_sentinel": {
            NS + "OwnerMemory.empty_representative", NS + "OwnerMemory.Tests.initialized_validity_and_header"},
        NS + "OwnerMemory.Tests.cache_queries_correspond": {NS + "OwnerMemory.Tests.source_initializer",
            NS + "OwnerMemory.Tests.actual_source_initializer", NS + "zigEmptyCacheGet"},
        "Compiler.Extraction.ExpressionMap.initialize_verified": {"Compiler.Extraction.ExpressionMap.root_size_pointer",
            "Compiler.ZigAir.Memory.store_subobject_total", "Compiler.ZigAir.Memory.load_alias_after_store"},
    }
    for claim, required in requirements.items():
        if not required <= dependencies[claim]:
            raise ValueError("graph initialization proof lost dependencies: " + claim)
    return {**checked, "checkedDependencies": sorted(requirements)}


def controls(output, env, lean):
    directory = ROOT / "lean/Compiler/Extraction"
    model = without_imports((directory / "InternerGraphInit.lean").read_text())
    owner = without_imports((directory / "InternerGraphInitMemory.lean").read_text())
    cache = without_imports((directory / "ExpressionMapEmpty.lean").read_text())
    map_init = without_imports((directory / "ExpressionMapInitialization.lean").read_text())
    owner_lock = without_imports((directory / "RepresentativeOwnerLock.lean").read_text())
    ownership = without_imports((directory / "InternerGraphInitOwnership.lean").read_text())
    ownership_tests = without_imports((directory / "InternerGraphInitOwnershipTests.lean").read_text())
    program = without_imports(admission.OUTPUT.read_text())
    tests = without_imports((directory / "InternerGraphInitTests.lean").read_text())
    owner_tests = without_imports((directory / "InternerGraphInitMemoryTests.lean").read_text())
    imported = ("import Compiler.Extraction.InternerBorrowedQuery\nimport Compiler.Extraction.InternerConstructorFrameTests\n"
        "import Compiler.Extraction.RepresentativeOwnerWrites\nimport Compiler.Extraction.InternerPublication\n"
        "import Compiler.Extraction.RepresentativeArrayAppend\n"
        "import Compiler.ZigAir.MemoryOptionalPointerTests\n"
        # Wrong initialized values expand large concrete memory terms in the
        # rejection diagnostic; retain a readable semantic failure.
        "set_option maxRecDepth 4096\n")
    source = imported + cache + map_init + owner_lock + model + owner + ownership + program + tests + owner_tests + ownership_tests
    mutations = (
        ("wrong-allocator", ":= run allocator before", ":= run (allocator + 1) before"),
        ("missing-representatives", "representatives := some []", "representatives := none"),
        ("manufactured-value", "read := Storage.readValue []", "read := fun _ => some 0"),
        ("seeded-cache", "table := fun _ => none", "table := fun _ => some 0"),
        ("lost-registry", "(allocator, ⟨emptyGraph, before⟩)", "(allocator, ⟨emptyGraph, { before with heap := fun _ => none }⟩)"),
        ("rewound-lifetime", "(allocator, ⟨emptyGraph, before⟩)", "(allocator, ⟨emptyGraph, { before with memory := { before.memory with nextId := 0 } }⟩)"),
        ("rewound-address", "(allocator, ⟨emptyGraph, before⟩)", "(allocator, ⟨emptyGraph, { before with memory := { before.memory with nextAddress := 8 } }⟩)"),
        ("owner-wrong-allocator", ".ok (GraphInit.run allocator { before with memory })",
         ".ok (GraphInit.run (allocator + 1) { before with memory })"),
        ("owner-nonempty-header", "initializeHeader runtimeSafety before.memory owner sentinel 0 0",
         "initializeHeader runtimeSafety before.memory owner sentinel 1 0"),
        ("owner-nonzero-capacity", "initializeHeader runtimeSafety before.memory owner sentinel 0 0",
         "initializeHeader runtimeSafety before.memory owner sentinel 0 1"),
        ("owner-lost-registry", ".ok (GraphInit.run allocator { before with memory })",
         ".ok (GraphInit.run allocator { before with memory, heap := fun _ => none })"),
        ("owner-discarded-header", ".ok (GraphInit.run allocator { before with memory })",
         "let _ := memory\n  .ok (GraphInit.run allocator before)"),
        ("owner-rewound-lifetime", ".ok (GraphInit.run allocator { before with memory })",
         ".ok (GraphInit.run allocator { before with memory := { memory with nextId := 0 } })"),
        ("owner-wrong-lifetime", "initializeHeader runtimeSafety before.memory owner sentinel 0 0",
         "initializeHeader runtimeSafety before.memory { owner with allocation := 0 } sentinel 0 0"),
        ("owner-wrong-mode", "initializeHeader runtimeSafety before.memory owner sentinel 0 0",
         "initializeHeader (!runtimeSafety) before.memory owner sentinel 0 0"),
        ("omitted-native-count", "let counted ← initializeSize runtimeSafety metadata owner",
         "let counted := metadata"),
        ("nonzero-native-count", "store state pointer (.scalar (.int false 32 0))",
         "store state pointer (.scalar (.int false 32 1))"),
        ("wrong-native-count-field", "cacheFieldPointer runtimeSafety state owner writable (sizeOffset runtimeSafety)", "cacheFieldPointer runtimeSafety state owner writable (availableOffset runtimeSafety)"),
        ("omitted-map-defaults", "let mapped ← Compiler.Extraction.ExpressionMap.Initialization.run runtimeSafety header owner",
         "let mapped ← Compiler.Extraction.ExpressionMap.initializeSize runtimeSafety header owner"),
        ("representative-lock-nonzero-default", "  store state selected (.scalar (.int false 64 0))",
         "  store state selected (.scalar (.int false 64 1))"),
        ("omitted-representative-lock", "let memory ← Compiler.Extraction.RepresentativeArray.Owner.NativeLock.initializeLock runtimeSafety mapped owner",
         "let memory := mapped"),
        ("representative-lock-wrong-mode", "let memory ← Compiler.Extraction.RepresentativeArray.Owner.NativeLock.initializeLock runtimeSafety mapped owner",
         "let memory ← Compiler.Extraction.RepresentativeArray.Owner.NativeLock.initializeLock false mapped owner"),
        ("omitted-null-metadata", "let metadata ← write runtimeSafety state owner .metadata", "let metadata := state"),
        ("omitted-availability", "let available ← write runtimeSafety counted owner .available", "let available := counted"),
        ("omitted-safety-lock", "\n  if runtimeSafety then write runtimeSafety available owner .lock else .ok available\n", "\n  .ok available\n"),
        ("locked-default", "| .lock => .scalar (.int false 64 0)\n\ndef Slot.region", "| .lock => .scalar (.int false 64 1)\n\ndef Slot.region"),
        ("ignored-metadata", "if metadata ≠ Slot.metadata.value then .error .unsupported else do", "let _ := metadata; do"),
        ("ignored-availability", "if available ≠ Slot.available.value then .error .unsupported else do", "let _ := available; do"),
        ("ignored-lock", "if lock ≠ Slot.lock.value then .error .unsupported else .ok ()", "let _ := lock; .ok ()"),
        ("fabricated-initial-ownership", "observeEmpty runtimeSafety memory owner\n  .ok (fun _ => none)",
         "observeEmpty runtimeSafety memory owner\n  .ok (fun _ => some ⟨88, 0⟩)"),
        ("invented-empty-hit", "then .ok none else .error .unsupported", "then .ok (some 0) else .error .unsupported"),
        ("uninitialized-count-ignored", "let size ← readSize runtimeSafety state owner", "let size := Value.scalar (.int false 32 0)"),
        ("nonempty-probing-accepted", "then .ok none else .error .unsupported", "then .ok none else .ok none"),
    )
    # Validate the entire inventory before spending time compiling any control.
    for name, before, _ in mutations:
        if source.count(before) != 1:
            raise ValueError("ambiguous graph initialization mutation: " + name)
    records = [mutation_check(output, "graph-init-unchanged", source, True, env, lean)]
    for name, before, after in mutations:
        records.append(mutation_check(output, "graph-init-" + name, source.replace(before, after), False, env, lean))
    for record in records:
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant",
                     (output / (record["name"] + ".stdout")).read_text(), re.I):
            raise ValueError("graph initializer control hit a resource or syntax failure: " + record["name"])
    return records


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.graph-init-verification.v1", "status": "failed", "jobs": 4,
        "scope": "ExpressionClasses.init complete container-default stores, empty native key projection and initial publication ownership in declared writable stack owner storage",
        "emptyInitializationVerified": False, "typedEmptyOwnerHeaderVerified": False, "nativeEmptyCacheQueriesVerified": False, "initialEmptyKeyOwnershipVerified": False,
        "nativeOwnerInitializationVerified": False,
        "nativeGraphMutationCorrespondenceVerified": False,
        "recursiveConstructorsVerified": False, "nativeBackendVerified": False, "wholeCompilerVerified": False}
    try:
        report["inputs"] = inputs()
        report["admission"] = admission.check()
        toolchain = json.loads(args.toolchain.read_bytes())
        compiler = Path(toolchain["compiler"]["path"])
        lib = Path(toolchain["compiler"]["zigLibDir"])
        report["toolchainReportSha256"], report["compilerSha256"] = digest(args.toolchain), digest(compiler)
        if (report["compilerSha256"] != toolchain["compiler"]["sha256"] or
                source_identity(lib.parent) != toolchain["sourceTree"]):
            raise ValueError("graph initialization toolchain inputs changed")
        report["pinnedStd"] = admission.check_std(lib)
        env, _, tools = lean_check.toolchain(args.lean_bin, 4)
        report["tools"] = tools
        run(output, "python-preflight", [sys.executable, "-m", "unittest", "discover", "-s", "test/lean", "-p", "test_graph_init.py"], cwd=ROOT)
        run(output, "cached-proof", [tools["lake"]["path"], "build", MODULE], cwd=ROOT / "lean", env=env)
        report["audit"] = audit(output, env, tools["lean"]["path"])
        report["controls"] = controls(output, env, tools["lean"]["path"])
        run(output, "version", [compiler, "version"])
        if text(output, "version") != "0.17.0":
            raise ValueError("graph initialization requires pinned Zig 0.17.0")
        array_output = output / "arrays"
        array_output.mkdir()
        report["nativeArrays"] = array.native(array_output, compiler, lib)
        report["native"] = []
        for mode in ("Debug", "ReleaseSafe", "ReleaseFast"):
            binary = output / ("graph-init-" + mode)
            run(output, "build-" + mode, [compiler, "build-exe", "-j4", "--zig-lib-dir", lib, "-fllvm",
                "-O", mode, "--dep", "compiler", "-Mroot=" + str(PROBE), "-O", mode,
                "-Mcompiler=" + str(ROOT / "src/modules.zig"), "--cache-dir", ROOT / ".zig-cache",
                "--global-cache-dir", output / "global-cache", "-femit-bin=" + str(binary)], cwd=ROOT)
            run(output, "probe-" + mode, [binary], cwd=ROOT)
            observation = output / ("probe-" + mode + ".stdout")
            entry = {"mode": mode, "binarySha256": digest(binary), "observationSha256": digest(observation), "accepted": False}
            report["native"].append(entry)
            write_json(output / "report.json", report)
            if observation.stat().st_size > 1024 * 1024:
                raise ValueError("native graph initialization observation exceeded bound")
            check_profile(json.loads(observation.read_bytes()), mode)
            if (output / ("build-" + mode + ".stderr")).read_bytes() or (output / ("probe-" + mode + ".stderr")).read_bytes():
                raise ValueError("unreviewed native graph initialization diagnostic")
            entry.update(accepted=True, allocatorContexts=2, queryCases=2048, emptyCacheQueries=2048)
        proof, artifacts = prove.check_module(MODULE, CLAIMS, lean_bin=args.lean_bin, jobs=4, fresh=True)
        directory = output / "proof"
        directory.mkdir()
        for name, data in artifacts.items():
            (directory / name).write_bytes(data)
        write_json(directory / "report.json", proof)
        report["proofReportSha256"] = digest(directory / "report.json")
        if (proof.get("status") != "passed" or proof.get("freshKernelReplay") is not True or
                proof.get("replayIncludesImports") is not True or proof.get("auditedDeclarations") != CLAIMS):
            raise ValueError("graph initialization proof or fresh imported replay failed")
        if (inputs() != report["inputs"] or digest(args.toolchain) != report["toolchainReportSha256"] or
                digest(compiler) != report["compilerSha256"] or source_identity(lib.parent) != toolchain["sourceTree"]):
            raise ValueError("graph initialization acceptance inputs changed")
        report.update(status="passed", emptyInitializationVerified=True, typedEmptyOwnerHeaderVerified=True,
            nativeEmptyCacheQueriesVerified=True, initialEmptyKeyOwnershipVerified=True)
    except BaseException as error:
        report["error"] = str(error)
        raise
    finally:
        write_json(output / "report.json", report)
    print("Complete container defaults and initial empty key ownership passed; owner allocation, allocator fields, nonempty map binding, map mutations and recursive constructors remain open.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    check(parser.parse_args())
