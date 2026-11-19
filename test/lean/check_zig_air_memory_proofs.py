#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Capture, decode, audit and replay the typed memory AIR client.
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""

import argparse
import copy
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "lean"))
sys.path.insert(0, str(ROOT / "lean/zig_air"))
import environment as lean_check
import prove
import check_zig_air_memory
from check_zig_air_proofs import inputs, mutation_check
from build_toolchain import digest, run, source_identity, write_json
from capture import read_json
from generate import captured_path
from generate_memory import Decoder, generate

CLAIMS = ["Compiler.ZigAir.Memory." + name for name in (
    "bounded_slice_iff", "unbounded_slice_iff", "larger_allocation_does_not_relax_view", "access_success_region",
    "replace_other", "cleanup_keeps_counters", "length_write_preserves_pointer", "length_read_observes_view",
    "layout_alignment_positive", "allocate_preserves_valid", "cleanup_preserves_valid", "writeCell_preserves_shape",
    "replace_typed_preserves_valid", "store_preserves_valid",
    "Heap.lookup_mem", "Cells.empty_valid", "Cells.lookup_set", "Cells.lookup_set_other", "Cells.set_preserves_valid",
    "Cells.fold_preserves_valid", "Cells.write_preserves_valid", "Cells.write_single", "Cells.write_success", "Cells.read_after_write")]
CLAIMS += ["Compiler.ZigAir.Memory." + name for name in (
    "Cells.read_eq_of_lookup", "Cells.fold_lookup_other", "Cells.read_frame",
    "Heap.lookup_replace", "writeCell_success", "readCell_after_writeCell",
    "store_success", "access_write_read", "access_replace_cells",
    "load_after_store", "load_alias_after_store", "load_eq_of_lookup",
    "load_other_after_store", "load_disjoint_after_store")]
CLAIMS += ["Compiler.ZigAir.MemoryClients." + name for name in ("load_store_success", "load_store_failure", "load_store_run")]
CLAIMS += ["Compiler.ZigAir.Memory." + name for name in (
    "load_after_two_scalar_stores", "pointerCast_address", "offsetPointer_add_address", "elementPointer_address")]
CLAIMS += ["Compiler.ZigAir.MemoryAir." + name for name in (
    "value_valid_of_hasType", "Ref.eval_local", "Ref.eval_constant",
    "Ref.eval_constant_of_valid", "Ref.natural_of_eval", "Ref.natural_eq",
    "Prim.eval_argument", "Prim.eval_cast", "Prim.eval_offset",
    "Prim.eval_load", "Prim.eval_store", "Code.eval_bind",
    "Code.eval_ret", "Program.run_of_valid_inputs")]
CLAIMS += ["Compiler.ZigAir.MemoryBufferClients." + name for name in (
    "buffer_alias_body", "buffer_alias_run_decoded", "buffer_alias_run")]
CLAIMS += ["Compiler.ZigAir.MemoryAir." + name for name in (
    "Prim.transition_preserves_valid", "Prim.failure_retains_state", "Prim.preserves_valid",
    "Code.preserves_valid", "Program.preserves_valid")]
CLAIMS += ["Compiler.ZigAir.MemoryTests." + name for name in (
    "bounded_slice_success", "original_view_bounds_are_required", "untaken_slice_is_not_checked", "taken_slice_is_checked", "taken_slice_success",
    "constant_result_keeps_source_guard", "unused_result_keeps_source_guard", "unused_slice_success", "constant_length_success",
    "unbounded_constant_length_success", "unbounded_constant_length_checks_memory", "static_array_bound_success",
    "memory_extent_is_also_required", "cleanup_on_success", "cleanup_on_failure", "generated_store_load", "generated_slice_field_alias",
    "generated_pointer_subtraction", "generated_pointer_subtraction_rejects_provenance", "lifetime_is_not_reused", "read_after_cleanup_rejects",
    "uninitialized_load_rejects", "array_uninitialized_rejects", "partial_slice_initialization_is_retained",
    "unaligned_load_rejects", "const_write_rejects", "allocation_readonly_rejects", "physical_wrap_is_distinct",
    "provenance_failure_is_distinct", "last_byte_is_representable", "unrepresentable_empty_pointer_rejects", "explicit_resource_exhaustion",
    "generated_buffer_alias", "generated_buffer_separation", "unwritten_buffer_element_rejects", "buffer_view_bound_rejects",
    "generated_slice_initialization", "generated_slice_overwrite", "generated_partial_length", "generated_length_existing",
    "pointer_field_initializes_independently", "array_of_slices_aliases", "nested_array_element", "array_whole_value_remains_unsupported",
    "zero_stride_element_remains_unsupported", "misaligned_leaf_is_not_a_subobject", "outside_leaf_state_rejects",
    "duplicate_leaf_state_rejects", "wrong_leaf_type_rejects")]

CLAIMS += ["Compiler.ZigAir.Memory." + name for name in (
    "Field.layouts_eq_map", "Field.layout_eq_type", "Ty.project_root",
    "acceptsView_self", "acceptsView_array", "leafType_array",
    "Ty.aggregate_member_geometry", "Ty.aggregate_disjoint", "Ty.fieldAt_geometry",
    "root_fieldPointer")]
CLAIMS += ["Compiler.ZigAir.Memory.NestedTests." + name for name in (
    "complete_layout_and_initial_valid", "nested_type_equality_retains_fields", "nested_header_selection",
    "nested_components_keep_byte_offsets", "nested_header_field_selection", "typed_selection_supplies_no_initialization",
    "actual_nested_header_stores", "nested_readback_and_validity", "reached_prefix_does_not_initialize_capacity",
    "partial_nested_slice_rejects", "opaque_fields_and_whole_objects_stay_unsupported", "nominal_same_extent_cannot_admit_header",
    "exact_nested_record_view_retains_permissions", "altered_nested_fields_cannot_admit_view", "nonzero_owner_offset_keeps_lifetime",
    "nested_array_owner_bound_rejects", "nested_array_child_bounds_are_retained", "padding_and_interior_are_not_leaves",
    "invalid_nested_child_layout_rejects", "invalid_parent_view_rejects", "nested_parent_geometry_rejects", "readonly_nested_access_cannot_store",
    "stale_nested_lifetime_and_cleanup_reject", "nested_cells_require_declared_leaf_type")]
CLAIMS += ["Compiler.ZigAir.Memory." + name for name in ("fieldPointer_of_access", "array_access_permitted",
    "store_subobject_total", "Cells.read_record_unsupported", "Cells.read_aggregate_unsupported")]

OPTIONAL_OBJECT_CLAIMS = ["Compiler.ZigAir.Memory.OptionalObject." + name for name in (
    "value_valid", "payload_value", "read_after_store", "store_root")]
OPTIONAL_OBJECT_CLAIMS += ["Compiler.ZigAir.Memory.OptionalObject.Tests." + name for name in (
    "initial_valid_and_layout", "write_result", "every_payload", "missing_null_and_present",
    "address_offset_length_identity", "copying_is_not_pointee_liveness", "independent_word", "overwrite_clears_payload",
    "complete_ordered_fields_required", "exact_offsets_required", "field_type_and_range_required", "length_range_required",
    "exact_optional_type_required", "no_byte_projection", "readonly_misaligned_outside_and_dead", "invalid_geometry_rejects",
    "unsupported_child_rejects", "array_stride_and_bounds", "null_and_empty_slice_differ", "slice_permissions_and_length_checked",
    "nested_payload_checked")]
OPTIONAL_POINTER_CLAIMS = ["Compiler.ZigAir.Memory.OptionalObject.PointerTests." + name for name in (
    "initial_valid_and_layout", "every_payload", "missing_null_and_present", "nullable_word_does_not_allocate_pointee",
    "wrong_payload_rejects", "nullable_layout_is_exact", "no_pointer_or_discriminator_projection",
    "readonly_dead_and_misaligned_reject", "exhaustive_lock_tag_range")]
CLAIMS += OPTIONAL_OBJECT_CLAIMS + OPTIONAL_POINTER_CLAIMS

NATIVE_THEOREMS = {case: "Compiler.ZigAir.MemoryTests." + theorem for case, theorem in (
    ("bounded-slice", "bounded_slice_success"), ("untaken-slice", "untaken_slice_is_not_checked"),
    ("taken-valid-slice", "taken_slice_success"), ("array-slice", "static_array_bound_success"),
    ("constant-length", "constant_length_success"), ("unbounded-constant-length", "unbounded_constant_length_success"),
    ("unused-valid-slice", "unused_slice_success"), ("store-load", "generated_store_load"),
    ("slice-field-alias", "generated_slice_field_alias"), ("pointer-subtraction", "generated_pointer_subtraction"),
    ("buffer-alias", "generated_buffer_alias"), ("buffer-separation", "generated_buffer_separation"),
    ("slice-initialization", "generated_slice_overwrite"), ("length-field-only", "generated_length_existing"))}


def without_imports(text):
    return re.sub(r"^import [^\n]+\n", "", text, flags=re.MULTILINE)


def optional_object_dependencies(audit):
    """The optional result must derive from the same checked heap/store laws."""
    ns = "Compiler.ZigAir.Memory."
    optional = ns + "OptionalObject."
    required = {
        optional + "store_root": {ns + "root_store_total", ns + "store_preserves_valid",
                                  optional + "value_valid", optional + "read_after_store"},
        optional + "read_after_store": {ns + "load_alias_after_store", optional + "payload_value"},
        optional + "Tests.every_payload": {optional + "Tests.write_result", ns + "store_preserves_valid",
                                          optional + "read_after_store"},
        optional + "Tests.write_result": {optional + "store_root"},
    }
    claims = {c["theorem"]: set(c["dependencies"]) for c in audit["claims"]}
    for name, needed in required.items():
        if not needed <= claims.get(name, set()):
            raise ValueError("optional object lost checked dependencies: " + name)
    return {"checkedDependencies": sorted(required), "nativeFieldAssignmentVerified": False}


def memory_definitions():
    types = (ROOT / "lean/Compiler/ZigAir/MemoryTypes.lean").read_text()
    return types + "\n" + "\n".join(without_imports((ROOT / "lean/Compiler/ZigAir" / name).read_text())
                                   for name in ("MemoryStorage.lean", "Memory.lean", "WordBytes.lean", "MemoryWordArrayTypes.lean",
                                                "MemoryWordByteView.lean", "MemoryByteAccess.lean"))


def invariant_controls(output, env, lean):
    """Check universal memory laws against bound mutations, without fixture inputs."""
    memory = memory_definitions()
    client = without_imports((ROOT / "lean/Compiler/ZigAir/MemoryAir.lean").read_text())
    proofs = "\n".join(without_imports((ROOT / "lean/Compiler/ZigAir" / name).read_text())
                       for name in ("MemoryStorageProofs.lean", "MemoryProofs.lean", "MemoryEffects.lean", "MemoryReadTyping.lean", "MemoryPointers.lean", "MemoryAirLaws.lean", "MemoryInvariant.lean",
                                    "MemoryAllocationLaws.lean", "MemoryRelease.lean", "MemoryHeapFrame.lean", "MemorySlots.lean", "MemoryRecordFields.lean",
                                    "MemoryRecordViews.lean", "MemoryRecordWrites.lean", "MemoryNestedTests.lean",
                                    "MemoryOptionalScalar.lean", "MemoryOptionalScalarTests.lean",
                                    "MemoryOptionalObject.lean", "MemoryOptionalObjectTests.lean", "MemoryOptionalPointerTests.lean"))
    prefix = "import Compiler.ZigAir.ControlSafety\n"
    original = prefix + memory + client + proofs
    controls = [mutation_check(output, "invariants-unchanged", original, True, env, lean)]
    for name, owner, before, after in (
            ("nullable-pointer-wrong-extent", memory, "if layout = ⟨8, 8⟩ then some layout else none",
             "if layout = ⟨16, 8⟩ then some layout else none"),
            ("nullable-pointer-unchecked-layout", memory, "if layout = ⟨8, 8⟩ then some layout else none",
             "some layout"),
            ("lock-tag-wrong-layout", memory, ".scalar (.int false 1) => some ⟨1, 1⟩",
             ".scalar (.int false 1) => some ⟨8, 8⟩"),
            ("optional-object-too-small", memory, "payload.bytes ≤ layout.bytes", "True"),
            ("optional-object-under-aligned", memory, "layout.alignment % payload.alignment = 0", "True"),
            ("optional-object-invalid-stride", memory, "layout.bytes % layout.alignment = 0", "True"),
            ("optional-object-null-uninitialized", memory,
             "| .optionalObject child _ payload => match payload with\n    | none => true",
             "| .optionalObject child _ payload => match payload with\n    | none => false"),
            ("optional-object-unchecked-fields", memory, "Ty.aggregateValid layout fields && objectFieldsTyped values fields",
             "let _ := values; Ty.aggregateValid layout fields"),
            ("optional-object-unchecked-field-offset", memory, "decide (offset = base) && value.hasType field.type",
             "value.hasType field.type"),
            ("optional-object-incomplete-fields", memory, "| [], [] => true\n  | (offset, value)",
             "| [], _ => true\n  | (offset, value)"),
            ("optional-object-extra-fields", memory, "| [], [] => true\n  | (offset, value)",
             "| _, [] => true\n  | (offset, value)"),
            ("optional-object-unchecked-decoder", proofs, "if !value.hasType (.optionalObject child layout) then .error .malformed else",
             "if false then .error .malformed else"),
            ("optional-object-lost-payload", proofs, "| .optionalObject _ _ result => .ok result",
             "| .optionalObject _ _ result => let _ := result; .ok none"),
            ("optional-wrong-extent", memory, ".optionalScalar (.int false 8) => some ⟨2, 1⟩",
             ".optionalScalar (.int false 8) => some ⟨1, 1⟩"),
            ("optional-usize-wrong-extent", memory, ".optionalScalar (.int false 64) => some ⟨16, 8⟩",
             ".optionalScalar (.int false 64) => some ⟨8, 8⟩"),
            ("optional-signed-wrong-extent", memory, ".optionalScalar (.int true 64) => some ⟨16, 8⟩",
             ".optionalScalar (.int true 64) => some ⟨8, 8⟩"),
            ("optional-signed-wrong-alignment", memory, ".optionalScalar (.int true 64) => some ⟨16, 8⟩",
             ".optionalScalar (.int true 64) => some ⟨16, 4⟩"),
            ("optional-word-wrong-extent", memory, ".optionalScalar (.int false 256) => some ⟨48, 16⟩",
             ".optionalScalar (.int false 256) => some ⟨32, 16⟩"),
            ("optional-word-wrong-alignment", memory, ".optionalScalar (.int false 256) => some ⟨48, 16⟩",
             ".optionalScalar (.int false 256) => some ⟨48, 8⟩"),
            ("optional-null-uninitialized", memory, "| .optionalScalar child payload => match payload with\n    | none => true",
             "| .optionalScalar child payload => match payload with\n    | none => false"),
            ("optional-unchecked-payload-type", memory, "decide (value.type = child) && value.valid", "value.valid"),
            ("optional-unchecked-payload-range", memory, "decide (value.type = child) && value.valid", "decide (value.type = child)"),
            ("optional-exposes-payload-field", memory, "@[simp] def sliceFieldType (type : Ty) (offset : Nat) : Option Ty :=\n  match type with",
             "@[simp] def sliceFieldType (type : Ty) (offset : Nat) : Option Ty :=\n  match type with\n  | .optionalScalar child => if offset = 0 then some (.scalar child) else none"),
            ("optional-null-is-missing", proofs, "| .optionalScalar _ none => .ok none",
             "| .optionalScalar _ none => .error .uninitialized"),
            ("optional-zero-is-null", proofs, ".ok (some (BitVec.ofInt bits value))",
             "if value = 0 then .ok none else .ok (some (BitVec.ofInt bits value))"),
            ("optional-unchecked-decoder", proofs, "if !value.hasType (unsigned bits) then .error .malformed else",
             "if false then .error .malformed else"),
            ("optional-truncates-wide-payload", proofs, ".ok (some (BitVec.ofInt bits value))",
             ".ok (some (BitVec.ofInt bits (value % 2^64)))"),
            ("unaligned-allocation", memory,
             "(layout.alignment - state.nextAddress % layout.alignment) % layout.alignment", "0"),
            ("overlapping-allocation", memory, "let base := state.nextAddress +", "let base := 8 +"),
            ("duplicate-lifetime", memory, "(state.nextId, allocation) :: state.heap", "(0, allocation) :: state.heap"),
            ("untyped-cell-write", memory, "(offset, value) :: cells.filter",
             "(offset, .scalar .unit) :: cells.filter"),
            ("cleanup-address-rewind", memory, "{ state with heap := state.heap.filter",
             "{ state with nextAddress := 8, heap := state.heap.filter"),
            ("lost-store-update", memory, ".ok { state with heap := state.heap.replace address.allocation after }",
             ".ok (let _ := after; state)"),
            ("store-changes-other-allocation", memory, "else item)", "else (item.1, value))"),
            ("store-erases-other-leaves", memory, "(offset, value) :: cells.filter (fun entry => entry.1 != offset)",
             "[(offset, value)]"),
            ("pointer-cast-rebases-offset", memory, ".ok (.pointer target address)",
             ".ok (.pointer target { address with offset := 0 })"),
            ("pointer-offset-loses-stride", memory, "let amount := count * layout.bytes", "let amount := count"),
            ("indexed-pointer-wrong-index", memory, "let shifted ← offsetPointer state false pointer index",
             "let shifted ← offsetPointer state false pointer (index + 1)"),
            ("pointer-offset-loses-lifetime", memory, "let next := { address with offset := offset }",
             "let next : Address := { allocation := 0, offset := offset }"),
            ("failure-discards-prefix", client, ".error fault => (.error fault, state)",
             ".error fault => (.error fault, { state with heap := [] })"),
            ("field-loses-extent-check", memory, "offset + child.bytes ≤ layout.bytes", "True"),
            ("field-loses-alignment-check", memory, "offset % child.alignment = 0", "True"),
            ("field-loses-parent-alignment", memory, "layout.alignment % child.alignment = 0", "True"),
            ("field-loses-disjointness", memory,
             "decide (fields.Pairwise fun a b => a.1 + (a.2.getD ⟨0, 1⟩).bytes ≤ b.1)", "true"),
            ("nested-lost-relative-offset", memory, "Field.project select field (offset - base)",
             "Field.project select field offset"),
            ("nested-lost-parent-validation", memory,
             "if Ty.aggregateValid layout fields then Field.projectFields select fields offset else none",
             "let _ := layout; Field.projectFields select fields offset"),
            ("nested-lost-containing-bound", memory, "base ≤ offset ∧ offset < base + layout.bytes", "base ≤ offset ∧ 0 < layout.bytes"),
            ("nested-lost-view-type", memory, "if select field then some field else none", "some field")):
        if owner.count(before) != 1 or original.count(owner) != 1:
            raise ValueError("invariant mutation was not bound to current semantics: " + name)
        changed = original.replace(owner, owner.replace(before, after))
        controls.append(mutation_check(output, name, changed, False, env, lean))
    for record in controls:
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant",
                     (output / (record["name"] + ".stdout")).read_text(), re.I):
            raise ValueError("memory control hit a resource or syntax failure: " + record["name"])
    return controls


def buffer_controls(output, env, lean, generated):
    """Mutate captured code under the universal proof; no concrete fixtures."""
    client = without_imports((ROOT / "lean/Compiler/ZigAir/MemoryBufferClients.lean").read_text())
    original = ("import Compiler.ZigAir.MemoryPointers\nimport Compiler.ZigAir.MemoryAirLaws\n" +
                without_imports(generated) + client)
    controls = [mutation_check(output, "buffer-unchanged", original, True, env, lean)]
    for name, before, after in (
            ("buffer-redirect-second-write", "(.store (.local 6) (.local 3))", "(.store (.local 4) (.local 3))"),
            ("buffer-corrupt-first-value", "(.store (.local 4) (.local 2))", "(.store (.local 4) (.local 3))")):
        if generated.count(before) != 1 or original.count(before) != 1:
            raise ValueError("buffer mutation was not bound to captured program: " + name)
        changed = original.replace(before, after)
        controls.append(mutation_check(output, name, changed, False, env, lean))
    return controls


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.memory-air-acceptance.v1", "status": "failed", "proofScope": "zigFreshAir",
              "sourceSafetyVerified": False, "nativeBackendVerified": False, "wholeCompilerVerified": False, "jobs": 4}
    try:
        report["pythonInputs"], report["leanInputs"] = inputs(), lean_check.source_inputs()
        report["toolchainReportSha256"] = digest(args.toolchain)
        run(output, "python-tests", [sys.executable, "-m", "unittest", "discover", "-s", "test/lean", "-p", "test_zig_air_*.py"], cwd=ROOT)
        captures = output / "captures"
        check_zig_air_memory.check(argparse.Namespace(toolchain=args.toolchain, output=captures))
        report["captureReportSha256"] = digest(captures / "report.json")
        groups = (("GeneratedMemory", captures / "slices/ReleaseFast/report.json", "zig_air_validity",
                   ("bounded_slice", "conditional_slice", "array_slice", "constant_length", "unused_slice", "unbounded_constant_length")),
                  ("GeneratedMemoryCells", captures / "ReleaseFast/report.json", "zig_air_memory",
                   ("move_back", "load_store", "slice_fields", "buffer_alias", "initialize_slice", "initialize_length")))
        generated, records = {}, {}
        report["generation"], report["rejections"] = {}, {}
        for module, capture_path, prefix, names in groups:
            target = output / (module + ".lean")
            report["generation"][module] = generate(capture_path, [prefix + "." + name for name in names], target, output / (module + ".json"))
            if target.read_bytes() != (ROOT / "lean/Compiler/ZigAir" / (module + ".lean")).read_bytes():
                raise ValueError("generated memory program changed: " + module)
            generated[module] = target.read_text()
            captured = read_json(capture_path)
            for root, entry in captured["functions"].items():
                if not entry["requested"]:
                    continue
                path = captured_path(capture_path, entry)
                if digest(path) != entry["sha256"]:
                    raise ValueError("memory capture identity changed")
                record = read_json(path)
                records[root] = record
                if root not in report["generation"][module]["functions"]:
                    try:
                        Decoder(record).program(record)
                    except ValueError as error:
                        report["rejections"][root] = {"airSha256": entry["sha256"], "reason": str(error)}
                    else:
                        raise ValueError("unsupported memory root was admitted: " + root)
        env, _, tools = lean_check.toolchain(args.lean_bin, 4)
        run(output, "cached-build", [tools["lake"]["path"], "build", "Compiler.ZigAir.MemoryAudit"], cwd=ROOT / "lean", env=env)
        run(output, "closure-audit", [tools["lean"]["path"], "-DwarningAsError=true", "Compiler/ZigAir/MemoryAudit.lean"], cwd=ROOT / "lean", env=env)
        audit = read_json(output / "closure-audit.stdout")
        if audit.get("schema") != "oksolc.memory-air-audit.v1" or [claim["theorem"] for claim in audit["claims"]] != CLAIMS:
            raise ValueError("unexpected memory declaration audit")
        report["optionalObjectDependencies"] = optional_object_dependencies(audit)
        negatives = output / "mutation-controls"
        negatives.mkdir()
        tests = without_imports((ROOT / "lean/Compiler/ZigAir/MemoryTests.lean").read_text())
        definitions = "\n".join(without_imports(text) for text in generated.values())
        original = "import Compiler.ZigAir.MemoryAir\n" + definitions + tests
        report["mutationControls"] = [mutation_check(negatives, "unchanged", original, True, env, tools["lean"]["path"])]
        for name, root, mutation in (
            ("drop-original-bound", "zig_air_validity.bounded_slice", "unbounded"),
            ("drop-dead-guard", "zig_air_validity.unused_slice", "remove"),
            ("replace-view-with-allocation", "zig_air_validity.constant_length", "array")):
            record = records[root]
            before = Decoder(record).program(record)
            changed = copy.deepcopy(record)
            if mutation == "remove":
                changed["sourceValidity"]["slices"].pop()
            else:
                changed["sourceValidity"]["slices"][-1]["upperBound"] = (
                    {"kind": "unboundedPointer", "requiresMemoryValidity": True} if mutation == "unbounded" else {"kind": "arrayLength", "value": 16})
            after = Decoder(changed).program(changed)
            if before == after or original.count(before) != 1:
                raise ValueError("source guard mutation was not bound to generated AIR")
            write_json(negatives / (name + ".air.json"), changed)
            report["mutationControls"].append(mutation_check(negatives, name, original.replace(before, after), False, env, tools["lean"]["path"]))
        memory = memory_definitions()
        client = without_imports((ROOT / "lean/Compiler/ZigAir/MemoryAir.lean").read_text())
        concrete = memory + client + definitions + tests
        report["mutationControls"].append(mutation_check(negatives, "memory-unchanged", concrete, True, env, tools["lean"]["path"]))
        for name, before, after in (
            ("lost-slice-alias", "(offset, value) :: cells.filter", "if offset = 8 then cells else (offset, value) :: cells.filter"),
            ("lost-array-view-bound", "⟨if many then 0 else layout.bytes, layout.alignment⟩", "⟨if many then 0 else 0, layout.alignment⟩"),
            ("reused-lifetime", "{ state with heap := state.heap.filter", "{ state with nextId := mark, heap := state.heap.filter"),
            ("invented-initialization", ".error .uninitialized", ".ok (.scalar (.int false 8 0))"),
            ("lost-array-extent", "if 0 < layout.bytes ∧ offset / layout.bytes < length then\n      Ty.project select child", "if 0 < layout.bytes then\n      Ty.project select child")):
            if memory.count(before) != 1:
                raise ValueError("memory mutation was not bound to current semantics")
            report["mutationControls"].append(mutation_check(negatives, name, memory.replace(before, after) + client + definitions + tests,
                                                             False, env, tools["lean"]["path"]))
        report["mutationControls"].extend(invariant_controls(negatives, env, tools["lean"]["path"]))
        report["mutationControls"].extend(buffer_controls(negatives, env, tools["lean"]["path"], generated["GeneratedMemoryCells"]))
        libraries = []
        for label, directory in (("slices", captures / "slices/ReleaseFast"), ("cells", captures / "ReleaseFast")):
            command = read_json(directory / "ordinary.process.json")["command"]
            command[command.index("build-obj")] = "build-lib"
            command.append("-dynamic")
            library = output / (label + ".dylib")
            command[command.index("--cache-dir") + 1] = str(output / (label + "-native-cache"))
            command = ["-femit-bin=" + str(library) if a.startswith("-femit-bin=") else a for a in command]
            run(output, "native-build-" + label, command)
            libraries.append(library)
        run(output, "native-cases", [sys.executable, ROOT / "test/lean/zig_air_memory_native.py",
            "--slices", libraries[0], "--cells", libraries[1], "--output", output / "native-observations.json"])
        report["nativeObservationsSha256"] = digest(output / "native-observations.json")
        observations = read_json(output / "native-observations.json")["cases"]
        if ({case["case"] for case in observations} != set(NATIVE_THEOREMS) or len(observations) != len(NATIVE_THEOREMS) or
                any(case["expected"] != case["actual"] for case in observations) or not set(NATIVE_THEOREMS.values()) <= set(CLAIMS)):
            raise ValueError("native observations lack matching checked model cases")
        report["nativeModelTheorems"] = NATIVE_THEOREMS
        report["nativeLibraries"] = {p.name: digest(p) for p in libraries}
        proof, artifacts = prove.check_module("Compiler.ZigAir.MemoryAudit", CLAIMS, lean_bin=args.lean_bin, jobs=4, fresh=True)
        proofs = output / "proofs"
        proofs.mkdir()
        for name, data in artifacts.items():
            (proofs / name).write_bytes(data)
        report["proofReportSha256"] = digest(proofs / "report.json")
        if (proof["status"] != "passed" or not proof["freshKernelReplay"] or not proof["replayIncludesImports"] or proof["auditedDeclarations"] != CLAIMS):
            raise ValueError("memory proof audit or fresh kernel replay failed")
        if report["pythonInputs"] != inputs() or report["leanInputs"] != lean_check.source_inputs():
            raise ValueError("memory acceptance inputs changed")
        if digest(args.toolchain) != report["toolchainReportSha256"] or digest(captures / "report.json") != report["captureReportSha256"]:
            raise ValueError("memory capture/toolchain report changed")
        toolchain = read_json(args.toolchain)
        if (digest(Path(toolchain["compiler"]["path"])) != toolchain["compiler"]["sha256"] or
                source_identity(Path(toolchain["compiler"]["zigLibDir"]).parent) != toolchain["sourceTree"]):
            raise ValueError("memory toolchain changed")
        report.update(status="passed", auditedDeclarations=CLAIMS, freshKernelReplay=True)
    except BaseException as error:
        report["error"] = str(error) or type(error).__name__
        raise
    finally:
        write_json(output / "report.json", report)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    check(parser.parse_args())
