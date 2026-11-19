#!/usr/bin/env python3
"""Check source-bound native representative headers and typed pointer readers.
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
import extract_representative_append as append_admission
import extract_representative_publication as publication_admission
import extract_representative_growth as growth_admission
import extract_representative_capacity as capacity_admission
import generate_representative_array_layout as admission
import prove
from build_toolchain import digest, run, source_identity, text, write_json
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

MODULE = "Compiler.Extraction.RepresentativeGrowingAppendTests"
NS = "Compiler.Extraction.RepresentativeArray."
MEM = "Compiler.ZigAir.Memory."
CLAIMS = [MEM + name for name in ("array_access", "recordView_address", "recordView_parent")]
CLAIMS += [NS + name for name in ("layout_checked", "element_layout_checked", "field_types_checked",
    "readItems_from_root", "header_after_stores", "invalid_from_loaded_header", "element_pointer",
    "element_record_view", "representative_from_array")]
CLAIMS += [NS + "Tests." + name for name in ("complete_valid", "header_reads_both_fields",
    "first_and_second_representatives", "source_pointer_derivation", "capacity_does_not_widen_length",
    "pointer_loads_complete_expression", "independent_unsorted_offset_borrow", "readonly_return_cannot_store",
    "empty_sentinel_is_not_dereferenced", "invalid_id_does_not_dereference", "valid_id_needs_live_backing",
    "missing_header_pointer_rejects", "missing_header_length_rejects", "capacity_is_not_read_by_lookup",
    "invalid_header_leaf_rejects", "header_interior_and_extent_reject", "misaligned_data_rejects",
    "backing_extent_is_checked", "nominal_extent_is_not_complete_shape", "foreign_same_extent_rejects",
    "omitted_expression_field_rejects", "wrong_nominal_identity_rejects", "wrong_nominal_layout_rejects",
    "record_view_preserves_constness", "live_pointer_is_not_initialized_record", "stale_backing_lifetime_rejects",
    "same_address_new_lifetime_is_not_old_pointer", "source_header_store_derivation")]
CLAIMS += [MEM + "store_retains_shape", "Compiler.Extraction.Expression.fields_after_subobject_stores"]
CLAIMS += [NS + name for name in ("element_fieldPointer", "fields_after_array_stores",
    "readItems_after_other_store", "representativeFields_after_stores")]
CLAIMS += [NS + "FieldTests." + name for name in ("initial_valid", "source_element_selector", "four_actual_stores",
    "source_bound_complete_observation", "nonzero_element_is_not_first", "initialized_selector_does_not_initialize_payload",
    "reached_prefix_is_not_complete", "partial_slice_rejects", "older_descriptor_and_allocations_survive",
    "offset_unsorted_borrow_keeps_identity", "readonly_element_rejects_write", "source_bound_precedes_field_reads",
    "array_extent_rejects_field_selector", "stale_lifetime_rejects_complete_fields")]
CLAIMS += [MEM + name for name in ("access_subregion", "Value.leaves_shift", "Cells.write_subobject_total")]
CLAIMS += [NS + name for name in ("field_store_total", "initializeFields_of_stores", "initializeFields_stores",
    "initializeFields_verified", "representativeFields_after_initialization")]
CLAIMS += [NS + "WriteTests." + name for name in ("actual_four_store_execution", "initialization_without_store_premises",
    "source_bound_initialization", "actual_source_bound_readback", "spare_slot_still_needs_source_length",
    "array_extent_rejects_initialization", "readonly_backing_rejects_initialization", "stale_lifetime_rejects_initialization",
    "wrong_allocation_kind_rejects_initialization", "invalid_slice_length_rejects_initialization",
    "invalid_id_rejects_initialization", "invalid_sequence_rejects_initialization", "exact_offset_borrow_and_older_fields")]
CLAIMS += [MEM + name for name in ("Cells.readLeaf_hasType", "access_read_write", "Value.usize_valid",
    "length_write_preserves_pointer", "Cells.read_slice_after_length_write", "load_slice_after_length_store")]
CLAIMS += [NS + "readField_after_other_store"]
CLAIMS += [NS + "Append." + name for name in ("length_type_checked", "length_store_total", "readItems_after_length_store",
    "readCapacity_after_length_store", "nextLength_bounded", "readHeader_from_parts", "readHeader_parts",
    "append_of_steps", "appendWithoutGrowth_verified", "representativeFields_after_append")]
CLAIMS += [NS + "Append.Tests." + name for name in ("initial_header_and_missing_slot", "actual_length_store",
    "length_increment_precedes_initialization", "actual_append", "append_without_store_premises", "source_bound_append",
    "actual_source_bound_append", "no_allocation_or_payload_change", "source_length_stays_distinct_from_capacity",
    "offset_unsorted_arguments_after_append", "exact_capacity_is_enough", "empty_ready_array_appends_first_slot",
    "growth_is_scope_rejection", "readonly_header_or_backing_rejects", "stale_backing_rejects", "malformed_evaluated_fields_reject")]
CLAIMS += [MEM + name for name in ("heap_after_store_other", "Heap.lookup_ne_of_type_ne", "load_other_after_store", "WordArray.write_allocation_frame")]
CLAIMS += [NS + "Append." + name for name in ("appendWithoutGrowth_framed", "append_parent_borrow")]
CLAIMS += [NS + "Append.BorrowTests." + name for name in ("initial_parent_contents", "persistent_offset_parent_frame",
    "actual_persistent_parent", "extended_parent_contents", "actual_extended_append", "extended_parent_frame",
    "stack_and_readonly_metadata_survive", "readonly_borrow_cannot_write", "source_bound_and_outside_words_survive",
    "no_new_lifetime_or_revived_alias", "descriptor_alias_is_not_an_independent_parent", "descriptor_backing_rejects_word_array_admission")]
CLAIMS += [MEM + "root_access", MEM + "root_fieldPointer"]
CLAIMS += [NS + "Owner." + name for name in ("layout_checked", "header_layout_checked", "regions_checked",
    "header_address_identity", "header_region_access", "root_header_region")]
CLAIMS += [NS + "Owner.Tests." + name for name in ("initial_valid", "header_from_declared_owner", "writable_header_from_declared_owner",
    "readonly_permission_is_not_upgraded", "nonzero_owner_offset_retains_parent", "geometry_does_not_admit_nested_header_fields",
    "nominal_header_extent_is_not_complete_admission", "header_region_is_not_initialized_storage", "interior_owner_pointer_is_checked",
    "standalone_header_does_not_supply_whole_owner", "embedded_header_is_not_a_separate_allocation", "malformed_physical_regions_reject",
    "stale_owner_lifetime_rejects", "stack_cleanup_invalidates_embedded_header")]
CLAIMS += [MEM + name for name in ("fieldPointer_of_access", "array_access_permitted", "store_subobject_total",
    "Cells.read_record_unsupported", "Cells.read_aggregate_unsupported")]
CLAIMS += [NS + "header_after_subobject_stores"]
CLAIMS += [NS + "Owner." + name for name in ("view_layout_checked", "header_field_checked", "header_view_checked",
    "header_value_views_checked", "header_leaf_types_checked", "header_pointer", "root_header_pointer", "root_owner_view",
    "array_header_pointer", "root_header_fields", "header_store_total", "initializeHeader_verified")]
CLAIMS += [NS + "Owner.FieldTests." + name for name in ("initial_valid", "nominal_owner_resolves_complete_fields",
    "embedded_selection_preserves_permission", "header_selection_does_not_initialize", "actual_two_header_stores",
    "actual_header_assignment", "header_assignment_without_store_premises", "readonly_readback_from_assignment",
    "source_bound_complete_representative", "ordinary_source_bound_is_retained", "reached_prefix_keeps_capacity_uninitialized",
    "partial_nested_slice_rejects", "unrelated_storage_and_lifetimes_survive", "readonly_owner_cannot_store",
    "malformed_evaluated_header_rejects", "opaque_fields_and_whole_owner_are_unsupported", "wrong_mode_owner_is_not_the_same_type",
    "omitted_owner_field_does_not_supply_complete_view", "stale_owner_and_cleanup_reject", "nonzero_readonly_owner_selection",
    "nonzero_header_assignment_and_readback", "nonzero_assignment_preserves_first_header", "enclosing_array_extent_is_retained",
    "owner_is_not_representative_backing")]
CLAIMS += [MEM + "RegionAllocation." + name for name in ("extend_valid", "extend_lookup", "extend_shape", "extend_load_other",
    "reserve_empty", "reserve_overflow", "reserve_failed", "reserve_admitted", "reserve_nonempty_success", "reserve_preserves_valid", "reserve_heap_other")]
CLAIMS += [NS + "Backing." + name for name in ("layout_checked", "reserve_verified", "reserve_preserves_valid", "reserve_parent_borrow")]
CLAIMS += [NS + "Backing.Tests." + name for name in ("initial_valid", "fits", "actual_request", "admitted_without_final_premises",
    "complete_uninitialized_backing", "fresh_lifetime_and_high_water", "allocation_does_not_publish_header", "parent_contents",
    "offset_parent_survives", "live_backing_survives_reservation", "still_live_region_cannot_be_reused", "empty_skips_allocator", "oom_retains_effects", "overflow_skips_allocator", "invalid_capacity_rejects",
    "invalid_heap_rejects_before_request", "null_and_word_only_alignment_reject", "overlap_and_address_overflow_reject",
    "every_response_valid", "every_response_preserves_parent", "unsupported_metadata_rejects")]
CLAIMS += [MEM + name for name in ("Value.leaf_offsets", "Value.usize_value", "Cells.read_hasType", "load_hasType")]
CLAIMS += [NS + "Copy." + name for name in ("readField_hasType", "slot_declared", "fields_storage", "copyFrom_storage", "run_storage",
    "slot_offsets_apart", "readField_after_store", "readField_after_slot_store", "fields_read_frame", "copyFrom_read_frame", "run_read_frame",
    "field_store_readback", "fields_verified", "captured_slots_unique", "copyFrom_verified", "run_empty", "run_verified",
    "readFields_eq_of_slots", "run_parent_borrow")]
CLAIMS += [NS + "Copy.Tests." + name for name in ("initial_valid", "initialized_source", "first_row", "second_row", "actual_complete_copy",
    "copy_without_success_premise", "complete_readback_from_copy", "untouched_spare_fields", "distinct_rows_and_slice_identity",
    "untouched_source_header_and_spare_capacity", "no_allocation_or_release", "copied_offset_borrow", "parent_contents",
    "every_length_preserves_parent", "spare_row", "copying_spare_source_rejects_after_prefix", "short_target_retains_first_descriptor",
    "partial_first_row", "partial_second_row", "partial_slice_retains_item_and_prior_descriptor", "readonly_target_rejects_without_writes", "readonly_first_row", "readonly_second_row",
    "readonly_source_is_sufficient", "overlapping_copy_rejects", "empty_sentinels_are_not_dereferenced", "stale_source_or_target_rejects",
    "source_extent_rejects_separately")]
CLAIMS += [MEM + name for name in ("Cells.read_slice_parts", "Cells.read_slice_of_parts", "Cells.readLeaf_after_single_write",
    "Cells.read_slice_after_pointer_write", "load_slice_after_pointer_store")]
CLAIMS += [NS + "Publication." + name for name in ("pointer_field_checked", "write_is_store", "steps_storage", "run_storage",
    "owner_pointer_selector", "owner_pointer_store_total", "run_of_stores", "header_after_pointer_capacity_stores",
    "run_verified", "run_parent_borrow")]
CLAIMS += [NS + "Publication.Tests." + name for name in ("initial_valid", "pointer_assignment", "capacity_assignment",
    "actual_publication", "publication_without_store_premises", "readback_from_publication",
    "pointer_prefix_preserves_length_and_old_capacity", "malformed_capacity_retains_pointer", "readonly_rejects_before_writes",
    "stale_or_misaligned_owner_rejects", "publication_does_not_allocate_or_release", "published_copy_uses_new_backing", "publication_neither_reads_nor_initializes_length",
    "empty_length_stays_empty", "capacity_assignment_does_not_extend_backing",
    "parent_contents", "all_outcomes_preserve_offset_parent", "nested_owner_keeps_other_header")]
CLAIMS += [MEM + "fieldPointer_eq_of_lookup"]
CLAIMS += [NS + name for name in ("readField_eq_of_lookup", "allocatedSlice_empty", "readItemsData_from_loaded")]
CLAIMS += [NS + "Growth." + name for name in ("run_first", "first_of_reservation_and_publication", "first_oom",
    "run_verified", "run_oom", "run_unchanged", "lock_rejected", "first_storage", "run_storage", "run_parent_borrow")]
CLAIMS += [NS + "Growth.Tests." + name for name in ("initial_valid", "initialized_empty_header", "fits", "actual_first_growth",
    "growth_without_final_premises", "header_and_backing_from_growth", "allocation_view_does_not_read_length",
    "oom_before_length_read", "missing_length_retains_reservation", "readonly_rejection_retains_reservation",
    "nonempty_length_retains_reservation", "zero_skips_pointer_length_and_allocator", "missing_pointer_rejects_before_allocator",
    "capacity_failure_precedes_allocation", "overflow_is_oom_without_callback", "rejected_allocator_keeps_effects",
    "nonempty_growth_is_unsupported", "existing_capacity_skips_allocator", "allocated_capacity_includes_uninitialized_spare",
    "allocation_view_checks_backing_extent", "parent_contents", "all_outcomes_preserve_parent",
    "fixture_lock", "empty_unlocked", "lock_observations", "lock_failure_precedes_capacity_and_allocator")]
CLAIMS += [NS + "Append." + name for name in ("readItems_after_length_store_at", "readCapacity_after_length_store_at", "append_at_framed")]
CLAIMS += [NS + "Owner." + name for name in ("length_store_total", "appendWithoutGrowth_framed", "append_parent_borrow")]
CLAIMS += [NS + "Owner.AppendTests." + name for name in ("initial_owner_and_spare", "actual_length_store", "length_precedes_descriptor",
    "actual_append", "append_without_final_premises", "derived_readback", "source_bound_and_older_descriptor", "parent_contents",
    "parent_survives_same_append", "owner_metadata_and_lifetimes", "readonly_owner_rejects", "readonly_backing_rejects",
    "owner_lifetime_and_location_checked", "standalone_header_is_not_owner", "stale_backing_rejects", "missing_header_leaf_rejects",
    "invalid_evaluated_fields_reject", "full_capacity_is_scope_rejection")]
CLAIMS += [NS + "Capacity." + name for name in ("initial_capacity_checked", "inner_sum_bounded", "grow_bounded", "grow_sufficient",
    "grow_positive", "first_capacity_checked", "ensure_unchanged", "ensure_growing", "first_verified", "first_oom", "ensure_storage", "ensure_parent_borrow")]
CLAIMS += [NS + "Capacity.Tests." + name for name in ("arithmetic_boundaries", "fits", "actual_first_growth", "derived_first_growth",
    "derived_header_and_storage", "zero_skips_other_fields_and_allocator", "equality_skips_growth_policy", "oom_uses_selected_capacity",
    "oom_precedes_length_read", "saturation_byte_overflow_is_oom", "invalid_usize_is_not_oom", "capacity_fault_precedes_allocation",
    "unsupported_nonempty_growth_retains_state", "saved_view_fault_precedes_remap", "readonly_rejection_retains_reservation", "invalid_region_retains_effects", "parent_survives_all_outcomes", "spare_capacity_skips_lock")]
CLAIMS += [MEM + "recordView_result_parent"]
CLAIMS += [NS + name for name in ("initializeFields_reached_iff", "writeFields_storage")]
CLAIMS += [NS + "Append.Execution." + name for name in (
    "finish_success_iff", "assumeCapacity_of_spare", "finish_storage", "length_write_is_store", "assumeCapacity_storage", "run_valid",
    "owner_length_from_items", "first_verified", "first_oom", "spare_verified", "selected_descriptor_parent", "word_array_has_no_descriptor",
    "finish_allocation_frame", "assumeCapacity_allocation_frame", "run_allocation_frame",
    "finish_word_frame", "assumeCapacity_word_frame", "run_word_frame", "owner_parent_borrow")]
CLAIMS += [NS + "Append.Execution.Tests." + name for name in (
    "capacity_prefix", "reached_prefix", "actual_first_append", "actual_owner_first_append", "first_without_final_premises", "derived_readback",
    "spare_uses_same_run", "spare_without_final_premises", "oom_skips_assignment", "derived_owner_oom",
    "malformed_arguments_keep_length_and_item", "malformed_id_keeps_arguments", "malformed_sequence_keeps_id", "partial_descriptor_is_not_complete",
    "length_read_precedes_capacity_oom", "missing_pointer_keeps_length_store", "readonly_length_precedes_pointer_read",
    "readonly_growth_retains_reservation", "invalid_region_keeps_effects", "length_overflow_is_rejection_before_allocator",
    "nonempty_growth_remains_unsupported", "missing_saved_view_precedes_remap", "parent_survives_all_outcomes")]
PROBES = {"layout": ROOT / "test/lean/representative_array_layout.zig",
          "reader": ROOT / "test/lean/representative_array.zig"}


def inputs():
    saved = check_compiler.snapshot()
    saved.update({str(path.relative_to(ROOT)): digest(path) for path in (ROOT / "test/lean").rglob("*.py")})
    saved.update({str(path.relative_to(ROOT)): digest(path) for path in PROBES.values()})
    return saved


def check_growth_allocator(first, new_capacity):
    for key, expected in (("allocated_bytes", new_capacity * 32), ("allocations", 1), ("allocation_calls", 2), ("requested_bytes", new_capacity * 32),
            ("requested_alignment", 8), ("resize_calls", 0), ("remap_calls", 0), ("free_calls", 0)):
        if type(first[key]) is not int or first[key] != expected:
            raise ValueError("changed native first-growth allocator effects: " + key)


def check_first_growth(first, new_capacity):
    if (not isinstance(first, dict) or set(first) != {"before", "noop", "noop_skipped_allocator", "oom_reported", "oom_induced",
            "failed", "after", "unchanged", "allocated_bytes", "allocations", "allocation_calls", "requested_bytes",
            "requested_alignment", "resize_calls", "remap_calls", "free_calls"} or
            any(first[key] is not True for key in ("noop_skipped_allocator", "oom_reported", "oom_induced"))):
        raise ValueError("incomplete native first-growth outcomes")
    for key in ("before", "noop", "failed", "after", "unchanged"):
        record = first[key]
        if (not isinstance(record, dict) or set(record) != {"pointer", "length", "capacity"} or
                any(type(value) is not int for value in record.values()) or not 0 <= record["pointer"] < 2**64 or
                record["length"] != 0 or record["capacity"] != (new_capacity if key in ("after", "unchanged") else 0)):
            raise ValueError("changed native first-growth header: " + key)
    if first["noop"] != first["before"] or first["failed"] != first["before"] or first["unchanged"] != first["after"]:
        raise ValueError("native first-growth OOM or unchanged branch changed header")
    check_growth_allocator(first, new_capacity)
    return first["after"]["pointer"], new_capacity * 32, 8


def check_capacity_selection(selection):
    if (not isinstance(selection, dict) or set(selection) != {"arch", "cache_line", "samples", "first_growth",
            "overflow_oom", "overflow_before", "overflow_after"} or selection["arch"] != "aarch64" or
            type(selection["cache_line"]) is not int or selection["cache_line"] != 128 or selection["overflow_oom"] is not True):
        raise ValueError("incomplete native capacity selection")
    minima = (0, 1, 2, 3, 8, 2**63 - 1, 2**64 - 2, 2**64 - 1)
    samples = selection["samples"]
    if not isinstance(samples, list) or len(samples) != len(minima):
        raise ValueError("incomplete native capacity samples")
    for row, minimum in zip(samples, minima):
        if (not isinstance(row, dict) or set(row) != {"minimum", "capacity"} or
                any(type(v) is not int for v in row.values()) or row["minimum"] != minimum or
                row["capacity"] != min(2**64 - 1, minimum + minimum // 2 + 4)):
            raise ValueError("native capacity policy changed")
    for name in ("overflow_before", "overflow_after"):
        row = selection[name]
        if (not isinstance(row, dict) or set(row) != {"pointer", "length", "capacity"} or
                any(type(v) is not int for v in row.values()) or not 0 <= row["pointer"] < 2**64 or
                row["length"] != 0 or row["capacity"] != 0):
            raise ValueError("native capacity overflow header changed")
    if selection["overflow_before"] != selection["overflow_after"]:
        raise ValueError("native capacity overflow mutated header")
    return check_first_growth(selection["first_growth"], 5)


def check_growing_append(append, profile, records):
    if (not isinstance(append, dict) or set(append) != {"before", "failed", "after", "oom_reported", "oom_induced",
            "allocated_bytes", "allocations", "allocation_calls", "requested_bytes", "requested_alignment",
            "resize_calls", "remap_calls", "free_calls", "record", "parent_after"} or
            append["oom_reported"] is not True or append["oom_induced"] is not True):
        raise ValueError("incomplete native growing append")
    for name in ("before", "failed", "after"):
        row = append[name]
        if (not isinstance(row, dict) or set(row) != {"pointer", "length", "capacity"} or
                any(type(v) is not int for v in row.values()) or not 0 <= row["pointer"] < 2**64 or
                row["length"] != (1 if name == "after" else 0) or row["capacity"] != (5 if name == "after" else 0)):
            raise ValueError("native growing append header changed")
    if append["before"] != append["failed"]:
        raise ValueError("native growing append OOM mutated header")
    check_growth_allocator(append, 5)
    expected = {"pointer": append["after"]["pointer"], "readonly": True, "item_pointer": records[4]["item_pointer"],
        "arguments_pointer": profile["parent_pointer"] + 4, "arguments_length": 2, "arguments": [3, 2],
        "id": 0, "sequence_number": 29}
    if json.dumps(append["record"], sort_keys=True) != json.dumps(expected, sort_keys=True):
        raise ValueError("native growing append descriptor changed")
    if json.dumps(append["parent_after"]) != json.dumps(profile["parent_before"]):
        raise ValueError("native growing append changed parent borrow")
    return append["after"]["pointer"], 160, 8


def check_rows(records, data, expected_arguments, sequences):
    regions = []
    if not isinstance(records, list) or len(records) != len(expected_arguments):
        raise ValueError("incomplete native representative inventory")
    row_keys = {"pointer", "readonly", "item_pointer", "arguments_pointer", "arguments_length",
        "arguments", "id", "sequence_number"}
    for index, (record, arguments) in enumerate(zip(records, expected_arguments)):
        if (not isinstance(record, dict) or set(record) != row_keys or record["readonly"] is not True or
                any(type(record[key]) is not int for key in row_keys - {"readonly", "arguments"}) or
                not isinstance(record["arguments"], list) or
                any(type(value) is not int for value in record["arguments"]) or record["arguments"] != arguments or
                record["arguments_length"] != len(arguments) or record["id"] != index or
                record["sequence_number"] != sequences[index]):
            raise ValueError("incomplete or changed native representative fields: " + str(index))
        if type(data) is not int or record["pointer"] != data + index * 32:
            raise ValueError("native representative lost its exact backing offset")
        regions.append((record["item_pointer"], 224, 16))
        if arguments:
            regions.append((record["arguments_pointer"], len(arguments) * 4, 4))
        elif not 0 <= record["arguments_pointer"] < 2**64:
            raise ValueError("invalid empty argument sentinel representation")
    return regions


def check_owned_append(owned, owner_size):
    if (type(owned) is not dict or set(owned) != {"owner_pointer", "before", "first_header", "first", "after", "rows",
            "length_rejected", "capacity_rejected"} or owned["length_rejected"] is not True or owned["capacity_rejected"] is not True):
        raise ValueError("incomplete owned first/spare append observations")
    for label, length, capacity in (("before", 0, 0), ("first_header", 1, 5), ("after", 2, 5)):
        header = owned[label]
        if (type(header) is not dict or set(header) != {"pointer", "length", "capacity"} or
                any(type(value) is not int for value in header.values()) or not 0 <= header["pointer"] < 2**64 or
                header["length"] != length or header["capacity"] != capacity):
            raise ValueError("changed owned append header: " + label)
    data = owned["after"]["pointer"]
    if owned["first_header"]["pointer"] != data:
        raise ValueError("owned spare append changed its backing")
    regions = check_rows(owned["rows"], data, ([], [0]), (0, 0))
    if json.dumps(owned["first"], sort_keys=True) != json.dumps(owned["rows"][0], sort_keys=True):
        raise ValueError("owned spare append changed its old row")
    return regions + [(owned["owner_pointer"], owner_size, 8), (data, 160, 8)]


def check_observations(profile, mode):
    keys = {"schema", "zigVersion", "mode", "backend", "header_pointer", "header_bytes", "header_alignment",
        "owner_pointer", "owner_bytes", "owner_alignment", "allocator_pointer", "expressions_pointer",
        "items_pointer", "length", "capacity", "element_bytes", "element_alignment", "empty_rejected",
        "before_append_length", "before_append_capacity", "before_append_pointer", "append_size_increased",
        "parent_pointer", "parent_before", "parent_after", "parent_offset", "parent_length",
        "append_capacity_unchanged", "append_backing_unchanged", "append_id_matches_previous_length",
        "length_rejected", "capacity_rejected", "maximum_rejected", "cache_hit", "cache_hit_size_unchanged", "representatives", "copy", "publication", "first_growth", "capacity_selection", "growing_append", "owned_append"}
    if (not isinstance(profile, dict) or set(profile) != keys or
            profile["schema"] != "oksolc.representative-array-observations.v11" or profile["zigVersion"] != "0.17.0" or
            profile["mode"] != mode or profile["backend"] != "stage2_llvm"):
        raise ValueError("unsupported native representative observations")
    owner_size, _ = admission.CAPTURED[mode]
    for key, value in (("owner_bytes", owner_size), ("owner_alignment", 8), ("header_bytes", 24 if mode == "ReleaseFast" else 32), ("header_alignment", 8), ("element_bytes", 32),
            ("element_alignment", 8), ("length", 5)):
        if type(profile[key]) is not int or profile[key] != value:
            raise ValueError("changed representative extent/alignment: " + key)
    capacity = profile["capacity"]
    if type(capacity) is not int or not profile["length"] < capacity < 2**32:
        raise ValueError("representative reader fixture lost bounded spare capacity")
    for key in ("empty_rejected", "length_rejected", "capacity_rejected", "maximum_rejected", "cache_hit", "cache_hit_size_unchanged",
            "append_size_increased", "append_capacity_unchanged", "append_backing_unchanged", "append_id_matches_previous_length"):
        if profile[key] is not True:
            raise ValueError("native representative bound did not reject: " + key)
    owner, data = profile["owner_pointer"], profile["items_pointer"]
    if (type(owner) is not int or
            any(type(profile[key]) is not int or profile[key] != owner + offset
                for key, offset in (("allocator_pointer", 0), ("header_pointer", 16), ("expressions_pointer", 40 if mode == "ReleaseFast" else 48)))):
        raise ValueError("native owner fields lost their exact embedded offsets")
    for key, value in (("before_append_length", 4), ("before_append_capacity", capacity), ("before_append_pointer", data)):
        if type(profile[key]) is not int or profile[key] != value:
            raise ValueError("native spare-capacity append observation changed: " + key)
    for key in ("parent_before", "parent_after"):
        if (not isinstance(profile[key], list) or len(profile[key]) != 4 or
                any(type(value) is not int for value in profile[key]) or profile[key] != [777, 3, 2, 5]):
            raise ValueError("native parent borrow contents changed: " + key)
    for key, expected in (("parent_offset", 1), ("parent_length", 2)):
        if type(profile[key]) is not int or profile[key] != expected:
            raise ValueError("native parent borrow view changed: " + key)
    regions = [(owner, owner_size, 8), (data, capacity * 32, 8), (profile["parent_pointer"], 16, 4)]
    regions.append(check_first_growth(profile["first_growth"], 3))
    regions.append(check_capacity_selection(profile["capacity_selection"]))
    records = profile["representatives"]
    regions.extend(check_rows(records, data, ([], [], [0], [1], [3, 2]), (0, 0, 0, 0, 23)))
    regions.extend(check_owned_append(profile["owned_append"], owner_size))
    regions.append(check_growing_append(profile["growing_append"], profile, records))
    copied = profile["copy"]
    if (not isinstance(copied, dict) or set(copied) !=
            {"source_before", "header_before", "target_pointer", "target_capacity", "copied"} or
            type(copied["target_pointer"]) is not int or type(copied["target_capacity"]) is not int or
            copied["target_capacity"] != profile["length"] + 2):
        raise ValueError("incomplete native prefix-copy observation")
    # JSON equality retains scalar types: Python's True == 1 is insufficient.
    for label, observed, expected in (
            ("source", copied["source_before"], records),
            ("header", copied["header_before"], {"pointer": data, "length": profile["length"], "capacity": capacity}),
            ("destination", copied["copied"], [dict(record, pointer=copied["target_pointer"] + index * 32)
                for index, record in enumerate(records)])):
        if json.dumps(observed, sort_keys=True) != json.dumps(expected, sort_keys=True):
            raise ValueError("native prefix copy changed " + label)
    published = profile["publication"]
    if (not isinstance(published, dict) or set(published) != {"before", "after", "representatives"} or
            not isinstance(published["after"], dict) or set(published["after"]) != {"pointer", "length", "capacity"} or
            type(published["after"]["pointer"]) is not int):
        raise ValueError("incomplete native publication observation")
    final = published["after"]
    for label, observed, expected in (
            ("initial header", published["before"], {"pointer": copied["target_pointer"], "length": 5, "capacity": 7}),
            ("final header", final, {"pointer": final["pointer"], "length": 5, "capacity": 10}),
            ("descriptors", published["representatives"], [dict(record, pointer=final["pointer"] + index * 32)
                for index, record in enumerate(records)])):
        if json.dumps(observed, sort_keys=True) != json.dumps(expected, sort_keys=True):
            raise ValueError("native publication changed " + label)
    # The old scratch allocation may have been released or remapped. Check
    # each observation's live extent independently, never their mutual overlap.
    for backing in ((copied["target_pointer"], 7 * 32, 8), (final["pointer"], 10 * 32, 8)):
        live = regions + [backing]
        if (any(type(base) is not int or not 0 < base < 2**64 or base + size > 2**64 or base % alignment
                for base, size, alignment in live) or
                any(not (a + size <= b or b + other <= a)
                    for index, (a, size, _) in enumerate(live) for b, other, _ in live[index + 1:])):
            raise ValueError("invalid, misaligned or aliased native representative backing")


def audit(output, env, lean):
    checked = check_word_swap.audit(output, env, lean, MODULE, CLAIMS)
    records = json.loads((output / "audit.json").read_bytes())["claims"]
    dependencies = {record["theorem"]: set(record["dependencies"]) for record in records}
    required = {
        MEM + "recordView_result_parent": {MEM + "recordView_address", MEM + "recordView_parent"},
        NS + "initializeFields_reached_iff": {NS + "initializeFields", NS + "initializeFieldsReached"},
        NS + "writeFields_storage": {NS + "writeFields", MEM + "store_retains_shape", MEM + "store_preserves_valid", MEM + "heap_after_store_other"},
        NS + "Append.Execution.assumeCapacity_of_spare": {NS + "Append.appendWithoutGrowth", NS + "Append.Execution.assumeCapacity", NS + "Append.Execution.finish_success_iff"},
        NS + "Append.Execution.first_verified": {NS + "Capacity.first_verified", NS + "Owner.appendWithoutGrowth_framed", NS + "Append.Execution.assumeCapacity_of_spare", NS + "Append.Execution.owner_length_from_items"},
        NS + "Append.Execution.first_oom": {NS + "Capacity.first_oom", NS + "Append.Execution.owner_length_from_items", NS + "readItemsData_from_loaded"},
        NS + "Append.Execution.spare_verified": {NS + "Owner.appendWithoutGrowth_framed", NS + "Capacity.ensure_unchanged", NS + "Append.nextLength_bounded", NS + "Append.Execution.assumeCapacity_of_spare"},
        NS + "Append.Execution.finish_word_frame": {NS + "Append.Execution.selected_descriptor_parent", NS + "Append.Execution.word_array_has_no_descriptor", NS + "writeFields_storage", MEM + "recordView_result_parent"},
        NS + "Append.Execution.run_word_frame": {NS + "Capacity.ensure_storage", NS + "Append.Execution.assumeCapacity_allocation_frame", NS + "Append.Execution.run_allocation_frame", MEM + "valid_lookup"},
        NS + "Append.Execution.owner_parent_borrow": {NS + "Append.Execution.run_word_frame", NS + "Append.Execution.run_valid", MEM + "Heap.lookup_ne_of_type_ne", MEM + "load_eq_of_lookup"},
        NS + "Append.Execution.Tests.derived_readback": {NS + "Append.Execution.Tests.first_without_final_premises", NS + "Append.Execution.Tests.actual_owner_first_append"},
        NS + "Append.Execution.Tests.spare_without_final_premises": {NS + "Append.Execution.spare_verified"},
        NS + "Append.Execution.Tests.parent_survives_all_outcomes": {NS + "Append.Execution.owner_parent_borrow"},
        NS + "Capacity.ensure_growing": {NS + "Capacity.ensure", NS + "Capacity.grow", NS + "Growth.run", NS + "Append.hasCapacity"},
        NS + "Capacity.first_verified": {NS + "Capacity.ensure_growing", NS + "Capacity.grow_positive", NS + "Growth.run_verified"},
        NS + "Capacity.first_oom": {NS + "Capacity.ensure_growing", NS + "Growth.run_oom"},
        NS + "Capacity.ensure_storage": {NS + "Growth.run_storage"},
        NS + "Capacity.ensure_parent_borrow": {NS + "Capacity.ensure_storage", MEM + "WordAllocation.source_older", MEM + "load_eq_of_lookup"},
        NS + "Capacity.Tests.derived_header_and_storage": {NS + "Capacity.Tests.derived_first_growth", NS + "Capacity.Tests.actual_first_growth"},
        NS + "Append.append_at_framed": {NS + "Append.readItems_after_length_store_at", NS + "Append.readCapacity_after_length_store_at",
            NS + "initializeFields_stores", NS + "Append.append_of_steps", MEM + "heap_after_store_other"},
        NS + "Owner.length_store_total": {MEM + "root_access", NS + "Owner.header_region_access", MEM + "fieldPointer_of_access",
            MEM + "store_subobject_total", MEM + "Value.usize_valid"},
        NS + "Owner.appendWithoutGrowth_framed": {NS + "Owner.length_store_total", NS + "Owner.root_header_pointer",
            NS + "Owner.root_header_fields", NS + "Append.append_at_framed", MEM + "Heap.lookup_ne_of_type_ne"},
        NS + "Owner.append_parent_borrow": {NS + "Owner.appendWithoutGrowth_framed", MEM + "Heap.lookup_ne_of_type_ne",
            MEM + "load_eq_of_lookup", MEM + "WordArray.Represents"},
        NS + "Owner.AppendTests.append_without_final_premises": {NS + "Owner.appendWithoutGrowth_framed"},
        NS + "Owner.AppendTests.derived_readback": {NS + "Owner.AppendTests.append_without_final_premises", NS + "Owner.AppendTests.actual_append"},
        NS + "Owner.AppendTests.parent_survives_same_append": {NS + "Owner.append_parent_borrow", NS + "Owner.AppendTests.actual_append"},
        MEM + "recordView_parent": {MEM + "recordView", MEM + "access", MEM + "acceptsView"},
        NS + "header_after_stores": {MEM + "root_fieldPointer", MEM + "fieldPointer_after_store",
            MEM + "load_disjoint_after_store", MEM + "load_alias_after_store"},
        NS + "representative_from_array": {NS + "representative", NS + "readItems", MEM + "array_access",
            MEM + "recordView", MEM + "pointerCast", MEM + "sliceElementPointer",
            "Compiler.Extraction.Storage.representativeProgram"},
        NS + "Tests.source_pointer_derivation": {NS + "representative_from_array", MEM + "State.valid"},
        NS + "Tests.source_header_store_derivation": {NS + "header_after_stores", MEM + "store"},
        "Compiler.Extraction.Expression.fields_after_subobject_stores": {MEM + "fieldPointer_after_store",
            MEM + "load_disjoint_after_store", MEM + "load_alias_after_store"},
        NS + "fields_after_array_stores": {NS + "element_fieldPointer", MEM + "array_access",
            "Compiler.Extraction.Expression.fields_after_subobject_stores"},
        NS + "readItems_after_other_store": {MEM + "fieldPointer_after_store", MEM + "fieldPointer_address",
            MEM + "load_other_after_store"},
        NS + "representativeFields_after_stores": {NS + "representative_from_array", NS + "fields_after_array_stores",
            NS + "readItems_after_other_store", MEM + "store_retains_shape", MEM + "store_preserves_valid"},
        NS + "FieldTests.source_bound_complete_observation": {NS + "representativeFields_after_stores",
            NS + "FieldTests.four_actual_stores", NS + "FieldTests.initial_valid"},
        MEM + "Cells.write_subobject_total": {MEM + "Cells.write_root", MEM + "Cells.write_success", MEM + "Value.leaves_shift"},
        NS + "field_store_total": {MEM + "array_access", MEM + "access_subregion", MEM + "Cells.write_subobject_total", MEM + "store_of_access"},
        NS + "initializeFields_stores": {NS + "field_store_total", MEM + "store_retains_shape", MEM + "store_preserves_valid"},
        NS + "initializeFields_verified": {NS + "initializeFields_stores", NS + "initializeFields_of_stores", NS + "fields_after_array_stores"},
        NS + "representativeFields_after_initialization": {NS + "initializeFields_stores", NS + "initializeFields_of_stores",
            NS + "representativeFields_after_stores", MEM + "WordArray.number_valid"},
        NS + "WriteTests.actual_source_bound_readback": {NS + "WriteTests.source_bound_initialization",
            NS + "WriteTests.actual_four_store_execution", NS + "representativeFields_after_initialization"},
        MEM + "Cells.read_slice_after_length_write": {MEM + "Cells.readLeaf_hasType", MEM + "Cells.write_success",
            MEM + "Cells.lookup_set_other"},
        MEM + "load_slice_after_length_store": {MEM + "Cells.read_slice_after_length_write", MEM + "store_success", MEM + "access_replace_cells"},
        NS + "Append.length_store_total": {MEM + "access_read_write", MEM + "access_subregion", MEM + "Cells.write_subobject_total",
            MEM + "Value.usize_valid", MEM + "root_fieldPointer", MEM + "store_of_access"},
        NS + "Append.nextLength_bounded": {MEM + "valid_lookup"},
        NS + "Append.appendWithoutGrowth_verified": {NS + "Append.nextLength_bounded", NS + "Append.length_store_total",
            NS + "Append.readItems_after_length_store_at", NS + "Append.readCapacity_after_length_store_at", NS + "initializeFields_stores",
            NS + "Append.append_of_steps", NS + "readField_after_other_store", NS + "element_pointer", NS + "element_record_view"},
        NS + "Append.representativeFields_after_append": {NS + "Append.appendWithoutGrowth_verified", NS + "representative_from_array"},
        NS + "Append.Tests.actual_source_bound_append": {NS + "Append.Tests.source_bound_append", NS + "Append.Tests.actual_append",
            NS + "Append.representativeFields_after_append"},
        MEM + "WordArray.write_allocation_frame": {MEM + "heap_after_store_other", MEM + "store_keeps_counters"},
        MEM + "load_other_after_store": {MEM + "heap_after_store_other", MEM + "load_eq_of_lookup"},
        NS + "Append.appendWithoutGrowth_framed": {MEM + "heap_after_store_other", MEM + "store_keeps_counters", MEM + "Heap.lookup_ne_of_type_ne"},
        NS + "Append.append_parent_borrow": {NS + "Append.appendWithoutGrowth_framed", MEM + "Heap.lookup_ne_of_type_ne", MEM + "load_eq_of_lookup", MEM + "WordArray.Represents"},
        NS + "Append.BorrowTests.actual_persistent_parent": {NS + "Append.append_parent_borrow", NS + "Append.Tests.actual_append"},
        MEM + "root_access": {MEM + "valid_lookup", MEM + "access"},
        MEM + "root_fieldPointer": {MEM + "root_access", MEM + "fieldPointer"},
        NS + "Owner.header_region_access": {MEM + "access_subregion", NS + "Owner.headerAddress"},
        NS + "Owner.root_header_region": {MEM + "root_access", NS + "Owner.header_region_access", NS + "Owner.layout_checked"},
        NS + "Owner.Tests.header_from_declared_owner": {NS + "Owner.root_header_region", NS + "Owner.Tests.initial_valid"},
        NS + "Owner.Tests.nonzero_owner_offset_retains_parent": {NS + "Owner.header_region_access"},
        MEM + "fieldPointer_of_access": {MEM + "fieldPointer"},
        MEM + "array_access_permitted": {MEM + "valid_lookup", MEM + "access"},
        MEM + "store_subobject_total": {MEM + "Cells.write_subobject_total", MEM + "store_of_access"},
        NS + "header_after_subobject_stores": {MEM + "fieldPointer_after_store", MEM + "load_disjoint_after_store", MEM + "load_alias_after_store"},
        NS + "Owner.header_pointer": {MEM + "fieldPointer_of_access", NS + "Owner.view_layout_checked", NS + "Owner.header_field_checked"},
        NS + "Owner.root_owner_view": {MEM + "root_access", MEM + "recordView", MEM + "acceptsView_self"},
        NS + "Owner.array_header_pointer": {MEM + "array_access_permitted", MEM + "acceptsView_array", NS + "Owner.header_pointer"},
        NS + "Owner.root_header_fields": {MEM + "root_access", NS + "Owner.header_region_access", MEM + "fieldPointer_of_access"},
        NS + "Owner.header_store_total": {MEM + "root_access", NS + "Owner.header_region_access", MEM + "access_subregion",
            MEM + "store_subobject_total", NS + "Owner.header_value_views_checked", NS + "Owner.header_leaf_types_checked"},
        NS + "Owner.initializeHeader_verified": {NS + "Owner.header_store_total", NS + "Owner.root_header_pointer", NS + "Owner.root_header_fields",
            NS + "header_after_subobject_stores", MEM + "store_preserves_valid", MEM + "store_retains_shape", MEM + "store_keeps_counters",
            MEM + "heap_after_store_other"},
        NS + "Owner.FieldTests.header_assignment_without_store_premises": {NS + "Owner.initializeHeader_verified"},
        NS + "Owner.FieldTests.nonzero_assignment_preserves_first_header": {NS + "Owner.array_header_pointer", NS + "Owner.initializeHeader"},
    }
    required.update({
        NS + "Backing.reserve_verified": {MEM + "RegionAllocation." + name for name in
            ("Fits", "reserve_admitted", "extend_valid", "extend_shape", "extend_lookup")},
        NS + "Backing.reserve_parent_borrow": {MEM + "RegionAllocation.reserve_heap_other", MEM + "load_eq_of_lookup", MEM + "WordAllocation.source_older"},
        NS + "Backing.Tests.admitted_without_final_premises": {NS + "Backing.reserve_verified", NS + "Backing.Tests.fits"},
        NS + "Backing.Tests.offset_parent_survives": {NS + "Backing.reserve_parent_borrow", NS + "Backing.Tests.actual_request"},
    })
    required.update({
        MEM + "load_hasType": {MEM + "Cells.read_hasType", MEM + "access"},
        NS + "Copy.readField_hasType": {MEM + "load_hasType", MEM + "fieldPointer_address"},
        NS + "Copy.readField_after_slot_store": {MEM + "Value.leaf_offsets", NS + "Copy.slot_offsets_apart", MEM + "store_success"},
        NS + "Copy.fields_verified": {NS + "field_store_total", NS + "Copy.readField_hasType", NS + "Copy.field_store_readback",
            NS + "Copy.fields_read_frame", MEM + "store_retains_shape"},
        NS + "Copy.copyFrom_verified": {NS + "Copy.fields_verified", NS + "Copy.copyFrom_read_frame", NS + "Copy.fields_storage"},
        NS + "Copy.run_verified": {NS + "Copy.copyFrom_verified", NS + "Copy.run_storage"},
        NS + "Copy.run_parent_borrow": {MEM + "Heap.lookup_ne_of_type_ne", MEM + "load_eq_of_lookup", NS + "Copy.run_storage"},
        NS + "Copy.Tests.copy_without_success_premise": {NS + "Copy.run_verified", NS + "Copy.Tests.initialized_source"},
        NS + "Copy.Tests.complete_readback_from_copy": {NS + "Copy.readFields_eq_of_slots", NS + "Copy.Tests.copy_without_success_premise", NS + "Copy.Tests.actual_complete_copy"},
        NS + "Copy.Tests.untouched_spare_fields": {NS + "Copy.run_read_frame"},
        MEM + "Cells.read_slice_after_pointer_write": {MEM + "Cells.read_slice_parts", MEM + "Cells.read_slice_of_parts",
            MEM + "Cells.readLeaf_after_single_write"},
        NS + "Publication.owner_pointer_store_total": {MEM + "store_subobject_total", NS + "Owner.header_leaf_types_checked"},
        NS + "Publication.header_after_pointer_capacity_stores": {MEM + "load_slice_after_pointer_store", MEM + "load_disjoint_after_store",
            MEM + "load_alias_after_store", MEM + "fieldPointer_after_store"},
        NS + "Publication.run_verified": {NS + "Publication.owner_pointer_store_total", NS + "Owner.header_store_total",
            NS + "Publication.run_of_stores", NS + "Publication.run_storage", NS + "Publication.header_after_pointer_capacity_stores"},
        NS + "Publication.run_of_stores": {NS + "Publication.program", NS + "Publication.steps", NS + "Publication.write", MEM + "fieldPointer_after_store"},
        NS + "Publication.run_parent_borrow": {MEM + "Heap.lookup_ne_of_type_ne", MEM + "load_eq_of_lookup", NS + "Publication.run_storage"},
        NS + "Publication.Tests.publication_without_store_premises": {NS + "Publication.run_verified"},
        NS + "Publication.Tests.readback_from_publication": {NS + "Publication.Tests.publication_without_store_premises", NS + "Publication.Tests.actual_publication"},
        NS + "readField_eq_of_lookup": {MEM + "fieldPointer_eq_of_lookup", MEM + "load_eq_of_lookup", MEM + "fieldPointer_address"},
        NS + "readItemsData_from_loaded": {NS + "Owner.root_header_fields", NS + "Publication.owner_pointer_selector",
            MEM + "Cells.read_slice_parts", MEM + "access_subregion"},
        NS + "Growth.lock_rejected": {NS + "Owner.NativeLock.checkHeader", NS + "Growth.prepare"},
        NS + "Growth.run_verified": {NS + "Backing.reserve_verified", NS + "Publication.run_verified",
            NS + "readItemsData_from_loaded", NS + "allocatedSlice_empty", NS + "readField_eq_of_lookup",
            NS + "Growth.run_first", NS + "Growth.first_of_reservation_and_publication"},
        NS + "Growth.run_oom": {NS + "allocatedSlice_empty", NS + "Growth.run_first", NS + "Growth.first_oom", MEM + "RegionAllocation.reserve_failed"},
        NS + "Growth.run_parent_borrow": {NS + "Growth.run_storage", MEM + "load_eq_of_lookup", MEM + "WordAllocation.source_older"},
        NS + "Growth.Tests.growth_without_final_premises": {NS + "Growth.run_verified", NS + "Growth.Tests.fits"},
        NS + "Growth.Tests.header_and_backing_from_growth": {NS + "Growth.Tests.growth_without_final_premises", NS + "Growth.Tests.actual_first_growth"},
        NS + "Growth.Tests.oom_before_length_read": {NS + "Growth.run_oom"},
        NS + "Growth.Tests.all_outcomes_preserve_parent": {NS + "Growth.run_parent_borrow"},
    })
    for claim, entries in required.items():
        if not entries <= dependencies[claim]:
            raise ValueError("representative proof lost dependencies: " + claim)
    return {**checked, "checkedDependencies": sorted(required)}


def controls(output, env, lean, *, names=None):
    source = "import Compiler.Extraction.ExpressionFieldTests\nimport Compiler.Extraction.StorageRead\n"
    source += "import Compiler.ZigAir.MemoryArrayGeometry\nimport Compiler.ZigAir.MemoryAllocationShape\n"
    source += "import Compiler.ZigAir.MemoryWordArray\nimport Compiler.ZigAir.MemoryOptionalPointerTests\n"
    source += "import Compiler.ZigAir.MemorySliceUpdates\n"
    source += "import Compiler.ZigAir.MemoryWordArrayWrites\nimport Compiler.ZigAir.MemoryWordAllocationProofs\nimport Compiler.ZigAir.MemoryRelease\n"
    source += "set_option pp.maxSteps 8\nset_option pp.deepTerms false\nset_option pp.notation false\n"
    for name in ("ZigAir/MemoryRecordViews.lean", "Extraction/RepresentativeArrayLayout.lean",
            "Extraction/StorageProgram.lean", "Extraction/RepresentativeArray.lean", "Extraction/RepresentativeArrayTests.lean",
            "Extraction/RepresentativeArrayFields.lean", "Extraction/RepresentativeArrayFieldTests.lean",
            "Extraction/RepresentativeArrayWrites.lean", "Extraction/RepresentativeArrayWriteTests.lean",
            "Extraction/RepresentativeAppendProgram.lean", "Extraction/RepresentativeArrayAppend.lean", "Extraction/RepresentativeArrayAppendTests.lean",
            "Extraction/RepresentativeArrayBorrowFrame.lean", "Extraction/RepresentativeArrayBorrowFrameTests.lean",
            "Extraction/ExpressionMapLayout.lean", "Extraction/RepresentativeOwnerLayout.lean", "Extraction/RepresentativeOwner.lean", "Extraction/RepresentativeOwnerTests.lean",
            "Extraction/RepresentativeOwnerFields.lean", "Extraction/RepresentativeOwnerWrites.lean", "Extraction/RepresentativeOwnerFieldTests.lean",
            "Extraction/ExpressionMapEmpty.lean", "Extraction/ExpressionMapInitialization.lean", "Extraction/RepresentativeOwnerLock.lean",
            "Extraction/RepresentativeArrayAllocation.lean", "Extraction/RepresentativeArrayAllocationTests.lean",
            "Extraction/RepresentativeArrayCopy.lean", "Extraction/RepresentativeArrayCopyFrame.lean",
            "Extraction/RepresentativeArrayCopyProofs.lean", "Extraction/RepresentativeArrayCopyTests.lean",
            "Extraction/RepresentativePublicationProgram.lean", "Extraction/RepresentativeArrayPublication.lean",
            "Extraction/RepresentativePublicationProofs.lean", "Extraction/RepresentativePublicationTests.lean",
            "Extraction/RepresentativeArrayAllocationView.lean", "Extraction/RepresentativeGrowthProgram.lean",
            "Extraction/RepresentativeArrayGrowth.lean", "Extraction/RepresentativeGrowthProofs.lean",
            "Extraction/RepresentativeGrowthStorage.lean", "Extraction/RepresentativeGrowthTests.lean",
            "Extraction/RepresentativeOwnerAppend.lean", "Extraction/RepresentativeOwnerAppendTests.lean",
            "Extraction/RepresentativeCapacityProgram.lean", "Extraction/RepresentativeArrayCapacity.lean", "Extraction/RepresentativeCapacityTests.lean",
            "Extraction/RepresentativeAppendExecution.lean", "Extraction/RepresentativeGrowingAppend.lean",
            "Extraction/RepresentativeAppendFrame.lean", "Extraction/RepresentativeGrowingAppendTests.lean"):
        source += without_imports((ROOT / "lean/Compiler" / name).read_text()) + "\n"
    mutations = (
            ("native-lock-mode-bypass", "if cell.type = viewType true then checkUnlocked true state", "if cell.type = viewType true then checkUnlocked false state"),
            ("precise-growth-ignores-lock", "  Owner.NativeLock.checkHeader state header\n  if capacity", "  if capacity"),
            ("reached-fields-rewind-on-rejection", "    | .ok after => writeFields after lifetime index rest",
             "    | .ok after =>\n      let (result, reached) := writeFields after lifetime index rest\n      match result with\n      | .error fault => (.error fault, state)\n      | .ok () => (.ok (), reached)"),
            ("growing-append-bypasses-capacity", "    let ((capacity, ready), reached) := ensure state header newLength effects",
             "    let ((capacity, ready), reached) : (Except ε (Option Unit) × State) × σ := ((.ok (some ()), state), effects)"),
            ("growing-append-rewinds-assignment-fault", "      | .error fault => ((.error (reject fault), after), reached)",
             "      | .error fault => ((.error (reject fault), state), reached)"),
            ("growing-append-discards-private-effects", "      | .ok () => ((.ok (some ()), after), reached)",
             "      | .ok () => ((.ok (some ()), after), effects)"),
            ("growing-append-oom-is-not-success", "    match capacity with\n    | .error fault => ((.error fault, ready), reached)\n    | .ok none => ((.ok none, ready), reached)",
             "    match capacity with\n    | .error fault => ((.error fault, ready), reached)\n    | .ok none => ((.ok (some ()), ready), reached)"),
            ("reached-append-selects-before-length-store", "      | .ok ready => finish ready header newLength itemAddress argumentsAddress argumentsLength id sequence",
             "      | .ok ready => finish state header newLength itemAddress argumentsAddress argumentsLength id sequence"),
            ("reached-append-omits-length-store", "      match writeLength state header newLength with\n      | .error fault => (.error fault, state)",
             "      match (Except.ok state : Except Fault State) with\n      | .error fault => (.error fault, state)"),
            ("reached-append-prechecks-pointer", "      let newLength := nextLength length.toNat\n      if !hasCapacity capacity.toNat newLength then",
             "      let newLength := nextLength length.toNat\n      if readItems state header = .error .uninitialized then (.error .uninitialized, state) else\n      if !hasCapacity capacity.toNat newLength then"),
            ("growing-append-forges-owner-header", "  | .ok (.pointer _ header) => runWithCapacity reject ensure state header itemAddress argumentsAddress argumentsLength id sequence effects",
             "  | .ok (.pointer _ header) => runWithCapacity reject ensure state owner itemAddress argumentsAddress argumentsLength id sequence effects"),
            ("capacity-wrong-initial-policy", "def initialCapacity : Nat := max 1 (128 / 32)", "def initialCapacity : Nat := 1"),
            ("capacity-does-not-saturate", "min (Compiler.ZigAir.Memory.addressLimit - 1) (minimum + (minimum / 2 + initialCapacity))",
             "minimum + (minimum / 2 + initialCapacity)"),
            ("capacity-wrong-division", "min (Compiler.ZigAir.Memory.addressLimit - 1) (minimum + (minimum / 2 + initialCapacity))",
             "min (Compiler.ZigAir.Memory.addressLimit - 1) (minimum + (minimum / 3 + initialCapacity))"),
            ("capacity-applies-policy-before-check", "if Append.hasCapacity capacity.toNat minimum then", "if Append.hasCapacity capacity.toNat (grow minimum) then"),
            ("capacity-bypasses-selected-request", "  | .ok (some capacity) => Growth.run state header capacity allocate effects",
             "  | .ok (some capacity) => Growth.run state header minimum allocate effects"),
            ("capacity-discards-reached-effects", "  | .ok (some capacity) => Growth.run state header capacity allocate effects",
             "  | .ok (some capacity) =>\n    let (outcome, _) := Growth.run state header capacity allocate effects\n    (outcome, effects)"),
            ("owner-append-ignores-selected-header", "  Append.appendWithoutGrowth state header itemAddress argumentsAddress argumentsLength id sequence",
             "  Append.appendWithoutGrowth state owner itemAddress argumentsAddress argumentsLength id sequence"),
            ("owner-append-forges-selected-lifetime", "  Append.appendWithoutGrowth state header itemAddress argumentsAddress argumentsLength id sequence",
             "  Append.appendWithoutGrowth state ⟨owner.allocation + 1, header.offset⟩ itemAddress argumentsAddress argumentsLength id sequence"),
            ("owner-append-omits-descriptor", "  Append.appendWithoutGrowth state header itemAddress argumentsAddress argumentsLength id sequence", "  .ok state"),
            ("owner-append-frame-includes-owner", "after.nextId = state.nextId ∧ after.nextAddress = state.nextAddress ∧\n      (∀ other, other ≠ owner → other ≠ lifetime → after.heap.lookup other = state.heap.lookup other) := by\n  have location : headerAddress",
             "after.nextId = state.nextId ∧ after.nextAddress = state.nextAddress ∧\n      (∀ other, other ≠ lifetime → other ≠ lifetime → after.heap.lookup other = state.heap.lookup other) := by\n  have location : headerAddress"),
            ("growth-skips-equal-capacity", "if oldCapacity ≥ newCapacity then .unchanged else", "if oldCapacity > newCapacity then .unchanged else"),
            ("growth-wrong-empty-branch", "if oldCapacity = 0 then firstAllocation state header capacity allocate effects", "if oldCapacity = 1 then firstAllocation state header capacity allocate effects"),
            ("growth-conflates-unsupported-oom", "else ((.error .unsupported, state), effects)", "else ((.ok none, state), effects)"),
            ("growth-oom-becomes-rejection", "| .ok none => ((.ok none, ready), reached)\n  | .ok (some data)", "| .ok none => ((.error .memoryValidity, ready), reached)\n  | .ok (some data)"),
            ("growth-discards-allocation-on-read-fault", "match readItems ready header with\n    | .error fault => ((.error fault, ready), reached)", "match readItems ready header with\n    | .error fault => ((.error fault, state), reached)"),
            ("growth-discards-private-effects", "| .ok none => ((.ok none, ready), reached)\n  | .ok (some data)", "| .ok none => ((.ok none, ready), effects)\n  | .ok (some data)"),
            ("growth-discards-publication-rejection", "| .error fault => ((.error fault, afterPublication), reached)", "| .error fault => ((.ok (some ()), afterPublication), reached)"),
            ("growth-reads-length-before-oom", "  let ((reserved, ready), reached) := Backing.reserve state capacity allocate effects",
             "  if readItems state header = .error .uninitialized then ((.error .uninitialized, state), effects) else\n  let ((reserved, ready), reached) := Backing.reserve state capacity allocate effects"),
            ("allocation-view-reads-length", "  let .scalar (.int false 64 capacity) ← readField state header capacityOffset | .error .malformed",
             "  let .scalar (.int false 64 capacity) ← readField state header 8 | .error .malformed"),
            ("allocation-view-dereferences-empty-sentinel", "  if capacity = 0 then .ok (.slice itemsType data 0)\n  else makeSlice state itemsType pointer capacity.toNat",
             "  makeSlice state itemsType pointer capacity.toNat"),
            ("publication-order", "def program : List Update := [.itemsPointer, .capacity]", "def program : List Update := [.capacity, .itemsPointer]"),
            ("publication-omits-pointer", "def program : List Update := [.itemsPointer, .capacity]", "def program : List Update := [.capacity]"),
            ("publication-omits-capacity", "def program : List Update := [.itemsPointer, .capacity]", "def program : List Update := [.itemsPointer]"),
            ("publication-overwrites-length", "store state pointer (.pointer pointerType data)",
             "store state (.pointer (.pointer true false itemsType) ⟨header.allocation, header.offset + itemsOffset⟩) (.slice itemsType data 0)"),
            ("publication-wrong-pointer-field", "  fieldPointer state items 0\n", "  fieldPointer state items 8\n"),
            ("publication-wrong-capacity", "store state pointer (.scalar (.int false 64 capacity))", "store state pointer (.scalar (.int false 64 (capacity + 1)))"),
            ("publication-rolls-back-fault", "  steps program state header data capacity", "  let result := steps program state header data capacity\n  match result.1 with\n  | .ok () => result\n  | .error fault => (.error fault, state)"),
            ("copy-wrong-source-index", "    let (result, middle) := fields expressionSlots ⟨source, index * 32⟩ ⟨target, index * 32⟩ state", "    let (result, middle) := fields expressionSlots ⟨source, 0⟩ ⟨target, index * 32⟩ state"),
            ("copy-wrong-target-stride", "    let (result, middle) := fields expressionSlots ⟨source, index * 32⟩ ⟨target, index * 32⟩ state", "    let (result, middle) := fields expressionSlots ⟨source, index * 32⟩ ⟨target, index * 16⟩ state"),
            ("copy-omits-item-field", "    let (result, middle) := fields expressionSlots ⟨source, index * 32⟩ ⟨target, index * 32⟩ state", "    let (result, middle) := fields (expressionSlots.drop 1) ⟨source, index * 32⟩ ⟨target, index * 32⟩ state"),
            ("copy-skips-last-row", "else copyFrom source target length 0 state", "else copyFrom source target (length - 1) 0 state"),
            ("copy-reads-spare-row", "else copyFrom source target length 0 state", "else copyFrom source target (length + 1) 0 state"),
            ("copy-discards-fault-prefix", "| .error fault => (.error fault, middle)", "| .error fault => (.error fault, state)"),
            ("copy-accepts-overlap", "if source = target then (.error .memoryValidity, state) else copyFrom source target length 0 state",
             "copyFrom source target length 0 state"),
            ("copy-rejects-empty-sentinel", "if length = 0 then (.ok (), state) else", "if length = 0 then (.error .unallocated, state) else"),
            ("copy-requires-writable-source", "match Expression.readField state false source offset with", "match Expression.readField state true source offset with"),
            ("backing-nominal-type", "def type (capacity : Nat) : Ty := .array capacity Expression.allocationType",
             "def type (capacity : Nat) : Ty := .array capacity elementType"),
            ("backing-short-capacity", "def type (capacity : Nat) : Ty := .array capacity Expression.allocationType",
             "def type (capacity : Nat) : Ty := .array (capacity - 1) Expression.allocationType"),
            ("backing-missing-capacity-guard", "if capacity ≥ addressLimit then ((.error .malformed, state), effects) else\n  RegionAllocation.reserve",
             "if false then ((.error .malformed, state), effects) else\n  RegionAllocation.reserve"),
            ("backing-loses-parent", "  RegionAllocation.reserve state (type capacity) allocate effects",
             "  RegionAllocation.reserve {state with heap := []} (type capacity) allocate effects"),
            ("incorrect-bound", "def representativeProgram : Lookup := { bound := .ge, index := .requested }",
             "def representativeProgram : Lookup := { bound := .gt, index := .requested }"),
            ("incorrect-index", "def representativeProgram : Lookup := { bound := .ge, index := .requested }",
             "def representativeProgram : Lookup := { bound := .ge, index := .literal 0 }"),
            ("lost-live-subobject", "if !acceptsView cell.type address.offset target then .error .unsupported else", "if false then .error .unsupported else"),
            ("lost-record-identity", "if name ≠ identity ∨ declared ≠ captured", "if declared ≠ captured"),
            ("lost-record-layout", "if name ≠ identity ∨ declared ≠ captured", "if name ≠ identity"),
            ("lost-lifetime", "  .ok (.pointer (.pointer writable many target) address)",
             "  .ok (.pointer (.pointer writable many target) { address with allocation := 0 })"),
            ("lost-readonly", "pointerCast state (.pointer false false Expression.allocationType) complete",
             "pointerCast state (.pointer true false Expression.allocationType) complete"),
            ("wrong-header-field", "readField state header itemsOffset", "readField state header capacityOffset"),
            ("wrong-observed-id", "let result ← representative state header id", "let result ← representative state header 0"),
            ("lost-observed-offset", "Expression.readFields state false address",
             "Expression.readFields state false { address with offset := 0 }"),
            ("lost-observed-lifetime", "Expression.readFields state false address",
             "Expression.readFields state false { address with allocation := 0 }"),
            ("omitted-observed-fields", "return .ok (← Expression.readFields state false address)", "return .ok []"),
            ("invalid-id-is-not-success", "  | .error fault => return .error fault", "  | .error _ => return .ok []"),
            ("initialize-wrong-element", "match store state (.pointer (.pointer true false value.type) ⟨lifetime, index * 32 + offset⟩) value with", "match store state (.pointer (.pointer true false value.type) ⟨lifetime, offset⟩) value with"),
            ("initialize-wrong-lifetime", "match store state (.pointer (.pointer true false value.type) ⟨lifetime, index * 32 + offset⟩) value with", "match store state (.pointer (.pointer true false value.type) ⟨0, index * 32 + offset⟩) value with"),
            ("initialize-short-slice", "(Expression.argumentsOffset, .slice Expression.argumentsType argumentsAddress length)",
             "(Expression.argumentsOffset, .slice Expression.argumentsType argumentsAddress 0)"),
            ("initialize-wrong-id", "(Expression.idOffset, .scalar (.int false 32 id))", "(Expression.idOffset, .scalar (.int false 32 sequence))"),
            ("initialize-omitted-sequence", "   (Expression.idOffset, .scalar (.int false 32 id)),\n   (Expression.sequence_numberOffset, .scalar (.int false 32 sequence))]",
             "   (Expression.idOffset, .scalar (.int false 32 id))]"),
            ("append-wrong-capacity-comparison", "def hasCapacity (capacity newLength : Nat) : Bool := decide (capacity ≥ newLength)",
             "def hasCapacity (capacity newLength : Nat) : Bool := decide (capacity > newLength)"),
            ("append-wrong-length-increment", "def nextLength (length : Nat) : Nat := length + 1", "def nextLength (length : Nat) : Nat := length + 2"),
            ("append-wrong-slot", "def selectedIndex (newLength : Nat) : Nat := newLength - 1", "def selectedIndex (_ : Nat) : Nat := 0"),
            ("append-omitted-length-write", "let ready ← writeLength state header newLength", "let ready ← .ok state"),
            ("append-old-slice", "let address ← selectNewElement ready header newLength", "let address ← selectNewElement state header newLength"),
            ("append-overwritten-capacity", "allocationType) header) lengthOffset\n  store state field", "allocationType) header) capacityOffset\n  store state field"),
            ("append-growth-is-not-native-oom", "if !hasCapacity capacity.toNat newLength then .error .unsupported", "if !hasCapacity capacity.toNat newLength then .error .outOfMemory"),
            ("append-frame-includes-mutated-backing", "∀ other, other ≠ header → other ≠ lifetime → after.heap.lookup other = state.heap.lookup other",
             "∀ other, other ≠ header → after.heap.lookup other = state.heap.lookup other"),
            ("parent-without-array-admission", "parentTyped : parent.type = .array extent WordArray.word", "parentTyped : parent.type = parent.type"),
            ("parent-final-contents-assumed-initial", "WordArray.Represents after source values ∧\n      after.nextId", "WordArray.Represents state source values ∧\n      after.nextId"),
            ("parent-readonly-upgraded", "after.heap.lookup source.allocation = some parent ∧ WordArray.Represents", "after.heap.lookup source.allocation = some { parent with writable := true } ∧ WordArray.Represents"),
            ("parent-stack-ownership-erased", "after.heap.lookup source.allocation = some parent ∧ WordArray.Represents", "after.heap.lookup source.allocation = some { parent with stack := false } ∧ WordArray.Represents"),
            ("append-rewinds-lifetime", "  initializeFields ready address.allocation (address.offset / 32) itemAddress argumentsAddress argumentsLength id sequence",
             "  let finalState ← initializeFields ready address.allocation (address.offset / 32) itemAddress argumentsAddress argumentsLength id sequence\n  .ok { finalState with nextId := state.nextId - 1 }"),
            ("owner-header-overlaps-allocator", "def representativesOffset : Nat := 16", "def representativesOffset : Nat := 8"),
            ("owner-fast-extent-omits-cache", "⟨if runtimeSafety then 72 else 56, 8⟩", "⟨if runtimeSafety then 72 else 48, 8⟩"),
            ("owner-safety-extent-omits-lock", "⟨if runtimeSafety then 72 else 56, 8⟩", "⟨if runtimeSafety then 64 else 56, 8⟩"),
            ("owner-header-extent-truncated", "def representativesLayout : Compiler.ZigAir.Memory.Layout := ⟨24, 8⟩",
             "def representativesLayout : Compiler.ZigAir.Memory.Layout := ⟨16, 8⟩"),
            ("owner-cache-region-omitted", ", (expressionsOffset runtimeSafety, expressionsLayout runtimeSafety)]", "]"),
            ("owner-projection-forges-lifetime", "  ⟨owner.allocation, owner.offset + representativesOffset⟩",
             "  ⟨0, owner.offset + representativesOffset⟩"),
            ("owner-projection-discards-parent-offset", "  ⟨owner.allocation, owner.offset + representativesOffset⟩",
             "  ⟨owner.allocation, representativesOffset⟩"),
            ("owner-root-type-binding-removed", "typed : cell.type = allocationType runtimeSafety) (permitted",
             "typed : cell.type = cell.type) (permitted"),
            ("owner-view-header-is-opaque", "(representativesOffset, .object Compiler.Extraction.RepresentativeArray.allocationType)",
             '(representativesOffset, .object (.record "std.ArrayList(src/libevmasm/expression_classes.zig::Expression)" representativesLayout))'),
            ("owner-view-cache-omitted", '[(expressionsOffset runtimeSafety, .object (Compiler.Extraction.ExpressionMap.allocationType runtimeSafety))]', "[]"),
            ("owner-initialize-wrong-lifetime", "  let selected ← fieldPointer state (.pointer (.pointer true false (viewType runtimeSafety)) owner) representativesOffset\n  let .pointer _ header := selected | .error .malformed\n  let withItems",
             "  let selected ← fieldPointer state (.pointer (.pointer true false (viewType runtimeSafety)) { owner with allocation := 0 }) representativesOffset\n  let .pointer _ header := selected | .error .malformed\n  let withItems"),
            ("owner-initialize-short-slice", "(.slice itemsType data length)\n  store withItems", "(.slice itemsType data 0)\n  store withItems"),
            ("owner-initialize-lost-offset", "⟨header.allocation, header.offset + itemsOffset⟩)\n    (.slice itemsType data length)\n  store withItems",
             "⟨header.allocation, itemsOffset⟩)\n    (.slice itemsType data length)\n  store withItems"),
            ("owner-initialize-readonly-target", "let withItems ← store state (.pointer (.pointer true false itemsType) ⟨header.allocation, header.offset + itemsOffset⟩)",
             "let withItems ← store state (.pointer (.pointer false false itemsType) ⟨header.allocation, header.offset + itemsOffset⟩)"),
            ("owner-initialize-omitted-capacity", "  store withItems (.pointer (.pointer true false usize) ⟨header.allocation, header.offset + capacityOffset⟩)\n    (.scalar (.int false 64 capacity))",
             "  let _ := capacity\n  .ok withItems"),
            ("owner-initialize-rewinds-lifetime", "  store withItems (.pointer (.pointer true false usize) ⟨header.allocation, header.offset + capacityOffset⟩)\n    (.scalar (.int false 64 capacity))",
             "  let after ← store withItems (.pointer (.pointer true false usize) ⟨header.allocation, header.offset + capacityOffset⟩)\n    (.scalar (.int false 64 capacity))\n  .ok { after with nextId := state.nextId - 1 }"),
    )
    # Validate every selector before starting Lean; a new shared helper must not
    # leave a late ambiguous match after otherwise expensive mutation runs.
    available = {name for name, _, _ in mutations}
    if len(available) != len(mutations):
        raise ValueError("duplicate representative control name")
    for name, before, _ in mutations:
        if source.count(before) != 1:
            raise ValueError("ambiguous representative mutation: " + name)
    if names is not None and names - available:
        raise ValueError("unknown representative controls: " + ", ".join(sorted(names - available)))
    records = [mutation_check(output, "representative-unchanged", source, True, env, lean)]
    for name, before, after in mutations:
        if names is not None and name not in names:
            continue
        records.append(mutation_check(output, "representative-" + name, source.replace(before, after, 1), False, env, lean))
    for record in records:
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant|invalidDottedIdent",
                     (output / (record["name"] + ".stdout")).read_text(), re.I):
            raise ValueError("representative control hit a resource or syntax failure: " + record["name"])
    return records


def native(output, compiler, lib, modes=("Debug", "ReleaseSafe", "ReleaseFast")):
    records = []
    for mode in modes:
        entry = {"mode": mode, "accepted": False}
        records.append(entry)
        for kind, probe in PROBES.items():
            label = kind + "-" + mode
            binary = output / label
            run(output, "build-" + label, [compiler, "build-exe", "-j4", "--zig-lib-dir", lib, "-fllvm", "-O", mode,
                "--dep", "compiler", "-Mroot=" + str(probe), "-O", mode, "-Mcompiler=" + str(ROOT / "src/modules.zig"),
                "--cache-dir", ROOT / ".zig-cache", "--global-cache-dir", output / "global-cache", "-femit-bin=" + str(binary)], cwd=ROOT)
            run(output, "probe-" + label, [binary], cwd=ROOT)
            raw = output / ("probe-" + label + ".stdout")
            observation = output / ("probe-" + label + ".json")
            observation.write_bytes(raw.read_bytes())
            entry[kind] = {"binarySha256": digest(binary), "observationSha256": digest(observation)}
            write_json(output / "native-array.json", records)
            if observation.stat().st_size > 16384:
                raise ValueError("native representative profile exceeded bound")
            profile = json.loads(observation.read_bytes())
            if kind == "layout":
                generated = admission.programs(profile, lib)
                if profile["target"]["mode"] != mode or any(data != path.read_bytes() for path, data in generated.items()):
                    raise ValueError("native representative header/owner differs from admitted layout")
            else:
                check_observations(profile, mode)
            if (output / ("build-" + label + ".stderr")).read_bytes() or (output / ("probe-" + label + ".stderr")).read_bytes():
                raise ValueError("unreviewed native representative diagnostic")
        entry.update(accepted=True, headerFields=3, ownerFields=3, embeddedHeaderOffset=16,
            representativeCases=5, spareCapacity=True, unsortedArguments=[3, 2],
            nonzeroSequenceNumber=23, cacheHit=True, spareCapacityAppend=True, parentBorrowOffset=1, parentBorrowLength=2,
            copiedDescriptorCount=5, copySpareCapacity=2, publicationLength=5, publicationCapacity=10,
            ownedFirstGrowthCapacity=5, ownedSpareLength=2,
            firstPreciseGrowthCapacity=3, firstGrowthOom=True, firstGrowthRawRemaps=0, firstSelectedGrowthCapacity=5, selectedGrowthOverflowOom=True, firstGrowingAppendCapacity=5, firstGrowingAppendLength=1, firstGrowingAppendOom=True)
        write_json(output / "native-array.json", records)
    return records


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.representative-array-verification.v1", "status": "failed", "jobs": 4,
        "scope": "captured owner geometry and typed header assignment with evaluated inputs, ArrayList(Expression) fields, spare-capacity append through standalone and captured-owner headers with independent parent-borrow frame from ready typed backing; checked external representative backing reservation, initialized descriptor-prefix copy and reached pointer/capacity publication; precise growth from zero capacity through allocation, empty copy/release and publication; source-selected saturating capacity wrapper for the captured aarch64 target; complete reached append for initially empty or spare-capacity captured owners with first-growth, OOM and partial-rejection parent frames",
        "typedRepresentativeReaderVerified": False, "typedFieldStoreReadbackVerified": False, "typedDescriptorInitializationVerified": False,
        "typedSpareCapacityAppendVerified": False, "checkedBackingReservationVerified": False, "typedDescriptorPrefixCopyVerified": False, "nativeGrowthVerified": False,
        "typedFirstGrowingAppendVerified": False, "typedCapacitySelectionVerified": False, "typedParentBorrowFrameVerified": False, "typedHeaderPublicationVerified": False, "typedFirstPreciseGrowthVerified": False,
        "nativeOwnerGeometryVerified": False, "typedOwnerHeaderAssignmentVerified": False, "nativeOwnerTypedHeaderVerified": False,
        "nativeGraphMutationCorrespondenceVerified": False,
        "recursiveConstructorsVerified": False, "nativeBackendVerified": False, "wholeCompilerVerified": False}
    try:
        report["inputs"] = inputs()
        toolchain = json.loads(args.toolchain.read_bytes())
        compiler, lib = Path(toolchain["compiler"]["path"]), Path(toolchain["compiler"]["zigLibDir"])
        report["toolchainReportSha256"], report["compilerSha256"] = digest(args.toolchain), digest(compiler)
        if report["compilerSha256"] != toolchain["compiler"]["sha256"] or source_identity(lib.parent) != toolchain["sourceTree"]:
            raise ValueError("representative toolchain inputs changed")
        report["appendAdmission"] = append_admission.check(lib)
        report["publicationAdmission"] = publication_admission.check(lib)
        report["growthAdmission"] = growth_admission.check(lib)
        report["capacityAdmission"] = capacity_admission.check(lib)
        env, _, tools = lean_check.toolchain(args.lean_bin, 4)
        report["tools"] = tools
        run(output, "python-preflight", [sys.executable, "-m", "unittest", "discover", "-s", "test/lean", "-p", "test_representative_array.py"], cwd=ROOT)
        run(output, "append-python-preflight", [sys.executable, "-m", "unittest", "discover", "-s", "test/lean", "-p", "test_representative_append.py"], cwd=ROOT)
        run(output, "publication-python-preflight", [sys.executable, "-m", "unittest", "discover", "-s", "test/lean", "-p", "test_representative_publication.py"], cwd=ROOT)
        run(output, "growth-python-preflight", [sys.executable, "-m", "unittest", "discover", "-s", "test/lean", "-p", "test_representative_growth.py"], cwd=ROOT)
        run(output, "capacity-python-preflight", [sys.executable, "-m", "unittest", "discover", "-s", "test/lean", "-p", "test_representative_capacity.py"], cwd=ROOT)
        run(output, "cached-proof", [tools["lake"]["path"], "build", MODULE], cwd=ROOT / "lean", env=env)
        report["audit"] = audit(output, env, tools["lean"]["path"])
        report["controls"] = controls(output, env, tools["lean"]["path"])
        run(output, "version", [compiler, "version"])
        if text(output, "version") != "0.17.0":
            raise ValueError("representative reader requires pinned Zig 0.17.0")
        report["native"] = native(output, compiler, lib)
        proof, artifacts = prove.check_module(MODULE, CLAIMS, lean_bin=args.lean_bin, jobs=4, fresh=True)
        directory = output / "proof"
        directory.mkdir()
        for name, data in artifacts.items():
            (directory / name).write_bytes(data)
        write_json(directory / "report.json", proof)
        report["proofReportSha256"] = digest(directory / "report.json")
        if (proof.get("status") != "passed" or proof.get("freshKernelReplay") is not True or
                proof.get("replayIncludesImports") is not True or proof.get("auditedDeclarations") != CLAIMS):
            raise ValueError("representative proof or fresh imported replay failed")
        if (inputs() != report["inputs"] or digest(args.toolchain) != report["toolchainReportSha256"] or
                digest(compiler) != report["compilerSha256"] or source_identity(lib.parent) != toolchain["sourceTree"]):
            raise ValueError("representative acceptance inputs changed")
        report.update(status="passed", typedRepresentativeReaderVerified=True, typedFieldStoreReadbackVerified=True,
            typedDescriptorInitializationVerified=True, typedSpareCapacityAppendVerified=True, typedParentBorrowFrameVerified=True,
            nativeOwnerGeometryVerified=True, typedOwnerHeaderAssignmentVerified=True, checkedBackingReservationVerified=True,
            typedDescriptorPrefixCopyVerified=True, typedHeaderPublicationVerified=True, typedFirstPreciseGrowthVerified=True, typedCapacitySelectionVerified=True, typedFirstGrowingAppendVerified=True)
    except BaseException as error:
        report["error"] = str(error)
        raise
    finally:
        write_json(output / "report.json", report)
    print("Typed owner headers, representative reservation, copy, publication and first precise growth, scoped append and parent-borrow frames passed; full native growth, initialization, graph correspondence and recursive constructors remain open.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    check(parser.parse_args())
