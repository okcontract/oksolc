#!/usr/bin/env python3
"""Check registered representative reservation, copying and full-capacity release.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(ROOT / "lean"), str(ROOT / "lean/zig_air")]
import environment as lean_check
import check_compiler
import check_word_swap
import check_representative_array as array_gate
import extract_representative_append as append_admission
import extract_representative_growth as admission
import extract_representative_remap as remap_admission
import representative_remap_checks
import prove
from build_toolchain import digest, run, source_identity, text, write_json
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

MODULE = "Compiler.Extraction.RepresentativeRemapGrowthTests"
NS = "Compiler.Extraction.RepresentativeArray.Backing.Release."
REG = "Compiler.Extraction.RepresentativeArray.Backing.Registry."
COPY = "Compiler.Extraction.RepresentativeArray.Backing.RegisteredCopy."
PUB = "Compiler.Extraction.RepresentativeArray.Publication.Registered."
MOVE = "Compiler.Extraction.RepresentativeArray.Backing.Relocation."
FALL = "Compiler.Extraction.RepresentativeArray.Backing.Fallback."
DESC = "Compiler.Extraction.RepresentativeArray.DescriptorRelation."
MEM = "Compiler.ZigAir.Memory."
PROBE = ROOT / "test/lean/representative_release.zig"
FILES = ("RepresentativeBackingRelease.lean", "RepresentativeBackingReleaseFrame.lean", "RepresentativeBackingReleaseTests.lean",
    "RepresentativeBackingRegistry.lean", "RepresentativeBackingRegistryFrame.lean", "RepresentativeBackingRegistryTests.lean",
    "RepresentativeBackingCopy.lean", "RepresentativeBackingCopyTests.lean", "RepresentativeRegisteredPublication.lean",
    "RepresentativeRelocation.lean", "RepresentativeRelocationProofs.lean", "RepresentativeRelocationFrame.lean", "RepresentativeRelocationTests.lean",
    "RepresentativeFallback.lean", "RepresentativeFallbackProofs.lean", "RepresentativeFallbackFrame.lean", "RepresentativeFallbackTests.lean",
    "RepresentativeAppendExecution.lean", "RepresentativeGrowingAppend.lean", "RepresentativeAppendFrame.lean", "RepresentativeGrowingAppendTests.lean",
    "RepresentativeDescriptorRelation.lean", "RepresentativeDescriptorPreservation.lean", "RepresentativeDescriptorTests.lean",
    "RepresentativeDescriptorAppendFrame.lean", "RepresentativeDescriptorAppend.lean", "RepresentativeDescriptorAppendTests.lean",
    "RepresentativeDescriptorRegistry.lean", "RepresentativeDescriptorRegistryTests.lean",
    "RepresentativeFirstRegistry.lean", "RepresentativeFirstRegistryTests.lean",
    "RepresentativeFallbackRegistry.lean", "RepresentativeFallbackRegistryTests.lean")
CLAIMS = [MEM + "releaseOwned_shape"]
CLAIMS += [NS + name for name in (
    "empty", "checked_of_owned", "check_shape", "erased_post", "verified", "rejected",
    "Post.frame", "Post.dead", "Post.stale_alias", "run_storage", "run_word_frame", "parent_borrow", "run_graph_frame", "fromHeader_word_frame")]
CLAIMS += [NS + "Tests." + name for name in (
    "initial_valid", "initial_owned", "actual_release", "without_final_premises", "checked_post", "header_uses_capacity",
    "length_is_not_read", "uninitialized_capacity_can_be_freed", "initialized_prefix_is_not_extent", "oversized_extent_rejects",
    "interior_pointer_rejects", "wrong_allocator_rejects", "stale_registry_rejects", "wrong_registry_type_rejects",
    "readonly_rejects", "stack_rejects", "same_bytes_wrong_type_rejects", "missing_memory_rejects", "corrupt_state_rejects",
    "empty_ignores_sentinel", "parent_contents", "parent_survives_every_outcome", "aliases_die_history_survives",
    "readonly_stack_parent_survives", "graph_payload_survives")]
CLAIMS += [REG + name for name in ("empty", "reservation_shape", "reservation_frame", "reservation_valid", "register_valid",
    "verified", "storage", "frame", "graph_frame", "parent_borrow", "release_derived")]
CLAIMS += [REG + "Tests." + name for name in ("initial_valid", "fits", "actual_reservation", "without_final_premises", "ready_owned",
    "uninitialized_is_not_published", "actual_release", "release_without_owned_premise", "oom_keeps_effects", "wrong_region_keeps_effects",
    "overlap_keeps_old_backing", "null_region_rejects", "extent_overflow_is_oom", "capacity_width_rejects", "collision_keeps_allocation",
    "empty_does_not_register", "invalid_state_skips_allocator", "all_outcomes_preserve_parent", "old_vector_and_arguments_survive",
    "dead_address_has_new_lifetime", "selected_allocator_brand")]
CLAIMS += [COPY + name for name in ("storage", "owned", "parent_borrow", "verified", "read_field_frame", "reserve_verified")]
CLAIMS += [COPY + "Tests." + name for name in ("initial_valid", "source_owned", "target_owned", "actual_copy", "without_final_premises",
    "registered_arguments_survive", "both_release_permissions_survive", "offset_parent_survives", "copy_does_not_publish", "complete_fields",
    "partial_failure_keeps_writes", "prefix_failure_keeps_writes", "short_target_keeps_writes", "readonly_rejects", "overlap_rejects",
    "empty_skips_sentinels", "stale_source_rejects", "reserved_source_ready", "reservation_copy_without_final_premises")]
CLAIMS += [PUB + name for name in ("storage", "owned", "verified")]
CLAIMS += [MOVE + name for name in ("of_steps", "empty_source", "release_owner_frame", "finish_storage", "storage", "verified", "finish_parent_borrow", "parent_borrow")]
CLAIMS += [MOVE + "Tests." + name for name in ("initial_valid", "source_owned", "target_owned", "header_loaded", "first_copy", "second_copy",
    "actual_copy", "actual_release", "actual_publication", "actual_relocation", "source_ready", "without_final_premises", "stale_old_and_live_new",
    "parent_contents", "every_outcome_preserves_parent", "wrong_brand_keeps_copy", "short_free_keeps_copy", "capacity_fault_keeps_release_and_pointer",
    "partial_publication_observations", "items_fault_precedes_copy", "interior_target_rejects", "copy_fault_retains_prefix_without_release", "failed_copy_observations", "empty_sentinel_publication", "empty_sentinel_observations",
    "nonempty_interior_source_rejects", "empty_interior_target_rejects")]
CLAIMS += ["Compiler.Extraction.RepresentativeArray.allocatedSlice_nonempty", REG + "success_owned", REG + "failed"]
CLAIMS += [FALL + name for name in ("of_steps", "oom", "oom_verified", "verified", "storage", "parent_borrow")]
CLAIMS += [FALL + "Tests." + name for name in ("initial_valid", "fits", "actual_reservation", "reserved_is_suffix_fixture",
    "source_owned", "header_loaded", "saved_full_capacity", "source_ready", "actual_fallback", "without_final_premises",
    "oom_before_header", "bad_response_keeps_effects", "short_release_retains_allocation_and_copy", "bad_header_retains_allocation",
    "collision_retains_typed_allocation", "copy_fault_retains_allocation_and_prefix", "capacity_overflow_skips_allocation",
    "parent_contents", "every_outcome_preserves_parent")]
CLAIMS += ["Compiler.Extraction.Expression.readFields_parts"]
CLAIMS += [DESC + name for name in ("empty", "row_frame", "frame", "source_ready", "copied", "query",
    "initialization_frame", "initialize_prefix", "copy_verified", "fallback_verified")]
CLAIMS += [DESC + "Tests." + name for name in ("initial_valid", "first_initialized", "second_initialized", "prefix_from_initialization",
    "all_initial_queries", "fits", "fallback_without_final_premises", "offset_borrow_still_live", "wrong_item_rejects",
    "wrong_arguments_reject", "short_arguments_reject", "wrong_sequence_rejects", "arbitrary_descriptors_are_not_nodes",
    "missing_second_row_rejects", "wrong_stored_id_rejects", "interior_owned_arguments_reject", "rejected_initialization_keeps_old_row")]
CLAIMS += [DESC + name for name in ("extend", "selected_address", "finish_frame", "assumeCapacity_frame", "owner_spare_frame",
    "after_capacity_shape", "spare_append", "first_append")]
CLAIMS += [DESC + "AppendTests." + name for name in ("attempt_suffix", "actual_spare", "spare_without_final_premises", "spare_derived_queries",
    "old_rows_survive_all_rejections", "malformed_arguments_keep_length_and_item", "malformed_sequence_keeps_id", "partial_row_is_not_published",
    "full_capacity_does_not_widen_length", "actual_first", "first_without_final_premises", "first_derived_queries", "first_oom_keeps_empty",
    "empty_arguments_keep_sentinel")]
CLAIMS += [REG + "vector_write_valid", DESC + "spare_session", DESC + "spare_registered"]
CLAIMS += [DESC + "RegistryTests." + name for name in ("initial_valid", "registered_spare", "every_outcome_valid",
    "partial_keeps_old_vector", "wrong_allocator_rejects", "missing_row_rejects", "native_prefix_is_not_registration")]
CLAIMS += [DESC + name for name in ("first_continuation_backing", "owner_session_of_shape", "first_session",
    "first_reserved", "first_registered", "first_registry_oom")]
CLAIMS += [DESC + "FirstRegistryTests." + name for name in ("initial_valid", "registered_first", "actual_queries",
    "every_outcome_valid", "every_outcome_releasable", "oom_keeps_registry", "partial_execution", "partial_is_owned_not_complete",
    "empty_arguments_registered", "alias_registry_is_invalid", "registered_parent_offset", "different_callback_oom")]
CLAIMS += [DESC + name for name in ("fallback_registered", "fallback_registry_oom")]
CLAIMS += [DESC + "FallbackRegistryTests." + name for name in (
    "initial_valid", "source_owned", "registered_move", "raw_is_provisional", "every_outcome_valid", "parent_offset",
    "oom_keeps_vector", "wrong_vector_rejects", "partial_copy_execution", "partial_copy_is_not_move", "readonly_reservation",
    "readonly_first_copy", "readonly_second_copy", "readonly_copy", "readonly_release", "readonly_publication",
    "publication_fault_execution", "publication_fault_keeps_release", "publication_fault_is_not_move")]


CLAIMS += representative_remap_checks.CLAIMS


def inputs():
    saved = check_compiler.snapshot()
    saved.update({str(p.relative_to(ROOT)): digest(p) for p in (ROOT / "test/lean").rglob("*.py")})
    saved[str(PROBE.relative_to(ROOT))] = digest(PROBE)
    saved.update({str(path.relative_to(ROOT)): digest(path) for path in array_gate.PROBES.values()})
    return saved


def check_observation(profile, mode):
    """Validate exact fixture observations; booleans are not integer addresses."""
    expected = {
        "schema": "oksolc.representative-release-native.v6",
        "target": {"arch": "aarch64", "os": "macos", "mode": mode, "pointer_bytes": 8},
        "descriptor": {"bytes": 32, "alignment": 8},
        "backing": {"base": None, "length": 2, "capacity": 5},
        "allocation": {"calls": 1, "base": None, "bytes": 160, "alignment": 8},
        "copy_allocation": {"calls": 1, "base": None, "bytes": 224, "alignment": 8},
        "remap": {"calls": 1, "base": None, "bytes": 160, "new_bytes": 224, "alignment": 8},
        "header": {"base": None, "length": 2, "capacity": 7},
        "copy": {"base": None, "capacity": 7, "rows": [
            {"item_base": None, "arguments_base": None, "arguments_length": 2, "id": 0, "sequence": 23},
            {"item_base": None, "arguments_base": None, "arguments_length": 2, "id": 1, "sequence": 29}]},
        "release": {"calls": 1, "base": None, "bytes": 160, "alignment": 8},
        "order": 1312,
        "oom": {"failed": True, "calls": 1, "base": 0, "bytes": 160, "alignment": 8, "frees": 0, "order": 1},
        "growth_oom": {"failed": True, "calls": 2, "base": 0, "bytes": 224, "alignment": 8, "frees": 0, "order": 131,
            "remap": {"calls": 1, "base": None, "bytes": 160, "new_bytes": 224, "alignment": 8}, "old_base": None,
            "header": {"base": None, "length": 2, "capacity": 5}, "rows": [
                {"item_base": None, "arguments_base": None, "arguments_length": 2, "id": 0, "sequence": 23},
                {"item_base": None, "arguments_base": None, "arguments_length": 2, "id": 1, "sequence": 29}]},
        "empty_calls": 0,
        "empty_growth": {"sentinel_base": None, "source": None, "calls": 1, "base": None,
            "bytes": 160, "alignment": 8, "remaps": 0, "frees": 0, "order": 1,
            "header": {"base": None, "length": 0, "capacity": 5}},
        "item": {"base_before": None, "base_after": None, "instruction_after": "LT"},
        "parent": {"base": None, "arguments_base": None, "arguments_length": 2, "after": [777, 99, 1, 5]},
    }

    def match(actual, wanted, path):
        if wanted is None:
            if type(actual) is not int or not 0 < actual < 2**64:
                raise ValueError("invalid native address: " + path)
        elif type(wanted) is dict:
            if type(actual) is not dict or actual.keys() != wanted.keys():
                raise ValueError("invalid native fields: " + path)
            for key, value in wanted.items():
                match(actual[key], value, path + "/" + key)
        elif type(wanted) is list:
            if type(actual) is not list or len(actual) != len(wanted):
                raise ValueError("invalid native list: " + path)
            for index, (value, required) in enumerate(zip(actual, wanted)):
                match(value, required, path + "/" + str(index))
        elif type(actual) is not type(wanted) or actual != wanted:
            raise ValueError("unexpected native value: " + path)

    match(profile, expected, "")
    empty = profile["empty_growth"]
    if (empty["source"] != empty["sentinel_base"] + 32 or empty["sentinel_base"] % 8 or
            empty["sentinel_base"] + 64 > 2**64 or empty["base"] % 8 or empty["base"] + 160 > 2**64 or
            empty["header"]["base"] != empty["base"] or
            empty["base"] < empty["sentinel_base"] + 64 and empty["sentinel_base"] < empty["base"] + 160):
        raise ValueError("empty growth sentinel or allocation identity changed")
    backing, freed, item, parent = (profile[k] for k in ("backing", "release", "item", "parent"))
    if (backing["base"] != profile["allocation"]["base"] or backing["base"] != freed["base"] or
            freed["base"] % 8 or freed["base"] + freed["bytes"] > 2**64 or
            item["base_before"] != item["base_after"] or parent["base"] % 4 or
            parent["arguments_base"] != parent["base"] + 4 or parent["base"] + 16 > 2**64):
        raise ValueError("native extent or borrowed pointer identity changed")
    if (freed["base"] < parent["base"] + 16 and parent["base"] < freed["base"] + freed["bytes"] or
            freed["base"] <= item["base_before"] < freed["base"] + freed["bytes"]):
        raise ValueError("borrowed payload overlaps released storage")
    copied, allocation = profile["copy"], profile["copy_allocation"]
    if profile["remap"]["base"] != backing["base"] or profile["header"]["base"] != copied["base"]:
        raise ValueError("remap input or published header identity changed")
    if (copied["base"] != allocation["base"] or copied["base"] % 8 or copied["base"] + allocation["bytes"] > 2**64 or
            copied["base"] < freed["base"] + freed["bytes"] and freed["base"] < copied["base"] + allocation["bytes"] or
            copied["base"] < parent["base"] + 16 and parent["base"] < copied["base"] + allocation["bytes"] or
            copied["base"] <= item["base_after"] < copied["base"] + allocation["bytes"]):
        raise ValueError("copy allocation extent or separation changed")
    for row in copied["rows"]:
        if row["item_base"] != item["base_after"] or row["arguments_base"] != parent["arguments_base"]:
            raise ValueError("copy changed borrowed descriptor pointers")
    failed = profile["growth_oom"]
    old = failed["old_base"]
    if (old != failed["header"]["base"] or old != failed["remap"]["base"] or old % 8 or old + 160 > 2**64 or
            old < parent["base"] + 16 and parent["base"] < old + 160 or old <= item["base_after"] < old + 160 or
            old < copied["base"] + allocation["bytes"] and copied["base"] < old + 160):
        raise ValueError("OOM changed backing identity or separation")
    if failed["rows"] != copied["rows"]:
        raise ValueError("OOM changed initialized descriptors")


def audit(output, env, lean):
    checked = check_word_swap.audit(output, env, lean, MODULE, CLAIMS)
    records = json.loads((output / "audit.json").read_bytes())["claims"]
    dependencies = {r["theorem"]: set(r["dependencies"]) for r in records}
    required = {
        NS + "check_shape": {NS + "check", MEM + "releaseOwned_shape", "Compiler.Extraction.Memory.release_success"},
        NS + "verified": {NS + "checked_of_owned", NS + "check_shape", NS + "erased_post", MEM + "valid_lookup",
            "Compiler.Extraction.RepresentativeArray.Backing.layout_checked"},
        NS + "run_storage": {NS + "check_shape", NS + "erased_post", NS + "Post.frame"},
        NS + "run_word_frame": {NS + "check_shape", MEM + "Heap.lookup_ne_of_type_ne", MEM + "erase_lookup"},
        NS + "parent_borrow": {NS + "run_word_frame", MEM + "load_eq_of_lookup"},
        NS + "run_graph_frame": {NS + "check_shape", "Compiler.Extraction.Memory.resident_vector_write"},
        NS + "fromHeader_word_frame": {NS + "run_word_frame", "Compiler.Extraction.RepresentativeArray.allocatedSlice"},
        NS + "Post.stale_alias": {MEM + "erase_load_dead"},
        NS + "Tests.without_final_premises": {NS + "verified", NS + "Tests.initial_valid", NS + "Tests.initial_owned"},
        NS + "Tests.graph_payload_survives": {NS + "run_graph_frame"},
        REG + "reservation_shape": {MEM + "RegionAllocation.reserve_nonempty_success"},
        REG + "reservation_valid": {REG + "reservation_frame", "Compiler.Extraction.Memory.Arguments.Normalization.Injected.fresh",
            "Compiler.Extraction.Memory.Arguments.Normalization.related_allocation_frame"},
        REG + "verified": {REG + "reservation_valid", REG + "register_valid", MEM + "RegionAllocation.reserve_admitted",
            "Compiler.Extraction.Memory.Arguments.Normalization.Injected.fresh"},
        REG + "storage": {REG + "reservation_shape", REG + "reservation_valid", REG + "register_valid"},
        REG + "graph_frame": {REG + "storage", "Compiler.Extraction.Memory.resident_fresh_write"},
        REG + "parent_borrow": {REG + "frame", MEM + "valid_lookup", MEM + "load_eq_of_lookup"},
        REG + "release_derived": {REG + "verified", NS + "verified", MEM + "WordAllocation.next_id_fresh"},
        REG + "Tests.without_final_premises": {REG + "verified", REG + "Tests.initial_valid", REG + "Tests.fits"},
        REG + "Tests.release_without_owned_premise": {REG + "release_derived"},
        COPY + "storage": {"Compiler.Extraction.RepresentativeArray.Copy.run_storage",
            "Compiler.Extraction.Memory.Arguments.Normalization.Injected.retained",
            "Compiler.Extraction.Memory.Arguments.Normalization.represented_frame"},
        COPY + "owned": {"Compiler.Extraction.RepresentativeArray.Copy.run_storage"},
        COPY + "parent_borrow": {"Compiler.Extraction.RepresentativeArray.Copy.run_parent_borrow"},
        COPY + "verified": {COPY + "storage", COPY + "owned", "Compiler.Extraction.RepresentativeArray.Copy.run_verified",
            "Compiler.Extraction.RepresentativeArray.Copy.readFields_eq_of_slots"},
        COPY + "reserve_verified": {REG + "verified", COPY + "verified", COPY + "read_field_frame", MEM + "valid_lookup"},
        COPY + "Tests.without_final_premises": {COPY + "verified", COPY + "Tests.initial_valid", COPY + "Tests.target_owned"},
        COPY + "Tests.reservation_copy_without_final_premises": {COPY + "reserve_verified", COPY + "Tests.reserved_source_ready"},
        PUB + "storage": {"Compiler.Extraction.RepresentativeArray.Publication.run_storage", MEM + "Heap.lookup_ne_of_type_ne",
            "Compiler.Extraction.Memory.Arguments.Normalization.Injected.retained"},
        PUB + "verified": {PUB + "storage", "Compiler.Extraction.RepresentativeArray.Publication.run_verified"},
        MOVE + "release_owner_frame": {NS + "check_shape", MEM + "Heap.lookup_ne_of_type_ne"},
        MOVE + "storage": {COPY + "storage", MOVE + "finish_storage"},
        MOVE + "verified": {COPY + "verified", COPY + "owned", NS + "verified", PUB + "verified", PUB + "owned",
            MOVE + "of_steps", "Compiler.Extraction.RepresentativeArray.readField_eq_of_lookup", MEM + "valid_lookup"},
        MOVE + "parent_borrow": {COPY + "parent_borrow", MOVE + "finish_parent_borrow"},
        MOVE + "finish_parent_borrow": {NS + "parent_borrow", MOVE + "release_owner_frame",
            "Compiler.Extraction.RepresentativeArray.Publication.run_parent_borrow"},
        MOVE + "Tests.without_final_premises": {MOVE + "verified", MOVE + "Tests.initial_valid", MOVE + "Tests.source_ready"},
        MOVE + "Tests.every_outcome_preserves_parent": {MOVE + "parent_borrow"},
        "Compiler.Extraction.RepresentativeArray.allocatedSlice_nonempty": {MEM + "root_access", MEM + "valid_lookup", MEM + "makeSlice"},
        REG + "success_owned": {REG + "reservation_shape", "Compiler.Extraction.Memory.Arguments.Normalization.Injected.fresh"},
        FALL + "verified": {REG + "verified", MOVE + "verified", COPY + "read_field_frame", FALL + "of_steps", MEM + "valid_lookup"},
        FALL + "oom_verified": {REG + "failed", FALL + "oom"},
        FALL + "Tests.oom_before_header": {FALL + "oom_verified", FALL + "Tests.initial_valid"},
        FALL + "storage": {REG + "storage", REG + "success_owned", MOVE + "storage"},
        FALL + "parent_borrow": {REG + "parent_borrow", REG + "success_owned", MOVE + "parent_borrow"},
        FALL + "Tests.saved_full_capacity": {"Compiler.Extraction.RepresentativeArray.allocatedSlice_nonempty",
            "Compiler.Extraction.RepresentativeArray.readItemsData_from_loaded"},
        FALL + "Tests.without_final_premises": {FALL + "verified", FALL + "Tests.initial_valid", FALL + "Tests.fits", FALL + "Tests.source_ready"},
        FALL + "Tests.every_outcome_preserves_parent": {FALL + "parent_borrow"},
        DESC + "source_ready": {"Compiler.Extraction.Expression.readFields_parts", DESC + "Prefix"},
        DESC + "query": {"Compiler.Extraction.RepresentativeArray.representative_from_array",
            "Compiler.Extraction.RepresentativeArray.invalid_from_loaded_header", "Compiler.Extraction.Storage.representativeProgram"},
        DESC + "initialization_frame": {"Compiler.Extraction.RepresentativeArray.Copy.readField_after_slot_store"},
        DESC + "initialize_prefix": {"Compiler.Extraction.RepresentativeArray.initializeFields_verified", DESC + "initialization_frame",
            "Compiler.Extraction.Storage.idFor_toNat"},
        DESC + "copy_verified": {COPY + "verified", DESC + "source_ready", DESC + "copied"},
        DESC + "fallback_verified": {FALL + "verified", DESC + "source_ready", DESC + "copied", DESC + "query"},
        DESC + "Tests.prefix_from_initialization": {DESC + "initialize_prefix", DESC + "empty"},
        DESC + "Tests.all_initial_queries": {DESC + "query", DESC + "Tests.prefix_from_initialization"},
        DESC + "Tests.fallback_without_final_premises": {DESC + "fallback_verified", DESC + "Tests.prefix_from_initialization"},
        DESC + "Tests.rejected_initialization_keeps_old_row": {DESC + "initialization_frame"},
        DESC + "selected_address": {MEM + "sliceElementPointer_address", MEM + "recordView_address"},
        DESC + "finish_frame": {DESC + "selected_address", DESC + "initialization_frame"},
        DESC + "assumeCapacity_frame": {DESC + "finish_frame", DESC + "frame",
            "Compiler.Extraction.RepresentativeArray.Append.Execution.length_write_is_store"},
        DESC + "owner_spare_frame": {DESC + "assumeCapacity_frame", "Compiler.Extraction.RepresentativeArray.Capacity.ensure_unchanged"},
        DESC + "after_capacity_shape": {"Compiler.Extraction.RepresentativeArray.Append.Execution.assumeCapacity_storage"},
        DESC + "spare_append": {DESC + "owner_spare_frame", DESC + "extend", DESC + "query",
            "Compiler.Extraction.RepresentativeArray.Append.Execution.spare_verified"},
        DESC + "first_append": {DESC + "first_continuation_backing", DESC + "extend", DESC + "query",
            "Compiler.Extraction.RepresentativeArray.Append.Execution.first_verified"},
        DESC + "AppendTests.spare_without_final_premises": {DESC + "spare_append", DESC + "Tests.prefix_from_initialization"},
        DESC + "AppendTests.actual_spare": {DESC + "AppendTests.attempt_suffix"},
        DESC + "AppendTests.attempt_suffix": {"Compiler.Extraction.RepresentativeArray.Capacity.ensure_unchanged"},
        DESC + "AppendTests.first_without_final_premises": {DESC + "first_append"},
        DESC + "AppendTests.spare_derived_queries": {DESC + "AppendTests.spare_without_final_premises", DESC + "AppendTests.actual_spare"},
        DESC + "AppendTests.first_derived_queries": {DESC + "AppendTests.first_without_final_premises", DESC + "AppendTests.actual_first"},
        DESC + "AppendTests.partial_row_is_not_published": {DESC + "AppendTests.old_rows_survive_all_rejections"},
        REG + "register_valid": {REG + "vector_write_valid"},
        DESC + "spare_session": {DESC + "after_capacity_shape", DESC + "owner_session_of_shape"},
        DESC + "spare_registered": {DESC + "spare_append", DESC + "spare_session", REG + "vector_write_valid",
            "Compiler.Extraction.Memory.resident_vector_write"},
        DESC + "RegistryTests.registered_spare": {DESC + "spare_registered", DESC + "RegistryTests.initial_valid"},
        DESC + "RegistryTests.every_outcome_valid": {DESC + "spare_session"},
        DESC + "RegistryTests.partial_keeps_old_vector": {DESC + "RegistryTests.every_outcome_valid", DESC + "AppendTests.partial_row_is_not_published"},
        DESC + "RegistryTests.native_prefix_is_not_registration": {DESC + "Tests.prefix_from_initialization"},
        DESC + "first_continuation_backing": {DESC + "after_capacity_shape", "Compiler.Extraction.RepresentativeArray.Capacity.first_verified"},
        DESC + "owner_session_of_shape": {"Compiler.Extraction.RepresentativeArray.Append.Execution.owner_parent_borrow",
            "Compiler.Extraction.RepresentativeArray.Append.Execution.run_valid", "Compiler.Extraction.Memory.Arguments.Normalization.Injected.retained"},
        DESC + "first_session": {DESC + "owner_session_of_shape", DESC + "first_continuation_backing"},
        DESC + "first_reserved": {DESC + "first_session", DESC + "first_continuation_backing", REG + "register_valid"},
        DESC + "first_registered": {DESC + "first_append", DESC + "first_session", DESC + "first_continuation_backing",
            REG + "vector_write_valid", "Compiler.Extraction.Memory.resident_fresh_write", "Compiler.Extraction.Memory.Arguments.Normalization.Injected.fresh"},
        DESC + "first_registry_oom": {"Compiler.Extraction.RepresentativeArray.Append.Execution.first_oom",
            "Compiler.Extraction.Memory.Arguments.Normalization.Injected.fresh"},
        DESC + "FirstRegistryTests.registered_first": {DESC + "first_registered", DESC + "FirstRegistryTests.initial_valid"},
        DESC + "FirstRegistryTests.actual_queries": {DESC + "FirstRegistryTests.registered_first", DESC + "AppendTests.actual_first"},
        DESC + "FirstRegistryTests.every_outcome_valid": {DESC + "first_session"},
        DESC + "FirstRegistryTests.every_outcome_releasable": {DESC + "first_reserved"},
        DESC + "FirstRegistryTests.oom_keeps_registry": {DESC + "first_registry_oom"},
        DESC + "FirstRegistryTests.partial_execution": {"Compiler.Extraction.RepresentativeArray.Append.Execution.Tests.malformed_arguments_keep_length_and_item"},
        DESC + "FirstRegistryTests.partial_is_owned_not_complete": {DESC + "FirstRegistryTests.every_outcome_releasable",
            DESC + "FirstRegistryTests.partial_execution", "Compiler.Extraction.RepresentativeArray.Append.Execution.Tests.partial_descriptor_is_not_complete"},
        DESC + "FirstRegistryTests.empty_arguments_registered": {DESC + "first_registered"},
        DESC + "FirstRegistryTests.registered_parent_offset": {DESC + "FirstRegistryTests.registered_first",
            "Compiler.Extraction.RepresentativeArray.Append.Execution.owner_parent_borrow"},
        DESC + "FirstRegistryTests.different_callback_oom": {DESC + "first_registry_oom"},
        DESC + "fallback_registered": {FALL + "verified", DESC + "source_ready", DESC + "copied", DESC + "query",
            REG + "vector_write_valid", "Compiler.Extraction.Memory.move_vector_eq",
            "Compiler.Extraction.Memory.Arguments.Normalization.Injected.fresh",
            "Compiler.Extraction.Memory.resident_fresh_write", "Compiler.Extraction.Memory.resident_vector_write"},
        DESC + "fallback_registry_oom": {FALL + "oom_verified", "Compiler.Extraction.Memory.move_vector_oom"},
        DESC + "FallbackRegistryTests.initial_valid": {REG + "vector_write_valid", DESC + "Tests.initial_valid"},
        DESC + "FallbackRegistryTests.registered_move": {DESC + "fallback_registered", DESC + "FallbackRegistryTests.initial_valid",
            DESC + "Tests.prefix_from_initialization"},
        DESC + "FallbackRegistryTests.raw_is_provisional": {DESC + "FallbackRegistryTests.registered_move"},
        DESC + "FallbackRegistryTests.every_outcome_valid": {FALL + "storage"},
        DESC + "FallbackRegistryTests.parent_offset": {FALL + "parent_borrow"},
        DESC + "FallbackRegistryTests.oom_keeps_vector": {DESC + "fallback_registry_oom"},
        DESC + "FallbackRegistryTests.partial_copy_is_not_move": {"Compiler.Extraction.Memory.move_vector_eq"},
        DESC + "FallbackRegistryTests.readonly_copy": {DESC + "FallbackRegistryTests.readonly_first_copy",
            DESC + "FallbackRegistryTests.readonly_second_copy"},
        DESC + "FallbackRegistryTests.publication_fault_execution": {DESC + "FallbackRegistryTests.readonly_reservation",
            DESC + "FallbackRegistryTests.readonly_copy", DESC + "FallbackRegistryTests.readonly_release", DESC + "FallbackRegistryTests.readonly_publication"},
        DESC + "FallbackRegistryTests.publication_fault_keeps_release": {DESC + "FallbackRegistryTests.publication_fault_execution"},
        DESC + "FallbackRegistryTests.publication_fault_is_not_move": {DESC + "FallbackRegistryTests.publication_fault_keeps_release",
            "Compiler.Extraction.Memory.move_vector_eq"},
    }
    for name, wanted in required.items():
        if not wanted <= dependencies[name]:
            raise ValueError("release proof lost dependencies: " + name + ": " + ", ".join(sorted(wanted - dependencies[name])))
    return {"declarations": checked, "checkedDependencies": sorted(required),
            "refusingRemapGrowth": representative_remap_checks.audit(dependencies)}


def control_source():
    source = "\n".join("import " + module for module in (
        "Compiler.Extraction.RepresentativeArrayAllocation", "Compiler.Extraction.RepresentativeArrayAllocationView",
        "Compiler.Extraction.NormalizationMemoryContracts", "Compiler.Extraction.RepresentativeArrayTests",
        "Compiler.Extraction.ArgumentMemoryAllocation", "Compiler.Extraction.RepresentativeArrayCopyTests",
        "Compiler.Extraction.RepresentativePublicationTests", "Compiler.Extraction.RepresentativeCapacityTests",
        "Compiler.ZigAir.MemorySliceElements")) + "\n"
    # Bound diagnostic rendering of deliberately false concrete heap equations;
    # proof evaluation limits and the rejection checks below stay unchanged.
    source += "set_option pp.maxSteps 8\nset_option pp.deepTerms false\nset_option pp.notation false\n"
    return source + "\n".join(without_imports((ROOT / "lean/Compiler/Extraction" / name).read_text()) for name in FILES)


MUTATIONS = (
    ("wrong-empty-guard", "if capacity = 0 then (.ok (), before)", "if capacity = 1 then (.ok (), before)"),
    ("interior-free", "if data.offset ≠ 0 then .error (.memory .memoryValidity) else", "if data.offset > 32 then .error (.memory .memoryValidity) else"),
    ("wrong-brand", "Memory.release before.heap allocator data.allocation).mapError", "Memory.release before.heap (allocator + 1) data.allocation).mapError"),
    ("wrong-extent", "releaseOwned before.memory data.allocation (Backing.type capacity)).mapError", "releaseOwned before.memory data.allocation (Backing.type (capacity + 1))).mapError"),
    ("short-free", "external allocator base (capacity * 32) 8 before.effects⟩)", "external allocator base ((capacity - 1) * 32) 8 before.effects⟩)"),
    ("wrong-alignment", "external allocator base (capacity * 32) 8 before.effects⟩)", "external allocator base (capacity * 32) 4 before.effects⟩)"),
    ("wrong-base", ".ok (heap, memory, cell.base)", ".ok (heap, memory, cell.base + 8)"),
    ("callback-on-rejection", "| .error fault => (.error fault, before)\n  | .ok (heap, memory, base)",
        "| .error fault => (.error fault, { before with effects := external allocator 0 (capacity * 32) 8 before.effects })\n  | .ok (heap, memory, base)"),
    ("forgot-invalidation", ".ok (heap, memory, cell.base)", ".ok (heap, before.memory, cell.base)"),
    ("read-length-for-free", "match allocatedSlice before.memory header with", "match readItems before.memory header with"),
    ("request-wrong-brand", "let ((result, memory), effects) := Backing.reserve before.memory capacity (allocate allocator) before.effects",
        "let ((result, memory), effects) := Backing.reserve before.memory capacity (allocate (allocator + 1)) before.effects"),
    ("register-wrong-brand", "Memory.allocate before.heap allocator data.allocation (.representatives []) true",
        "Memory.allocate before.heap (allocator + 1) data.allocation (.representatives []) true"),
    ("register-wrong-lifetime", "Memory.allocate before.heap allocator data.allocation (.representatives []) true",
        "Memory.allocate before.heap allocator (data.allocation + 1) (.representatives []) true"),
    ("overwrite-collision", "Memory.allocate before.heap allocator data.allocation (.representatives []) true",
        "Memory.allocate (Memory.write before.heap data.allocation none) allocator data.allocation (.representatives []) true"),
    ("register-empty", "if capacity = 0 then (.ok (some data), reached) else", "if capacity = 1 then (.ok (some data), reached) else"),
    ("forget-registration", "| .ok heap => (.ok (some data), { reached with heap })", "| .ok heap => (.ok (some data), reached)"),
    ("rollback-collision", "| .error fault => (.error (.registry fault), reached)", "| .error fault => (.error (.registry fault), before)"),
    ("discard-oom-effects", "| .ok none => (.ok none, reached)", "| .ok none => (.ok none, before)"),
    ("register-wrong-block", "Memory.allocate before.heap allocator data.allocation (.representatives []) true",
        "Memory.allocate before.heap allocator data.allocation (.bytes (capacity * 32)) true"),
    ("register-oom", "| .ok none => (.ok none, reached)",
        "| .ok none => (.ok none, { reached with heap := Compiler.Extraction.Memory.write before.heap before.memory.nextId (some ⟨allocator, .representatives []⟩) })"),
    ("copy-wrong-source", "Copy.run before.memory source target length\n", "Copy.run before.memory (source + 1) target length\n"),
    ("copy-short-prefix", "Copy.run before.memory source target length\n", "Copy.run before.memory source target (length - 1)\n"),
    ("copy-reversed", "Copy.run before.memory source target length\n", "Copy.run before.memory target source length\n"),
    ("copy-forget-writes", "(result, { before with memory })", "(result, before)"),
    ("copy-forget-ownership", "(result, { before with memory })",
        "(result, { before with memory, heap := Compiler.Extraction.Memory.write before.heap target none })"),
    ("copy-ignore-failure", "(result, { before with memory })", "(.ok (), { before with memory })"),
    ("copy-change-lifetime", "(result, { before with memory })",
        "(result, { before with memory := { memory with nextId := before.memory.nextId + 1 } })"),
    ("relocate-wrong-free", "Release.run release allocator oldData oldCapacity before\n",
        "Release.run release allocator data capacity before\n"),
    ("relocate-short-free", "Release.run release allocator oldData oldCapacity before\n",
        "Release.run release allocator oldData (oldCapacity - 1) before\n"),
    ("relocate-forget-release", "Publication.Registered.run header data capacity afterRelease\n",
        "Publication.Registered.run header data capacity before\n"),
    ("relocate-forget-copy", "finish release allocator header oldData data oldCapacity capacity afterCopy\n",
        "finish release allocator header oldData data oldCapacity capacity before\n"),
    ("relocate-rollback-copy-fault", "| .error fault => (.error (.memory fault), afterCopy)",
        "| .error fault => (.error (.memory fault), before)"),
    ("relocate-publish-old-pointer", "Publication.Registered.run header data capacity afterRelease\n",
        "Publication.Registered.run header oldData capacity afterRelease\n"),
    ("relocate-rollback-publication-fault", "(published.mapError (fun fault => .memory fault), afterPublication)",
        "(published.mapError (fun fault => .memory fault), match published with | .error _ => afterRelease | .ok _ => afterPublication)"),
    ("relocate-ignore-publication-fault", "(published.mapError (fun fault => .memory fault), afterPublication)",
        "(.ok (), afterPublication)"),
    ("relocate-ignore-offset", "if (length ≠ 0 ∧ source.offset ≠ 0) ∨ data.offset ≠ 0 then", "if length ≠ 0 ∧ source.offset ≠ 0 then"),
    ("relocate-reject-empty-offset", "if (length ≠ 0 ∧ source.offset ≠ 0) ∨ data.offset ≠ 0 then", "if source.offset ≠ 0 ∨ data.offset ≠ 0 then"),
    ("relocate-ignore-source-offset", "if (length ≠ 0 ∧ source.offset ≠ 0) ∨ data.offset ≠ 0 then", "if data.offset ≠ 0 then"),
    ("publication-forget-stores", "(published, { before with memory })", "(published, before)"),
    ("fallback-wrong-allocator", "let (allocated, reserved) := Registry.run allocate allocator capacity before",
        "let (allocated, reserved) := Registry.run allocate (allocator + 1) capacity before"),
    ("fallback-rollback-allocation-fault", "| .error (.memory fault) => (.error (.memory fault), reserved)",
        "| .error (.memory fault) => (.error (.memory fault), before)"),
    ("fallback-wrong-registry-fault", "| .error (.registry fault) => (.error (.ownership fault), reserved)",
        "| .error (.registry _) => (.error (.memory .malformed), reserved)"),
    ("fallback-rollback-oom", "| .ok none => (.ok none, reserved)", "| .ok none => (.ok none, before)"),
    ("fallback-oom-success", "| .ok none => (.ok none, reserved)", "| .ok none => (.ok (some ()), reserved)"),
    ("fallback-forget-allocation", "Relocation.run release allocator header oldData data oldCapacity capacity reserved\n",
        "Relocation.run release allocator header oldData data oldCapacity capacity before\n"),
    ("fallback-reuse-old-backing", "Relocation.run release allocator header oldData data oldCapacity capacity reserved\n",
        "Relocation.run release allocator header oldData oldData oldCapacity capacity reserved\n"),
    ("fallback-rollback-suffix", "(relocated.map some, reached)", "(relocated.map some, reserved)"),
    ("fallback-rollback-suffix-fault", "(relocated.map some, reached)",
        "(relocated.map some, match relocated with | .error _ => before | .ok _ => reached)"),
    ("fallback-ignore-suffix-fault", "(relocated.map some, reached)", "(.ok (some ()), reached)"),
    ("descriptor-item-root", "(descriptorFields ⟨cell.itemAddress, 0⟩", "(descriptorFields ⟨cell.itemAddress, 8⟩"),
    ("descriptor-argument-root", "⟨cell.argumentsAddress, 0⟩ cell.arguments.length index", "⟨cell.argumentsAddress, 4⟩ cell.arguments.length index"),
    ("descriptor-argument-length", "cell.arguments.length index cell.sequence.toNat).map", "(cell.arguments.length + 1) index cell.sequence.toNat).map"),
    ("descriptor-stored-id", "cell.arguments.length index cell.sequence.toNat).map", "cell.arguments.length 0 cell.sequence.toNat).map"),
    ("descriptor-sequence", "cell.arguments.length index cell.sequence.toNat).map", "cell.arguments.length index 0).map"),
    ("descriptor-ignore-later-rows", "cells[index]? = some cell → Row state lifetime index cell",
        "cells[index]? = some cell → index = 0 → Row state lifetime index cell"),
    ("append-bypasses-capacity", "    let ((capacity, ready), reached) := ensure state header newLength effects",
        "    let ((capacity, ready), reached) : (Except ε (Option Unit) × State) × σ := ((.ok (some ()), state), effects)"),
    ("append-rewinds-assignment-fault", "      | .error fault => ((.error (reject fault), after), reached)",
        "      | .error fault => ((.error (reject fault), state), reached)"),
    ("append-discards-private-effects", "      | .ok () => ((.ok (some ()), after), reached)",
        "      | .ok () => ((.ok (some ()), after), effects)"),
    ("append-oom-is-success", "    | .ok none => ((.ok none, ready), reached)", "    | .ok none => ((.ok (some ()), ready), reached)"),
    ("append-selects-before-length-store", "      | .ok ready => finish ready header newLength itemAddress argumentsAddress argumentsLength id sequence",
        "      | .ok ready => finish state header newLength itemAddress argumentsAddress argumentsLength id sequence"),
    ("append-overwrites-first-row", "| .ok address => initializeFieldsReached state address.allocation (address.offset / 32)\n",
        "| .ok address => initializeFieldsReached state address.allocation 0\n"),
    ("registry-append-keeps-old-vector",
        "    heap := Compiler.Extraction.Memory.write before.heap lifetime (some ⟨allocator, .representatives (cells ++ [cell])⟩) }",
        "    heap := Compiler.Extraction.Memory.write before.heap lifetime (some ⟨allocator, .representatives cells⟩) }"),
    ("registry-append-discards-old-rows",
        "    heap := Compiler.Extraction.Memory.write before.heap lifetime (some ⟨allocator, .representatives (cells ++ [cell])⟩) }",
        "    heap := Compiler.Extraction.Memory.write before.heap lifetime (some ⟨allocator, .representatives [cell]⟩) }"),
    ("registry-append-wrong-allocator",
        "    heap := Compiler.Extraction.Memory.write before.heap lifetime (some ⟨allocator, .representatives (cells ++ [cell])⟩) }",
        "    heap := Compiler.Extraction.Memory.write before.heap lifetime (some ⟨allocator + 1, .representatives (cells ++ [cell])⟩) }"),
    ("registry-append-wrong-lifetime",
        "    heap := Compiler.Extraction.Memory.write before.heap lifetime (some ⟨allocator, .representatives (cells ++ [cell])⟩) }",
        "    heap := Compiler.Extraction.Memory.write before.heap (lifetime + 1) (some ⟨allocator, .representatives (cells ++ [cell])⟩) }"),
    ("first-registry-keeps-empty-vector",
        "    heap := Compiler.Extraction.Memory.write before.heap before.memory.nextId (some ⟨allocator, .representatives [cell]⟩) }",
        "    heap := Compiler.Extraction.Memory.write before.heap before.memory.nextId (some ⟨allocator, .representatives []⟩) }"),
    ("first-registry-uses-owner-lifetime",
        "    heap := Compiler.Extraction.Memory.write before.heap before.memory.nextId (some ⟨allocator, .representatives [cell]⟩) }",
        "    heap := Compiler.Extraction.Memory.write before.heap owner (some ⟨allocator, .representatives [cell]⟩) }"),
    ("first-registry-wrong-allocator",
        "    heap := Compiler.Extraction.Memory.write before.heap before.memory.nextId (some ⟨allocator, .representatives [cell]⟩) }",
        "    heap := Compiler.Extraction.Memory.write before.heap before.memory.nextId (some ⟨allocator + 1, .representatives [cell]⟩) }"),
    ("first-registry-discards-effects", "    effects := reached\n", "    effects := before.effects\n"),
    ("first-registry-publishes-unwritten-row",
        "      heap := Compiler.Extraction.Memory.write before.heap before.memory.nextId (some ⟨allocator, .representatives []⟩) }",
        "      heap := Compiler.Extraction.Memory.write before.heap before.memory.nextId (some ⟨allocator, .representatives [⟨⟨0, none, 0⟩, 0, 0, [], 0, 0⟩]⟩) }"),
    ("first-registry-selects-wrong-callback",
        "        cell.arguments.length 0 cell.sequence.toNat (allocate allocator) before.effects = ((.ok (some ()), after.memory), after.effects)",
        "        cell.arguments.length 0 cell.sequence.toNat (allocate (allocator + 1)) before.effects = ((.ok (some ()), after.memory), after.effects)"),
    ("fallback-registry-empty-vector",
        "    heap := Compiler.Extraction.Memory.write raw.heap before.memory.nextId (some ⟨allocator, .representatives cells⟩) }",
        "    heap := Compiler.Extraction.Memory.write raw.heap before.memory.nextId (some ⟨allocator, .representatives []⟩) }"),
    ("fallback-registry-wrong-owner",
        "    heap := Compiler.Extraction.Memory.write raw.heap before.memory.nextId (some ⟨allocator, .representatives cells⟩) }",
        "    heap := Compiler.Extraction.Memory.write raw.heap before.memory.nextId (some ⟨allocator + 1, .representatives cells⟩) }"),
    ("fallback-registry-wrong-lifetime",
        "    heap := Compiler.Extraction.Memory.write raw.heap before.memory.nextId (some ⟨allocator, .representatives cells⟩) }",
        "    heap := Compiler.Extraction.Memory.write raw.heap (before.memory.nextId + 1) (some ⟨allocator, .representatives cells⟩) }"),
    ("fallback-registry-keeps-old-entry",
        "    heap := Compiler.Extraction.Memory.write raw.heap before.memory.nextId (some ⟨allocator, .representatives cells⟩) }",
        "    heap := Compiler.Extraction.Memory.write before.heap before.memory.nextId (some ⟨allocator, .representatives cells⟩) }"),
    ("fallback-registry-discards-effects",
        "      after.memory = raw.memory ∧ after.effects = raw.effects ∧",
        "      after.memory = raw.memory ∧ after.effects = before.effects ∧"),
    ("fallback-registry-publishes-raw",
        "      raw.heap = Compiler.Extraction.Memory.write\n        (Compiler.Extraction.Memory.write before.heap before.memory.nextId (some ⟨allocator, .representatives []⟩)) source none ∧",
        "      raw.heap = Compiler.Extraction.Memory.write\n        (Compiler.Extraction.Memory.write before.heap before.memory.nextId (some ⟨allocator, .representatives cells⟩)) source none ∧"),
    ("fallback-registry-accepts-copy-fault",
        "      (.error (.memory .uninitialized), copyReached runtimeSafety) :=",
        "      (.ok (some ()), copyReached runtimeSafety) :="),
    ("fallback-registry-accepts-publication-fault",
        "      (.error (.memory .readOnly), readonlyReleased runtimeSafety) :=",
        "      (.ok (some ()), readonlyReleased runtimeSafety) :="),
    ("fallback-registry-wrong-callback",
        "      Backing.Fallback.run allocate release allocator (Owner.headerAddress ⟨owner, 0⟩) ⟨source, 0⟩ oldCapacity capacity before =",
        "      Backing.Fallback.run allocate release (allocator + 1) (Owner.headerAddress ⟨owner, 0⟩) ⟨source, 0⟩ oldCapacity capacity before ="),
)


def controls(output, env, lean, *, names=None):
    source = control_source()
    available = {name for name, _, _ in MUTATIONS}
    if len(available) != len(MUTATIONS) or names is not None and names - available:
        raise ValueError("invalid release control selection")
    for name, original, _ in MUTATIONS:
        if source.count(original) != 1:
            raise ValueError("ambiguous release mutation: " + name)
    records = [mutation_check(output, "release-unchanged", source, True, env, lean)]
    for name, original, replacement in MUTATIONS:
        if names is None or name in names:
            records.append(mutation_check(output, "release-" + name, source.replace(original, replacement, 1), False, env, lean))
    for record in records:
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant|invalidDottedIdent",
                     (output / (record["name"] + ".stdout")).read_text(), re.I):
            raise ValueError("release control hit a resource or syntax failure: " + record["name"])
    return records


def native(output, compiler, lib, modes=("Debug", "ReleaseSafe", "ReleaseFast")):
    records = []
    for mode in modes:
        binary = output / ("release-" + mode)
        run(output, "build-" + mode, [compiler, "build-exe", "-j4", "--zig-lib-dir", lib, "-fllvm", "-O", mode,
            "--dep", "compiler", "-Mroot=" + str(PROBE), "-O", mode, "-Mcompiler=" + str(ROOT / "src/modules.zig"),
            "--cache-dir", ROOT / ".zig-cache", "--global-cache-dir", output / "global-cache", "-femit-bin=" + str(binary)], cwd=ROOT)
        run(output, "probe-" + mode, [binary], cwd=ROOT)
        raw = (output / ("probe-" + mode + ".stdout")).read_bytes()
        observation = output / ("probe-" + mode + ".json")
        observation.write_bytes(raw)
        if len(raw) > 8192:
            raise ValueError("native release observation exceeded bound")
        check_observation(json.loads(raw), mode)
        if (output / ("build-" + mode + ".stderr")).read_bytes() or (output / ("probe-" + mode + ".stderr")).read_bytes():
            raise ValueError("unreviewed native release diagnostic")
        records.append({"mode": mode, "accepted": True, "binarySha256": digest(binary), "observationSha256": digest(observation)})
    return records


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.representative-release-verification.v1", "status": "failed", "jobs": 4,
        "scope": "logical-cell descriptor and registry-vector correspondence through complete first-growth and spare-capacity append and the admitted nonempty allocation fallback; fallback publication refines the existing logical move with identical reached memory and effects, invalidated old lifetimes and preserved independent parent views; raw provisional storage, partial copy/publication and ordinary OOM remain distinct; all-ID lookup agreement follows from reached fields and geometry; saved views remain evaluated under fixed host.allocation, host.copy and host.release; the shared growth prefix and source-bound noRemap refusal compose with fallback; callback identity, other remap implementations, complete native growth, item payloads, native allocator identity, map and recursive correspondence remain open",
        "fallbackRegistryCorrespondenceVerified": False, "firstAppendRegistryCorrespondenceVerified": False, "spareAppendRegistryCorrespondenceVerified": False, "typedAppendDescriptorCorrespondenceVerified": False, "typedDescriptorCorrespondenceVerified": False, "checkedAllocationFallbackVerified": False, "checkedRelocationSuffixVerified": False, "checkedRegisteredCopyVerified": False, "checkedRegisteredBackingReservationVerified": False, "checkedBackingReleaseVerified": False, "nativeGrowthVerified": False, "nativeGraphMutationCorrespondenceVerified": False,
        "recursiveConstructorsVerified": False, "nativeBackendVerified": False, "wholeCompilerVerified": False}
    try:
        report["inputs"] = inputs()
        toolchain = json.loads(args.toolchain.read_bytes())
        compiler, lib = Path(toolchain["compiler"]["path"]), Path(toolchain["compiler"]["zigLibDir"])
        report["toolchainReportSha256"], report["compilerSha256"] = digest(args.toolchain), digest(compiler)
        if report["compilerSha256"] != toolchain["compiler"]["sha256"] or source_identity(lib.parent) != toolchain["sourceTree"]:
            raise ValueError("release toolchain inputs changed")
        report["wrapperAdmission"] = admission.check(lib)
        report["refusingRemapAdmission"] = remap_admission.check(lib)
        report["descriptorAdmission"] = append_admission.check(lib)
        report["capacityAdmission"] = array_gate.capacity_admission.check(lib)
        report["sourceFunctions"] = ["ExpressionClasses.insertOwned", "ExpressionClasses.representative", "ArrayList(Expression).append",
            "ArrayList(Expression).addOne", "ArrayList(Expression).addOneAssumeCapacity", "ArrayList(Expression).ensureTotalCapacity",
            "ArrayList(Expression).growCapacity", "ArrayList(Expression).ensureTotalCapacityPrecise",
            "ArrayList(Expression).allocatedSlice", "Allocator.remap", "Allocator.rawRemap", "Allocator.noRemap", "Allocator.free"]
        report["hostCalls"] = ["Allocator.alloc: host.allocation", "@memcpy: host.copy", "Allocator.free: host.release"]
        env, _, tools = lean_check.toolchain(args.lean_bin, 4)
        report["tools"] = tools
        run(output, "python-preflight", [sys.executable, "-m", "unittest", "discover", "-s", "test/lean", "-p", "test_representative_release.py"], cwd=ROOT)
        run(output, "source-preflight", [sys.executable, "-m", "unittest", "discover", "-s", "test/lean", "-p", "test_representative_growth.py"], cwd=ROOT)
        run(output, "remap-preflight", [sys.executable, "-m", "unittest", "discover", "-s", "test/lean", "-p", "test_representative_remap.py"], cwd=ROOT)
        run(output, "descriptor-preflight", [sys.executable, "-m", "unittest", "discover", "-s", "test/lean", "-p", "test_representative_array.py"], cwd=ROOT)
        run(output, "assignment-preflight", [sys.executable, "-m", "unittest", "discover", "-s", "test/lean", "-p", "test_representative_append.py"], cwd=ROOT)
        run(output, "capacity-preflight", [sys.executable, "-m", "unittest", "discover", "-s", "test/lean", "-p", "test_representative_capacity.py"], cwd=ROOT)
        run(output, "cached-proof", [tools["lake"]["path"], "build", MODULE], cwd=ROOT / "lean", env=env)
        report["audit"] = audit(output, env, tools["lean"]["path"])
        report["controls"] = controls(output, env, tools["lean"]["path"]) + representative_remap_checks.controls(output, env, tools["lean"]["path"])
        run(output, "version", [compiler, "version"])
        if text(output, "version") != "0.17.0":
            raise ValueError("release requires pinned Zig 0.17.0")
        report["native"] = native(output, compiler, lib)
        report["nativeDescriptors"] = array_gate.native(output, compiler, lib)
        write_json(output / "report.json", report)
        proof, artifacts = prove.check_module(MODULE, CLAIMS, lean_bin=args.lean_bin, jobs=4, fresh=True)
        directory = output / "proof"
        directory.mkdir()
        for name, data in artifacts.items():
            (directory / name).write_bytes(data)
        write_json(directory / "report.json", proof)
        report["proofReportSha256"] = digest(directory / "report.json")
        if (proof.get("status") != "passed" or proof.get("freshKernelReplay") is not True or
                proof.get("replayIncludesImports") is not True or proof.get("auditedDeclarations") != CLAIMS):
            raise ValueError("release proof or fresh imported replay failed")
        if (inputs() != report["inputs"] or digest(args.toolchain) != report["toolchainReportSha256"] or
                digest(compiler) != report["compilerSha256"] or source_identity(lib.parent) != toolchain["sourceTree"]):
            raise ValueError("release acceptance inputs changed")
        report.update(status="passed", checkedBackingReleaseVerified=True, checkedRegisteredBackingReservationVerified=True,
            checkedRegisteredCopyVerified=True, checkedRelocationSuffixVerified=True, checkedAllocationFallbackVerified=True,
            typedDescriptorCorrespondenceVerified=True, typedAppendDescriptorCorrespondenceVerified=True,
            spareAppendRegistryCorrespondenceVerified=True, firstAppendRegistryCorrespondenceVerified=True, fallbackRegistryCorrespondenceVerified=True)
    except BaseException as error:
        report["error"] = str(error)
        raise
    finally:
        write_json(output / "report.json", report)
    print("Descriptor correspondence and source-bound remap refusal/fallback passed; callback identity, other remaps, complete native graph correspondence and recursive constructors remain open.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    check(parser.parse_args())
