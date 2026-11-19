#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Check the production algebraic rewrite table, its Lean proofs and negative controls.
This is a development/CI gate for pure word rewrites, not a bytecode certificate.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "lean"))
import environment as source
import prove
import extract_compiler
import compiler_ir
import extract_storage
import extract_cache
import extract_assembly_clone
import extract_owned_keys
import extract_interner
import extract_constructor
import extract_folding
import extract_nested
import extract_nested_construction
import extract_associative
import extract_shift_masks
import extract_opposite_shifts
import extract_signextend_mask
import extract_binary_logarithm
import extract_address_mask
import extract_alternating_mask
import extract_dispatch
from test_compiler_nested import opcode_mutation as nested_opcode_mutation
from test_compiler_nested_construction import opcode_mutation as nested_construction_opcode_mutation
from test_compiler_associative import opcode_mutation as associative_opcode_mutation
from test_compiler_shift_masks import opcode_mutation as shift_masks_opcode_mutation
from test_compiler_opposite_shifts import opcode_mutation as opposite_shifts_opcode_mutation
from test_compiler_signextend_mask import opcode_mutation as signextend_mask_opcode_mutation
from test_compiler_address_mask import opcode_mutation as address_mask_opcode_mutation
from test_compiler_alternating_mask import opcode_mutation as alternating_mask_opcode_mutation
from test_compiler_dispatch import opcode_mutation as dispatch_opcode_mutation
from test_compiler_folding import MUTATIONS as FOLDING_MUTATIONS, mutated as folding_mutated
from test_compiler_constructor import MUTATIONS as CONSTRUCTOR_MUTATIONS, mutated as constructor_mutated
from test_compiler_interner import MUTATIONS as INTERNER_MUTATIONS, mutated as interner_mutated
from test_compiler_cache import MUTATIONS as CACHE_MUTATIONS, mutated as cache_mutated
from test_compiler_assembly_clone import MUTATIONS as ASSEMBLY_CLONE_MUTATIONS, mutated as assembly_clone_mutated
from test_compiler_storage import MUTATIONS as STORAGE_MUTATIONS, READ_MUTATIONS
from test_compiler_extraction import CONSTRUCTION_MUTATIONS, MUTATIONS, mutate

CLAIMS = ["Compiler.Algebraic." + name for name in (
    "matches_sound", "select_sound", "replacement_eval", "production_rules_sound",
    "production_selection_sound", "production_expression_sound",
    "zigMatches_eq", "productionOpcode_injective", "zigSelectFrom_eq",
    "zigSelectFrom_unknown", "zigSelect_sound", "Effect.bind_failure",
    "replacement_build_sound", "zigApply_eq", "zigApply_sound", "zigRewrite_sound")] + [
    "Compiler.Validation." + name for name in (
        "normalize_sound", "equivalent_sound", "evaluate_expand", "validate_sound")] + [
    "Compiler.Validation." + name for name in (
        "WordBlock.run_map", "WordBlock.validate_sound", "WordBlock.metered_of_execute",
        "SolidityWord.lower_sound", "SolidityWord.bytecode_sound", "SolidityWord.metered_bytecode_sound")] + [
    "Compiler.Extraction.IR." + name for name in (
        "matcher_correspondence", "selection_correspondence", "construction_correspondence", "each_return_null")] + [
    "Compiler.Extraction.Storage." + name for name in (
        "insert_safe_any", "insert_outcome", "insert_progress", "idFor_toNat", "published_preserves",
        "published_returns", "failure_restores", "representative_correct", "representative_no_fault",
        "constant_correct", "constant_fact_sound", "constant_stable", "discoveredFacts_reliable")] + [
    "Compiler.Extraction.Cache." + name for name in (
        "equality_iff", "key_sound", "key_missing_instruction", "readArguments_length", "readArguments_stable", "key_stable",
        "valid_stable", "hit_sound", "put_valid", "put_returns", "commutative_sound", "normalize_binary",
        "normalize_noncommutative", "normalize_constant", "normalize_missing_instruction")] + [
    "Compiler.Extraction.Interner." + name for name in (
        "Safe.bind", "publish_safe", "miss_safe", "owned_safe", "find_safe", "find_ensures",
        "force_safe", "inserted_stable", "insert_transaction_safe",
        "buildOpcode_correct", "constructorMeaning_laws", "constant_request_sound", "operation_request_sound",
        "constant_safe", "operation_safe", "implemented_builder_safe", "replacement_safe_of_builder",
        "replacement_safe", "extracted_apply_safe", "extracted_rewrite_safe")] + [
    "Compiler.Extraction.Folding." + name for name in (
        "highBit_toNat",
        "highBit_test",
        "signMask_correct",
        "signedDivision_correct",
        "signedModulo_correct",
        "byteValue_correct",
        "shiftLeft_correct",
        "shiftRight_correct",
        "addMod_correct",
        "mulMod_correct",
        "powerLoop_correct",
        "wrappingPower_correct",
        "signExtend_correct",
        "folding_correct",
        "folding_unknown",
        "folding_wrong_arity")] + [
    "Compiler.Extraction.Storage." + name for name in (
        "operation_correct", "operation_found", "coherent_empty", "item_stable", "append_read_stable",
        "coherent_append", "coherent_nodesAfter", "operation_fact_sound", "operation_no_fault", "operation_stable")] + [
    "Compiler.Extraction.Memory." + name for name in (
        "write_same", "write_other", "slice_read",
        "empty_release", "wrong_allocator", "allocation_failure",
        "resident_vector_write", "resident_fresh_write", "move_vector_eq",
        "move_vector_preserves", "move_vector_oom", "move_vector_in_place",
        "operation_borrow_read", "operation_borrow_after_move", "representative_refines",
        "vector_append_preserves", "fresh_cleanup_preserves", "release_success",
        "release_fresh_preserves")] + [
    "Compiler.Extraction.Folding." + name for name in (
        "decode_word_opcode", "word_meaning_operation", "word_meaning_other", "folding_meaning")] + [
    "Compiler.Extraction.Nested." + name for name in (
        "nested_not_opcode", "storage_reads_sound", "cancel_found",
        "absorbed_found", "negation_found", "split_constant_found",
        "split_constant_sound", "cancel_xor_sound", "absorbed_and_sound",
        "absorbed_or_sound", "negation_sound", "storage_cancel_xor_sound",
        "storage_helpers_total", "operation_values", "unary_values", "binary_values", "word_operation_request_sound", "interner_constructs",
        "read_action_bind_safe", "nested_iszero_opcode", "double_iszero_safe", "repeated_operands_found",
        "repeated_operands_sound", "idempotent_arity", "idempotent_repeat", "drop_repeated_safe",
        "interner_drop_repeated_safe")] + [
    "Compiler.Extraction.Associative." + name for name in (
        "supported_arity", "commutative", "associative", "interner_constant_safe", "constructor_meaning_pushes",
        "selection_complete", "combination_correct", "combination_fault", "implemented_constructors_sound",
        "split_value", "folded_value", "moved_value", "reassociate_safe", "interner_reassociate_safe")] + [
    "Compiler.Extraction.ShiftMasks." + name for name in (
        "power_shift_value", "divisor_shift_value", "coverage_contains", "covered_mask_value", "shl_opcode", "shr_opcode",
        "coverage_correct", "coverage_fault", "shift_product_safe", "remove_mask_safe", "interner_helpers_safe")] + [
    "Compiler.Extraction.OppositeShifts." + name for name in (
        "right_after_left", "left_after_right", "masked_net", "and_opcode", "opposite_opcode",
        "native_mask_correct", "native_mask_fault", "combine_cast_fault", "difference_correct", "difference_fault",
        "evm_shift", "net_safe", "combine_safe", "interner_combine_safe")] + [
    "Compiler.Extraction.SignExtendMask." + name for name in (
        "masked_sign_extension", "masked_evm_signextend", "signextend_opcode", "and_opcode",
        "native_low_mask_correct", "low_mask_read_correct", "low_mask_read_fault", "strip_safe", "interner_strip_safe")] + [
    "Compiler.Extraction.BinaryLogarithm." + name for name in (
        "clear_lowest_bit", "power_nonzero", "word_clear", "ctz_bound", "ctz_power", "zero_rejected",
        "native_correct", "found_iff", "none_iff", "result_exact", "found_sound", "found_shift_value")] + [
    "Compiler.Extraction.AddressMask." + name for name in (
        "address_operation", "other_operation", "address_mask", "kind_mask", "context_address", "context_caller",
        "native_mask", "native_mask_subtraction", "supported_opcode", "search_found", "address_found", "found_sound",
        "search_total", "storage_total", "interner_rebuild_safe")] + [
    "Compiler.Extraction.AlternatingMask." + name for name in (
        "distribution", "and_opcode", "or_opcode", "candidate_found", "candidate_sound", "build_safe",
        "search_safe", "distribute_safe", "interner_distribute_safe", "search_skips", "search_stops",
        "search_failure", "search_miss")] + [
    "Compiler.Extraction.Dispatch." + name for name in (
        "arithmetic_bind_safe", "or_next_safe", "or_next_failure", "or_next_match", "or_next_miss",
        "collected_values", "folding_found", "constant_stage_safe", "default_options", "revision_gates",
        "triple_iszero", "boolean_double_iszero", "equality_of_zero_test", "operation_some_safe",
        "operation_probe_safe", "unary_not_safe", "unary_iszero_safe", "unary_stage_safe",
        "interner_unary_stage_safe", "unary_stage_miss",
        "pure_miss_unchanged", "terminal_miss_unchanged", "read_miss_unchanged", "arithmetic_miss_unchanged",
        "constant_stage_miss", "or_next_safe_of_unchanged", "binary_word_opcode", "binary_word_eval",
        "algebraic_builder_safe", "algebraic_apply_safe", "selected_word_value", "algebraic_selected_safe",
        "constant_facts_reliable", "equal_facts_reliable", "binary_comparison_safe", "binary_comparison_miss",
        "comparison_evm_stage", "comparison_simplify_safe", "interner_comparison_simplify_safe",
        "never_miss_unchanged", "bind_never_miss", "terminal_never_miss",
        "or_next_miss_unchanged", "optional_bind_eq", "optional_bind_safe_of_unchanged",
        "optional_bind_miss_unchanged", "binary_simplify_safe", "constant_some_safe", "constant_left_operation_some_safe",
        "reassociate_miss", "repeated_miss", "reassociation_pair_safe",
        "repeated_pair_safe", "xor_capture_value", "or_absorption_value",
        "or_negation_value", "binary_add_or_xor_safe", "binary_add_or_xor_miss",
        "add_or_xor_evm_stage", "add_or_xor_simplify_safe", "interner_add_or_xor_simplify_safe",
        "signed_division_zero_right", "signed_division_zero_left", "signed_division_one",
        "signed_division_inline_safe", "binary_signed_safe", "binary_signed_miss",
        "signed_evm_stage", "signed_simplify_safe", "interner_signed_simplify_safe",
        "unary_simplify_safe", "word_unary_evm_stage",
        "word_unary_simplify_safe", "interner_word_unary_simplify_safe",
        "shift_product_miss", "shift_product_pair_safe", "binary_mul_safe",
        "binary_mul_miss", "binary_log_mul_value", "constant_shift_some_safe",
        "mul_power_candidate_safe", "mul_evm_stage_safe", "mul_evm_miss",
        "mul_simplify_safe", "interner_mul_simplify_safe",
        "shift_divisor_safe", "binary_div_safe", "binary_div_miss", "binary_log_div_value",
        "div_evm_stage_safe", "div_evm_miss", "div_simplify_safe", "interner_div_simplify_safe",
        "evm_stage_other_arity", "other_arity_simplify", "other_arity_simplify_safe",
        "other_arity_simplify_miss", "ternary_simplify_safe", "interner_ternary_simplify_safe",
        "mod_power_positive", "mod_power_predecessor", "mod_power_mask_value",
        "mod_power_wrapped_value", "mod_power_add_value", "mod_power_mul_value",
        "mod_nested_candidate_safe", "mod_mask_candidate_safe", "mod_inline_safe",
        "binary_mod_safe", "binary_mod_miss", "mod_evm_stage",
        "mod_simplify_safe", "interner_mod_simplify_safe",
        "word_power_one", "exp_zero_value", "exp_one_value",
        "exp_two_value", "word_power_minus_one", "exp_minus_one_value",
        "exp_minus_one_safe", "exp_evm_stage_safe", "binary_exp_safe",
        "binary_exp_miss", "exp_evm_miss", "exp_simplify_safe",
        "interner_exp_simplify_safe",
        "sub_constant_value", "sub_left_add_value", "sub_right_add_value",
        "sub_left_sub_right_value", "sub_left_sub_left_value", "sub_right_sub_right_value",
        "sub_right_sub_left_value", "sub_rebuild_safe", "sub_left_add_safe",
        "sub_right_add_safe", "sub_left_sub_safe", "sub_right_sub_safe",
        "sub_inline_safe", "binary_sub_safe", "binary_sub_miss",
        "sub_evm_stage", "sub_simplify_safe", "interner_sub_simplify_safe",
        "byte_bits", "byte_zero_value", "byte_large_value",
        "byte_last_value", "byte_left_shift_value", "byte_right_shift_zero_value",
        "byte_right_shift_value", "byte_index_add", "byte_index_sub",
        "byte_left_candidate_safe", "byte_right_candidate_safe", "byte_tail_safe",
        "binary_byte_safe", "binary_byte_miss", "byte_evm_stage",
        "byte_simplify_safe", "interner_byte_simplify_safe",
        "shift_word_value", "shift_large_value", "shift_sum_threshold",
        "same_shift_nat_value", "same_shift_zero_value", "same_shift_sum_value",
        "shift_index_add", "shift_mask_value", "same_shift_candidate_safe",
        "opposite_shift_candidate_safe", "masked_shift_candidate_safe", "shr_tail_safe",
        "binary_shr_safe", "binary_shr_miss", "shr_evm_stage",
        "shr_simplify_safe", "interner_shr_simplify_safe",
        "signextend_bits", "shift_byte_alignment", "shift_byte_quotient",
        "shl_signextend_value", "shl_signextend_index_add", "shl_signextend_candidate_safe",
        "shl_tail_safe", "binary_shl_safe", "binary_shl_miss",
        "shl_evm_stage", "shl_simplify_safe", "interner_shl_simplify_safe")] + ["Compiler.Extraction.ArithmeticShift." + name for name in (
        "value_nat", "value_signed_floor", "value_large",
        "operation", "other_operation", "interner_constructs")] + ["Compiler.Extraction.Dispatch." + name for name in (
        "signextend_min_value", "signextend_repeat_value", "signextend_large_value",
        "signextend_shr_value", "signextend_shift_sub", "signextend_index_add",
        "signextend_nested_safe", "signextend_shift_safe", "signextend_tail_safe",
        "binary_signextend_safe", "binary_signextend_miss", "signextend_evm_stage",
        "signextend_simplify_safe", "interner_signextend_simplify_safe")] + ["Compiler.Extraction.AddressMask.interner_constructs"] + ["Compiler.Extraction.Dispatch." + name for name in (
        "signextend_mask_miss", "covered_mask_miss", "alternating_search_miss",
        "byte_value_mask", "byte_mask_candidate_safe", "and_absorption_value",
        "and_negation_value", "and_shifts_value", "merged_shifts_safe",
        "address_mask_candidate_safe", "and_tail_safe", "binary_and_safe",
        "binary_and_miss", "and_evm_stage", "and_simplify_safe",
        "interner_and_simplify_safe")] + ["Compiler.Extraction.Dispatch." + name for name in (
        "address_shift_commute", "word_dispatch_address_model", "word_dispatch_operation",
        "word_dispatch_other", "word_dispatch_decoded", "word_binary_simplify_safe",
        "word_simplify_safe", "decoded_word_simplify_safe", "interner_word_simplify_safe")] + ["Compiler.Extraction.Dispatch." + name for name in (
        "nonword_opcode", "nonword_table", "nonword_binary", "nonword_unary", "nonword_evm_stage",
        "nonword_constant_safe", "nonword_binary_safe", "nonword_binary_miss", "nonword_simplify_safe",
        "simplify_without_balance_safe", "default_simplify_safe", "interner_default_simplify_safe",
        "default_key_simplify_safe")] + ["Compiler.Extraction.Recursive." + name for name in (
        "constructors_interner", "constructors_sound", "constructors_address", "constructors_sar",
        "make_key_kind", "miss_operation_only", "owned_operation_only", "find_operation_only",
        "step_source_body", "step_ignores_seed_simplifier", "step_safe", "unfold_safe",
        "executes_safe", "unsupported_not_execution", "Tests.pushes", "Tests.reads_sound",
        "Tests.allocate_safe", "Tests.primitive_contracts", "Tests.completed", "Tests.preserved")] + [
    "Compiler.Extraction.Cache.commutative_word_opcode",
    "Compiler.Extraction.Cache.read_eval_wrong_arity",
    "Compiler.Extraction.Cache.read_eval_binary_permutation",
    "Compiler.Extraction.Cache.normalize_word",
    "Compiler.Extraction.Cache.normalizes_of_source",
    "Compiler.Extraction.Recursive.unfold_normalized_safe",
    "Compiler.Extraction.Cache.NormalizationTests.sort_permutation",
    "Compiler.Extraction.Cache.NormalizationTests.refines",
    "Compiler.Extraction.Cache.NormalizationTests.normalizes",
    "Compiler.Extraction.Cache.NormalizationTests.recursive_safe",
    "Compiler.Extraction.Cache.NormalizationTests.preserved",
    "Compiler.Extraction.Cache.NormalizationTests.failure_refines",
    "Compiler.Extraction.Cache.NormalizationOwnership.run_safe",
    "Compiler.Extraction.Cache.NormalizationOwnership.exact_fit",
    "Compiler.Extraction.Cache.NormalizationOwnership.heap_transfer",
    "Compiler.Extraction.Cache.NormalizationOwnership.threshold_agrees",
    "Compiler.Extraction.Cache.NormalizationOwnership.Tests.failure_order",
    "Compiler.Extraction.Cache.NormalizationOwnership.Tests.no_reallocation",
    "Compiler.Extraction.Interner.abstract_invariant_iff",
    "Compiler.Extraction.Interner.observed_invariant",
    "Compiler.Extraction.Interner.invariant_observations",
    "Compiler.Extraction.Interner.representative_reads_sound",
    "Compiler.Extraction.Interner.publication_preserves_observations",
    "Compiler.Extraction.Recursive.unfold_representatives_safe",
    "Compiler.Extraction.Interner.ObservedTests.constant_coherent",
    "Compiler.Extraction.Interner.ObservedTests.caller_coherent",
    "Compiler.Extraction.Interner.ObservedTests.constant_valid",
    "Compiler.Extraction.Interner.ObservedTests.caller_valid",
    "Compiler.Extraction.Interner.ObservedTests.same_values",
    "Compiler.Extraction.Interner.ObservedTests.forged_read_rejected",
    "Compiler.Extraction.Interner.ObservedTests.forged_structure_rejected",
    "Compiler.Extraction.Interner.ObservedTests.contracts",
    "Compiler.Extraction.Interner.ObservedTests.preserved",
    "Compiler.Extraction.Interner.insert_result_read",
    "Compiler.Extraction.Interner.observed_insert_transaction_safe",
    "Compiler.Extraction.Interner.observed_insert_retains_cells",
    "Compiler.Extraction.Interner.observed_insert_safe",
    "Compiler.Extraction.Interner.insertion_preserves_cell",
    "Compiler.Extraction.Interner.insertion_preserves_constant",
    "Compiler.Extraction.Interner.insertion_preserves_operation",
    "Compiler.Extraction.Interner.ObservedStorageTests.binding",
    "Compiler.Extraction.Interner.ObservedStorageTests.denotation",
    "Compiler.Extraction.Interner.ObservedStorageTests.preserved",
    "Compiler.Extraction.Interner.ObservedStorageTests.action_preserved",
    "Compiler.Extraction.Interner.ObservedStorageTests.each_failure_restores",
    "Compiler.Extraction.Interner.ObservedStorageTests.uncached_preserved",
    "Compiler.Extraction.Interner.ObservedStorageTests.wrong_binding_rejected",
    "Compiler.Extraction.Interner.ObservedStorageTests.wrong_cell_rejected",
    "Compiler.Extraction.AssemblyClone.clone_none",
    "Compiler.Extraction.AssemblyClone.clone_some",
    "Compiler.Extraction.AssemblyClone.clone_safe",
    "Compiler.Extraction.AssemblyClone.clone_item",
    "Compiler.Extraction.AssemblyClone.clone_key",
    "Compiler.Extraction.AssemblyClone.clone_denotation",
    "Compiler.Extraction.AssemblyClone.deinit_invalidates",
    "Compiler.Extraction.AssemblyClone.deinit_none",
    "Compiler.Extraction.AssemblyClone.deinit_some",
    "Compiler.Extraction.AssemblyClone.clone_cleanup",
    "Compiler.Extraction.AssemblyClone.Fixtures.duplicate_safe",
    "Compiler.Extraction.AssemblyClone.Fixtures.duplicate_free",
    "Compiler.Extraction.AssemblyClone.Fixtures.preserved",
    "Compiler.Extraction.AssemblyClone.Fixtures.cleaned",
    "Compiler.Extraction.AssemblyClone.Fixtures.allocation_failure",
    "Compiler.Extraction.AssemblyClone.Fixtures.no_payload_no_allocation",
    "Compiler.Extraction.AssemblyClone.Fixtures.empty_no_allocation",
    "Compiler.Extraction.AssemblyClone.Fixtures.shallow_rejected",
    "Compiler.Extraction.AssemblyClone.Fixtures.empty_owned",
    "Compiler.Extraction.Interner.Extends.refl",
    "Compiler.Extraction.Interner.Extends.trans",
    "Compiler.Extraction.Interner.Frames.pure",
    "Compiler.Extraction.Interner.Frames.fail",
    "Compiler.Extraction.Interner.Frames.lift",
    "Compiler.Extraction.Interner.Frames.get",
    "Compiler.Extraction.Interner.Frames.ite",
    "Compiler.Extraction.Interner.Frames.option",
    "Compiler.Extraction.Interner.Frames.bind",
    "Compiler.Extraction.Interner.Frames.read",
    "Compiler.Extraction.Interner.Frames.arithmetic",
    "Compiler.Extraction.Interner.Frames.publish",
    "Compiler.Extraction.Interner.Frames.insert",
    "Compiler.Extraction.Interner.Extends.cell",
    "Compiler.Extraction.Interner.Extends.constant",
    "Compiler.Extraction.Interner.Extends.operation",
    "Compiler.Extraction.Dispatch.add_word_frames",
    "Compiler.Extraction.Dispatch.sub_word_frames",
    "Compiler.Extraction.Dispatch.or_next_frames",
    "Compiler.Extraction.Dispatch.apply_frames",
    "Compiler.Extraction.Dispatch.double_iszero_frames",
    "Compiler.Extraction.Dispatch.drop_repeated_frames",
    "Compiler.Extraction.Dispatch.reassociate_frames",
    "Compiler.Extraction.Dispatch.remove_shift_mask_frames",
    "Compiler.Extraction.Dispatch.shift_product_frames",
    "Compiler.Extraction.Dispatch.signextend_mask_frames",
    "Compiler.Extraction.Dispatch.net_shift_frames",
    "Compiler.Extraction.Dispatch.opposite_shifts_frames",
    "Compiler.Extraction.Dispatch.alternating_build_frames",
    "Compiler.Extraction.Dispatch.alternating_search_frames",
    "Compiler.Extraction.Dispatch.alternating_frames",
    "Compiler.Extraction.Dispatch.constant_stage_frames",
    "Compiler.Extraction.Dispatch.unary_stage_frames",
    "Compiler.Extraction.Dispatch.evm_stage_frames",
    "Compiler.Extraction.Dispatch.binary_stage_frames",
    "Compiler.Extraction.Dispatch.simplify_options_frames",
    "Compiler.Extraction.Dispatch.simplify_frames",
    "Compiler.Extraction.Recursive.constructors_frames",
    "Compiler.Extraction.Recursive.miss_frames",
    "Compiler.Extraction.Recursive.owned_frames",
    "Compiler.Extraction.Recursive.find_frames",
    "Compiler.Extraction.Recursive.simplifier_frames",
    "Compiler.Extraction.Recursive.step_frames",
    "Compiler.Extraction.Recursive.unfold_frames",
    "Compiler.Extraction.Recursive.executes_frames",
    "Compiler.Extraction.Recursive.FrameTests.primitive_frames",
    "Compiler.Extraction.Recursive.FrameTests.all_depths",
    "Compiler.Extraction.Recursive.FrameTests.success_retains",
    "Compiler.Extraction.Recursive.FrameTests.failure_retains",
    "Compiler.Extraction.Recursive.FrameTests.executed",
    "Compiler.Extraction.Recursive.FrameTests.old_operation_retained",
    "Compiler.Extraction.Recursive.FrameTests.old_constant_retained",
    "Compiler.Extraction.Recursive.FrameTests.changed_kind_rejected",
    "Compiler.Extraction.Recursive.FrameTests.detached_rejected",
    "Compiler.Extraction.Interner.Invariant.with_cursor",
    "Compiler.Extraction.Interner.Frames.local",
    "Compiler.Extraction.Interner.lift_local_from_except",
    "Compiler.Extraction.Interner.local_result",
    "Compiler.Extraction.Interner.local_cursor",
    "Compiler.Extraction.Interner.local_observations",
    "Compiler.Extraction.Interner.local_safe",
    "Compiler.Extraction.Interner.lift_local_bind",
    "Compiler.Extraction.Interner.local_sequential_failure",
    "Compiler.Extraction.Interner.observed_insert_cursor",
    "Compiler.Extraction.Interner.publish_cursor",
    "Compiler.Extraction.Interner.LocalTests.contracts",
    "Compiler.Extraction.Interner.LocalTests.all_depths",
    "Compiler.Extraction.Interner.LocalTests.first_preserved",
    "Compiler.Extraction.Interner.LocalTests.second_preserved",
    "Compiler.Extraction.Interner.LocalTests.transfer_success",
    "Compiler.Extraction.Interner.LocalTests.transfer_failure",
    "Compiler.Extraction.Interner.LocalTests.no_stateless_transfer",
    "Compiler.Extraction.Interner.LocalTests.represented_insert_safe",
    "Compiler.Extraction.Interner.LocalTests.force_preserved",
    "Compiler.Extraction.Storage.scope_retains_effects",
    "Compiler.Extraction.Storage.insert_effect_projection",
    "Compiler.Extraction.Storage.insert_effect_safe",
    "Compiler.Extraction.Storage.insert_effect_capacity",
    "Compiler.Extraction.Storage.EffectTests.safe",
    "Compiler.Extraction.Storage.EffectTests.complete_order",
    "Compiler.Extraction.Storage.EffectTests.nondeterministic_order",
    "Compiler.Extraction.Storage.EffectTests.repeated_failure",
    "Compiler.Extraction.Storage.EffectTests.publication_rollback",
    "Compiler.Extraction.Storage.EffectTests.variable_safe",
    "Compiler.Extraction.Interner.insert_effect_transaction_projection",
    "Compiler.Extraction.Interner.insert_effect_transaction_safe",
    "Compiler.Extraction.Interner.observed_insert_with_safe",
    "Compiler.Extraction.Interner.insert_effect_transaction_cells",
    "Compiler.Extraction.Interner.Frames.insertWith",
    "Compiler.Extraction.Interner.publish_with_safe",
    "Compiler.Extraction.Interner.Frames.publishWith",
    "Compiler.Extraction.Interner.InsertEffectTests.inserted_safe",
    "Compiler.Extraction.Interner.InsertEffectTests.repeated_safe",
    "Compiler.Extraction.Interner.InsertEffectTests.rollback_safe",
    "Compiler.Extraction.Interner.InsertEffectTests.each_failure_restores",
    "Compiler.Extraction.Interner.InsertEffectTests.publication_safe",
    "Compiler.Extraction.Interner.InsertEffectTests.primitive_frames",
    "Compiler.Extraction.Interner.InsertEffectTests.all_depths",
    "Compiler.Extraction.Interner.InsertEffectTests.recursive_retains",
    "Compiler.Extraction.Cache.NormalizationOwnership.init_with_ready",
    "Compiler.Extraction.Cache.NormalizationOwnership.take_with_success",
    "Compiler.Extraction.Cache.NormalizationOwnership.take_with_failure",
    "Compiler.Extraction.Cache.NormalizationOwnership.deinit_with_ready",
    "Compiler.Extraction.Cache.NormalizationOwnership.deinit_with_taken",
    "Compiler.Extraction.Cache.NormalizationOwnership.run_with_projection",
    "Compiler.Extraction.Cache.NormalizationOwnership.run_with_safe",
    "Compiler.Extraction.Cache.NormalizationOwnership.EffectTests.safe",
    "Compiler.Extraction.Cache.NormalizationOwnership.EffectTests.temporary_transfer",
    "Compiler.Extraction.Cache.NormalizationOwnership.EffectTests.repeated_failure",
    "Compiler.Extraction.Cache.NormalizationOwnership.EffectTests.lookup_cleanup",
    "Compiler.Extraction.Cache.NormalizationOwnership.EffectTests.caller_cleanup",
    "Compiler.Extraction.Cache.NormalizationOwnership.EffectTests.scratch_cleanup",
    "Compiler.Extraction.Cache.NormalizationOwnership.EffectTests.live_ready",
    "Compiler.Extraction.Cache.NormalizationOwnership.EffectTests.transferred_taken",
    "Compiler.Extraction.Cache.NormalizationOwnership.EffectTests.reuse_after_release",
    "Compiler.Extraction.OwnedKeys.view_store",
    "Compiler.Extraction.OwnedKeys.run_failure",
    "Compiler.Extraction.OwnedKeys.finish_eq",
    "Compiler.Extraction.OwnedKeys.run_success",
    "Compiler.Extraction.OwnedKeys.retire_frame",
    "Compiler.Extraction.OwnedKeys.retire_slice",
    "Compiler.Extraction.OwnedKeys.replaced_released",
    "Compiler.Extraction.OwnedKeys.after_live",
    "Compiler.Extraction.OwnedKeys.store_unique",
    "Compiler.Extraction.OwnedKeys.store_apart",
    "Compiler.Extraction.OwnedKeys.after_frame",
    "Compiler.Extraction.OwnedKeys.frame_resident",
    "Compiler.Extraction.OwnedKeys.after_semantics",
    "Compiler.Extraction.OwnedKeys.run_preserves",
    "Compiler.Extraction.OwnedKeys.run_semantics",
    "Compiler.Extraction.OwnedKeys.Tests.initial_live",
    "Compiler.Extraction.OwnedKeys.Tests.initial_unique",
    "Compiler.Extraction.OwnedKeys.Tests.incoming_fresh",
    "Compiler.Extraction.OwnedKeys.Tests.replacement",
    "Compiler.Extraction.OwnedKeys.Tests.other_key_preserved",
    "Compiler.Extraction.OwnedKeys.Tests.incoming_and_graph_live",
    "Compiler.Extraction.OwnedKeys.Tests.ownership_preserved",
    "Compiler.Extraction.OwnedKeys.Tests.repeated_failure",
    "Compiler.Extraction.OwnedKeys.Tests.release_effect_controls_later_attempt",
    "Compiler.Extraction.OwnedKeys.Tests.empty_sentinel",
    "Compiler.Extraction.OwnedKeys.Tests.new_key",
    "Compiler.Extraction.OwnedKeys.Tests.missing_free_leaks",
    "Compiler.Extraction.OwnedKeys.Tests.missing_store_dangles",
    "Compiler.Extraction.OwnedKeys.Tests.aliased_input_dangles",
    "Compiler.Extraction.OwnedKeys.Tests.wrong_allocator_fault",
    "Compiler.Extraction.Interner.control_miss_projection",
    "Compiler.Extraction.Interner.control_owned_projection",
    "Compiler.Extraction.Interner.control_find_projection",
    "Compiler.Extraction.Interner.control_force_projection",
    "Compiler.Extraction.Interner.Scoped.Checked.pure",
    "Compiler.Extraction.Interner.Scoped.Checked.bind",
    "Compiler.Extraction.Interner.Scoped.Checked.weaken",
    "Compiler.Extraction.Interner.Scoped.lift_graph_checked",
    "Compiler.Extraction.Interner.Scoped.commutative_projection",
    "Compiler.Extraction.Interner.Scoped.initialize_projection",
    "Compiler.Extraction.Interner.Scoped.initialize_checked",
    "Compiler.Extraction.Interner.Scoped.take_checked",
    "Compiler.Extraction.Interner.Scoped.handoff_checked",
    "Compiler.Extraction.Interner.Scoped.close_frame",
    "Compiler.Extraction.Interner.Scoped.close_closed",
    "Compiler.Extraction.Interner.Scoped.graph_preserves",
    "Compiler.Extraction.Interner.Scoped.failure_checked",
    "Compiler.Extraction.Interner.Scoped.handoff_insert_checked",
    "Compiler.Extraction.Interner.Scoped.miss_checked",
    "Compiler.Extraction.Interner.Scoped.owned_checked",
    "Compiler.Extraction.Interner.Scoped.find_checked",
    "Compiler.Extraction.Interner.Scoped.force_checked",
    "Compiler.Extraction.Interner.Scoped.finish_closed",
    "Compiler.Extraction.Interner.Scoped.find_closed",
    "Compiler.Extraction.Interner.Scoped.force_closed",
    "Compiler.Extraction.ScopedRecursive.detailed_projection",
    "Compiler.Extraction.ScopedRecursive.all_scopes_closed",
    "Compiler.Extraction.Interner.Scoped.Tests.all_depths",
    "Compiler.Extraction.Interner.Scoped.Tests.recursive_success",
    "Compiler.Extraction.Interner.Scoped.Tests.failed_parent_cleans",
    "Compiler.Extraction.Interner.Scoped.Tests.failed_parent_keeps_child",
    "Compiler.Extraction.Interner.Scoped.Tests.failed_child_cleans_parent",
    "Compiler.Extraction.Interner.Scoped.Tests.incomplete_unwinds",
    "Compiler.Extraction.Interner.Scoped.Tests.cleanup_affects_next_call",
    "Compiler.Extraction.Interner.Scoped.Tests.temporary_hit_frees",
    "Compiler.Extraction.Interner.Scoped.Tests.deterministic_error_frees",
    "Compiler.Extraction.Interner.Scoped.Tests.transferred_temporary_freed_once",
    "Compiler.Extraction.Interner.Scoped.Tests.no_handle_before_initialization",
    "Compiler.Extraction.Interner.Scoped.Tests.insertion_owns_failure",
    "Compiler.Extraction.Interner.Scoped.Tests.force_cleanup",
    "Compiler.Extraction.Interner.Scoped.Tests.force_closed_fixture",
    "Compiler.Extraction.Interner.Scoped.initialize_local",
    "Compiler.Extraction.Interner.Scoped.take_local",
    "Compiler.Extraction.Interner.Scoped.handoff_local",
    "Compiler.Extraction.Interner.Scoped.close_heap",
    "Compiler.Extraction.Interner.Scoped.Frames.pure",
    "Compiler.Extraction.Interner.Scoped.Frames.local",
    "Compiler.Extraction.Interner.Scoped.Frames.graph",
    "Compiler.Extraction.Interner.Scoped.Frames.bind",
    "Compiler.Extraction.Interner.Scoped.miss_frames",
    "Compiler.Extraction.Interner.Scoped.owned_frames",
    "Compiler.Extraction.Interner.Scoped.control_find_frames",
    "Compiler.Extraction.Interner.Scoped.control_force_frames",
    "Compiler.Extraction.Interner.Scoped.finish_frames",
    "Compiler.Extraction.Interner.Scoped.find_frames",
    "Compiler.Extraction.Interner.Scoped.force_frames",
    "Compiler.Extraction.ScopedRecursive.step_frames",
    "Compiler.Extraction.ScopedRecursive.unfold_frames",
    "Compiler.Extraction.ScopedRecursive.detailed_frames",
    "Compiler.Extraction.ScopedRecursive.detailed_preserves",
    "Compiler.Extraction.Interner.Scoped.FrameTests.all_depths",
    "Compiler.Extraction.Interner.Scoped.FrameTests.old_operation_retained",
    "Compiler.Extraction.Interner.Scoped.FrameTests.old_constant_retained",
    "Compiler.Extraction.Interner.Scoped.FrameTests.parent_failure_child_read",
    "Compiler.Extraction.Interner.Scoped.FrameTests.forced_failure_frames",
    "Compiler.Extraction.Interner.Scoped.FrameTests.dropped_scope_closed",
    "Compiler.Extraction.Interner.Scoped.FrameTests.dropped_reads_unchanged",
    "Compiler.Extraction.Interner.Scoped.FrameTests.missing_frame_rejected",
    "Compiler.Extraction.Interner.Scoped.FrameTests.dropping_primitive_rejected",
    "Compiler.Extraction.Interner.makeKey_sound",
    "Compiler.Extraction.Interner.Scoped.Safe.pure",
    "Compiler.Extraction.Interner.Scoped.Safe.graph",
    "Compiler.Extraction.Interner.Scoped.Safe.bind",
    "Compiler.Extraction.Interner.Scoped.Safe.local",
    "Compiler.Extraction.Interner.Scoped.local_bind_safe",
    "Compiler.Extraction.Interner.Scoped.lift_bind_safe",
    "Compiler.Extraction.Interner.Scoped.get_bind_safe",
    "Compiler.Extraction.Interner.Scoped.handoff_insert_safe",
    "Compiler.Extraction.Interner.Scoped.miss_safe",
    "Compiler.Extraction.Interner.Scoped.owned_safe",
    "Compiler.Extraction.Interner.Scoped.control_find_safe",
    "Compiler.Extraction.Interner.Scoped.control_force_safe",
    "Compiler.Extraction.Interner.Scoped.finish_safe",
    "Compiler.Extraction.Interner.Scoped.find_safe",
    "Compiler.Extraction.Interner.Scoped.force_safe",
    "Compiler.Extraction.ScopedRecursive.step_safe",
    "Compiler.Extraction.ScopedRecursive.unfold_safe",
    "Compiler.Extraction.ScopedRecursive.unfold_representatives_safe",
    "Compiler.Extraction.ScopedRecursive.detailed_safe",
    "Compiler.Extraction.ScopedRecursive.detailed_verified",
    "Compiler.Extraction.ScopedRecursive.executes_safe",
    "Compiler.Extraction.ScopedRecursive.unsupported_not_execution",
    "Compiler.Extraction.Interner.Scoped.SemanticTests.insert_safe",
    "Compiler.Extraction.Interner.Scoped.SemanticTests.insert_frames",
    "Compiler.Extraction.Interner.Scoped.SemanticTests.graph_contracts",
    "Compiler.Extraction.Interner.Scoped.SemanticTests.graph_frames",
    "Compiler.Extraction.Interner.Scoped.SemanticTests.sort_permutation",
    "Compiler.Extraction.Interner.Scoped.SemanticTests.initial_valid",
    "Compiler.Extraction.Interner.Scoped.SemanticTests.all_depths_verified",
    "Compiler.Extraction.Interner.Scoped.SemanticTests.success",
    "Compiler.Extraction.Interner.Scoped.SemanticTests.failed_parent_retains_semantics",
    "Compiler.Extraction.Interner.Scoped.SemanticTests.repeated_failure_preserves",
    "Compiler.Extraction.Interner.Scoped.SemanticTests.cutoff_preserves",
    "Compiler.Extraction.Interner.Scoped.SemanticTests.completed",
    "Compiler.Extraction.Interner.Scoped.SemanticTests.cutoff_not_completed",
    "Compiler.Extraction.Interner.Scoped.SemanticTests.force_equal_safe",
    "Compiler.Extraction.Interner.Scoped.SemanticTests.unbound_fixture_key_rejected",
    "Compiler.Extraction.Interner.Scoped.SemanticTests.bad_sort_changes_value",
    "Compiler.Extraction.Interner.Scoped.SemanticTests.bad_sort_not_permutation",
    "Compiler.Extraction.Interner.Scoped.SemanticTests.wrong_force_closed",
    "Compiler.Extraction.Interner.Scoped.SemanticTests.wrong_force_invalid"]
RULES = ROOT / "lean/Compiler/Algebraic/Rules.lean"
PRELUDE = "import Compiler.Algebraic.Proofs\nopen Compiler.Algebraic Contract.Yul\n"
NESTED_PRELUDE = ("import Compiler.Extraction.StorageOperationTests\n"
                  "open Compiler.Extraction.Storage Compiler.Extraction.Storage.OperationTests\n")
MEMORY_PRELUDE = ("import Compiler.Extraction.MemoryTests\n"
                  "open Compiler.Extraction.Memory Compiler.Extraction.Memory.Tests\n"
                  "open Compiler.Extraction.Storage Compiler.Extraction.Storage.OperationTests\n")
HELPER_PRELUDE = ("import Compiler.Extraction.NestedTests\n"
                  "open Compiler.Extraction.Nested Compiler.Extraction.Nested.Tests\n"
                  "open Compiler.Extraction.Storage Contract.Yul\n")
NESTED_BUILD_PRELUDE = ("import Compiler.Extraction.NestedConstructionTests\n"
    "open Compiler.Extraction.Nested Compiler.Extraction.Nested.Tests\n"
    "open Compiler.Extraction.Nested.ConstructionTests Compiler.Extraction.Interner\n")
ASSOCIATIVE_PRELUDE = ("import Compiler.Extraction.AssociativeTests\n"
    "open Compiler.Extraction.Associative Compiler.Extraction.Associative.Tests\n"
    "open Compiler.Extraction.Nested.ConstructionTests (callKey failing)\n")
SHIFT_MASKS_PRELUDE = ("import Compiler.Extraction.ShiftMasksTests\n"
    "open Compiler.Extraction.ShiftMasks Compiler.Extraction.ShiftMasks.Tests\n"
    "open Compiler.Extraction.Nested.ConstructionTests (callKey recording failing)\n")
OPPOSITE_SHIFTS_PRELUDE = ("import Compiler.Extraction.OppositeShiftsTests\n"
    "open Compiler.Extraction.OppositeShifts\n"
    "open Compiler.Extraction.Associative.Tests (constructors)\n"
    "open Compiler.Extraction.Nested.ConstructionTests (callKey initial failing)\n")
SIGNEXTEND_MASK_PRELUDE = ("import Compiler.Extraction.SignExtendMaskTests\n"
    "open Compiler.Extraction.SignExtendMask Compiler.Extraction.SignExtendMask.Tests\n"
    "open Compiler.Extraction.Associative.Tests (constructors)\n"
    "open Compiler.Extraction.Nested.ConstructionTests (callKey failing)\n")
BINARY_LOGARITHM_PRELUDE = ("import Compiler.Extraction.BinaryLogarithmTests\n"
    "open Compiler.Extraction.BinaryLogarithm\nset_option maxRecDepth 4096\n")
ADDRESS_MASK_PRELUDE = ("import Compiler.Extraction.AddressMaskTests\n"
    "open Compiler.Extraction.AddressMask Compiler.Extraction.AddressMask.Tests\n")
ALTERNATING_MASK_PRELUDE = ("import Compiler.Extraction.AlternatingMaskTests\n"
    "open Compiler.Extraction.AlternatingMask Compiler.Extraction.AlternatingMask.Tests\n"
    "open Compiler.Extraction.Nested.ConstructionTests (callKey)\n")
DISPATCH_PRELUDE = ("import Compiler.Extraction.DispatchTests\n"
    "open Compiler.Extraction.Dispatch Compiler.Extraction.Dispatch.Tests\n")
UNARY_PRELUDE = ("import Compiler.Extraction.DispatchUnaryTests\n"
    "open Compiler.Extraction.Dispatch Compiler.Extraction.Dispatch.Tests Compiler.Extraction.Dispatch.UnaryTests\n"
    "open Compiler.Extraction.Nested Contract.Yul\n")
COMPARISON_PRELUDE = ("import Compiler.Extraction.DispatchComparisonTests\n"
    "open Compiler.Extraction.Dispatch Compiler.Extraction.Dispatch.Tests Compiler.Extraction.Dispatch.ComparisonTests\n"
    "open Compiler.Algebraic Compiler.Extraction Contract.Yul\n")
ASSOCIATIVE_DISPATCH_PRELUDE = ("import Compiler.Extraction.DispatchAssociativeTests\n"
    "open Compiler.Extraction.Dispatch Compiler.Extraction.Dispatch.Tests\n"
    "open Compiler.Extraction.Dispatch.AssociativeTests\n")
SIGNED_DISPATCH_PRELUDE = ("import Compiler.Extraction.DispatchSignedTests\n"
    "open Compiler.Extraction.Dispatch Compiler.Extraction.Dispatch.Tests\n"
    "open Compiler.Extraction.Dispatch.SignedTests\n")
MUL_DISPATCH_PRELUDE = ("import Compiler.Extraction.DispatchMultiplicationTests\n"
    "open Compiler.Extraction.Dispatch Compiler.Extraction.Dispatch.Tests\n"
    "open Compiler.Extraction.Dispatch.MultiplicationTests\n"
    "set_option maxRecDepth 4096\n")
DIV_DISPATCH_PRELUDE = ("import Compiler.Extraction.DispatchDivisionTests\n"
    "open Compiler.Extraction.Dispatch Compiler.Extraction.Dispatch.Tests\n"
    "open Compiler.Extraction.Dispatch.DivisionTests\n"
    "set_option maxRecDepth 4096\n")
ARITY_DISPATCH_PRELUDE = ("import Compiler.Extraction.DispatchArityTests\n"
    "open Compiler.Extraction.Dispatch Compiler.Extraction.Dispatch.Tests\n"
    "open Compiler.Extraction.Dispatch.ArityTests\n"
    "set_option exponentiation.threshold 512\n")
MOD_DISPATCH_PRELUDE = ("import Compiler.Extraction.DispatchModuloTests\n"
    "open Compiler.Extraction.Dispatch Compiler.Extraction.Dispatch.Tests\n"
    "open Compiler.Extraction.Dispatch.ModuloTests Compiler.Extraction Contract.Yul\n"
    "set_option maxRecDepth 4096\nset_option exponentiation.threshold 512\n")
EXP_DISPATCH_PRELUDE = ("import Compiler.Extraction.DispatchExponentTests\n"
    "open Compiler.Extraction.Dispatch Compiler.Extraction.Dispatch.Tests\n"
    "open Compiler.Extraction.Dispatch.ExponentTests Compiler.Extraction Contract.Yul\n"
    "set_option maxRecDepth 8192\nset_option maxHeartbeats 1000000\n")
SUB_DISPATCH_PRELUDE = ("import Compiler.Extraction.DispatchSubtractionTests\n"
    "open Compiler.Extraction.Dispatch Compiler.Extraction.Dispatch.Tests\n"
    "open Compiler.Extraction.Dispatch.SubtractionTests Contract.Yul\n"
    "set_option maxRecDepth 8192\nset_option maxHeartbeats 1000000\n")
BYTE_DISPATCH_PRELUDE = ("import Compiler.Extraction.DispatchByteTests\n"
    "open Compiler.Extraction.Dispatch Compiler.Extraction.Dispatch.Tests\n"
    "open Compiler.Extraction.Dispatch.ByteTests Compiler.Extraction Contract.Yul\n"
    "set_option maxRecDepth 8192\nset_option maxHeartbeats 1000000\n")
SHR_DISPATCH_PRELUDE = ("import Compiler.Extraction.DispatchShiftRightTests\n"
    "open Compiler.Extraction.Dispatch Compiler.Extraction.Dispatch.Tests\n"
    "open Compiler.Extraction.Dispatch.ShiftRightTests Compiler.Extraction Contract.Yul\n"
    "set_option maxRecDepth 8192\nset_option maxHeartbeats 1000000\n")
SHL_DISPATCH_PRELUDE = ("import Compiler.Extraction.DispatchShiftLeftTests\n"
    "open Compiler.Extraction.Dispatch Compiler.Extraction.Dispatch.Tests\n"
    "open Compiler.Extraction.Dispatch.ShiftLeftTests Compiler.Extraction Contract.Yul\n"
    "set_option maxRecDepth 8192\nset_option maxHeartbeats 1000000\n")
SIGNEXTEND_DISPATCH_PRELUDE = ("import Compiler.Extraction.DispatchSignExtendTests\n"
    "open Compiler.Extraction.Dispatch Compiler.Extraction.Dispatch.Tests\n"
    "open Compiler.Extraction.Dispatch.SignExtendTests Compiler.Extraction Contract.Yul\n"
    "set_option maxRecDepth 8192\nset_option maxHeartbeats 1000000\n")
AND_DISPATCH_PRELUDE = ("import Compiler.Extraction.DispatchAndTests\n"
    "open Compiler.Extraction.Dispatch Compiler.Extraction.Dispatch.Tests\n"
    "open Compiler.Extraction.Dispatch.AndTests Compiler.Extraction Contract.Yul\n"
    "set_option maxRecDepth 8192\nset_option maxHeartbeats 1000000\n")
WORD_DISPATCH_PRELUDE = ("import Compiler.Extraction.DispatchWordTests\n"
    "open Compiler.Extraction.Dispatch Compiler.Extraction.Dispatch.Tests\n"
    "open Compiler.Extraction.Dispatch.WordTests Compiler.Extraction Contract.Yul\n"
    "set_option maxRecDepth 8192\nset_option maxHeartbeats 1000000\n"
    "set_option exponentiation.threshold 1024\n")
DEFAULT_DISPATCH_PRELUDE = ("import Compiler.Extraction.DispatchDefaultTests\n"
    "open Compiler.Extraction.Dispatch Compiler.Extraction.Dispatch.Tests\n"
    "open Compiler.Extraction.Dispatch.DefaultTests Compiler.Extraction Contract.Yul\n"
    "set_option maxRecDepth 8192\nset_option maxHeartbeats 1000000\n")
RECURSIVE_PRELUDE = ("import Compiler.Extraction.RecursiveTests\n"
    "open Compiler.Extraction.Recursive Compiler.Extraction.Recursive.Tests\n"
    "set_option maxRecDepth 8192\nset_option maxHeartbeats 1000000\n")
NORMALIZATION_PRELUDE = ("import Compiler.Extraction.NormalizationTests\n"
    "open Compiler.Extraction.Cache Compiler.Extraction.Cache.NormalizationTests Compiler.Algebraic\n"
    "set_option maxRecDepth 8192\nset_option maxHeartbeats 1000000\n")
NORMALIZATION_OWNERSHIP_PRELUDE = ("import Compiler.Extraction.NormalizationOwnershipTests\n"
    "open Compiler.Extraction.Cache.NormalizationOwnership Compiler.Extraction.Cache.NormalizationOwnership.Tests\n")
OBSERVED_HEAP_PRELUDE = ("import Compiler.Extraction.ObservedHeapTests\n"
    "open Compiler.Extraction.Interner Compiler.Extraction.Interner.ObservedTests\n")
OBSERVED_STORAGE_PRELUDE = ("import Compiler.Extraction.ObservedStorageTests\n"
    "open Compiler.Extraction.Interner Compiler.Extraction.Interner.ObservedStorageTests Compiler.Extraction.Cache\n")
ASSEMBLY_CLONE_PRELUDE = ("import Compiler.Extraction.AssemblyCloneTests\n"
    "open Compiler.Extraction.AssemblyClone Compiler.Extraction.AssemblyClone.Fixtures Compiler.Extraction.Cache\n")
RECURSIVE_FRAME_PRELUDE = ("import Compiler.Extraction.RecursiveFrameTests\n"
    "open Compiler.Extraction.Interner Compiler.Extraction.Recursive.FrameTests\n")
LOCAL_STATE_PRELUDE = ("import Compiler.Extraction.LocalStateTests\n"
    "open Compiler.Extraction.Interner Compiler.Extraction.Interner.LocalTests\n")
STORAGE_EFFECT_PRELUDE = ("import Compiler.Extraction.StorageEffectTests\n"
    "open Compiler.Extraction.Storage Compiler.Extraction.Storage.EffectTests\n")
INSERTION_EFFECT_PRELUDE = ("import Compiler.Extraction.InsertionEffectTests\n"
    "open Compiler.Extraction.Interner Compiler.Extraction.Interner.InsertEffectTests\n"
    "open Compiler.Extraction.Interner.ObservedStorageTests (cell key)\n")
NORMALIZATION_EFFECT_PRELUDE = ("import Compiler.Extraction.NormalizationEffectTests\n"
    "open Compiler.Extraction.Cache.NormalizationOwnership Compiler.Extraction.Cache.NormalizationOwnership.EffectTests\n")
OWNED_KEY_PRELUDE = ("import Compiler.Extraction.OwnedKeysTests\n"
    "open Compiler.Extraction.OwnedKeys Compiler.Extraction.OwnedKeys.Tests\n")
SCOPED_INTERNER_PRELUDE = ("import Compiler.Extraction.InternerScopeTests\n"
    "open Compiler.Extraction.Interner.Scoped Compiler.Extraction.Interner.Scoped.Tests\n"
    "open Compiler.Extraction.Recursive\n")
SCOPED_SEMANTIC_PRELUDE = ("import Compiler.Extraction.ScopedSemanticTests\n"
    "open Compiler.Extraction.Interner.Scoped.SemanticTests\n")
NEGATIVES = {
    "scoped_semantic_wrong_id": (SCOPED_SEMANTIC_PRELUDE +
        "example : (result 99 2).1 = .ok 1 := by rfl\n", "Tactic `rfl` failed"),
    "scoped_semantic_wrong_word": (SCOPED_SEMANTIC_PRELUDE +
        "example : (result 99 2).2.heap.read 3 = some 10 := by rfl\n", "Tactic `rfl` failed"),
    "scoped_semantic_failed_parent_loses_word": (SCOPED_SEMANTIC_PRELUDE +
        "example : (result 6 2).2.heap.read 3 = none := by rfl\n", "Tactic `rfl` failed"),
    "scoped_semantic_repeated_failure_loses_word": (SCOPED_SEMANTIC_PRELUDE +
        "example : next.2.heap.read 3 = none := by rfl\n", "Tactic `rfl` failed"),
    "scoped_semantic_cleanup_effect_ignored": (SCOPED_SEMANTIC_PRELUDE +
        "example : next.1 = .ok 3 := by rfl\n", "Tactic `rfl` failed"),
    "scoped_semantic_cutoff_completed": (SCOPED_SEMANTIC_PRELUDE +
        "example : (result 99 1).1 = .ok 3 := by rfl\n", "Tactic `rfl` failed"),
    "scoped_semantic_bad_sort_preserves_word": (SCOPED_SEMANTIC_PRELUDE +
        "example : changed.2.heap.read 3 = some 42 := by rfl\n", "Tactic `rfl` failed"),
    "scoped_semantic_wrong_force_has_equal_word": (SCOPED_SEMANTIC_PRELUDE +
        "example : wrongForce.2.heap.read 1 = some 42 := by rfl\n", "Tactic `rfl` failed"),
    "scoped_semantic_wrong_force_did_not_publish": (SCOPED_SEMANTIC_PRELUDE +
        "example : wrongForce.2.heap.table ⟨1, 1, 0, [1, 2], 0⟩ = none := by rfl\n", "Tactic `rfl` failed"),
    "scoped_semantic_unbound_fixture_accepted": (SCOPED_SEMANTIC_PRELUDE +
        "example : (insert 99 rejectedKey true Compiler.Extraction.Recursive.FrameTests.initial).1 = .ok 3 := by rfl\n", "Tactic `rfl` failed"),
    "scoped_frame_old_operation_lost": (SCOPED_INTERNER_PRELUDE +
        "example : (Compiler.Extraction.Interner.representativeReads parentFailure.2.heap).operation 0 0x33 = .ok none := by rfl\n", "Tactic `rfl` failed"),
    "scoped_frame_old_constant_lost": (SCOPED_INTERNER_PRELUDE +
        "example : (Compiler.Extraction.Interner.representativeReads cutoff.2.heap).constant 1 = .ok none := by rfl\n", "Tactic `rfl` failed"),
    "scoped_frame_child_descriptor_lost": (SCOPED_INTERNER_PRELUDE +
        "example : (Compiler.Extraction.Interner.representativeReads parentFailure.2.heap).constant 3 = .ok none := by rfl\n", "Tactic `rfl` failed"),
    "scoped_frame_force_changes_graph": (SCOPED_INTERNER_PRELUDE +
        "example : forceFailure.2.heap.representatives = none := by rfl\n", "Tactic `rfl` failed"),
    "scoped_frame_missing_primitive_hidden": ("import Compiler.Extraction.ScopedFrameTests\n" +
        "example : Compiler.Extraction.Interner.Scoped.FrameTests.dropped.2.heap.representatives.isSome = true := by rfl\n", "Tactic `rfl` failed"),
    "scoped_frame_value_observation_confused": ("import Compiler.Extraction.ScopedFrameTests\n" +
        "example : Compiler.Extraction.Interner.Scoped.FrameTests.dropped.2.heap.read 1 = none := by rfl\n", "Tactic `rfl` failed"),
    "scoped_parent_omits_cleanup": (SCOPED_INTERNER_PRELUDE +
        "example : parentFailure.2.heap.allocationCursor = 7 := by rfl\n", "Tactic `rfl` failed"),
    "scoped_parent_rolls_back_child": (SCOPED_INTERNER_PRELUDE +
        "example : parentFailure.2.heap.representatives = some FrameTests.cells := by rfl\n", "Tactic `rfl` failed"),
    "scoped_parent_false_publication": (SCOPED_INTERNER_PRELUDE +
        "example : parentFailure.2.heap.table ⟨1, 1, 0, [1, 2], 77⟩ = some 3 := by rfl\n", "Tactic `rfl` failed"),
    "scoped_parent_loses_child_cache": (SCOPED_INTERNER_PRELUDE +
        "example : parentFailure.2.heap.table ⟨2, 0, 42, [], 0⟩ = none := by rfl\n", "Tactic `rfl` failed"),
    "scoped_child_omits_parent_cleanup": (SCOPED_INTERNER_PRELUDE +
        "example : childFailure.2.heap.allocationCursor = 6 := by rfl\n", "Tactic `rfl` failed"),
    "scoped_cutoff_omits_cleanup": (SCOPED_INTERNER_PRELUDE +
        "example : cutoff.2.heap.allocationCursor = 1 := by rfl\n", "Tactic `rfl` failed"),
    "scoped_cutoff_succeeds": (SCOPED_INTERNER_PRELUDE +
        "example : cutoff.1 = .ok 3 := by rfl\n", "Tactic `rfl` failed"),
    "scoped_release_effect_ignored": (SCOPED_INTERNER_PRELUDE +
        "example : afterFailure.1 = .ok 3 := by rfl\n", "Tactic `rfl` failed"),
    "scoped_hit_duplicates": (SCOPED_INTERNER_PRELUDE +
        "example : hit.2.heap.allocationCursor = 3 := by rfl\n", "Tactic `rfl` failed"),
    "scoped_hit_hands_off": (SCOPED_INTERNER_PRELUDE +
        "example : hit.2.scope.phase = .transfer := by rfl\n", "Tactic `rfl` failed"),
    "scoped_determinism_error_leaks": (SCOPED_INTERNER_PRELUDE +
        "example : deterministicError.2.scope.lookup.map (·.owner) = some .lookup := by rfl\n", "Tactic `rfl` failed"),
    "scoped_temporary_double_free": (SCOPED_INTERNER_PRELUDE +
        "example : simplifyError.2.heap.allocationCursor = 3 := by rfl\n", "Tactic `rfl` failed"),
    "scoped_temporary_invalid": (SCOPED_INTERNER_PRELUDE +
        "example : simplifyError.2.scope.lookup.map (·.invalid) = some true := by rfl\n", "Tactic `rfl` failed"),
    "scoped_failed_initializer_freed": (SCOPED_INTERNER_PRELUDE +
        "example : initFailure.2.heap.allocationCursor = 2 := by rfl\n", "Tactic `rfl` failed"),
    "scoped_capacity_allocates": (SCOPED_INTERNER_PRELUDE +
        "example : capacity.2.heap.allocationCursor = 1 := by rfl\n", "Tactic `rfl` failed"),
    "scoped_insertion_double_free": (SCOPED_INTERNER_PRELUDE +
        "example : insertionFailure.2.heap.allocationCursor = 3 := by rfl\n", "Tactic `rfl` failed"),
    "scoped_insertion_caller_frees": (SCOPED_INTERNER_PRELUDE +
        "example : insertionFailure.2.scope.lookup.map (·.owner) = some .released := by rfl\n", "Tactic `rfl` failed"),
    "scoped_force_early_handoff": (SCOPED_INTERNER_PRELUDE +
        "example : forceFailure.2.heap.allocationCursor = 2 := by rfl\n", "Tactic `rfl` failed"),
    "scoped_force_published_failure": (SCOPED_INTERNER_PRELUDE +
        "example : forceFailure.2.scope.phase = .transfer := by rfl\n", "Tactic `rfl` failed"),
    "scoped_invalid_force_allocates": (SCOPED_INTERNER_PRELUDE +
        "example : invalidForce.2.heap.allocationCursor = 1 := by rfl\n", "Tactic `rfl` failed"),
    "owned_key_retains_old_buffer": (OWNED_KEY_PRELUDE +
        "example : nominal.1.2.memory 10 = before.memory 10 := by rfl\n", "Tactic `rfl` failed"),
    "owned_key_retains_old_id": (OWNED_KEY_PRELUDE +
        "example : nominal.1.2.table key = some ⟨30, 2⟩ := by rfl\n", "Tactic `rfl` failed"),
    "owned_key_retains_old_address": (OWNED_KEY_PRELUDE +
        "example : nominal.1.2.table key = some ⟨10, 5⟩ := by rfl\n", "Tactic `rfl` failed"),
    "owned_key_frees_incoming": (OWNED_KEY_PRELUDE +
        "example : nominal.1.2.memory 30 = none := by rfl\n", "Tactic `rfl` failed"),
    "owned_key_frees_other_key": (OWNED_KEY_PRELUDE +
        "example : nominal.1.2.memory 40 = none := by rfl\n", "Tactic `rfl` failed"),
    "owned_key_changes_other_value": (OWNED_KEY_PRELUDE +
        "example : nominal.1.2.table other = some incoming := by rfl\n", "Tactic `rfl` failed"),
    "owned_key_frees_representative": (OWNED_KEY_PRELUDE +
        "example : nominal.1.2.memory 20 = none := by rfl\n", "Tactic `rfl` failed"),
    "owned_key_frees_borrowed_arguments": (OWNED_KEY_PRELUDE +
        "example : nominal.1.2.memory 21 = none := by rfl\n", "Tactic `rfl` failed"),
    "owned_key_repeated_success": (OWNED_KEY_PRELUDE +
        "example : (run (state := nominal.1.2) (trace := nominal.2)).1.1 = .ok () := by rfl\n", "Tactic `rfl` failed"),
    "owned_key_oom_rewinds": (OWNED_KEY_PRELUDE +
        "example : (run (state := nominal.1.2) (trace := nominal.2)).2.attempts = 1 := by rfl\n", "Tactic `rfl` failed"),
    "owned_key_oom_frees_caller": (OWNED_KEY_PRELUDE +
        "example : (run (state := nominal.1.2) (trace := nominal.2)).2.frees = [10, 30] := by rfl\n", "Tactic `rfl` failed"),
    "owned_key_empty_frees_sentinel": (OWNED_KEY_PRELUDE +
        "example : emptyRun.1.2.memory 20 = none := by rfl\n", "Tactic `rfl` failed"),
    "owned_key_empty_free_event": (OWNED_KEY_PRELUDE +
        "example : emptyRun.2.frees = [20] := by rfl\n", "Tactic `rfl` failed"),
    "owned_key_new_entry_frees": (OWNED_KEY_PRELUDE +
        "example : (run (state := absentState)).2.frees = [30] := by rfl\n", "Tactic `rfl` failed"),
    "owned_key_missing_free_safe": (OWNED_KEY_PRELUDE +
        "example : (run (code := missingFree)).1.2.memory 10 = none := by rfl\n", "Tactic `rfl` failed"),
    "owned_key_missing_store_safe": (OWNED_KEY_PRELUDE +
        "example : (run (code := missingStore)).1.2.table key = some incoming := by rfl\n", "Tactic `rfl` failed"),
    "owned_key_alias_live": (OWNED_KEY_PRELUDE +
        "example : (run (entry := ⟨10, 5⟩)).1.2.memory 10 = before.memory 10 := by rfl\n", "Tactic `rfl` failed"),
    "owned_key_wrong_allocator_succeeds": (OWNED_KEY_PRELUDE +
        "example : (publicationCode.run getOrPut onFree 2 key incoming before ({} : Trace)).1.1 = .ok () := by rfl\n", "Tactic `rfl` failed"),
    "owned_key_release_effect_lost": (OWNED_KEY_PRELUDE +
        "example : reused.1.1 = .error .outOfMemory := by rfl\n", "Tactic `rfl` failed"),
    "owned_key_reused_free_lost": (OWNED_KEY_PRELUDE +
        "example : reused.2.frees = [30] := by rfl\n", "Tactic `rfl` failed"),
    "normalization_effect_temporary_duplicates": (NORMALIZATION_EFFECT_PRELUDE +
        "example : allocated.2.events = [.allocate .temporary, .allocate .duplicate] := by rfl\n", "Tactic `rfl` failed"),
    "normalization_effect_transfer_frees": (NORMALIZATION_EFFECT_PRELUDE +
        "example : allocated.2.frees = 1 := by rfl\n", "Tactic `rfl` failed"),
    "normalization_effect_repeat_succeeds": (NORMALIZATION_EFFECT_PRELUDE +
        "example : repeated.1.1 = .transferred := by rfl\n", "Tactic `rfl` failed"),
    "normalization_effect_repeat_rewinds": (NORMALIZATION_EFFECT_PRELUDE +
        "example : repeated.2.attempts = 1 := by rfl\n", "Tactic `rfl` failed"),
    "normalization_effect_hit_leaks": (NORMALIZATION_EFFECT_PRELUDE +
        "example : hit.2.frees = 0 := by rfl\n", "Tactic `rfl` failed"),
    "normalization_effect_hit_releases_caller": (NORMALIZATION_EFFECT_PRELUDE +
        "example : hit.2.events = [.allocate .temporary, .release .allocation .caller true false] := by rfl\n", "Tactic `rfl` failed"),
    "normalization_effect_cleanup_double_free": (NORMALIZATION_EFFECT_PRELUDE +
        "example : cleaned.2.frees = 2 := by rfl\n", "Tactic `rfl` failed"),
    "normalization_effect_scratch_releases_lookup": (NORMALIZATION_EFFECT_PRELUDE +
        "example : scratch.2.events = [.allocate .duplicate, .release .scratch .lookup false false] := by rfl\n", "Tactic `rfl` failed"),
    "normalization_effect_borrowed_temporary": (NORMALIZATION_EFFECT_PRELUDE +
        "example : borrowed.2.events = [.allocate .temporary] := by rfl\n", "Tactic `rfl` failed"),
    "normalization_effect_failed_duplicate_free": (NORMALIZATION_EFFECT_PRELUDE +
        "example : duplicateFailure.2.frees = 1 := by rfl\n", "Tactic `rfl` failed"),
    "normalization_effect_failed_initializer_free": (NORMALIZATION_EFFECT_PRELUDE +
        "example : allocationFailure.2.frees = 1 := by rfl\n", "Tactic `rfl` failed"),
    "normalization_effect_early_lookup_allocates": (NORMALIZATION_EFFECT_PRELUDE +
        "example : (run false 9 2 0 .lookup).2.attempts = 1 := by rfl\n", "Tactic `rfl` failed"),
    "normalization_effect_empty_allocates": (NORMALIZATION_EFFECT_PRELUDE +
        "example : empty.2.attempts = 1 := by rfl\n", "Tactic `rfl` failed"),
    "normalization_effect_empty_frees": (NORMALIZATION_EFFECT_PRELUDE +
        "example : empty.2.frees = 1 := by rfl\n", "Tactic `rfl` failed"),
    "normalization_effect_transfer_retains_owned": (NORMALIZATION_EFFECT_PRELUDE +
        "example : transferred.1.2.owned = true := by rfl\n", "Tactic `rfl` failed"),
    "normalization_effect_initializer_invalid": (NORMALIZATION_EFFECT_PRELUDE +
        "example : live.invalid = true := by rfl\n", "Tactic `rfl` failed"),
    "normalization_effect_release_effect_lost": (NORMALIZATION_EFFECT_PRELUDE +
        "example : reused.2.frees = 0 := by rfl\n", "Tactic `rfl` failed"),
    "normalization_effect_reuse_fails": (NORMALIZATION_EFFECT_PRELUDE +
        "example : reused.1.1 = .allocationFailure := by rfl\n", "Tactic `rfl` failed"),
    "normalization_effect_double_free_valid": (NORMALIZATION_EFFECT_PRELUDE +
        "example : doubleFree.1.2.invalid = false := by rfl\n", "Tactic `rfl` failed"),
    "normalization_effect_leak_released": (NORMALIZATION_EFFECT_PRELUDE +
        "example : leaked.1.2.owner = .released := by rfl\n", "Tactic `rfl` failed"),
    "normalization_effect_owns_scratch": (NORMALIZATION_EFFECT_PRELUDE +
        "example : Ready { origin := .scratch, owner := .lookup, owned := true } := by unfold Ready; decide\n", "is false"),
    "normalization_effect_taken_still_owned": (NORMALIZATION_EFFECT_PRELUDE +
        "example : Taken { origin := .allocation, owner := .caller, owned := true } := by unfold Taken; decide\n", "is false"),

    "insertion_effect_insertion_cursor": (INSERTION_EFFECT_PRELUDE +
        "example : inserted.2.allocationCursor = 0 := by rfl\n", "Tactic `rfl` failed"),
    "insertion_effect_repeated_succeeds": (INSERTION_EFFECT_PRELUDE +
        "example : repeated.1 = .ok 2 := by rfl\n", "Tactic `rfl` failed"),
    "insertion_effect_repeated_loses_node": (INSERTION_EFFECT_PRELUDE +
        "example : repeated.2.read 1 = none := by rfl\n", "Tactic `rfl` failed"),
    "insertion_effect_rollback_rewinds": (INSERTION_EFFECT_PRELUDE +
        "example : rollback.2.allocationCursor = 2 := by rfl\n", "Tactic `rfl` failed"),
    "insertion_effect_rollback_keeps_node": (INSERTION_EFFECT_PRELUDE +
        "example : rollback.2.read 1 = some cell.value := by rfl\n", "Tactic `rfl` failed"),
    "insertion_effect_rollback_publishes": (INSERTION_EFFECT_PRELUDE +
        "example : rollback.2.table key = some 1 := by rfl\n", "Tactic `rfl` failed"),
    "insertion_effect_publication_rewinds": (INSERTION_EFFECT_PRELUDE +
        "example : publicationFailure.2.allocationCursor = 7 := by rfl\n", "Tactic `rfl` failed"),
    "insertion_effect_publication_publishes": (INSERTION_EFFECT_PRELUDE +
        "example : publicationFailure.2.table publicationKey = some 1 := by rfl\n", "Tactic `rfl` failed"),
    "insertion_effect_publication_loses_cache": (INSERTION_EFFECT_PRELUDE +
        "example : publicationFailure.2.table key = none := by rfl\n", "Tactic `rfl` failed"),
    "insertion_effect_missing_view_proceeds": (INSERTION_EFFECT_PRELUDE +
        "example : (observedInsertWith cell key true (allocation 0) ObservedTests.unrepresented).1 = .error .outOfMemory := by rfl\n", "Tactic `rfl` failed"),
    "insertion_effect_recursive_cursor": (INSERTION_EFFECT_PRELUDE +
        "example : success.2.allocationCursor = 6 := by rfl\n", "Tactic `rfl` failed"),
    "insertion_effect_cache_advances": (INSERTION_EFFECT_PRELUDE +
        "example : cached.2.allocationCursor = 8 := by rfl\n", "Tactic `rfl` failed"),
    "insertion_effect_parent_drops_child": (INSERTION_EFFECT_PRELUDE +
        "example : parentFailure.2.read 3 = none := by rfl\n", "Tactic `rfl` failed"),
    "insertion_effect_parent_publishes": (INSERTION_EFFECT_PRELUDE +
        "example : parentFailure.2.table ⟨1, 1, 0, [1, 2], 77⟩ = some 3 := by rfl\n", "Tactic `rfl` failed"),
    "insertion_effect_child_keeps_node": (INSERTION_EFFECT_PRELUDE +
        "example : childFailure.2.read 3 = some 42 := by rfl\n", "Tactic `rfl` failed"),
    "insertion_effect_child_rewinds": (INSERTION_EFFECT_PRELUDE +
        "example : childFailure.2.allocationCursor = 1 := by rfl\n", "Tactic `rfl` failed"),
    "insertion_effect_cutoff_rewinds": (INSERTION_EFFECT_PRELUDE +
        "example : (recursive 99 1).2.allocationCursor = 0 := by rfl\n", "Tactic `rfl` failed"),
    "insertion_effect_transfer_continues": (INSERTION_EFFECT_PRELUDE +
        "example : (recursive 0 2).2.allocationCursor = 2 := by rfl\n", "Tactic `rfl` failed"),

    "storage_effect_deterministic_order": (STORAGE_EFFECT_PRELUDE +
        "example : successful.2.calls = [.item, .arguments, .clone, .append, .publish] := by rfl\n", "Tactic `rfl` failed"),
    "storage_effect_nondeterministic_duplicates": (STORAGE_EFFECT_PRELUDE +
        "example : (run 9 false true).2.calls = [.arguments, .item, .clone, .append] := by rfl\n", "Tactic `rfl` failed"),
    "storage_effect_nondeterministic_publishes": (STORAGE_EFFECT_PRELUDE +
        "example : (run 9 false true).1.2.published = true := by rfl\n", "Tactic `rfl` failed"),
    "storage_effect_capacity_attempts": (STORAGE_EFFECT_PRELUDE +
        "example : (run 0 true false).2.cursor = 1 := by rfl\n", "Tactic `rfl` failed"),
    "storage_effect_arguments_continues": (STORAGE_EFFECT_PRELUDE +
        "example : (run 0 true true).2.calls = [.arguments, .item] := by rfl\n", "Tactic `rfl` failed"),
    "storage_effect_clone_continues": (STORAGE_EFFECT_PRELUDE +
        "example : (run 2 true true).2.calls = [.arguments, .item, .clone, .append] := by rfl\n", "Tactic `rfl` failed"),
    "storage_effect_append_publishes": (STORAGE_EFFECT_PRELUDE +
        "example : (run 3 true true).2.calls = [.arguments, .item, .clone, .append, .publish] := by rfl\n", "Tactic `rfl` failed"),
    "storage_effect_failure_rewinds": (STORAGE_EFFECT_PRELUDE +
        "example : failedPublication.2.cursor = 0 := by rfl\n", "Tactic `rfl` failed"),
    "storage_effect_failure_keeps_node": (STORAGE_EFFECT_PRELUDE +
        "example : failedPublication.1.2.appended = true := by rfl\n", "Tactic `rfl` failed"),
    "storage_effect_failure_keeps_cache": (STORAGE_EFFECT_PRELUDE +
        "example : failedPublication.1.2.published = true := by rfl\n", "Tactic `rfl` failed"),
    "storage_effect_repeat_succeeds": (STORAGE_EFFECT_PRELUDE +
        "example : repeated.1.1 = some .success := by rfl\n", "Tactic `rfl` failed"),
    "storage_effect_repeat_rewinds": (STORAGE_EFFECT_PRELUDE +
        "example : repeated.2.cursor = 1 := by rfl\n", "Tactic `rfl` failed"),
    "storage_effect_ignored_policy_controls": (STORAGE_EFFECT_PRELUDE +
        "example : successful.1.1 = some .allocationFailure := by rfl\n", "Tactic `rfl` failed"),
    "storage_effect_clone_allocates": (STORAGE_EFFECT_PRELUDE +
        "example : (variableAttempt .clone ⟨[], 1⟩).2.cursor = 2 := by rfl\n", "Tactic `rfl` failed"),
    "storage_effect_append_single_event": (STORAGE_EFFECT_PRELUDE +
        "example : (variableAttempt .append ⟨[], 1⟩).2.cursor = 2 := by rfl\n", "Tactic `rfl` failed"),
    "storage_effect_failed_item_missing_event": (STORAGE_EFFECT_PRELUDE +
        "example : (run 0 false true).2.calls = [] := by rfl\n", "Tactic `rfl` failed"),

    "local_state_force_rewinds": (LOCAL_STATE_PRELUDE +
        "example : forceFailure.2.allocationCursor = 1 := by rfl\n", "Tactic `rfl` failed"),
    "local_state_force_succeeds": (LOCAL_STATE_PRELUDE +
        "example : forceFailure.1 = .ok () := by rfl\n", "Tactic `rfl` failed"),
    "local_state_force_publishes": (LOCAL_STATE_PRELUDE +
        "example : forceFailure.2.table ⟨1, 1, 0, [0, 1], 0⟩ = some 7 := by rfl\n", "Tactic `rfl` failed"),
    "local_state_validation_attempts_normalization": (LOCAL_STATE_PRELUDE +
        "example : validationFailure.2.allocationCursor = 2 := by rfl\n", "Tactic `rfl` failed"),
    "local_state_first_cursor": (LOCAL_STATE_PRELUDE +
        "example : first.2.allocationCursor = 0 := by rfl\n", "Tactic `rfl` failed"),
    "local_state_recursive_reset": (LOCAL_STATE_PRELUDE +
        "example : first.2.allocationCursor = 2 := by rfl\n", "Tactic `rfl` failed"),
    "local_state_second_succeeds": (LOCAL_STATE_PRELUDE +
        "example : second.1 = .ok 7 := by rfl\n", "Tactic `rfl` failed"),
    "local_state_second_rewinds": (LOCAL_STATE_PRELUDE +
        "example : second.2.allocationCursor = 1 := by rfl\n", "Tactic `rfl` failed"),
    "local_state_second_drops_value": (LOCAL_STATE_PRELUDE +
        "example : second.2.read 7 = none := by rfl\n", "Tactic `rfl` failed"),
    "local_state_second_publishes": (LOCAL_STATE_PRELUDE +
        "example : second.2.table ⟨1, 1, 0, [0, 1], 78⟩ = some 7 := by rfl\n", "Tactic `rfl` failed"),
    "local_state_second_drops_cache": (LOCAL_STATE_PRELUDE +
        "example : second.2.table ⟨1, 1, 0, [0, 1], 77⟩ = none := by rfl\n", "Tactic `rfl` failed"),
    "local_state_cache_attempts_transfer": (LOCAL_STATE_PRELUDE +
        "example : cached.2.allocationCursor = 2 := by rfl\n", "Tactic `rfl` failed"),
    "local_state_empty_attempts_allocation": (LOCAL_STATE_PRELUDE +
        "example : transfer [] 1 = (.error .outOfMemory, 2) := by rfl\n", "Tactic `rfl` failed"),
    "local_state_normalize_after_cache": (LOCAL_STATE_PRELUDE +
        "example : normalizationFailure.1 = .ok 7 := by rfl\n", "Tactic `rfl` failed"),
    "local_state_normalize_rewinds": (LOCAL_STATE_PRELUDE +
        "example : normalizationFailure.2.allocationCursor = 1 := by rfl\n", "Tactic `rfl` failed"),
    "local_state_capacity_attempts_normalization": (LOCAL_STATE_PRELUDE +
        "example : capacityFirst.2.allocationCursor = 2 := by rfl\n", "Tactic `rfl` failed"),
    "local_state_local_discards_structure": (LOCAL_STATE_PRELUDE +
        "example : (liftLocal attempt represented).2.representatives = none := by rfl\n", "Tactic `rfl` failed"),
    "local_state_insert_resets_cursor": (LOCAL_STATE_PRELUDE +
        "example : inserted.2.allocationCursor = 0 := by rfl\n", "Tactic `rfl` failed"),
    "local_state_sequence_ignores_state": (LOCAL_STATE_PRELUDE +
        "example : twoAttempts.1 = .ok () := by rfl\n", "Tactic `rfl` failed"),
    "local_state_sequence_rewinds": (LOCAL_STATE_PRELUDE +
        "example : twoAttempts.2.allocationCursor = 0 := by rfl\n", "Tactic `rfl` failed"),

    "recursive_frame_success_detaches": (RECURSIVE_FRAME_PRELUDE +
        "example : result.2.representatives = none := by rfl\n", "Tactic `rfl` failed"),
    "recursive_frame_success_omits_clone": (RECURSIVE_FRAME_PRELUDE +
        "example : result.2.representatives = some cells := by rfl\n", "Tactic `rfl` failed"),
    "recursive_frame_reorders_prefix": (RECURSIVE_FRAME_PRELUDE +
        "example : result.2.representatives = some (cells.reverse ++ [newCell]) := by rfl\n", "Tactic `rfl` failed"),
    "recursive_frame_caller_is_constant": (RECURSIVE_FRAME_PRELUDE +
        "example : (representativeReads result.2).constant 0 = .ok (some 3) := by rfl\n", "Tactic `rfl` failed"),
    "recursive_frame_old_constant_changes": (RECURSIVE_FRAME_PRELUDE +
        "example : (representativeReads result.2).constant 1 = .ok (some 32) := by rfl\n", "Tactic `rfl` failed"),
    "recursive_frame_old_slice_address": (RECURSIVE_FRAME_PRELUDE +
        "example : (representativeReads result.2).operation 0 0x33 = .ok (some ⟨1, []⟩) := by rfl\n", "Tactic `rfl` failed"),
    "recursive_frame_old_slice_contents": (RECURSIVE_FRAME_PRELUDE +
        "example : (representativeReads result.2).operation 0 0x33 = .ok (some ⟨0, [1]⟩) := by rfl\n", "Tactic `rfl` failed"),
    "recursive_frame_failure_undoes_recursion": (RECURSIVE_FRAME_PRELUDE +
        "example : publicationFailure.2.representatives = some cells := by rfl\n", "Tactic `rfl` failed"),
    "recursive_frame_failure_loses_clone_value": (RECURSIVE_FRAME_PRELUDE +
        "example : publicationFailure.2.read 3 = none := by rfl\n", "Tactic `rfl` failed"),
    "recursive_frame_failure_loses_recursive_cache": (RECURSIVE_FRAME_PRELUDE +
        "example : publicationFailure.2.table ⟨2, 0, 42, [], 0⟩ = none := by rfl\n", "Tactic `rfl` failed"),
    "recursive_frame_failure_publishes_parent": (RECURSIVE_FRAME_PRELUDE +
        "example : publicationFailure.2.table ⟨1, 1, 0, [1, 2], 77⟩ = some 3 := by rfl\n", "Tactic `rfl` failed"),
    "recursive_frame_allocation_failure_grows": (RECURSIVE_FRAME_PRELUDE +
        "example : allocationFailure.2.representatives = some (cells ++ [newCell]) := by rfl\n", "Tactic `rfl` failed"),
    "recursive_frame_cutoff_success": (RECURSIVE_FRAME_PRELUDE +
        "example : cutoff.1 = .ok 3 := by rfl\n", "Tactic `rfl` failed"),
    "recursive_frame_normalization_order": (RECURSIVE_FRAME_PRELUDE +
        "example : result.2.table ⟨1, 1, 0, [2, 1], 77⟩ = some 3 := by rfl\n", "Tactic `rfl` failed"),
    "recursive_frame_clone_epoch": (RECURSIVE_FRAME_PRELUDE +
        "example : newCell.sequence = 77 := by rfl\n", "Tactic `rfl` failed"),
    "recursive_frame_wrong_return_id": (RECURSIVE_FRAME_PRELUDE +
        "example : result.1 = .ok 2 := by rfl\n", "Tactic `rfl` failed"),

    "assembly_clone_payload_address": (ASSEMBLY_CLONE_PRELUDE +
        "example : (cloneCode.run (duplicate true) original initial).1 = .ok original := by rfl\n", "Tactic `rfl` failed"),
    "assembly_clone_metadata": (ASSEMBLY_CLONE_PRELUDE +
        "example : copied.metadata = [] := by rfl\n", "Tactic `rfl` failed"),
    "assembly_clone_payload_contents": (ASSEMBLY_CLONE_PRELUDE +
        "example : copied.verbatim.map (fun p => p.data.contents) = some [0] := by rfl\n", "Tactic `rfl` failed"),
    "assembly_clone_argument_count": (ASSEMBLY_CLONE_PRELUDE +
        "example : copied.verbatim.map (fun p => p.arguments) = some 0 := by rfl\n", "Tactic `rfl` failed"),
    "assembly_clone_return_count": (ASSEMBLY_CLONE_PRELUDE +
        "example : copied.verbatim.map (fun p => p.returns) = some 0 := by rfl\n", "Tactic `rfl` failed"),
    "assembly_clone_oom_succeeds": (ASSEMBLY_CLONE_PRELUDE +
        "example : (cloneCode.run (duplicate false) original initial).1 = .ok copied := by rfl\n", "Tactic `rfl` failed"),
    "assembly_clone_oom_allocates": (ASSEMBLY_CLONE_PRELUDE +
        "example : (cloneCode.run (duplicate false) original initial).2 = allocated := by rfl\n", "Tactic `rfl` failed"),
    "assembly_clone_absent_allocates": (ASSEMBLY_CLONE_PRELUDE +
        "example : (cloneCode.run (duplicate false) plain initial).1 = .error .outOfMemory := by rfl\n", "Tactic `rfl` failed"),
    "assembly_clone_empty_allocates": (ASSEMBLY_CLONE_PRELUDE +
        "example : (cloneCode.run (duplicate false) empty initial).2 = allocated := by rfl\n", "Tactic `rfl` failed"),
    "assembly_clone_cleanup_retains": (ASSEMBLY_CLONE_PRELUDE +
        "example : (deinitCode.run free copied allocated).2 = allocated := by rfl\n", "Tactic `rfl` failed"),
    "assembly_clone_cleanup_frees_source": (ASSEMBLY_CLONE_PRELUDE +
        "example : (deinitCode.run free copied allocated).2 = [] := by rfl\n", "Tactic `rfl` failed"),
    "assembly_clone_cleanup_live_value": (ASSEMBLY_CLONE_PRELUDE +
        "example : (deinitCode.run free copied allocated).1 = some copied := by rfl\n", "Tactic `rfl` failed"),

    "observed_storage_result_id": (OBSERVED_STORAGE_PRELUDE +
        "example : result.1 = .ok 2 := by rfl\n", "Tactic `rfl` failed"),
    "observed_storage_cloned_value": (OBSERVED_STORAGE_PRELUDE +
        "example : result.2.read 1 = some 3 := by rfl\n", "Tactic `rfl` failed"),
    "observed_storage_old_value": (OBSERVED_STORAGE_PRELUDE +
        "example : result.2.read 0 = some 0 := by rfl\n", "Tactic `rfl` failed"),
    "observed_storage_slice_address": (OBSERVED_STORAGE_PRELUDE +
        "example : (representativeReads result.2).operation 1 0x19 = .ok (some ⟨0, [0]⟩) := by rfl\n", "Tactic `rfl` failed"),
    "observed_storage_slice_operands": (OBSERVED_STORAGE_PRELUDE +
        "example : (representativeReads result.2).operation 1 0x19 = .ok (some ⟨40, [1]⟩) := by rfl\n", "Tactic `rfl` failed"),
    "observed_storage_key_epoch": (OBSERVED_STORAGE_PRELUDE +
        "example : result.2.table { key with sequence := 0 } = some 1 := by rfl\n", "Tactic `rfl` failed"),
    "observed_storage_rollback_value": (OBSERVED_STORAGE_PRELUDE +
        "example : (failure .publish).2.read 1 = some cell.value := by rfl\n", "Tactic `rfl` failed"),
    "observed_storage_rollback_view": (OBSERVED_STORAGE_PRELUDE +
        "example : (failure .publish).2.representatives = none := by rfl\n", "Tactic `rfl` failed"),
    "observed_storage_rollback_cell": (OBSERVED_STORAGE_PRELUDE +
        "example : (representativeReads (failure .publish).2).operation 1 0x19 = .ok (some ⟨40, [0]⟩) := by rfl\n", "Tactic `rfl` failed"),
    "observed_storage_rollback_cache": (OBSERVED_STORAGE_PRELUDE +
        "example : (failure .publish).2.table key = some 1 := by rfl\n", "Tactic `rfl` failed"),
    "observed_storage_uncached_publication": (OBSERVED_STORAGE_PRELUDE +
        "example : uncached.2.table key = some 1 := by rfl\n", "Tactic `rfl` failed"),
    "observed_storage_uncached_allocation": (OBSERVED_STORAGE_PRELUDE +
        "example : uncached.1 = .error .outOfMemory := by rfl\n", "Tactic `rfl` failed"),
    "observed_storage_missing_view": (OBSERVED_STORAGE_PRELUDE +
        "example : (observedInsert cell key true succeeds ObservedTests.unrepresented).1 = .ok 1 := by rfl\n", "Tactic `rfl` failed"),
    "observed_storage_clone_binding": (OBSERVED_STORAGE_PRELUDE +
        "example : keyCode.run wrongCell.item wrongCell.arguments wrongCell.sequence = some key := by rfl\n", "Tactic `rfl` failed"),
    "observed_storage_clone_epoch": (OBSERVED_STORAGE_PRELUDE +
        "example : keyCode.run cell.item cell.arguments cell.sequence = some { key with sequence := 0 } := by rfl\n", "Tactic `rfl` failed"),
    "observed_storage_old_kind": (OBSERVED_STORAGE_PRELUDE +
        "example : (representativeReads result.2).constant 0 = .ok (some 3) := by rfl\n", "Tactic `rfl` failed"),

    "observed_heap_constant_kind": (OBSERVED_HEAP_PRELUDE +
        "example : (representativeReads callerHeap).constant 0 = .ok (some 3) := by rfl\n", "Tactic `rfl` failed"),
    "observed_heap_operation_kind": (OBSERVED_HEAP_PRELUDE +
        "example : (representativeReads constantHeap).operation 0 0x33 = .ok (some ⟨0, []⟩) := by rfl\n", "Tactic `rfl` failed"),
    "observed_heap_operand_slice": (OBSERVED_HEAP_PRELUDE +
        "example : (representativeReads callerHeap).operation 0 0x33 = .ok (some ⟨0, [0]⟩) := by rfl\n", "Tactic `rfl` failed"),
    "observed_heap_invalid_id": (OBSERVED_HEAP_PRELUDE +
        "example : (representativeReads callerHeap).constant 1 = .ok (some 0) := by rfl\n", "Tactic `rfl` failed"),
    "observed_heap_unrepresented_constant": (OBSERVED_HEAP_PRELUDE +
        "example : (representativeReads unrepresented).constant 0 = .ok none := by rfl\n", "Tactic `rfl` failed"),
    "observed_heap_unrepresented_operation": (OBSERVED_HEAP_PRELUDE +
        "example : (representativeReads unrepresented).operation 0 0x33 = .ok none := by rfl\n", "Tactic `rfl` failed"),
    "observed_heap_idempotence": (OBSERVED_HEAP_PRELUDE +
        "example : result.1 = .ok 1 := by rfl\n", "Tactic `rfl` failed"),
    "observed_heap_value": (OBSERVED_HEAP_PRELUDE +
        "example : result.2.read 0 = some 4 := by rfl\n", "Tactic `rfl` failed"),
    "observed_heap_request_epoch": (OBSERVED_HEAP_PRELUDE +
        "example : result.2.table ⟨1, 0x16, 0, [0, 0], 0⟩ = some 0 := by rfl\n", "Tactic `rfl` failed"),
    "observed_heap_lost_representatives": (OBSERVED_HEAP_PRELUDE +
        "example : result.2.representatives = none := by rfl\n", "Tactic `rfl` failed"),
    "observed_heap_publication_failure_view": (OBSERVED_HEAP_PRELUDE +
        "example : publicationFailure.2.representatives = none := by rfl\n", "Tactic `rfl` failed"),
    "observed_heap_publication_failure_cache": (OBSERVED_HEAP_PRELUDE +
        "example : publicationFailure.2.table ⟨1, 0x16, 0, [0, 0], 99⟩ = some 0 := by rfl\n", "Tactic `rfl` failed"),
    "observed_heap_recursive_failure": (OBSERVED_HEAP_PRELUDE +
        "example : recursiveFailure.1 = .error .capacity := by rfl\n", "Tactic `rfl` failed"),
    "observed_heap_recursive_failure_view": (OBSERVED_HEAP_PRELUDE +
        "example : recursiveFailure.2.representatives = none := by rfl\n", "Tactic `rfl` failed"),

    "normalization_ownership_input_free": (NORMALIZATION_OWNERSHIP_PRELUDE +
        "example : borrowed.2.owner = .released := by rfl\n", "Tactic `rfl` failed"),
    "normalization_ownership_scratch_free": (NORMALIZATION_OWNERSHIP_PRELUDE +
        "example : scratch.2.owner = .released := by rfl\n", "Tactic `rfl` failed"),
    "normalization_ownership_heap_not_cleared": (NORMALIZATION_OWNERSHIP_PRELUDE +
        "example : allocated.2.owned = true := by rfl\n", "Tactic `rfl` failed"),
    "normalization_ownership_hit_transfer": (NORMALIZATION_OWNERSHIP_PRELUDE +
        "example : hit.2.owner = .caller := by rfl\n", "Tactic `rfl` failed"),
    "normalization_ownership_cleanup_transfer": (NORMALIZATION_OWNERSHIP_PRELUDE +
        "example : cleaned.2.owner = .caller := by rfl\n", "Tactic `rfl` failed"),
    "normalization_ownership_duplicate_failure": (NORMALIZATION_OWNERSHIP_PRELUDE +
        "example : duplicateFailure.1 = .transferred := by rfl\n", "Tactic `rfl` failed"),
    "normalization_ownership_allocation_retry": (NORMALIZATION_OWNERSHIP_PRELUDE +
        "example : allocationFailure.1 = .transferred := by rfl\n", "Tactic `rfl` failed"),
    "normalization_ownership_missing_clear": (NORMALIZATION_OWNERSHIP_PRELUDE +
        "example : noClear.2.invalid = false := by rfl\n", "Tactic `rfl` failed"),
    "normalization_ownership_missing_free": (NORMALIZATION_OWNERSHIP_PRELUDE +
        "example : noFree.2.owner = .released := by rfl\n", "Tactic `rfl` failed"),
    "normalization_ownership_scratch_owned": (NORMALIZATION_OWNERSHIP_PRELUDE +
        "example : ownScratch.2.invalid = false := by rfl\n", "Tactic `rfl` failed"),
    "normalization_ownership_scratch_bounds": (NORMALIZATION_OWNERSHIP_PRELUDE +
        "example : outOfBounds.2.invalid = false := by rfl\n", "Tactic `rfl` failed"),
    "normalization_ownership_allocation_origin": (NORMALIZATION_OWNERSHIP_PRELUDE +
        "example : allocated.2.origin = .scratch := by rfl\n", "Tactic `rfl` failed"),

    "normalization_missing_left": (NORMALIZATION_PRELUDE +
        "example : evaluate ⟨1, some 1, 0⟩ [2, 1] = some 32 := by rfl\n", "Tactic `rfl` failed"),
    "normalization_missing_right": (NORMALIZATION_PRELUDE +
        "example : evaluate ⟨1, some 1, 0⟩ [1, 2] = some 32 := by rfl\n", "Tactic `rfl` failed"),
    "normalization_missing_both": (NORMALIZATION_PRELUDE +
        "example : evaluate ⟨1, some 1, 0⟩ [2, 3] = some 0 := by rfl\n", "Tactic `rfl` failed"),
    "normalization_empty_arity": (NORMALIZATION_PRELUDE +
        "example : evaluate ⟨1, some 1, 0⟩ [] = some 0 := by rfl\n", "Tactic `rfl` failed"),
    "normalization_unary_arity": (NORMALIZATION_PRELUDE +
        "example : evaluate ⟨1, some 1, 0⟩ [0] = some 10 := by rfl\n", "Tactic `rfl` failed"),
    "normalization_ternary_arity": (NORMALIZATION_PRELUDE +
        "example : evaluate ⟨1, some 1, 0⟩ [1, 0, 0] = some 42 := by rfl\n", "Tactic `rfl` failed"),
    "normalization_duplicate_operand": (NORMALIZATION_PRELUDE +
        "example : evaluate ⟨1, some 1, 0⟩ [1, 1] = some 32 := by rfl\n", "Tactic `rfl` failed"),
    "normalization_subtraction_order": (NORMALIZATION_PRELUDE +
        "example : evaluate ⟨1, some 3, 0⟩ [1, 0] = evaluate ⟨1, some 3, 0⟩ [0, 1] := by rfl\n", "Tactic `rfl` failed"),
    "normalization_other_epoch": (NORMALIZATION_PRELUDE +
        "example : evaluate ⟨1, some 49, 0⟩ [1, 0] = some 32 := by rfl\n", "Tactic `rfl` failed"),
    "normalization_atom_order": (NORMALIZATION_PRELUDE +
        "example : evaluate ⟨2, some 1, 5⟩ [1, 0] = some 92 := by rfl\n", "Tactic `rfl` failed"),
    "normalization_missing_empty_instruction": (NORMALIZATION_PRELUDE +
        "example : normalize ⟨⟨1, none, 0⟩, [], 77⟩ = .ok [] := by rfl\n", "Tactic `rfl` failed"),
    "normalization_missing_instruction": (NORMALIZATION_PRELUDE +
        "example : normalize ⟨⟨1, none, 0⟩, [1, 0], 77⟩ = .ok [0, 1] := by rfl\n", "Tactic `rfl` failed"),
    "normalization_normalized_key": (NORMALIZATION_PRELUDE +
        "example : result.2.table ⟨1, 1, 0, [1, 0], 77⟩ = some 7 := by rfl\n", "Tactic `rfl` failed"),
    "normalization_recursive_value": (NORMALIZATION_PRELUDE +
        "example : result.2.read 7 = some 41 := by rfl\n", "Tactic `rfl` failed"),
    "normalization_multiplication": (NORMALIZATION_PRELUDE +
        "example : evaluate ⟨1, some 2, 0⟩ [1, 0] = some 42 := by rfl\n", "Tactic `rfl` failed"),
    "normalization_bitwise_and": (NORMALIZATION_PRELUDE +
        "example : evaluate ⟨1, some 22, 0⟩ [1, 0] = some 42 := by rfl\n", "Tactic `rfl` failed"),
    "normalization_lost_operand": (NORMALIZATION_PRELUDE +
        "example : lostOperand = none := by rfl\n", "Tactic `rfl` failed"),
    "normalization_permutation_required": (NORMALIZATION_PRELUDE +
        "example : (List.drop 1 ([1, 1, 0] : List NodeId)).Perm [1, 1, 0] := by decide\n", "is false"),

    "recursive_zero_cutoff": (RECURSIVE_PRELUDE +
        "example : (result 0).1 = .ok 7 := by rfl\n", "Tactic `rfl` failed"),
    "recursive_nested_cutoff": (RECURSIVE_PRELUDE +
        "example : (result 1).1 = .ok 7 := by rfl\n", "Tactic `rfl` failed"),
    "recursive_completed_depth": (RECURSIVE_PRELUDE +
        "example : (result 2).1 = .error .unsupported := by rfl\n", "Tactic `rfl` failed"),
    "recursive_value": (RECURSIVE_PRELUDE +
        "example : (result 2).2.read 7 = some 41 := by rfl\n", "Tactic `rfl` failed"),
    "recursive_request_epoch": (RECURSIVE_PRELUDE +
        "example : (result 2).2.table ⟨1, 1, 0, [0, 1], 0⟩ = some 7 := by rfl\n", "Tactic `rfl` failed"),
    "recursive_constructor_epoch": (RECURSIVE_PRELUDE +
        "example : (result 2).2.table ⟨2, 0, 42, [], 77⟩ = some 7 := by rfl\n", "Tactic `rfl` failed"),
    "recursive_seed_callback": (RECURSIVE_PRELUDE +
        "example : (result 2).1 = .error .safetyFault := by rfl\n", "Tactic `rfl` failed"),
    "recursive_old_id": (RECURSIVE_PRELUDE +
        "example : (result 2).2.read 0 = some 42 := by rfl\n", "Tactic `rfl` failed"),
    "recursive_publication_failure": (RECURSIVE_PRELUDE +
        "example : (publishFailure 2).1 = .ok 7 := by rfl\n", "Tactic `rfl` failed"),
    "recursive_failure_rollback": (RECURSIVE_PRELUDE +
        "example : (publishFailure 2).2.read 7 = none := by rfl\n", "Tactic `rfl` failed"),
    "recursive_failure_cache": (RECURSIVE_PRELUDE +
        "example : (publishFailure 2).2.table ⟨1, 1, 0, [0, 1], 77⟩ = some 7 := by rfl\n", "Tactic `rfl` failed"),
    "recursive_cache_hit": (RECURSIVE_PRELUDE +
        "example : cacheHit.1 = .error .unsupported := by rfl\n", "Tactic `rfl` failed"),
    "recursive_constant_entry": (RECURSIVE_PRELUDE +
        "example : constantRoot.1 = .error .unsupported := by rfl\n", "Tactic `rfl` failed"),
    "recursive_capacity_order": (RECURSIVE_PRELUDE +
        "example : capacityFirst.1 = .error .outOfMemory := by rfl\n", "Tactic `rfl` failed"),

    "default_dispatch_opcode_scope": (DEFAULT_DISPATCH_PRELUDE +
        "example : nonwords.length = 233 := by rfl\n", "Tactic `rfl` failed"),
    "default_dispatch_left_fault_order": (DEFAULT_DISPATCH_PRELUDE +
        "example : outcomeEqual (faults 0 [0, 1] true).1 (.error .invalidOptional) = true := by rfl\n", "Tactic `rfl` failed"),
    "default_dispatch_right_fault_ignored": (DEFAULT_DISPATCH_PRELUDE +
        "example : outcomeEqual (faults 0 [0, 1] false).1 (.ok none) = true := by rfl\n", "Tactic `rfl` failed"),
    "default_dispatch_sar_read_fault": (DEFAULT_DISPATCH_PRELUDE +
        "example : outcomeEqual (faults 29 [0, 1] false).1 (.ok none) = true := by rfl\n", "Tactic `rfl` failed"),
    "default_dispatch_unary_operation_read": (DEFAULT_DISPATCH_PRELUDE +
        "example : outcomeEqual (faults 0 [0] false).1 (.error .safetyFault) = true := by rfl\n", "Tactic `rfl` failed"),
    "default_dispatch_ternary_short_circuit": (DEFAULT_DISPATCH_PRELUDE +
        "example : outcomeEqual (faults 0 [0, 1, 2] false).1 (.error .invalidOptional) = true := by rfl\n", "Tactic `rfl` failed"),
    "default_dispatch_zero_arity_read": (DEFAULT_DISPATCH_PRELUDE +
        "example : outcomeEqual (faults 0 [] true).1 (.error .invalidId) = true := by rfl\n", "Tactic `rfl` failed"),
    "default_dispatch_four_arity_read": (DEFAULT_DISPATCH_PRELUDE +
        "example : outcomeEqual (faults 0 [0, 1, 2, 3] true).1 (.error .invalidId) = true := by rfl\n", "Tactic `rfl` failed"),
    "default_dispatch_balance_disabled": (DEFAULT_DISPATCH_PRELUDE +
        "example : outcomeEqual (faults 49 [0] false).1 (.error .safetyFault) = true := by rfl\n", "Tactic `rfl` failed"),
    "default_dispatch_balance_enabled": (DEFAULT_DISPATCH_PRELUDE +
        "example : outcomeEqual (faults 49 [0] false ⟨false, some .osaka⟩).1 (.ok none) = true := by rfl\n", "Tactic `rfl` failed"),
    "default_dispatch_selfbalance_default": (DEFAULT_DISPATCH_PRELUDE +
        "example : traceMatches (selfBalance none) (.ok (some 1024)) [(1, 71, 0, [], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "default_dispatch_selfbalance_fork": (DEFAULT_DISPATCH_PRELUDE +
        "example : traceMatches (selfBalance (some .petersburg)) (.ok (some 1024)) [(1, 71, 0, [], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "default_dispatch_selfbalance_arity": (DEFAULT_DISPATCH_PRELUDE +
        "example : traceMatches (selfBalance (some .osaka) [0, 0]) (.ok (some 1024)) [(1, 71, 0, [], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "default_dispatch_selfbalance_failure": (DEFAULT_DISPATCH_PRELUDE +
        "example : traceMatches (selfBalance (some .osaka) [0] 1) (.error .outOfMemory) [] = true := by rfl\n", "Tactic `rfl` failed"),

    "word_dispatch_address_binding": (WORD_DISPATCH_PRELUDE +
        "example : model.operation 48 77 [] = some 3 := by rfl\n", "Tactic `rfl` failed"),
    "word_dispatch_address_arity": (WORD_DISPATCH_PRELUDE +
        "example : model.operation 48 77 [1] = some 5 := by rfl\n", "Tactic `rfl` failed"),
    "word_dispatch_sar_rounding": (WORD_DISPATCH_PRELUDE +
        "example : model.operation 29 77 [1, BitVec.ofInt 256 (-3)] = some (BitVec.ofInt 256 (-1)) := by decide +kernel\n", "is false"),
    "word_dispatch_sar_large": (WORD_DISPATCH_PRELUDE +
        "example : model.operation 29 77 [256, BitVec.ofInt 256 (-3)] = some 0 := by rfl\n", "Tactic `rfl` failed"),
    "word_dispatch_sar_arity": (WORD_DISPATCH_PRELUDE +
        "example : model.operation 29 77 [1] = some 0 := by rfl\n", "Tactic `rfl` failed"),
    "word_dispatch_other_epoch": (WORD_DISPATCH_PRELUDE +
        "example : model.operation 49 78 [5] = some 77 := by rfl\n", "Tactic `rfl` failed"),
    "word_dispatch_atom_epoch": (WORD_DISPATCH_PRELUDE +
        "example : model.atom 2 11 77 [] = some 11 := by rfl\n", "Tactic `rfl` failed"),
    "word_dispatch_decode_sar": (WORD_DISPATCH_PRELUDE +
        "example : Folding.decodeWord 29 = some .shr := by rfl\n", "Tactic `rfl` failed"),
    "word_dispatch_decode_balance": (WORD_DISPATCH_PRELUDE +
        "example : Folding.decodeWord 49 = some .and := by rfl\n", "Tactic `rfl` failed"),
    "word_dispatch_wrong_word_arity": (WORD_DISPATCH_PRELUDE +
        "example : model.operation 1 77 [7] = some 7 := by rfl\n", "Tactic `rfl` failed"),
    "word_dispatch_ternary_value": (WORD_DISPATCH_PRELUDE +
        "example : traceMatches (folded .mulmod) (.ok (some 1024)) [(2, 0, 21, [], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "word_dispatch_failure_retention": (WORD_DISPATCH_PRELUDE +
        "example : traceMatches (folded .add 1) (.error .outOfMemory) [] = true := by rfl\n", "Tactic `rfl` failed"),

    "and_dispatch_byte_mask": (AND_DISPATCH_PRELUDE +
        "example : traceMatches (byteTrial 256) (.ok (some 1024)) [(1, 26, 0, [2, 3], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "and_dispatch_byte_reverse": (AND_DISPATCH_PRELUDE +
        "example : traceMatches (byteTrial 255 true) (.ok (some 1024)) [(1, 26, 0, [2, 3], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "and_dispatch_byte_arity": (AND_DISPATCH_PRELUDE +
        "example : outcomeEqual (byteTrial 255 false [2]).1 (.ok none) = true := by rfl\n", "Tactic `rfl` failed"),
    "and_dispatch_byte_failure_fallback": (AND_DISPATCH_PRELUDE +
        "example : outcomeEqual (byteFirst 1).1 (.error .invalidOptional) = true := by rfl\n", "Tactic `rfl` failed"),
    "and_dispatch_byte_table_priority": (AND_DISPATCH_PRELUDE +
        "example : traceMatches (byteTrial (BitVec.allOnes 256)) (.ok (some 1024)) [(1, 26, 0, [2, 3], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "and_dispatch_strip_materialization": (AND_DISPATCH_PRELUDE +
        "example : traceMatches (stripTrial 255 0) (.ok (some 1025)) [(2, 0, 255, [], 42), (1, 22, 0, [1024, 2], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "and_dispatch_strip_operands": (AND_DISPATCH_PRELUDE +
        "example : traceMatches (stripTrial 255 0) (.ok (some 1025)) [(3, 0, 255, [0], 42), (1, 22, 0, [2, 1024], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "and_dispatch_strip_guard": (AND_DISPATCH_PRELUDE +
        "example : traceMatches (stripTrial 255 31) (.ok (some 1025)) stripCalls = true := by rfl\n", "Tactic `rfl` failed"),
    "and_dispatch_address_mask": (AND_DISPATCH_PRELUDE +
        "example : traceMatches (addressTrial 48 false (AddressMask.mask - 1)) (.ok (some 1024)) [(1, 48, 0, [], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "and_dispatch_address_kind": (AND_DISPATCH_PRELUDE +
        "example : traceMatches (addressTrial 65) (.ok (some 1024)) [(1, 50, 0, [], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "and_dispatch_reassociate_order": (AND_DISPATCH_PRELUDE +
        "example : traceMatches (reassociateTrial true) (.ok (some 1026)) (reassociateCalls false) = true := by rfl\n", "Tactic `rfl` failed"),
    "and_dispatch_alternating_mask": (AND_DISPATCH_PRELUDE +
        "example : traceMatches (alternatingTrial false) (.ok (some 1028)) [(2, 0, 3, [], 42), (1, 22, 0, [2, 1024], 42), (3, 0, 6, [0], 42), (1, 22, 0, [3, 1026], 42), (1, 23, 0, [1025, 1027], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "and_dispatch_alternating_materialization": (AND_DISPATCH_PRELUDE +
        "example : traceMatches (alternatingTrial false) (.ok (some 1028)) [(2, 0, 2, [], 42), (1, 22, 0, [2, 1024], 42), (3, 0, 6, [1], 42), (1, 22, 0, [3, 1026], 42), (1, 23, 0, [1025, 1027], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "and_dispatch_alternating_final_opcode": (AND_DISPATCH_PRELUDE +
        "example : traceMatches (alternatingTrial false) (.ok (some 1028)) [(2, 0, 2, [], 42), (1, 22, 0, [2, 1024], 42), (3, 0, 6, [0], 42), (1, 22, 0, [3, 1026], 42), (1, 22, 0, [1025, 1027], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "and_dispatch_failure_rollback": (AND_DISPATCH_PRELUDE +
        "example : (alternatingTrial false 5).2.read 0 = some 4 := by rfl\n", "Tactic `rfl` failed"),
    "and_dispatch_covered_large": (AND_DISPATCH_PRELUDE +
        "example : traceMatches (coveredTrial 257 1) (.ok (some 1024)) [(1, 28, 0, [1, 2], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "and_dispatch_covered_table_priority": (AND_DISPATCH_PRELUDE +
        "example : traceMatches (coveredTrial 7 (BitVec.allOnes 256)) (.ok (some 1024)) [(1, 28, 0, [1, 2], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "and_dispatch_merged_large": (AND_DISPATCH_PRELUDE +
        "example : traceMatches (mergedTrial (some 256)) (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "and_dispatch_merged_operands": (AND_DISPATCH_PRELUDE +
        "example : traceMatches (mergedTrial none) (.ok (some 1025)) [(1, 22, 0, [1, 2], 42), (1, 27, 0, [1024, 0], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "and_dispatch_merged_read_order": (AND_DISPATCH_PRELUDE +
        "example : outcomeEqual mergedFault.1 (.ok none) = true := by rfl\n", "Tactic `rfl` failed"),

    "signextend_dispatch_minimum": (SIGNEXTEND_DISPATCH_PRELUDE +
        "example : traceMatches (nestedTrial 7 2) (.ok (some 1025)) (nestedCalls 7) = true := by rfl\n", "Tactic `rfl` failed"),
    "signextend_dispatch_equal_unknown": (SIGNEXTEND_DISPATCH_PRELUDE +
        "example : outcomeEqual (repeatTrial none).1 (.ok none) = true := by rfl\n", "Tactic `rfl` failed"),
    "signextend_dispatch_equal_allocation": (SIGNEXTEND_DISPATCH_PRELUDE +
        "example : traceMatches (repeatTrial (some 31)) (.ok (some 1025)) [(2, 0, 31, [], 42), (1, 11, 0, [1024, 1], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "signextend_dispatch_large_priority": (SIGNEXTEND_DISPATCH_PRELUDE +
        "example : outcomeEqual (nestedTrial 31 0).1 (.ok (some 3)) = true := by rfl\n", "Tactic `rfl` failed"),
    "signextend_dispatch_operand_order": (SIGNEXTEND_DISPATCH_PRELUDE +
        "example : traceMatches (nestedTrial 7 2) (.ok (some 1025)) [(2, 0, 2, [], 42), (1, 11, 0, [2, 1024], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "signextend_dispatch_failure_rollback": (SIGNEXTEND_DISPATCH_PRELUDE +
        "example : (nestedTrial 7 2 2).2.read 0 = some 1 := by rfl\n", "Tactic `rfl` failed"),
    "signextend_dispatch_failure_fallback": (SIGNEXTEND_DISPATCH_PRELUDE +
        "example : outcomeEqual (firstTrial false false 2).1 (.error .invalidOptional) = true := by rfl\n", "Tactic `rfl` failed"),
    "signextend_dispatch_equality_read_priority": (SIGNEXTEND_DISPATCH_PRELUDE +
        "example : outcomeEqual (firstTrial true true).1 (.error .invalidOptional) = true := by rfl\n", "Tactic `rfl` failed"),
    "signextend_dispatch_read_failure_miss": (SIGNEXTEND_DISPATCH_PRELUDE +
        "example : outcomeEqual (firstTrial false true).1 (.ok none) = true := by rfl\n", "Tactic `rfl` failed"),
    "signextend_dispatch_sar_opcode": (SIGNEXTEND_DISPATCH_PRELUDE +
        "example : traceMatches (shiftTrial 2 232) (.ok (some 1024)) [(1, 28, 0, [1, 2], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "signextend_dispatch_sar_operands": (SIGNEXTEND_DISPATCH_PRELUDE +
        "example : traceMatches (shiftTrial 2 232) (.ok (some 1024)) [(1, 29, 0, [2, 1], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "signextend_dispatch_sar_position": (SIGNEXTEND_DISPATCH_PRELUDE +
        "example : traceMatches (shiftTrial 2 240) (.ok (some 1024)) sarCalls = true := by rfl\n", "Tactic `rfl` failed"),
    "signextend_dispatch_sar_alignment": (SIGNEXTEND_DISPATCH_PRELUDE +
        "example : traceMatches (shiftTrial 0 247) (.ok (some 1024)) sarCalls = true := by rfl\n", "Tactic `rfl` failed"),
    "signextend_dispatch_sar_large_amount": (SIGNEXTEND_DISPATCH_PRELUDE +
        "example : outcomeEqual (shiftTrial 2 256).1 (.error .safetyFault) = true := by rfl\n", "Tactic `rfl` failed"),
    "signextend_dispatch_sar_rounding": (SIGNEXTEND_DISPATCH_PRELUDE +
        "example : ArithmeticShift.value 1 (BitVec.allOnes 256) = (BitVec.allOnes 256) >>> 1 := by decide\n", "is false"),
    "signextend_dispatch_sar_sign_fill": (SIGNEXTEND_DISPATCH_PRELUDE +
        "example : ArithmeticShift.value 256 (1 <<< 255) = 0 := by decide\n", "is false"),
    "signextend_dispatch_sar_arity": (SIGNEXTEND_DISPATCH_PRELUDE +
        "example : ArithmeticShift.eval [1] = some 0 := by rfl\n", "Tactic `rfl` failed"),
    "signextend_dispatch_unaligned_value": (SIGNEXTEND_DISPATCH_PRELUDE +
        "example : Folding.Op.signextend.value 0 (Folding.Op.shr.value 247 (1 <<< 255) 0) 0 = ArithmeticShift.value 247 (1 <<< 255) := by decide\n", "is false"),
    "signextend_dispatch_early_read_failure": (SIGNEXTEND_DISPATCH_PRELUDE +
        "example : outcomeEqual (faultTrial (some 31) true).1 (.ok (some 3)) = true := by rfl\n", "Tactic `rfl` failed"),
    "signextend_dispatch_unknown_read_failure": (SIGNEXTEND_DISPATCH_PRELUDE +
        "example : outcomeEqual (faultTrial none true).1 (.ok none) = true := by rfl\n", "Tactic `rfl` failed"),

    "shl_dispatch_unaligned_value": (SHL_DISPATCH_PRELUDE +
        "example : Folding.Op.shl.value 1 (Folding.Op.signextend.value 0 0x40 0) 0 = Folding.Op.signextend.value 0 (Folding.Op.shl.value 1 0x40 0) 0 := by decide\n", "is false"),
    "shl_dispatch_index_value": (SHL_DISPATCH_PRELUDE +
        "example : traceMatches (extendTrial 8 2) (.ok (some 1026)) (extendCalls 4) = true := by rfl\n", "Tactic `rfl` failed"),
    "shl_dispatch_index_clipping": (SHL_DISPATCH_PRELUDE +
        "example : traceMatches (extendTrial 16 30) (.ok (some 1026)) (extendCalls 31) = true := by rfl\n", "Tactic `rfl` failed"),
    "shl_dispatch_unaligned_guard": (SHL_DISPATCH_PRELUDE +
        "example : traceMatches (extendTrial 9 2) (.ok (some 1026)) (extendCalls 3) = true := by rfl\n", "Tactic `rfl` failed"),
    "shl_dispatch_index_guard": (SHL_DISPATCH_PRELUDE +
        "example : traceMatches (extendTrial 8 33) (.ok (some 1026)) (extendCalls 34) = true := by rfl\n", "Tactic `rfl` failed"),
    "shl_dispatch_constructor_order": (SHL_DISPATCH_PRELUDE +
        "example : traceMatches (extendTrial 8 2) (.ok (some 1026)) [(2, 0, 3, [], 42), (1, 27, 0, [0, 2], 42), (1, 11, 0, [1024, 1025], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "shl_dispatch_shift_operand_order": (SHL_DISPATCH_PRELUDE +
        "example : traceMatches (extendTrial 8 2) (.ok (some 1026)) [(1, 27, 0, [2, 0], 42), (2, 0, 3, [], 42), (1, 11, 0, [1025, 1024], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "shl_dispatch_extend_operand_order": (SHL_DISPATCH_PRELUDE +
        "example : traceMatches (extendTrial 8 2) (.ok (some 1026)) [(1, 27, 0, [0, 2], 42), (2, 0, 3, [], 42), (1, 11, 0, [1024, 1025], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "shl_dispatch_zero_priority": (SHL_DISPATCH_PRELUDE +
        "example : traceMatches (extendTrial 0 2) (.ok (some 1026)) (extendCalls 2) = true := by rfl\n", "Tactic `rfl` failed"),
    "shl_dispatch_large_priority": (SHL_DISPATCH_PRELUDE +
        "example : traceMatches (extendTrial 256 0) (.ok (some 1026)) (extendCalls 32) = true := by rfl\n", "Tactic `rfl` failed"),
    "shl_dispatch_failure_rollback": (SHL_DISPATCH_PRELUDE +
        "example : (extendTrial 8 2 3).2.read 0 = some 2 := by rfl\n", "Tactic `rfl` failed"),
    "shl_dispatch_failure_fallback": (SHL_DISPATCH_PRELUDE +
        "example : outcomeEqual (firstTrial opAND 3).1 (.error .invalidOptional) = true := by rfl\n", "Tactic `rfl` failed"),
    "shl_dispatch_read_failure_miss": (SHL_DISPATCH_PRELUDE +
        "example : outcomeEqual (firstTrial 0).1 (.ok none) = true := by rfl\n", "Tactic `rfl` failed"),
    "shl_dispatch_opposite_large_miss": (SHL_DISPATCH_PRELUDE +
        "example : traceMatches (shiftTrial 1 256 opSHR) (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl\n", "Tactic `rfl` failed"),

    "shr_dispatch_sum_threshold": (SHR_DISPATCH_PRELUDE +
        "example : traceMatches (shiftTrial 1 255) (.ok (some 1025)) [(2, 0, 256, [], 42), (1, 28, 0, [1024, 2], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "shr_dispatch_sum_saturation": (SHR_DISPATCH_PRELUDE +
        "example : outcomeEqual (shiftTrial 1 (BitVec.allOnes 256)).1 (.error .safetyFault) = true := by rfl\n", "Tactic `rfl` failed"),
    "shr_dispatch_zero_table_priority": (SHR_DISPATCH_PRELUDE +
        "example : traceMatches (shiftTrial 0 (BitVec.allOnes 256)) (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "shr_dispatch_opposite_direction": (SHR_DISPATCH_PRELUDE +
        "example : traceMatches (shiftTrial 2 7 opSHL) (.ok (some 1027)) [(2, 0, 5, [], 42), (1, 28, 0, [1024, 2], 42), (2, 0, (BitVec.allOnes 256 <<< 7) >>> 2, [], 42), (1, 22, 0, [1025, 1026], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "shr_dispatch_opposite_equal": (SHR_DISPATCH_PRELUDE +
        "example : outcomeEqual (shiftTrial 8 8 opSHL).1 (.ok (some 2)) = true := by rfl\n", "Tactic `rfl` failed"),
    "shr_dispatch_opposite_mask": (SHR_DISPATCH_PRELUDE +
        "example : traceMatches (shiftTrial 7 2 opSHL) (.ok (some 1027)) [(2, 0, 5, [], 42), (1, 28, 0, [1024, 2], 42), (2, 0, BitVec.allOnes 256, [], 42), (1, 22, 0, [1025, 1026], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "shr_dispatch_opposite_large_miss": (SHR_DISPATCH_PRELUDE +
        "example : traceMatches (shiftTrial 1 256 opSHL) (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "shr_dispatch_mask_shift": (SHR_DISPATCH_PRELUDE +
        "example : traceMatches (maskTrial false) (.ok (some 1026)) [(1, 28, 0, [0, 2], 42), (2, 0, 0xff00, [], 42), (1, 22, 0, [1024, 1025], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "shr_dispatch_mask_operand_order": (SHR_DISPATCH_PRELUDE +
        "example : traceMatches (maskTrial false) (.ok (some 1026)) [(1, 28, 0, [2, 0], 42), (2, 0, 255, [], 42), (1, 22, 0, [1024, 1025], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "shr_dispatch_failure_rollback": (SHR_DISPATCH_PRELUDE +
        "example : (shiftTrial 7 2 opSHL 4).2.read 0 = some 3 := by rfl\n", "Tactic `rfl` failed"),
    "shr_dispatch_failure_fallback": (SHR_DISPATCH_PRELUDE +
        "example : outcomeEqual (firstTrial false 2).1 (.error .invalidOptional) = true := by rfl\n", "Tactic `rfl` failed"),
    "shr_dispatch_read_failure_miss": (SHR_DISPATCH_PRELUDE +
        "example : outcomeEqual (firstTrial true).1 (.ok none) = true := by rfl\n", "Tactic `rfl` failed"),
    "shr_dispatch_unknown_amount": (SHR_DISPATCH_PRELUDE +
        "example : outcomeEqual (faultTrial none).1 (.error .invalidOptional) = true := by rfl\n", "Tactic `rfl` failed"),
    "shr_dispatch_folding_priority": (SHR_DISPATCH_PRELUDE +
        "example : outcomeEqual (folded 0 7).1 (.ok (some 1)) = true := by rfl\n", "Tactic `rfl` failed"),
    "shr_dispatch_premature_zero": (SHR_DISPATCH_PRELUDE +
        "example : traceMatches (shiftTrial 1 254) (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl\n", "Tactic `rfl` failed"),

    "byte_dispatch_index_order": (BYTE_DISPATCH_PRELUDE +
        "example : traceMatches (shiftTrial 2 opSHL 8) (.ok (some 1025)) [(2, 0, 3, [], 42), (1, 26, 0, [2, 1024], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "byte_dispatch_unaligned_left": (BYTE_DISPATCH_PRELUDE +
        "example : traceMatches (shiftTrial 2 opSHL 9) (.ok (some 1025)) (byteCalls 3) = true := by rfl\n", "Tactic `rfl` failed"),
    "byte_dispatch_unaligned_zero": (BYTE_DISPATCH_PRELUDE +
        "example : outcomeEqual (shiftTrial 0 opSHR 9).1 (.ok none) = true := by rfl\n", "Tactic `rfl` failed"),
    "byte_dispatch_unaligned_right": (BYTE_DISPATCH_PRELUDE +
        "example : traceMatches (shiftTrial 1 opSHR 9) (.ok (some 1025)) (byteCalls 0) = true := by rfl\n", "Tactic `rfl` failed"),
    "byte_dispatch_index_underflow": (BYTE_DISPATCH_PRELUDE +
        "example : traceMatches (shiftTrial 0 opSHR 16) (.ok (some 1025)) (byteCalls (0 - 2)) = true := by rfl\n", "Tactic `rfl` failed"),
    "byte_dispatch_last_byte_priority": (BYTE_DISPATCH_PRELUDE +
        "example : traceMatches (shiftTrial 31 opSHR 256) (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "byte_dispatch_crossed_byte_boundary": (BYTE_DISPATCH_PRELUDE +
        "example : traceMatches (shiftTrial 30 opSHL 16) (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "byte_dispatch_failure_rollback": (BYTE_DISPATCH_PRELUDE +
        "example : (shiftTrial 2 opSHR 8 2).2.read 0 = some 1 := by rfl\n", "Tactic `rfl` failed"),
    "byte_dispatch_failure_fallback": (BYTE_DISPATCH_PRELUDE +
        "example : outcomeEqual (firstTrial 2).1 (.error .invalidOptional) = true := by rfl\n", "Tactic `rfl` failed"),
    "byte_dispatch_candidate_priority": (BYTE_DISPATCH_PRELUDE +
        "example : outcomeEqual (firstTrial 0).1 (.error .invalidOptional) = true := by rfl\n", "Tactic `rfl` failed"),
    "byte_dispatch_unknown_index": (BYTE_DISPATCH_PRELUDE +
        "example : outcomeEqual (faultTrial none).1 (.error .invalidOptional) = true := by rfl\n", "Tactic `rfl` failed"),
    "byte_dispatch_read_failure_miss": (BYTE_DISPATCH_PRELUDE +
        "example : outcomeEqual (faultTrial (some 0)).1 (.ok none) = true := by rfl\n", "Tactic `rfl` failed"),
    "byte_dispatch_folding_priority": (BYTE_DISPATCH_PRELUDE +
        "example : traceMatches (folded 31 0x1234) (.ok (some 1025)) maskCalls = true := by rfl\n", "Tactic `rfl` failed"),
    "byte_dispatch_left_alignment_semantics": (BYTE_DISPATCH_PRELUDE +
        "example : Folding.Op.byte.value 0 (Folding.Op.shl.value 1 (BitVec.ofNat 256 (2 ^ 247)) 0) 0 = Folding.Op.byte.value 0 (BitVec.ofNat 256 (2 ^ 247)) 0 := by rfl\n", "Tactic `rfl` failed"),
    "byte_dispatch_right_alignment_semantics": (BYTE_DISPATCH_PRELUDE +
        "example : Folding.Op.byte.value 1 (Folding.Op.shr.value 1 (BitVec.ofNat 256 (2 ^ 248)) 0) 0 = Folding.Op.byte.value 1 (BitVec.ofNat 256 (2 ^ 248)) 0 := by rfl\n", "Tactic `rfl` failed"),

    "sub_dispatch_wrapped_negation": (SUB_DISPATCH_PRELUDE +
        "example : traceMatches (constantTrial (BitVec.allOnes 256)) (.ok (some 1025)) [(2, 0, BitVec.allOnes 256, [], 42), (1, 1, 0, [0, 1024], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "sub_dispatch_materialization_kind": (SUB_DISPATCH_PRELUDE +
        "example : traceMatches (nestedTrial opADD false false) (.ok (some 1026)) [(1, 3, 0, [0, 3], 42), (2, 0, 7, [], 42), (1, 1, 0, [1024, 1025], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "sub_dispatch_materialization_identity": (SUB_DISPATCH_PRELUDE +
        "example : traceMatches (nestedTrial opADD false false) (.ok (some 1026)) [(1, 3, 0, [0, 3], 42), (3, 0, 7, [0], 42), (1, 1, 0, [1024, 1025], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "sub_dispatch_operand_order": (SUB_DISPATCH_PRELUDE +
        "example : traceMatches (nestedTrial opSUB false true) (.ok (some 1026)) [(1, 1, 0, [0, 3], 42), (3, 0, 7, [1], 42), (1, 3, 0, [1024, 1025], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "sub_dispatch_right_negation": (SUB_DISPATCH_PRELUDE +
        "example : traceMatches (nestedTrial opSUB true true) (.ok (some 1026)) [(1, 1, 0, [3, 0], 42), (2, 0, 7, [], 42), (1, 1, 0, [1024, 1025], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "sub_dispatch_failure_rollback": (SUB_DISPATCH_PRELUDE +
        "example : (nestedTrial opSUB false true 3).2.read 0 = some 2 := by rfl\n", "Tactic `rfl` failed"),
    "sub_dispatch_failure_fallback": (SUB_DISPATCH_PRELUDE +
        "example : outcomeEqual (orderedTrial 2).1 (.error .invalidOptional) = true := by rfl\n", "Tactic `rfl` failed"),
    "sub_dispatch_candidate_priority": (SUB_DISPATCH_PRELUDE +
        "example : outcomeEqual (orderedTrial 0).1 (.error .invalidOptional) = true := by rfl\n", "Tactic `rfl` failed"),
    "sub_dispatch_read_failure_miss": (SUB_DISPATCH_PRELUDE +
        "example : outcomeEqual faultyTrial.1 (.ok none) = true := by rfl\n", "Tactic `rfl` failed"),
    "sub_dispatch_constant_priority": (SUB_DISPATCH_PRELUDE +
        "example : traceMatches (bothConstants false) (.ok (some 1026)) [(1, 1, 0, [1, 3], 42), (3, 0, 7, [0], 42), (1, 3, 0, [1025, 1024], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "sub_dispatch_zero_table_priority": (SUB_DISPATCH_PRELUDE +
        "example : traceMatches (constantTrial 0) (.ok (some 1025)) [(2, 0, 0, [], 42), (1, 1, 0, [0, 1024], 42)] = true := by rfl\n", "Tactic `rfl` failed"),

    "exp_dispatch_parity_subtraction": (EXP_DISPATCH_PRELUDE +
        "example : traceMatches (minusTrial 0) (.ok (some 1027)) [(2, 0, 1, [], 42), (1, 22, 0, [1, 1024], 42), (1, 21, 0, [1025], 42), (1, 3, 0, [1025, 1026], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "exp_dispatch_failure_rollback": (EXP_DISPATCH_PRELUDE +
        "example : (minusTrial 4).2.read 0 = some 3 := by rfl\n", "Tactic `rfl` failed"),
    "exp_dispatch_failure_fallback": (EXP_DISPATCH_PRELUDE +
        "example : outcomeEqual (minusTrial 3).1 (.ok none) = true := by rfl\n", "Tactic `rfl` failed"),
    "exp_dispatch_revision_gate": (EXP_DISPATCH_PRELUDE +
        "example : traceMatches (baseTrial 2 (some .byzantium)) (.ok (some 1025)) shiftCalls = true := by rfl\n", "Tactic `rfl` failed"),
    "exp_dispatch_no_revision": (EXP_DISPATCH_PRELUDE +
        "example : outcomeEqual (baseTrial 1 none).1 (.ok (some 1024)) = true := by rfl\n", "Tactic `rfl` failed"),
    "exp_dispatch_shift_order": (EXP_DISPATCH_PRELUDE +
        "example : traceMatches (baseTrial 2 (some .osaka)) (.ok (some 1025)) [(2, 0, 1, [], 42), (1, 27, 0, [1024, 1], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "exp_dispatch_folding_priority": (EXP_DISPATCH_PRELUDE +
        "example : traceMatches (folded (BitVec.allOnes 256) 2) (.ok (some 1027)) minusCalls = true := by rfl\n", "Tactic `rfl` failed"),
    "exp_dispatch_zero_power": (EXP_DISPATCH_PRELUDE +
        "example : traceMatches (folded 0 0) (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "exp_dispatch_large_shift": (EXP_DISPATCH_PRELUDE +
        "example : traceMatches (folded 2 256) (.ok (some 1024)) [(2, 0, 1, [], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "exp_dispatch_unsupported_base": (EXP_DISPATCH_PRELUDE +
        "example : outcomeEqual (baseTrial 3 (some .osaka)).1 (.ok (some 1025)) = true := by rfl\n", "Tactic `rfl` failed"),

    "mod_dispatch_wrong_mask": (MOD_DISPATCH_PRELUDE +
        "example : traceMatches (nestedTrial opMUL false) (.ok (some 1025)) [(2, 0, 8, [], 42), (1, 22, 0, [2, 1024], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "mod_dispatch_failure_rollback": (MOD_DISPATCH_PRELUDE +
        "example : (nestedTrial opMUL false 2).2.read 0 = some 1 := by rfl\n", "Tactic `rfl` failed"),
    "mod_dispatch_failure_fallback": (MOD_DISPATCH_PRELUDE +
        "example : outcomeEqual (firstTrial 1).1 (.error .invalidOptional) = true := by rfl\n", "Tactic `rfl` failed"),
    "mod_dispatch_yul_gate": (MOD_DISPATCH_PRELUDE +
        "example : traceMatches (nestedTrial opMUL false) (.ok (some 1024)) [(1, 9, 0, [0, 1, 3], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "mod_dispatch_product_priority": (MOD_DISPATCH_PRELUDE +
        "example : outcomeEqual (firstTrial 0).1 (.error .invalidOptional) = true := by rfl\n", "Tactic `rfl` failed"),
    "mod_dispatch_nonpower_reads": (MOD_DISPATCH_PRELUDE +
        "example : outcomeEqual (faultyTrial 7).1 (.error .invalidOptional) = true := by rfl\n", "Tactic `rfl` failed"),
    "mod_dispatch_read_failure_fallback": (MOD_DISPATCH_PRELUDE +
        "example : outcomeEqual (faultyTrial 8).1 (.ok (some 1025)) = true := by rfl\n", "Tactic `rfl` failed"),
    "mod_dispatch_narrowing_miss": (MOD_DISPATCH_PRELUDE +
        "example : outcomeEqual (highTrial true 7).1 (.ok none) = true := by rfl\n", "Tactic `rfl` failed"),
    "mod_dispatch_nonpower_add": (MOD_DISPATCH_PRELUDE +
        "example : Folding.Op.mod.value (Folding.Op.add.value (BitVec.allOnes 256) 2 0) 3 0 = Folding.Op.addmod.value (BitVec.allOnes 256) 2 3 := by rfl\n", "Tactic `rfl` failed"),
    "mod_dispatch_nonpower_mul": (MOD_DISPATCH_PRELUDE +
        "example : Folding.Op.mod.value (Folding.Op.mul.value (BitVec.allOnes 256) 2 0) 3 0 = Folding.Op.mulmod.value (BitVec.allOnes 256) 2 3 := by rfl\n", "Tactic `rfl` failed"),

    "arity_dispatch_add_wrap": (ARITY_DISPATCH_PRELUDE +
        "example : traceMatches (modularTrial opADDMOD) (.ok (some 1024)) [(2, 0, 1, [], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "arity_dispatch_mul_wrap": (ARITY_DISPATCH_PRELUDE +
        "example : traceMatches (modularTrial opMULMOD) (.ok (some 1024)) [(2, 0, 2, [], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "arity_dispatch_zero_modulus": (ARITY_DISPATCH_PRELUDE +
        "example : traceMatches (zeroModulus opMULMOD) (.ok (some 1024)) [(2, 0, 63, [], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "arity_dispatch_missing_continues": (ARITY_DISPATCH_PRELUDE +
        "example : outcomeEqual (missingTrial [0, 1, 2]).1 (.error .invalidOptional) = true := by rfl\n", "Tactic `rfl` failed"),
    "arity_dispatch_read_failure_miss": (ARITY_DISPATCH_PRELUDE +
        "example : outcomeEqual (missingTrial [1, 0, 2]).1 (.ok none) = true := by rfl\n", "Tactic `rfl` failed"),
    "arity_dispatch_large_arity_reads": (ARITY_DISPATCH_PRELUDE +
        "example : outcomeEqual (missingTrial [1, 2, 3, 4]).1 (.error .invalidOptional) = true := by rfl\n", "Tactic `rfl` failed"),
    "arity_dispatch_failure_fallback": (ARITY_DISPATCH_PRELUDE +
        "example : outcomeEqual (modularTrial opADDMOD 1).1 (.ok none) = true := by rfl\n", "Tactic `rfl` failed"),
    "arity_dispatch_failure_rollback": (ARITY_DISPATCH_PRELUDE +
        "example : (modularTrial opADDMOD 1).2.read 0 = none := by rfl\n", "Tactic `rfl` failed"),

    "div_dispatch_power_count": (DIV_DISPATCH_PRELUDE +
        "example : traceMatches (revisionTrial 0) (.ok (some 1025)) [(2, 0, 8, [], 42), (1, 28, 0, [1024, 0], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "div_dispatch_failure_fallback": (DIV_DISPATCH_PRELUDE +
        "example : outcomeEqual (revisionTrial 1).1 (.error .invalidOptional) = true := by rfl\n", "Tactic `rfl` failed"),
    "div_dispatch_failure_rollback": (DIV_DISPATCH_PRELUDE +
        "example : (revisionTrial 2).2.read 0 = some 1 := by rfl\n", "Tactic `rfl` failed"),
    "div_dispatch_revision_disabled": (DIV_DISPATCH_PRELUDE +
        "example : outcomeEqual (highTrial 64 .byzantium).1 (.ok (some 1025)) = true := by rfl\n", "Tactic `rfl` failed"),
    "div_dispatch_narrowing_miss": (DIV_DISPATCH_PRELUDE +
        "example : outcomeEqual (highTrial 7 .osaka).1 (.ok none) = true := by rfl\n", "Tactic `rfl` failed"),
    "div_dispatch_shift_direction": (DIV_DISPATCH_PRELUDE +
        "example : traceMatches (shiftTrial 256 1) (.ok (some 1024)) [(1, 27, 0, [1, 0], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "div_dispatch_shift_base": (DIV_DISPATCH_PRELUDE +
        "example : outcomeEqual (shiftTrial 7 2).1 (.ok (some 1024)) = true := by rfl\n", "Tactic `rfl` failed"),
    "div_dispatch_folding_priority": (DIV_DISPATCH_PRELUDE +
        "example : traceMatches (run [⟨some 17, none, []⟩, ⟨some 8, none, []⟩] opDIV [0, 1] ⟨true, some .osaka⟩) (.ok (some 1025)) revisionCalls = true := by rfl\n", "Tactic `rfl` failed"),
    "div_dispatch_zero_divisor": (DIV_DISPATCH_PRELUDE +
        "example : traceMatches (run [⟨some 17, none, []⟩, ⟨some 0, none, []⟩] opDIV [0, 1]) (.ok (some 1024)) [(2, 0, 17, [], 42)] = true := by rfl\n", "Tactic `rfl` failed"),

    "mul_dispatch_power_count": (MUL_DISPATCH_PRELUDE +
        "example : traceMatches (revisionTrial 0) (.ok (some 1025)) [(2, 0, 8, [], 42), (1, 27, 0, [1024, 1], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "mul_dispatch_failure_fallback": (MUL_DISPATCH_PRELUDE +
        "example : outcomeEqual (revisionTrial 1).1 (.error .invalidOptional) = true := by rfl\n", "Tactic `rfl` failed"),
    "mul_dispatch_failure_rollback": (MUL_DISPATCH_PRELUDE +
        "example : (revisionTrial 2).2.read 0 = some 1 := by rfl\n", "Tactic `rfl` failed"),
    "mul_dispatch_revision_disabled": (MUL_DISPATCH_PRELUDE +
        "example : outcomeEqual (highTrial 64 .byzantium).1 (.ok (some 1025)) = true := by rfl\n", "Tactic `rfl` failed"),
    "mul_dispatch_narrowing_miss": (MUL_DISPATCH_PRELUDE +
        "example : outcomeEqual (highTrial 7 .osaka).1 (.ok none) = true := by rfl\n", "Tactic `rfl` failed"),
    "mul_dispatch_reassociation_priority": (MUL_DISPATCH_PRELUDE +
        "example : traceMatches (run competing opMUL [2, 5] ⟨true, some .osaka⟩) (.ok (some 1024)) [(1, 27, 0, [3, 2], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "mul_dispatch_folding_priority": (MUL_DISPATCH_PRELUDE +
        "example : traceMatches (run [⟨some 8, none, []⟩, ⟨some 3, none, []⟩] opMUL [0, 1] ⟨true, some .osaka⟩) (.ok (some 1025)) revisionCalls = true := by rfl\n", "Tactic `rfl` failed"),
    "mul_dispatch_nonpower": (MUL_DISPATCH_PRELUDE +
        "example : outcomeEqual (run [⟨some 3, none, []⟩, ⟨none, none, []⟩] opMUL [0, 1] ⟨true, some .osaka⟩).1 (.ok (some 1025)) = true := by rfl\n", "Tactic `rfl` failed"),
    "unary_full_constant_priority": (UNARY_PRELUDE +
        "example : outcomeEqual (fullConstant opNOT 0).1 (.error .invalidOptional) = true := by rfl\n", "Tactic `rfl` failed"),
    "unary_full_iszero_value": (UNARY_PRELUDE +
        "example : traceMatches (fullConstant opISZERO 0) (.ok (some 1024)) [(2, 0, 1, [], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "unary_full_failure_fallback": (UNARY_PRELUDE +
        "example : outcomeEqual (fullConstant opNOT 1).1 (.error .invalidOptional) = true := by rfl\n", "Tactic `rfl` failed"),
    "unary_full_failure_rollback": (UNARY_PRELUDE +
        "example : (fullConstant opNOT 1).2.read 0 = none := by rfl\n", "Tactic `rfl` failed"),
    "signed_dispatch_floor_division": (SIGNED_DISPATCH_PRELUDE +
        "example : traceMatches (run (signedPair (-7) 2) 5 [0, 1]) (.ok (some 1024)) [(2, 0, BitVec.ofInt 256 (-4), [], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "signed_dispatch_remainder_sign": (SIGNED_DISPATCH_PRELUDE +
        "example : traceMatches (run (signedPair (-7) 2) 7 [0, 1]) (.ok (some 1024)) [(2, 0, 1, [], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "signed_dispatch_overflow_saturates": (SIGNED_DISPATCH_PRELUDE +
        "example : traceMatches (run (signedPair (-(2^255)) (-1)) 5 [0, 1]) (.ok (some 1024)) [(2, 0, BitVec.ofNat 256 (2^255 - 1), [], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "signed_dispatch_fold_priority": (SIGNED_DISPATCH_PRELUDE +
        "example : traceMatches (run (signedPair 7 1) 5 [0, 1]) (.ok (some 0)) [] = true := by rfl\n", "Tactic `rfl` failed"),
    "signed_dispatch_smod_invented_rule": (SIGNED_DISPATCH_PRELUDE +
        "example : traceMatches (run zeroRight 7 [0, 1]) (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "signed_dispatch_error_is_miss": (SIGNED_DISPATCH_PRELUDE +
        "example : outcomeEqual (run zeroRight 5 [0, 1] {} 1).1 (.ok none) = true := by rfl\n", "Tactic `rfl` failed"),
    "signed_dispatch_failure_rollback": (SIGNED_DISPATCH_PRELUDE +
        "example : (run zeroRight 5 [0, 1] {} 1).2.read 0 = none := by rfl\n", "Tactic `rfl` failed"),
    "associative_dispatch_xor_capture": (ASSOCIATIVE_DISPATCH_PRELUDE +
        "example : traceMatches (run cancellation 24 [0, 2]) (.ok (some 0)) [] = true := by rfl\n", "Tactic `rfl` failed"),
    "associative_dispatch_or_capture": (ASSOCIATIVE_DISPATCH_PRELUDE +
        "example : traceMatches (run absorption 23 [2, 0]) (.ok (some 1)) [] = true := by rfl\n", "Tactic `rfl` failed"),
    "associative_dispatch_failure_fallback": (ASSOCIATIVE_DISPATCH_PRELUDE +
        "example : outcomeEqual (trapped 1).1 (.error .invalidOptional) = true := by rfl\n", "Tactic `rfl` failed"),
    "associative_dispatch_failure_rollback": (ASSOCIATIVE_DISPATCH_PRELUDE +
        "example : (trapped 2).2.read 0 = none := by rfl\n", "Tactic `rfl` failed"),
    "associative_dispatch_materialization": (ASSOCIATIVE_DISPATCH_PRELUDE +
        "example : traceMatches (trapped 0) (.ok (some 1026)) [(1, 1, 0, [0, 3], 42), (2, 0, 7, [], 42), (1, 1, 0, [1024, 1025], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "associative_dispatch_wrapping_fold": (ASSOCIATIVE_DISPATCH_PRELUDE +
        "example : traceMatches (run [⟨some (BitVec.allOnes 256), none, []⟩, ⟨some 1, none, []⟩] 1 [0, 1]) (.ok (some 1024)) [(2, 0, BitVec.allOnes 256, [], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "associative_dispatch_mutating_miss": (ASSOCIATIVE_DISPATCH_PRELUDE +
        "example : (orNext growingMiss (pure none) empty).2.read 0 = none := by rfl\n", "Tactic `rfl` failed"),
    "comparison_signed_word": (COMPARISON_PRELUDE +
        "example : Folding.Op.slt.eval [BitVec.allOnes 256, 0] = some 0 := by rfl\n", "Tactic `rfl` failed"),
    "comparison_signed_not_unsigned": (COMPARISON_PRELUDE +
        "example : (run zeroLeft 18 [0, 1]).1 = .ok (some 1025) := by rfl\n", "Tactic `rfl` failed"),
    "comparison_equality_value": (COMPARISON_PRELUDE +
        "example : traceMatches (run unknown 20 [0, 0]) (.ok (some 1024)) [(2, 0, 0, [], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "comparison_boolean_failure_fallback": (COMPARISON_PRELUDE +
        "example : (run zeroLeft 16 [0, 1] {} 2).1 = .ok none := by rfl\n", "Tactic `rfl` failed"),
    "comparison_boolean_failure_rollback": (COMPARISON_PRELUDE +
        "example : (run zeroLeft 16 [0, 1] {} 2).2.read 0 = some 1 := by rfl\n", "Tactic `rfl` failed"),
    "comparison_read_order": (COMPARISON_PRELUDE +
        "example : (binaryStage orderedFaults (constructors 0) 64 opLT 0 1 42 {} empty).1 = .error .safetyFault := by rfl\n", "Tactic `rfl` failed"),
    "comparison_constant_priority": (COMPARISON_PRELUDE +
        "example : traceMatches (run [⟨some 0, none, []⟩] 20 [0, 0]) (.ok (some 1024)) [(1, 21, 0, [0], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "comparison_unknown_table_opcode": (COMPARISON_PRELUDE +
        "example : zigSelect 5 .constants ⟨some 0, none, false⟩ = some .zero := by rfl\n", "Tactic `rfl` failed"),
    "unary_boolean_restriction": (UNARY_PRELUDE +
        "example : Unary.iszero.eval (Unary.iszero.eval (2 : Word)) = 2 := by rfl\n", "Tactic `rfl` failed"),
    "unary_fault_is_not_miss": (UNARY_PRELUDE +
        "example : (unaryStage (faultReads .invalidId) (constructors 0) opNOT 0 42 empty).1 = .ok none := by rfl\n", "Tactic `rfl` failed"),
    "unary_first_comparison": (UNARY_PRELUDE +
        "example : traceMatches (unaryStage firstComparison (constructors 0) opISZERO 2 42 empty) (.ok (some 1024)) [(1, 17, 0, [0, 0], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "unary_no_failure_fallback": (UNARY_PRELUDE +
        "example : (unaryStage firstComparison (constructors 1) opISZERO 2 42 empty).1 = .error .safetyFault := by rfl\n", "Tactic `rfl` failed"),
    "unary_retained_failure_state": (UNARY_PRELUDE +
        "example : (run tripleZero 21 [2] {} 1).2.read 0 = none := by rfl\n", "Tactic `rfl` failed"),
    "dispatch_constant_priority": (DISPATCH_PRELUDE +
        "example : (run [⟨some 7, none, []⟩, ⟨some 0, none, []⟩] 1 [0, 1]).1 = .ok (some 0) := by rfl\n", "Tactic `rfl` failed"),
    "dispatch_trace_value": (DISPATCH_PRELUDE +
        "example : traceMatches (run [⟨some 7, none, []⟩, ⟨some 3, none, []⟩] 1 [0, 1]) (.ok (some 1024)) [(2, 0, 11, [], 42)] = true := by rfl\n", "Tactic `rfl` failed"),
    "dispatch_failure_rollback": (DISPATCH_PRELUDE +
        "example : (run [⟨some 7, none, []⟩, ⟨some 3, none, []⟩] 1 [0, 1] {} 1).2.read 0 = none := by rfl\n", "Tactic `rfl` failed"),
    "dispatch_shifting_revision": (DISPATCH_PRELUDE +
        "example : hasBitwiseShifting .byzantium = true := by rfl\n", "Tactic `rfl` failed"),
    "dispatch_selfbalance_revision": (DISPATCH_PRELUDE +
        "example : hasSelfBalance .petersburg = true := by rfl\n", "Tactic `rfl` failed"),
    "dispatch_default_dialect": (DISPATCH_PRELUDE +
        "example : defaultOptions.forYul = true := by rfl\n", "Tactic `rfl` failed"),
    "alternating_mask_distribution": (ALTERNATING_MASK_PRELUDE +
        "example : outputValue 7 3 5 6 = 7 := by rfl\n", "Tactic `rfl` failed"),
    "alternating_mask_first_constant": (ALTERNATING_MASK_PRELUDE +
        "example : (run 0).2.table (callKey 22 [1, 10]) = some 42 := by rfl\n", "Tactic `rfl` failed"),
    "alternating_mask_other_alternative": (ALTERNATING_MASK_PRELUDE +
        "example : (run 0).2.table (callKey 22 [4, 12]) = some 42 := by rfl\n", "Tactic `rfl` failed"),
    "alternating_mask_materialization": (ALTERNATING_MASK_PRELUDE +
        "example : (run 0).2.table (callKey 254 [6, 6]) = some 42 := by rfl\n", "Tactic `rfl` failed"),
    "alternating_mask_rollback": (ALTERNATING_MASK_PRELUDE +
        "example : (run 3).2.read 0 = none := by rfl\n", "Tactic `rfl` failed"),
    "alternating_mask_failure_fallback": (ALTERNATING_MASK_PRELUDE +
        "example : (run 1).1 = .ok (some 14) := by rfl\n", "Tactic `rfl` failed"),
    "alternating_mask_debug": (ALTERNATING_MASK_PRELUDE +
        "example : (run 0).2.table (callKey 23 [11, 13]) = some 0 := by rfl\n", "Tactic `rfl` failed"),
    "address_mask_wide_word": (ADDRESS_MASK_PRELUDE +
        "example : BitVec.twoPow 256 160 &&& mask = BitVec.twoPow 256 160 := by rfl\n", "Tactic `rfl` failed"),
    "address_mask_environment": (ADDRESS_MASK_PRELUDE +
        "example : Kind.origin.value env = Kind.caller.value env := by rfl\n", "Tactic `rfl` failed"),
    "address_mask_arity": (ADDRESS_MASK_PRELUDE +
        "example : (meaning env Compiler.Extraction.Nested.Tests.fallback).operation 48 0 [1] = some 5 := by rfl\n", "Tactic `rfl` failed"),
    "address_mask_first_match": (ADDRESS_MASK_PRELUDE +
        "example : addressInstruction everyMatch 1 0 = .ok (some 51) := by rfl\n", "Tactic `rfl` failed"),
    "address_mask_prefix_fault": (ADDRESS_MASK_PRELUDE +
        "example : addressInstruction { everyMatch with operation := fun _ op => if op == 48 then (.error .safetyFault) else (.ok (some ⟨0, []⟩)) } 1 0 = .ok (some 51) := by rfl\n", "Tactic `rfl` failed"),
    "address_mask_missing_mask": (ADDRESS_MASK_PRELUDE +
        "example : addressInstruction reads 1 99 = .ok (some 48) := by rfl\n", "Tactic `rfl` failed"),
    "address_mask_self_caller": (ADDRESS_MASK_PRELUDE +
        "example : Kind.address.value env = Kind.caller.value env := by rfl\n", "Tactic `rfl` failed"),
    "binary_logarithm_zero": (BINARY_LOGARITHM_PRELUDE +
        "example : binaryLogarithm 64 0 = .ok (some 0) := by rfl\n", "Tactic `rfl` failed"),
    "binary_logarithm_nonpower": (BINARY_LOGARITHM_PRELUDE +
        "example : binaryLogarithm 64 3 = .ok (some 1) := by rfl\n", "Tactic `rfl` failed"),
    "binary_logarithm_direction": (BINARY_LOGARITHM_PRELUDE +
        "example : binaryLogarithm 64 (BitVec.twoPow 256 255) = .ok (some 0) := by rfl\n", "Tactic `rfl` failed"),
    "binary_logarithm_cast": (BINARY_LOGARITHM_PRELUDE +
        "example : binaryLogarithm 7 (BitVec.twoPow 256 128) = .ok (some 128) := by rfl\n", "Tactic `rfl` failed"),
    "binary_logarithm_zero_subtraction": (BINARY_LOGARITHM_PRELUDE +
        "example : binaryLogarithm 64 0 = .error .integerOverflow := by rfl\n", "Tactic `rfl` failed"),
    "binary_logarithm_rejection_order": (BINARY_LOGARITHM_PRELUDE +
        "example : binaryLogarithm 0 3 = .error .invalidCast := by rfl\n", "Tactic `rfl` failed"),
    "binary_logarithm_maximum": (BINARY_LOGARITHM_PRELUDE +
        "example : binaryLogarithm 64 (BitVec.allOnes 256) = .ok (some 255) := by rfl\n", "Tactic `rfl` failed"),
    "signextend_mask_cast": (SIGNEXTEND_MASK_PRELUDE +
        "example : nativeLowMask 31 = .ok (BitVec.allOnes 256) := by rfl\n", "Tactic `rfl` failed"),
    "signextend_mask_containment": (SIGNEXTEND_MASK_PRELUDE +
        "example : (stripRedundantSignExtendMask (reads 0 256) constructors 0 3 42 initial).1 = .ok (some 9) := by rfl\n", "Tactic `rfl` failed"),
    "signextend_mask_guard": (SIGNEXTEND_MASK_PRELUDE +
        "example : (stripRedundantSignExtendMask (reads 31 255) constructors 0 3 42 initial).1 = .error .safetyFault := by rfl\n", "Tactic `rfl` failed"),
    "signextend_mask_materialization": (SIGNEXTEND_MASK_PRELUDE +
        "example : (stripRedundantSignExtendMask (reads 0 255) constructors 0 3 42 initial).2.table (callKey 254 [3, 255]) = some 42 := by rfl\n", "Tactic `rfl` failed"),
    "signextend_mask_operand_order": (SIGNEXTEND_MASK_PRELUDE +
        "example : (stripRedundantSignExtendMask (reads 0 255) constructors 0 3 42 initial).2.table (callKey 22 [2, 8]) = some 42 := by rfl\n", "Tactic `rfl` failed"),
    "signextend_mask_lost_growth": (SIGNEXTEND_MASK_PRELUDE +
        "example : (stripRedundantSignExtendMask (reads 0 255) { constructors with operation := failing } 0 3 42 initial).2.read 8 = none := by rfl\n", "Tactic `rfl` failed"),
    "signextend_mask_lost_bits": (SIGNEXTEND_MASK_PRELUDE +
        "example : 256#256 &&& Compiler.Extraction.Folding.Op.signextend.value 0 128 0 = 256#256 &&& 128 := by rfl\n", "Tactic `rfl` failed"),
    "opposite_shifts_underflow": (OPPOSITE_SHIFTS_PRELUDE +
        "example : checkedDifference 0 1 = .ok (BitVec.allOnes 256) := by rfl\n", "Tactic `rfl` failed"),
    "opposite_shifts_cast": (OPPOSITE_SHIFTS_PRELUDE +
        "example : nativeMask 28 0 256 = .ok 0 := by rfl\n", "Tactic `rfl` failed"),
    "opposite_shifts_direction": (OPPOSITE_SHIFTS_PRELUDE +
        "example : (combineOppositeShifts constructors 28 1 3 0 42 initial).2.table (callKey 28 [8, 0]) = some 42 := by rfl\n", "Tactic `rfl` failed"),
    "opposite_shifts_equal_capture": (OPPOSITE_SHIFTS_PRELUDE +
        "example : (combineOppositeShifts constructors 28 3 3 0 42 initial).2.table (callKey 22 [8, 0]) = some 42 := by rfl\n", "Tactic `rfl` failed"),
    "opposite_shifts_mask": (OPPOSITE_SHIFTS_PRELUDE +
        "example : nativeMask 27 255 255 = .ok 1 := by rfl\n", "Tactic `rfl` failed"),
    "opposite_shifts_call_before_fault": (OPPOSITE_SHIFTS_PRELUDE +
        "example : (combineOppositeShifts constructors 27 0 256 0 42 initial).2.read 8 = some 0 := by rfl\n", "Tactic `rfl` failed"),
    "opposite_shifts_lost_growth": (OPPOSITE_SHIFTS_PRELUDE +
        "example : (combineOppositeShifts { constructors with operation := failing } 28 1 3 0 42 initial).2.read 8 = none := by rfl\n", "Tactic `rfl` failed"),
    "shift_masks_lost_cast_fault": (SHIFT_MASKS_PRELUDE +
        "example : shiftedCoverage 257 = .ok 0 := by rfl\n", "Tactic `rfl` failed"),
    "shift_masks_boundary": (SHIFT_MASKS_PRELUDE +
        "example : (removeCoveredShiftMask (reads 256 0) recording 4 5 42 (initial 256 0)).1 = .error .safetyFault := by rfl\n", "Tactic `rfl` failed"),
    "shift_masks_bad_coverage": (SHIFT_MASKS_PRELUDE +
        "example : (removeCoveredShiftMask (reads 255 0) recording 4 5 42 (initial 255 0)).1 = .ok (some 8) := by rfl\n", "Tactic `rfl` failed"),
    "shift_masks_operand_order": (SHIFT_MASKS_PRELUDE +
        "example : (powerOfTwoShiftProduct (reads 255 0) recording 2 3 42 (initial 255 0)).2.table (callKey 27 [2, 0]) = some 42 := by rfl\n", "Tactic `rfl` failed"),
    "shift_masks_one_required": (SHIFT_MASKS_PRELUDE +
        "open Compiler.Extraction.Nested Compiler.Extraction.Nested.Tests in\n"
        "example : (powerOfTwoShiftProduct (storageReads [literal 2, operation 27 [0, 0] 8]) recording 0 1 42 (initial 0 0)).1 = .ok (some 8) := by rfl\n", "Tactic `rfl` failed"),
    "shift_masks_lost_growth": (SHIFT_MASKS_PRELUDE +
        "example : (removeCoveredShiftMask (reads 256 0) failing 4 5 42 (initial 256 0)).2.read 8 = none := by rfl\n", "Tactic `rfl` failed"),
    "shift_masks_outside_guard": (SHIFT_MASKS_PRELUDE +
        "example : (removeCoveredShiftMask (reads 257 0) failing 4 5 42 (initial 257 0)).1 = .error .safetyFault := by rfl\n", "Tactic `rfl` failed"),
    "associative_bad_selection": (ASSOCIATIVE_PRELUDE +
        "example : isAssociative 3 = true := by rfl\n", "Tactic `rfl` failed"),
    "associative_overflow": (ASSOCIATIVE_PRELUDE +
        "example : combineConstants 1 (BitVec.allOnes 256) 1 = .ok (BitVec.allOnes 256) := by rfl\n", "Tactic `rfl` failed"),
    "associative_unreachable": (ASSOCIATIVE_PRELUDE +
        "example : combineConstants 3 7 2 = .ok 0 := by rfl\n", "Tactic `rfl` failed"),
    "associative_wrong_constant": (ASSOCIATIVE_PRELUDE +
        "example : (reassociate reads constructors 1 2 4 false 42 initial).2.table (callKey 0 [4]) = some 42 := by rfl\n", "Tactic `rfl` failed"),
    "associative_operand_order": (ASSOCIATIVE_PRELUDE +
        "example : (reassociate reads constructors 1 2 5 true 42 initial).2.table (callKey 1 [0, 5]) = some 42 := by rfl\n", "Tactic `rfl` failed"),
    "associative_materialize_id": (ASSOCIATIVE_PRELUDE +
        "example : (materializeConstant constant 99 5 42 initial).2.table (callKey 0 [99]) = some 42 := by rfl\n", "Tactic `rfl` failed"),
    "associative_lost_growth": (ASSOCIATIVE_PRELUDE +
        "example : let changed := { constructors with materialize := fun original value => failing 254 [original, value.setWidth 32] }\n"
        "    (reassociate reads changed 1 2 5 false 42 initial).2.read 8 = none := by rfl\n", "Tactic `rfl` failed"),
    "nested_build_capture_priority": (NESTED_BUILD_PRELUDE +
        "example : repeatedOperands indiscriminate 0 1 6 true = some [6, 1] := by rfl\n", "Tactic `rfl` failed"),
    "nested_build_nonidempotent": (NESTED_BUILD_PRELUDE +
        "example : Idempotent .add := by unfold Idempotent; decide\n", "is false"),
    "nested_build_swallowed_oom": (NESTED_BUILD_PRELUDE +
        "example : (dropRepeatedNested (storageReads cells) failing 22 3 0 false 42 initial).1 = .ok none := by rfl\n", "Tactic `rfl` failed"),
    "nested_build_lost_growth": (NESTED_BUILD_PRELUDE +
        "example : (doubleIsZero failSecond 0 42 initial).2.read 8 = none := by rfl\n", "Tactic `rfl` failed"),
    "nested_build_debug": (NESTED_BUILD_PRELUDE +
        "example : (dropRepeatedNested (storageReads cells) recording 22 3 0 false 42 initial).2.table (callKey 22 [0, 1]) = some 0 := by rfl\n", "Tactic `rfl` failed"),
    "nested_build_corrupt_read": (NESTED_BUILD_PRELUDE +
        "example : (dropRepeatedNested (storageReads corrupt) recording 22 0 0 true 42 initial).1 = .ok none := by rfl\n", "Tactic `rfl` failed"),
    "nested_build_missing_match": (NESTED_BUILD_PRELUDE +
        "example : (dropRepeatedNested (storageReads cells) failing 22 3 6 true 42 initial).1 = .error .outOfMemory := by rfl\n", "Tactic `rfl` failed"),
    "helper_wrong_cancel": (HELPER_PRELUDE +
        "example : cancelNestedBinary (storageReads cells) 24 0 2 = .ok (some 0) := by rfl\n", "Tactic `rfl` failed"),
    "helper_lost_capture": (HELPER_PRELUDE +
        "example : absorbedOccurrence indiscriminate 6 3 22 = .ok (some 1) := by rfl\n", "Tactic `rfl` failed"),
    "helper_lost_fault": (HELPER_PRELUDE +
        "example : isNegation (storageReads corrupt) 0 0 = .ok false := by rfl\n", "Tactic `rfl` failed"),
    "helper_constant_priority": (HELPER_PRELUDE +
        "example : splitConstant (storageReads cells) [0, 1] = .ok (some ⟨1, 0, 7⟩) := by rfl\n", "Tactic `rfl` failed"),
    "helper_unsound_equality": (HELPER_PRELUDE +
        "example : sameExpression indiscriminate 0 1 = true → readValue cells 0 = readValue cells 1 := by decide\n", "is false"),
    "memory_retired_vector": (MEMORY_PRELUDE +
        "example : readRepresentative moved 0 2 = .ok nested := by rfl\n", "Tactic `rfl` failed"),
    "memory_freed_operands": (MEMORY_PRELUDE +
        "example : readArgument (write heap 16 none) nested.argumentSlice 0 = .ok 0 := by rfl\n", "Tactic `rfl` failed"),
    "memory_live_collision": (MEMORY_PRELUDE +
        "example : moveVector heap 3 0 16 true = .ok moved := by rfl\n", "Tactic `rfl` failed"),
    "memory_allocator_pairing": (MEMORY_PRELUDE +
        "example : release heap 9 16 = .ok (write heap 16 none) := by rfl\n", "Tactic `rfl` failed"),
    "memory_forged_slice": (MEMORY_PRELUDE +
        "example : readArgument heap ⟨16, [9, 9]⟩ 0 = .ok 9 := by rfl\n", "Tactic `rfl` failed"),
    "memory_empty_free": (MEMORY_PRELUDE +
        "example : releaseSlice heap 3 ⟨0, []⟩ = .ok (write heap 0 none) := by rfl\n", "Tactic `rfl` failed"),
    "nested_invalid_optional": (NESTED_PRELUDE +
        "example : operationProgram.run [{ nested with item := ⟨1, none, 0⟩ }] 0 1 = .ok none := by rfl\n", "Tactic `rfl` failed"),
    "nested_lost_sequence": (NESTED_PRELUDE +
        "example : meaning.operation 1 0 [7, 2] = some 18 := by rfl\n", "Tactic `rfl` failed"),
    "nested_invalid_operands": (NESTED_PRELUDE +
        "example : Coherent meaning [left, right, { nested with arguments := [0, 9] }] := by\n"
        "  simp [Coherent, left, right, nested, Compiler.Extraction.Cache.Item.eval, meaning,\n"
        "    Compiler.Extraction.Cache.readArguments, readValue, Cell.value, Cell.isPush, Cell.dataValue]\n", "unsolved goals"),
    "interner_false_forced_equality": (
        "import Compiler.Extraction.InternerProgram\nimport Compiler.Extraction.InternerFixtures\n"
        "open Compiler.Extraction.Interner Compiler.Extraction.Interner.Fixtures\n"
        "example : let after := (forceCode.run primitives (fun _ _ => .ok ()) 0 request.item request.arguments empty).2\n"
        "    (after.table key).bind after.read = some 42 := by rfl\n", "Tactic `rfl` failed"),
    "wrong_replacement": (PRELUDE + "example : Rule.Sound ⟨.add, .right_zero, .zero⟩ := by\n"
        "  intro a b h\n  simp only [Guard.Holds] at h\n  subst b\n"
        "  simp [Binary.eval, Replacement.eval]\n", "unsolved goals"),
    "unreliable_constant": (PRELUDE +
        "example : Facts.Reliable { left := some 0 } 1 2 := by\n"
        "  constructor <;> simp_all\n", "unsolved goals"),
    "unreliable_equality": (PRELUDE +
        "example : Facts.Reliable { equal := true } 1 2 := by\n"
        "  constructor <;> simp_all\n", "unsolved goals"),
    "shift_operand_order": (PRELUDE +
        "example : Binary.shl.eval 1 0 = (1 : Word) := by decide\n", "is false"),
    "sorry": (PRELUDE + "theorem unfinished : False := by sorry\n", "sorry"),
    "native_axiom": ("import Contract.Check.Axioms\n"
        "theorem native : (1 : Nat) = 1 := by native_decide\n"
        "#audit_contract_proof native\n", "disallowed axiom"),
    "unapproved_axiom": ("import Contract.Check.Axioms\n"
        "axiom bad : False\ntheorem indirect : False := bad\n"
        "#audit_contract_proof indirect\n", "disallowed axiom"),
    "validator_invalid_graphs": ("import Compiler.Validation.Graph\nopen Compiler.Validation\n"
        "example : validate 4 [.unary .bitnot 0] [.unary .bitnot 0] 0 0 = true := by decide\n", "is false"),
    "validator_wrong_output": ("import Compiler.Validation.Graph\nopen Compiler.Validation\n"
        "example : validate 4 [.input \"x\", .literal 0, .binary .add 0 1] [.literal 0] 2 0 = true := by decide\n", "is false"),
    "validator_false_alias": ("import Compiler.Validation.Graph\nopen Compiler.Validation\n"
        "example : validate 4 [.input \"x\", .input \"y\", .binary .sub 0 1] [.literal 0] 2 0 = true := by decide\n", "is false"),
    "bytecode_wrong_opcode": ("import Compiler.Validation.WordBlock\nopen Compiler.Validation.WordBlock\n"
        "example : validate 8 [0x81, 0x81, 0x03] [\"x\", \"y\"] (.binary .add (.variable \"x\") (.variable \"y\")) = true := by decide\n", "is false"),
    "bytecode_lost_frame": ("import Compiler.Validation.WordBlock\nopen Compiler.Validation.WordBlock\n"
        "example : validate 8 [0x01] [\"x\", \"y\"] (.binary .add (.variable \"x\") (.variable \"y\")) = true := by decide\n", "is false"),
    "bytecode_truncated_push": ("import Compiler.Validation.WordBlock\nopen Compiler.Validation.WordBlock\n"
        "example : validate 8 [0x60] [] (.literal 0) = true := by decide\n", "is false"),
    "ir_return_null_fallthrough": ("import Compiler.Extraction.IR\n"
        "open Compiler.Extraction.IR Compiler.Algebraic\n"
        "example : each [false, true] (fun b => if b then .returned (some .left) else .returned none)"
        " = .returned (some .left) := by decide\n", "is false"),
    "ir_integer_width": ("import Compiler.Extraction.IR\nopen Compiler.Extraction.IR\n"
        "def bad : Expr [] .word := .opcode 0\n", "has type"),
    "storage_nonvacuous": ("import Compiler.Extraction.StorageProofs\nopen Compiler.Extraction.Storage\n"
        "example : (Program.capacityError.run ⟨true, true, fun _ => true⟩ {}).1 = some .success := by decide\n", "is false"),
    "cache_invalid_optional": ("import Compiler.Extraction.CacheProgram\nopen Compiler.Extraction.Cache\n"
        "example : normalizeCode.run id ⟨1, none, 0⟩ [] = some [] := by decide\n", "is false"),
}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def require_binding(exported, checked):
    if exported != checked:
        raise ValueError("production rule binding mismatch; review and prove the changed table")


def snapshot():
    # Include every Lean source (tests too), transitive Python proof tooling,
    # compiler source and the build graph. Generated caches are not inputs.
    paths = list((ROOT / "src").rglob("*.zig"))
    paths += [ROOT / "build.zig", ROOT / "build.zig.zon"]
    paths += list((ROOT / "test/lean").glob("*.py"))
    paths += [p for p in (ROOT / "lean").rglob("*.py") if ".lake" not in p.parts]
    result = {str(p.relative_to(ROOT)): source.file_digest(p) for p in sorted(set(paths))}
    result.update({"lean/" + key: value for key, value in source.source_inputs().items()})
    return result


def require_stable(before, after):
    if before != after:
        raise ValueError("compiler/proof inputs changed during verification")


def run(output, name, command, env, timeout, *, data=b"", cwd=ROOT):
    """Retain both streams and the actual exit status, including expected failures."""
    started = time.monotonic()
    record = {"command": list(map(str, command)), "cwd": str(cwd), "status": "failed"}
    (output / (name + ".stdin")).write_bytes(data)
    try:
        with (output / (name + ".stdin")).open("rb") as inp, \
                (output / (name + ".stdout")).open("wb") as out, \
                (output / (name + ".stderr")).open("wb") as err:
            child = subprocess.Popen(command, stdin=inp, stdout=out, stderr=err,
                                     cwd=cwd, env=env, start_new_session=True)
            try:
                record["exitCode"] = child.wait(timeout=timeout)
            except BaseException:
                try:
                    os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                finally:
                    child.wait()
                raise
        record["status"] = "completed"
        return record["exitCode"]
    finally:
        record["seconds"] = time.monotonic() - started
        (output / (name + ".process.json")).write_text(json.dumps(record, indent=2) + "\n")


def read(output, name, limit=16 * 1024 * 1024):
    path = output / name
    if path.stat().st_size > limit:
        raise ValueError("output limit exceeded: " + name)
    return path.read_bytes()


def require_success(output, name, command, env, timeout, *, stdout_limit=16 * 1024 * 1024, **kwargs):
    if run(output, name, command, env, timeout, **kwargs) != 0:
        raise ValueError(name + " failed; inspect its retained stdout/stderr")
    return read(output, name + ".stdout", limit=stdout_limit)


def extraction_negatives(output):
    """Retain mutated Zig inputs and return their generated kernel rejection checks."""
    negatives = {}
    data = extract_compiler.SOURCE.read_bytes()
    for name, (old, new, claim) in MUTATIONS.items():
        changed = mutate(data, old, new)
        (output / ("mutation-" + name + ".zig")).write_bytes(changed)
        definitions = extract_compiler.extract(changed).decode()
        # Separate namespace prevents accidental use of checked definitions.
        definitions = definitions.replace("namespace Compiler.Algebraic\n",
            "namespace Compiler.Algebraic.Mutation\n").replace("end Compiler.Algebraic\n",
            "end Compiler.Algebraic.Mutation\n")
        negatives["extraction_" + name] = (definitions +
            "open Compiler.Algebraic Compiler.Algebraic.Mutation Contract.Yul\n" +
            "example : " + claim + " := by decide\n", "is false")
    for name, (old, new, claim) in CONSTRUCTION_MUTATIONS.items():
        changed = mutate(data, old, new)
        (output / ("construction-mutation-" + name + ".zig")).write_bytes(changed)
        definitions = extract_compiler.extract_construction(changed).decode()
        definitions = definitions.replace("import Compiler.Extraction.Builder",
            "import Compiler.Extraction.ConstructionTests").replace("namespace Compiler.Algebraic\n",
            "namespace Compiler.Algebraic.Mutation\n").replace("end Compiler.Algebraic\n",
            "open Compiler.Algebraic.ConstructionTests\nexample : " + claim +
            " := by rfl\nend Compiler.Algebraic.Mutation\n")
        negatives["construction_" + name] = (definitions, "Tactic `rfl` failed")
    for name, mutation, claim in [
        ("matcher", MUTATIONS["guard_constant"],
         "mutantMatcher.eval (fun _ _ => false) (matcherEnv .left_zero { left := some 0 })"
         " = zigMatches .left_zero { left := some 0 }"),
        ("selection", MUTATIONS["wrong_stage"],
         "mutantSelection.eval evalMatcher (selectionEnv productionRules (productionOpcode .add)"
         " .constants { right := some 0 }) = .returned (zigSelect (productionOpcode .add)"
         " .constants { right := some 0 })"),
        ("construction", CONSTRUCTION_MUTATIONS["constant"],
         "mutantConstruction.eval callbacks 9 evalMatcher (constructionEnv .zero 2 3)"
         " = zigApply .zero callbacks 2 3 9"),
    ]:
        old, new, _ = mutation
        changed = mutate(data, old, new)
        (output / ("ir-" + name + ".zig")).write_bytes(changed)
        definitions = compiler_ir.extract(changed).decode().replace(
            "import Compiler.Extraction.IR", "import Compiler.Extraction.Correspondence\n"
            "import Compiler.Extraction.ConstructionTests")
        for original in ("matcher", "selection", "construction"):
            definitions = definitions.replace("def " + original + " :", "def mutant" + original.title() + " :")
        negatives["ir_correspondence_" + name] = (definitions +
            "\nopen Compiler.Extraction.IR Compiler.Algebraic Compiler.Algebraic.ConstructionTests\n"
            "example : " + claim + " := by rfl\n", "Tactic `rfl` failed")
    return negatives


def storage_negatives(output):
    negatives = {}
    original = extract_storage.SOURCE.read_bytes()
    for name, (old, new, observation) in {**STORAGE_MUTATIONS, **READ_MUTATIONS}.items():
        changed = mutate(original, old, new)
        (output / ("storage-" + name + ".zig")).write_bytes(changed)
        definitions = extract_storage.extract(changed).decode().replace(
            "import Compiler.Extraction.StorageRead", "import Compiler.Extraction.StorageProofs")
        for before, after in (("insertProgram", "mutantInsert"), ("representativeProgram", "mutantRepresentative"),
                              ("constantProgram", "mutantConstant"), ("operationProgram", "mutantOperation")):
            definitions = definitions.replace(before, after)
        if name in STORAGE_MUTATIONS:
            deterministic, room, *policy = observation.split()
            claim = f"SafeResult {deterministic} (mutantInsert.run ⟨{deterministic}, {room}, allocationPolicy {' '.join(policy)}⟩ {{}})"
            proof, diagnostic = "decide", "is false"
        else:
            claim, proof, diagnostic = observation, "rfl", "Tactic `rfl` failed"
        negatives["storage_" + name] = (definitions +
            "\nopen Compiler.Extraction.Storage\nset_option maxRecDepth 4096 in\n"
            "example : " + claim + " := by " + proof + "\n", diagnostic)
    return negatives


def interner_mutation_negatives():
    negatives = {}
    header = "import Compiler.Extraction.InternerControl\n"
    for name in INTERNER_MUTATIONS:
        definitions, claim = interner_mutated(name)
        definitions = definitions.decode()
        if definitions.count(header) != 1:
            raise ValueError("interner mutation interpreter import is missing or ambiguous")
        # Fixtures import the interpreter, without baseline generated definitions.
        definitions = definitions.replace(header,
            header + "import Compiler.Extraction.InternerFixtures\n", 1)
        negatives["interner_" + name] = (definitions +
            "\nopen Compiler.Extraction.Interner Compiler.Extraction.Interner.Fixtures\nexample : " +
            claim + " := by rfl\n", "Tactic `rfl` failed")
    return negatives


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True, help="new evidence directory")
    parser.add_argument("--lean-bin", type=Path)
    parser.add_argument("--jobs", type=int, default=4, choices=range(1, 5))
    parser.add_argument("--timeout", type=int, default=600, help="seconds per child process/phase")
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("timeout must be positive")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.compiler-verification.v1", "status": "failed",
              "scope": "pureEvmWordRewrites", "wholeCompilerVerified": False,
              "emittedEvmProof": False, "jobs": args.jobs, "buildMode": "ReleaseFast",
              "negativeControls": [], "phases": {}}
    try:
        before = snapshot()
        report["sourceSha256"] = before
        env, sysroot, tools = source.toolchain(args.lean_bin, args.jobs)
        zig = shutil.which("zig")
        if not zig:
            raise ValueError("Zig 0.17.0 is required")
        tools["zig"] = {"path": str(Path(zig).resolve()), "sha256": source.file_digest(Path(zig))}
        tools["python"] = {"path": str(Path(sys.executable).resolve()),
                           "sha256": source.file_digest(Path(sys.executable))}
        tools["leanchecker"] = {"path": str(sysroot / "bin/leanchecker"),
                                "sha256": source.file_digest(sysroot / "bin/leanchecker")}
        report["tools"] = tools
        require_success(output, "native", [zig, "build", "build-compiler-rules-export",
            "test-compiler-rewrites", "build-compiler-dispatch-trace", "test-compiler-dispatch-trace",
            "-j" + str(args.jobs), "-Doptimize=ReleaseFast", "--summary", "all"],
            env, args.timeout)
        report["phases"]["native"] = "passed"
        exporter = ROOT / "zig-out/bin/compiler-rules-export"
        exporter_digest = source.file_digest(exporter)
        exported = require_success(output, "export", [str(exporter)], env, args.timeout)
        checked = RULES.read_bytes()
        require_binding(exported, checked)
        report["binding"] = {"exporterSha256": exporter_digest, "tableSha256": digest(exported),
                             "comparison": "exactBytes", "status": "passed"}
        require_success(output, "extraction-tests", [sys.executable,
            "test/lean/test_compiler_extraction.py"], env, args.timeout)
        require_success(output, "storage-extraction-tests", [sys.executable,
            "test/lean/test_compiler_storage.py"], env, args.timeout)
        require_success(output, "cache-extraction-tests", [sys.executable,
            "test/lean/test_compiler_cache.py"], env, args.timeout)
        require_success(output, "assembly-clone-extraction-tests", [sys.executable,
            "test/lean/test_compiler_assembly_clone.py"], env, args.timeout)
        require_success(output, "owned-key-extraction-tests", [sys.executable,
            "test/lean/test_compiler_owned_keys.py"], env, args.timeout)
        require_success(output, "interner-extraction-tests", [sys.executable,
            "test/lean/test_compiler_interner.py"], env, args.timeout)
        require_success(output, "constructor-extraction-tests", [sys.executable,
            "test/lean/test_compiler_constructor.py"], env, args.timeout)
        require_success(output, "folding-extraction-tests", [sys.executable,
            "test/lean/test_compiler_folding.py"], env, args.timeout)
        require_success(output, "nested-extraction-tests", [sys.executable,
            "test/lean/test_compiler_nested.py"], env, args.timeout)
        require_success(output, "nested-construction-extraction-tests", [sys.executable,
            "test/lean/test_compiler_nested_construction.py"], env, args.timeout)
        require_success(output, "associative-extraction-tests", [sys.executable,
            "test/lean/test_compiler_associative.py"], env, args.timeout)
        require_success(output, "shift-masks-extraction-tests", [sys.executable,
            "test/lean/test_compiler_shift_masks.py"], env, args.timeout)
        require_success(output, "opposite-shifts-extraction-tests", [sys.executable,
            "test/lean/test_compiler_opposite_shifts.py"], env, args.timeout)
        require_success(output, "signextend-mask-extraction-tests", [sys.executable,
            "test/lean/test_compiler_signextend_mask.py"], env, args.timeout)
        require_success(output, "binary-logarithm-extraction-tests", [sys.executable,
            "test/lean/test_compiler_binary_logarithm.py"], env, args.timeout)
        require_success(output, "address-mask-extraction-tests", [sys.executable,
            "test/lean/test_compiler_address_mask.py"], env, args.timeout)
        require_success(output, "alternating-mask-extraction-tests", [sys.executable,
            "test/lean/test_compiler_alternating_mask.py"], env, args.timeout)
        require_success(output, "dispatch-extraction-tests", [sys.executable,
            "test/lean/test_compiler_dispatch.py"], env, args.timeout)
        require_success(output, "dispatch-batch-tests", [sys.executable,
            "test/lean/test_compiler_dispatch_batches.py"], env, args.timeout)
        require_success(output, "artifact-read-tests", [sys.executable,
            "test/lean/test_compiler_artifact_reads.py"], env, args.timeout)
        require_success(output, "dispatcher-comparison", [sys.executable,
            "test/lean/check_compiler_dispatch.py", "--output", str(output / "dispatcher"),
            "--jobs", str(args.jobs), "--timeout", str(args.timeout)] +
            (["--lean-bin", str(args.lean_bin)] if args.lean_bin else []), env, args.timeout)
        report["phases"]["dispatcherComparison"] = "passed"
        extracted = extract_compiler.extract(extract_compiler.SOURCE.read_bytes())
        if extracted != extract_compiler.OUTPUT.read_bytes():
            raise ValueError("extracted implementation binding mismatch")
        construction = extract_compiler.extract_construction(extract_compiler.SOURCE.read_bytes())
        if construction != extract_compiler.CONSTRUCTION.read_bytes():
            raise ValueError("extracted construction binding mismatch")
        ir = compiler_ir.extract(extract_compiler.SOURCE.read_bytes())
        if ir != compiler_ir.OUTPUT.read_bytes():
            raise ValueError("extracted typed IR binding mismatch")
        storage = extract_storage.extract(extract_storage.SOURCE.read_bytes())
        if storage != extract_storage.OUTPUT.read_bytes():
            raise ValueError("extracted storage binding mismatch")
        cache = extract_cache.extract(extract_cache.SOURCE.read_bytes(), extract_cache.SEMANTICS.read_bytes(),
            extract_cache.ITEMS.read_bytes(), extract_cache.OPCODES.read_bytes())
        if cache != extract_cache.OUTPUT.read_bytes():
            raise ValueError("extracted cache binding mismatch")
        assembly_clone = extract_assembly_clone.extract(extract_assembly_clone.SOURCE.read_bytes())
        if assembly_clone != extract_assembly_clone.OUTPUT.read_bytes():
            raise ValueError("extracted assembly clone binding mismatch")
        owned_keys = extract_owned_keys.extract(extract_owned_keys.SOURCE.read_bytes())
        if owned_keys != extract_owned_keys.OUTPUT.read_bytes():
            raise ValueError("owned-key extraction is stale")
        interner = extract_interner.extract(extract_interner.SOURCE.read_bytes())
        if interner != extract_interner.OUTPUT.read_bytes():
            raise ValueError("extracted interner binding mismatch")
        constructor = extract_constructor.extract(extract_constructor.SOURCE.read_bytes(),
            extract_constructor.ITEMS.read_bytes(), extract_constructor.OPCODES.read_bytes())
        if constructor != extract_constructor.OUTPUT.read_bytes():
            raise ValueError("extracted constructor binding mismatch")
        folding = extract_folding.extract(extract_folding.SOURCE.read_bytes(), extract_folding.OPCODES.read_bytes())
        if folding != extract_folding.OUTPUT.read_bytes():
            raise ValueError("extracted constant folder binding mismatch")
        nested = extract_nested.extract(extract_nested.SOURCE.read_bytes(), extract_nested.OPCODES.read_bytes(),
            extract_nested.STORAGE.read_bytes())
        if nested != extract_nested.OUTPUT.read_bytes():
            raise ValueError("extracted nested helper binding mismatch")
        nested_construction = extract_nested_construction.extract(extract_nested.SOURCE.read_bytes(),
            extract_nested.OPCODES.read_bytes(), extract_nested.STORAGE.read_bytes())
        if nested_construction != extract_nested_construction.OUTPUT.read_bytes():
            raise ValueError("extracted nested construction binding mismatch")
        associative = extract_associative.extract(extract_nested.SOURCE.read_bytes(),
            extract_nested.OPCODES.read_bytes(), extract_nested.STORAGE.read_bytes())
        if associative != extract_associative.OUTPUT.read_bytes():
            raise ValueError("extracted associative helper binding mismatch")
        shift_masks = extract_shift_masks.extract(extract_nested.SOURCE.read_bytes(),
            extract_nested.OPCODES.read_bytes(), extract_nested.STORAGE.read_bytes())
        if shift_masks != extract_shift_masks.OUTPUT.read_bytes():
            raise ValueError("extracted shift-mask helper binding mismatch")
        opposite_shifts = extract_opposite_shifts.extract(extract_nested.SOURCE.read_bytes(),
            extract_nested.OPCODES.read_bytes(), extract_nested.STORAGE.read_bytes())
        if opposite_shifts != extract_opposite_shifts.OUTPUT.read_bytes():
            raise ValueError("extracted opposite-shift helper binding mismatch")
        signextend_mask = extract_signextend_mask.extract(extract_nested.SOURCE.read_bytes(),
            extract_nested.OPCODES.read_bytes(), extract_nested.STORAGE.read_bytes())
        if signextend_mask != extract_signextend_mask.OUTPUT.read_bytes():
            raise ValueError("extracted sign-extension mask helper binding mismatch")
        binary_logarithm = extract_binary_logarithm.extract(extract_binary_logarithm.SOURCE.read_bytes())
        if binary_logarithm != extract_binary_logarithm.OUTPUT.read_bytes():
            raise ValueError("extracted binary-logarithm helper binding mismatch")
        address_mask = extract_address_mask.extract(extract_nested.SOURCE.read_bytes(),
            extract_nested.OPCODES.read_bytes(), extract_nested.STORAGE.read_bytes())
        if address_mask != extract_address_mask.OUTPUT.read_bytes():
            raise ValueError("extracted address-mask helper binding mismatch")
        alternating_mask = extract_alternating_mask.extract(extract_nested.SOURCE.read_bytes(),
            extract_nested.OPCODES.read_bytes(), extract_nested.STORAGE.read_bytes())
        if alternating_mask != extract_alternating_mask.OUTPUT.read_bytes():
            raise ValueError("extracted alternating-mask helper binding mismatch")
        dispatch = extract_dispatch.extract(extract_nested.SOURCE.read_bytes(),
            extract_nested.OPCODES.read_bytes(), extract_nested.STORAGE.read_bytes(), extract_dispatch.VERSIONS.read_bytes())
        if dispatch != extract_dispatch.OUTPUT.read_bytes():
            raise ValueError("extracted dispatcher binding mismatch")
        report["extraction"] = {"status": "passed", "comparison": "exactBytes",
            "implementationSha256": digest(extracted),
            "constructionSha256": digest(construction),
            "typedIrSha256": digest(ir),
            "irEncoderSha256": source.file_digest(Path(compiler_ir.__file__)),
            "storageIrSha256": digest(storage),
            "storageSourceSha256": source.file_digest(extract_storage.SOURCE),
            "storageEncoderSha256": source.file_digest(Path(extract_storage.__file__)),
            "cacheIrSha256": digest(cache),
            "cacheEncoderSha256": source.file_digest(Path(extract_cache.__file__)),
            "assemblyCloneIrSha256": digest(assembly_clone),
            "assemblyCloneSourceSha256": source.file_digest(extract_assembly_clone.SOURCE),
            "assemblyCloneEncoderSha256": source.file_digest(Path(extract_assembly_clone.__file__)),
            "assemblyClonePreservation": {
                "theorem": "Compiler.Extraction.AssemblyClone.clone_safe",
                "cleanupTheorem": "Compiler.Extraction.AssemblyClone.clone_cleanup",
                "scope": "sourceBoundItemCloneAndDeinit",
                "remainingPremises": ["dupeContentAndOwnership", "dupeFailureAtomicity",
                    "allocatorFrame", "matchingFree", "metadataBorrowLifetimes", "physicalMemoryRefinement"],
                "nativeMemoryRefinementComplete": False},
            "internerIrSha256": digest(interner),
            "internerEncoderSha256": source.file_digest(Path(extract_interner.__file__)),
            "foldingIrSha256": digest(folding),
            "foldingEncoderSha256": source.file_digest(Path(extract_folding.__file__)),
            "nestedHelperIrSha256": digest(nested),
            "nestedHelperEncoderSha256": source.file_digest(Path(extract_nested.__file__)),
            "nestedHelperScope": "fivePureMatchingHelpers",
            "nestedConstructionIrSha256": digest(nested_construction),
            "nestedConstructionEncoderSha256": source.file_digest(Path(extract_nested_construction.__file__)),
            "nestedConstructionScope": "doubleIsZeroAndDropRepeatedNested",
            "associativeIrSha256": digest(associative),
            "associativeEncoderSha256": source.file_digest(Path(extract_associative.__file__)),
            "associativeScope": "fiveOperationsAndNativeMaterialization",
            "shiftMasksIrSha256": digest(shift_masks),
            "shiftMasksEncoderSha256": source.file_digest(Path(extract_shift_masks.__file__)),
            "shiftMasksScope": "powerOfTwoShiftProductAndRemoveCoveredShiftMask",
            "oppositeShiftsIrSha256": digest(opposite_shifts),
            "oppositeShiftsEncoderSha256": source.file_digest(Path(extract_opposite_shifts.__file__)),
            "oppositeShiftsScope": "completeCombineOppositeShiftsWithNativeBounds",
            "signextendMaskIrSha256": digest(signextend_mask),
            "signextendMaskEncoderSha256": source.file_digest(Path(extract_signextend_mask.__file__)),
            "signextendMaskScope": "completeStripRedundantSignExtendMask",
            "binaryLogarithmIrSha256": digest(binary_logarithm),
            "binaryLogarithmEncoderSha256": source.file_digest(Path(extract_binary_logarithm.__file__)),
            "binaryLogarithmScope": "completeBinaryLogarithmWithExplicitUsizeWidth",
            "addressMaskIrSha256": digest(address_mask),
            "addressMaskEncoderSha256": source.file_digest(Path(extract_address_mask.__file__)),
            "addressMaskScope": "completeAddressInstructionWithFixedTypedEnvironment",
            "alternatingMaskIrSha256": digest(alternating_mask),
            "alternatingMaskEncoderSha256": source.file_digest(Path(extract_alternating_mask.__file__)),
            "alternatingMaskScope": "completeOrderedDistributionWithFiveFallibleConstructors",
            "dispatchIrSha256": digest(dispatch),
            "dispatchEncoderSha256": source.file_digest(Path(extract_dispatch.__file__)),
            "dispatchVersionSha256": source.file_digest(extract_dispatch.VERSIONS),
            "dispatchScope": "completeOrderedExecutionModelWithConstantUnaryComparisonAddAndOrXorSignedMulDivModExpSubByteLogicalShiftSignExtendAndTernaryPreservation",
            "dispatchComparisonOpcodes": ["EQ", "LT", "SLT", "GT", "SGT"],
            "dispatchAssociativeOpcodes": ["ADD", "AND", "OR", "XOR"],
            "dispatchSignedOpcodes": ["SDIV", "SMOD"],
            "dispatchUnaryOpcodes": ["NOT", "ISZERO"],
            "dispatchMultiplicationOpcodes": ["MUL"],
            "dispatchDivisionOpcodes": ["DIV"],
            "dispatchModuloOpcodes": ["MOD"],
            "dispatchExponentOpcodes": ["EXP"],
            "dispatchSubtractionOpcodes": ["SUB"],
            "dispatchByteOpcodes": ["BYTE"],
            "dispatchShiftOpcodes": ["SHL", "SHR"],
            "dispatchSignExtendOpcodes": ["SIGNEXTEND"],
            "dispatchArithmeticShiftMeaning": "EIP145SignedFloorWithUnsignedAmountAndSignFill",
            "dispatchTernaryOpcodes": ["ADDMOD", "MULMOD"],
            "dispatchOtherArities": "exactConstantStageWhenArityIsNeitherOneNorTwo",
            "dispatchWordPreservation": {
                "theorem": "Compiler.Extraction.Dispatch.word_simplify_safe",
                "vocabulary": "Compiler.Extraction.Folding.Op", "opcodeCount": 24,
                "inputScope": "allDefinedWordApplications",
                "model": "Compiler.Extraction.Dispatch.wordDispatchMeaning",
                "recursiveConstructorContractsDischarged": False},
            "dispatchDefaultPreservation": {
                "theorem": "Compiler.Extraction.Dispatch.default_simplify_safe",
                "entryPoint": "RuleList.simplify", "opcodeExclusions": [],
                "inputScope": "allDefinedApplications", "revisionTail": "disabledBySourceDefault",
                "recursiveConstructorContractsDischarged": False},
            "recursivePreservation": {
                "theorem": "Compiler.Extraction.Recursive.unfold_safe",
                "executionTheorem": "Compiler.Extraction.Recursive.executes_safe",
                "scope": "allFiniteUnfoldingsOfDefaultInternerDispatcherComposition",
                "recursivePreservationPremise": False,
                "cutoffOutcome": "unsupportedIncompleteObservation",
                "nativeExecutionRefinementComplete": False,
                "remainingPremises": ["readCoherence", "normalization", "insertion", "publication", "pushAtoms"]},
            "normalizationPreservation": {
                "theorem": "Compiler.Extraction.Cache.normalize_word",
                "recursiveTheorem": "Compiler.Extraction.Recursive.unfold_normalized_safe",
                "scope": "allItemKindsAritiesEpochsAndPartialReads",
                "semanticPreservationPremise": False,
                "remainingPremises": ["sourceSuccessRefinement", "copySortPermutation", "allocationAndBorrowFraming"],
                "nativeSortVerified": False},
            "normalizationOwnership": {
                "theorem": "Compiler.Extraction.Cache.NormalizationOwnership.run_safe",
                "scope": "sourceBoundSingleTransferLifecycleAllLengthsAndAllocationOutcomes",
                "methods": ["NormalizedArguments.init", "NormalizedArguments.takeOwned", "NormalizedArguments.deinit"],
                "remainingPremises": ["allocatorFreshnessAndPairing", "copySortFraming", "physicalSliceValidity", "machineLayout"],
                "nativeMemoryRefinementComplete": False},
            "representativeReadPreservation": {
                "theorem": "Compiler.Extraction.Interner.representative_reads_sound",
                "recursiveTheorem": "Compiler.Extraction.Recursive.unfold_representatives_safe",
                "scope": "heapInvariantWithSourceBoundRepresentativeObservations",
                "oracleCoherencePremise": False,
                "missingRepresentationOutcome": "modelSafetyFault",
                "remainingPremises": ["primitiveContracts", "nativeRepresentativeStateRefinement",
                    "nativeAllocationEventRefinement", "nativeReadTimingRefinement", "physicalMemoryRefinement"],
                "nativeExecutionRefinementComplete": False},
            "observedInsertionPreservation": {
                "theorem": "Compiler.Extraction.Interner.observed_insert_transaction_safe",
                "actionTheorem": "Compiler.Extraction.Interner.observed_insert_safe",
                "scope": "sourceBoundInsertionTransactionWithRepresentativeObservations",
                "oldRepresentativeReadsPreserved": True,
                "remainingPremises": ["clonedValueDenotation", "exactCloneKeyBinding", "ownedKeyPublicationRefinement", "physicalCloneAndAllocationContracts"],
                "nativeMemoryRefinementComplete": False},
            "recursiveRepresentativeFraming": {
                "theorem": "Compiler.Extraction.Recursive.unfold_frames",
                "executionTheorem": "Compiler.Extraction.Recursive.executes_frames",
                "scope": "allFiniteUnfoldingsOfComposedModelAllOutcomes",
                "dispatcherScope": "allOpcodesAritiesAndOptions",
                "remainingPremises": ["insertionAndPublicationFrames", "nativeAllocationEventRefinement",
                    "nativeReadTimingRefinement", "physicalMemoryRefinement"],
                "nativeExecutionRefinementComplete": False},
            "statefulLocalCallbacks": {
                "theorem": "Compiler.Extraction.Interner.local_safe",
                "compositionTheorem": "Compiler.Extraction.Interner.lift_local_bind",
                "scope": "normalizationAndOwnershipTransferCursor",
                "graphFrameByInterface": True,
                "remainingPremises": ["nativeAllocationEventBinding", "normalizationLocalOwnershipRefinement",
                    "physicalMemoryRefinement"],
                "nativeAllocationRefinementComplete": False},
            "statefulInsertionEffects": {
                "theorem": "Compiler.Extraction.Storage.insert_effect_safe",
                "projectionTheorem": "Compiler.Extraction.Storage.insert_effect_projection",
                "scope": "extractedInsertionPrimitiveEffects",
                "arbitraryPrivateEffectState": True,
                "remainingPremises": ["nativePrimitiveEffectRefinement",
                    "physicalMemoryRefinement"],
                "nativeAllocatorRefinementComplete": False},
            "sharedInsertionPublicationCursor": {
                "insertionTheorem": "Compiler.Extraction.Interner.observed_insert_with_safe",
                "publicationTheorem": "Compiler.Extraction.Interner.publish_with_safe",
                "frameTheorem": "Compiler.Extraction.Interner.Frames.insertWith",
                "executesInsertionProgramOnce": True,
                "remainingPremises": ["cloneKeyAndDenotationBinding", "ownedKeyPublicationRefinement", "nativePrimitiveEffectRefinement",
                    "normalizationLocalOwnershipRefinement", "nativeReadTimingRefinement", "physicalMemoryRefinement"],
                "nativeExecutionRefinementComplete": False},
            "normalizationStatefulOwnership": {
                "theorem": "Compiler.Extraction.Cache.NormalizationOwnership.run_with_safe",
                "projectionTheorem": "Compiler.Extraction.Cache.NormalizationOwnership.run_with_projection",
                "scope": "normalizedArgumentsAllocationTransferAndCleanup",
                "arbitraryPrivateAllocatorState": True,
                "remainingPremises": ["nativeOwnershipIntegration", "nativeAllocatorAndDeallocatorRefinement",
                    "copySortFraming", "physicalSliceValidity", "machineLayout"],
                "nativeMemoryRefinementComplete": False},
            "ownedKeyPublication": {
                "theorem": "Compiler.Extraction.OwnedKeys.run_preserves",
                "semanticTheorem": "Compiler.Extraction.OwnedKeys.run_semantics",
                "sourceProfileSha256": digest(owned_keys),
                "translatorSha256": source.file_digest(Path(extract_owned_keys.__file__)),
                "scope": "publishOwnedTypedAllocationLifetimesAndCacheProjection",
                "arbitraryPrivateAllocatorState": True,
                "remainingPremises": ["framedGetOrPutRefinement", "nativeAllocatorAndDeallocatorRefinement",
                    "incomingExclusiveOwnership", "initialTableOwnershipAndBorrowSeparation",
                    "internerPhysicalOwnershipStateBinding", "physicalSliceValidity", "machineLayout"],
                "nativeMemoryRefinementComplete": False},
            "scopedInternerOwnership": {
                "findTheorem": "Compiler.Extraction.Interner.Scoped.find_closed",
                "forceTheorem": "Compiler.Extraction.Interner.Scoped.force_closed",
                "recursiveTheorem": "Compiler.Extraction.ScopedRecursive.all_scopes_closed",
                "normalizationProjection": "Compiler.Extraction.Interner.Scoped.initialize_projection",
                "valueControlProjection": "Compiler.Extraction.Interner.control_find_projection",
                "scope": "sourceBoundInternerLocalOwnershipAllFiniteRecursiveDepths",
                "cleanupRetainsReachedGraphAndAllocatorEffects": True,
                "remainingPremises": ["graphPrimitivePreservation", "sortPermutation",
                    "nativeCompletedExecutionRefinement", "calleeOwnershipAndPrimitiveEffectRefinement",
                    "allocatorPairingAndFreshness", "copySortFraming", "physicalSliceValidity", "machineLayout"],
                "nativeMemoryRefinementComplete": False},
            "scopedInternerStructuralFrame": {
                "theorem": "Compiler.Extraction.ScopedRecursive.unfold_frames",
                "combinedOwnershipTheorem": "Compiler.Extraction.ScopedRecursive.detailed_preserves",
                "forceTheorem": "Compiler.Extraction.Interner.Scoped.force_frames",
                "scope": "representativePrefixAllFiniteScopedRecursiveDepths",
                "includesErrorOutcomesAndCleanupEffects": True,
                "requiresSemanticValuePremise": False,
                "remainingPremises": ["insertionAndPublicationFrames", "nativeCompletedExecutionRefinement",
                    "physicalAllocationAndBorrowRefinement"],
                "nativeMemoryRefinementComplete": False},
            "scopedRecursiveSemantics": {
                "theorem": "Compiler.Extraction.ScopedRecursive.unfold_representatives_safe",
                "combinedTheorem": "Compiler.Extraction.ScopedRecursive.detailed_verified",
                "completedExecutionTheorem": "Compiler.Extraction.ScopedRecursive.executes_safe",
                "forceTheorem": "Compiler.Extraction.Interner.Scoped.force_safe",
                "scope": "wordDispatcherAllFiniteScopedRecursiveDepths",
                "includesErrorOutcomesAndCleanupEffects": True,
                "recursiveCorrectnessPremise": False,
                "normalizationCallbackPremise": False,
                "representativeOraclePremise": False,
                "remainingPremises": ["wordDenotationAndInitialInvariant", "pushAtomSemantics", "sortPermutation",
                    "insertionAndPublicationSemanticPreservation", "insertionAndPublicationFrames", "nativeCompletedExecutionRefinement",
                    "calleeOwnershipAndPrimitiveEffectRefinement", "physicalAllocationAndBorrowRefinement"],
                "nativeExecutionRefinementComplete": False},
            "dispatchPreservationComplete": False,
            "foldingScope": "completeConstantFolderIntegerSemantics",
            "constructorIrSha256": digest(constructor),
            "constructorEncoderSha256": source.file_digest(Path(extract_constructor.__file__)),
            "irCorrespondenceChecked": False,
            "sourceSha256": source.file_digest(extract_compiler.SOURCE),
            "translatorSha256": source.file_digest(Path(extract_compiler.__file__)),
            "trustedTranslator": True, "functions": ["matches", "select", "apply"]}
        # This gate never refreshes a stale table. Exercise its rejection path.
        for name, mutation in [("changed_table", checked.replace(b".left", b".zero", 1)),
                               ("omitted_table", b""), ("added_table", checked + b"-- extra\n")]:
            try:
                require_binding(exported, mutation)
            except ValueError:
                report["negativeControls"].append({"case": name, "rejected": True})
            else:
                raise ValueError(name + " was unexpectedly accepted")
        try:
            require_stable(before, {**before, "changed-input": "changed"})
        except ValueError:
            report["negativeControls"].append({"case": "changed_inputs", "rejected": True})
        else:
            raise ValueError("changed inputs were unexpectedly accepted")

        # Reuse the existing strict proof driver and replay the proof module plus
        # all imports in a fresh kernel. No native-evaluation axiom is allowed.
        proof_report, artifacts = prove.check_module("Compiler.Algebraic.Audit", CLAIMS,
            lean_bin=args.lean_bin, jobs=args.jobs, timeout=args.timeout, fresh=True)
        proof_output = output / "proof"
        proof_output.mkdir()
        for name, data in artifacts.items():
            (proof_output / name).write_bytes(data)
        if (proof_report["status"] != "passed" or not proof_report["freshKernelReplay"]
                or proof_report["auditedDeclarations"] != CLAIMS):
            raise ValueError("proof audit/replay failed; inspect proof/report.json")
        report["phases"]["proof"] = "passed"
        report["extraction"]["irCorrespondenceChecked"] = True
        # Re-elaborate the audit command even on a cached build. It retains
        # complete statements and checks unsafe/partial dependencies as well.
        audit_bytes = require_success(output, "audit", [tools["lake"]["path"], "env", "lean",
            "-DwarningAsError=true", "Compiler/Algebraic/Audit.lean"], env, args.timeout,
            cwd=ROOT / "lean", stdout_limit=64 * 1024 * 1024)
        if read(output, "audit.stderr").strip():
            raise ValueError("unexpected audit stderr")
        audit = json.loads(audit_bytes)
        if (audit.get("schema") != "oksolc.compiler-algebraic-audit.v1"
                or [claim["theorem"] for claim in audit["claims"]] != CLAIMS
                or audit["ruleCount"] != checked.count("⟨.".encode())):
            raise ValueError("incomplete compiler theorem audit")
        report["ruleCount"] = audit["ruleCount"]
        report["claims"] = [{"theorem": c["theorem"], "axioms": c["axioms"]} for c in audit["claims"]]
        report["phases"]["audit"] = "passed"
        worker_env = {**env, "LEAN_NUM_THREADS": "1"}

        def reject(item):
            name, (text, expected) = item
            code = run(output, "negative-" + name, [tools["lake"]["path"], "env", "lean",
                "-DwarningAsError=true", "--stdin"], worker_env, args.timeout,
                data=text.encode(), cwd=ROOT / "lean")
            diagnostic = (read(output, "negative-" + name + ".stdout") +
                          read(output, "negative-" + name + ".stderr")).decode(errors="replace")
            if code == 0 or expected not in diagnostic:
                raise ValueError(name + ": unexpected acceptance or diagnostic")
            return {"case": name, "rejected": True, "exitCode": code}

        # No Lean workers from the proof/replay stages remain live here.
        cache_negatives = {}
        for name in CACHE_MUTATIONS:
            definitions, claim = cache_mutated(name)
            cache_negatives["cache_" + name] = (definitions.decode() +
                "\nopen Compiler.Extraction.Cache Contract.Yul\nexample : " + claim + " := by decide\n", "is false")
        assembly_clone_negatives = {}
        for name in ASSEMBLY_CLONE_MUTATIONS:
            definitions, claim = assembly_clone_mutated(name)
            definitions = definitions.decode().replace("import Compiler.Extraction.AssemblyClone\n",
                "import Compiler.Extraction.AssemblyCloneFixtures\n", 1)
            assembly_clone_negatives["assembly_clone_source_" + name] = (definitions +
                "\nopen Compiler.Extraction.AssemblyClone Compiler.Extraction.AssemblyClone.Fixtures\nexample : " +
                claim + " := by rfl\n", "Tactic `rfl` failed")
        interner_negatives = interner_mutation_negatives()
        constructor_negatives = {}
        for name in CONSTRUCTOR_MUTATIONS:
            definitions, claim = constructor_mutated(name)
            constructor_negatives["constructor_" + name] = (definitions.decode() +
                "\nopen Compiler.Extraction.Interner\nexample : " + claim + " := by rfl\n", "Tactic `rfl` failed")
        folding_negatives = {}
        for name in FOLDING_MUTATIONS:
            definitions, claim = folding_mutated(name)
            folding_negatives["folding_" + name] = (definitions.decode() +
                "\nopen Compiler.Extraction.Folding\nexample : " + claim + " := by rfl\n", "Tactic `rfl` failed")
        helper_negatives = {"helper_opcode": (nested_opcode_mutation().decode() +
            "\nopen Compiler.Extraction.Nested\nexample : nestedNotOpcode = 25 := by rfl\n", "Tactic `rfl` failed"),
            "nested_build_opcode": (nested_construction_opcode_mutation().decode() +
            "\nopen Compiler.Extraction.Nested\nexample : nestedIszeroOpcode = 21 := by rfl\n", "Tactic `rfl` failed"),
            "associative_opcode": (associative_opcode_mutation().decode() +
            "\nopen Compiler.Extraction.Associative\nexample : isAssociative 1 = true := by rfl\n", "Tactic `rfl` failed"),
            "shift_masks_opcode": (shift_masks_opcode_mutation().decode() +
            "\nopen Compiler.Extraction.ShiftMasks\nexample : shrOpcode = 28 := by rfl\n", "Tactic `rfl` failed"),
            "opposite_shifts_opcode": (opposite_shifts_opcode_mutation().decode() +
            "\nopen Compiler.Extraction.OppositeShifts\nexample : andOpcode = 22 := by rfl\n", "Tactic `rfl` failed"),
            "signextend_mask_opcode": (signextend_mask_opcode_mutation().decode() +
            "\nopen Compiler.Extraction.SignExtendMask\nexample : signextendOpcode = 11 := by rfl\n", "Tactic `rfl` failed"),
            "dispatch_opcode": (dispatch_opcode_mutation().decode() +
            "\nopen Compiler.Extraction.Dispatch\nexample : opSAR = 29 := by rfl\n", "Tactic `rfl` failed"),
            "alternating_mask_opcode": (alternating_mask_opcode_mutation().decode() +
            "\nopen Compiler.Extraction.AlternatingMask\nexample : orOpcode = 23 := by rfl\n", "Tactic `rfl` failed"),
            "address_mask_opcode": (address_mask_opcode_mutation().decode() +
            "\nopen Compiler.Extraction.AddressMask\nexample : addressOpcodes = [48, 51, 50, 65] := by rfl\n", "Tactic `rfl` failed")}
        negatives = {**NEGATIVES, **extraction_negatives(output), **storage_negatives(output),
                     **cache_negatives, **assembly_clone_negatives, **interner_negatives, **constructor_negatives, **folding_negatives, **helper_negatives}
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            report["negativeControls"].extend(pool.map(reject, negatives.items()))
        require_stable(before, snapshot())
        if source.file_digest(exporter) != exporter_digest:
            raise ValueError("exporter changed during verification")
        for tool in tools.values():
            if source.file_digest(Path(tool["path"])) != tool["sha256"]:
                raise ValueError("tool changed during verification: " + tool["path"])
        # Retain the small implementation/proof boundary, alongside hashes of
        # the complete inputs, for source review without a bulk repository copy.
        inputs = output / "inputs"
        for relative in ["src/libevmasm/algebraic_rules.zig", "src/libevmasm/rule_list.zig",
                         "src/compiler_rules_export.zig", "test/lean/check_compiler.py",
                         "test/lean/test_compiler_extraction.py", "lean/extract_compiler.py", "lean/compiler_ir.py",
                         "lean/extract_storage.py", "test/lean/test_compiler_storage.py",
                         "lean/extract_cache.py", "test/lean/test_compiler_cache.py",
                         "lean/extract_assembly_clone.py", "test/lean/test_compiler_assembly_clone.py",
                         "lean/extract_interner.py", "test/lean/test_compiler_interner.py",
                         "lean/extract_constructor.py", "test/lean/test_compiler_constructor.py",
                         "lean/extract_folding.py", "test/lean/test_compiler_folding.py",
                         "lean/extract_nested.py", "test/lean/test_compiler_nested.py",
                         "lean/extract_nested_construction.py", "test/lean/test_compiler_nested_construction.py",
                         "lean/extract_associative.py", "test/lean/test_compiler_associative.py",
                         "lean/extract_shift_masks.py", "test/lean/test_compiler_shift_masks.py",
                         "lean/extract_opposite_shifts.py", "test/lean/test_compiler_opposite_shifts.py",
                         "lean/extract_signextend_mask.py", "test/lean/test_compiler_signextend_mask.py",
                         "lean/extract_binary_logarithm.py", "test/lean/test_compiler_binary_logarithm.py",
                         "lean/extract_address_mask.py", "test/lean/test_compiler_address_mask.py",
                         "lean/extract_alternating_mask.py", "test/lean/test_compiler_alternating_mask.py",
                         "lean/extract_dispatch.py", "test/lean/test_compiler_dispatch.py",
                         "test/lean/check_compiler_dispatch.py", "test/lean/compiler_dispatch_cases.py",
                         "src/compiler_dispatch_trace.zig", "src/liblangutil/evm_version.zig",
                         "src/libevmasm/expression_classes.zig", "src/libevmasm/instruction.zig"] + [
                "lean/Compiler/Algebraic/" + name + ".lean" for name in ("Model", "Rules", "Proofs", "Audit")] + [
                "lean/Compiler/Extraction/" + name + ".lean" for name in (
                    "Control", "Matcher", "Proofs", "Builder", "Construction", "Graph",
                    "ConstructionProofs", "ConstructionTests", "IR", "Program", "Correspondence",
                    "StorageIR", "StorageRead", "StorageProgram", "StorageProofs",
                    "StorageOperations", "StorageOperationTests", "Memory", "MemoryProofs", "MemoryTests",
                    "CacheIR", "CacheProgram", "CacheProofs", "Interner", "InternerProgram",
                    "InternerProofs", "InternerStorage", "InternerFixtures", "InternerTests",
                    "Constructor", "ConstructorProgram", "ConstructorProofs",
                    "NestedConstruction", "NestedConstructionProgram", "NestedConstructionProofs", "NestedConstructionTests",
                    "Associative", "AssociativeProgram", "AssociativeProofs", "AssociativeTests",
                    "ShiftMasks", "ShiftMasksProgram", "ShiftMasksProofs", "ShiftMasksTests",
                    "OppositeShifts", "OppositeShiftsProgram", "OppositeShiftsProofs", "OppositeShiftsTests",
                    "SignExtendMask", "SignExtendMaskProgram", "SignExtendMaskProofs", "SignExtendMaskTests",
                    "BinaryLogarithm", "BinaryLogarithmProgram", "BinaryLogarithmProofs", "BinaryLogarithmTests",
                    "AddressMask", "AddressMaskProgram", "AddressMaskProofs", "AddressMaskTests",
                    "AlternatingMask", "AlternatingMaskProgram", "AlternatingMaskProofs", "AlternatingMaskTests",
                    "Dispatch", "DispatchProgram", "DispatchProofs", "DispatchTests", "DispatchUnaryProofs", "DispatchUnaryTests",
                    "DispatchAlgebraicProofs", "DispatchComparisonProofs", "DispatchComparisonTests",
                    "DispatchAssociativeProofs", "DispatchAssociativeTests",
                    "DispatchSignedProofs", "DispatchSignedTests",
                    "DispatchMultiplicationProofs", "DispatchMultiplicationTests",
                    "DispatchDivisionProofs", "DispatchDivisionTests",
                    "DispatchArityProofs", "DispatchArityTests",
                    "DispatchModuloProofs", "DispatchModuloTests",
                    "DispatchExponentProofs", "DispatchExponentTests",
                    "DispatchSubtractionProofs", "DispatchSubtractionTests",
                    "DispatchByteProofs", "DispatchByteTests",
                    "DispatchShiftProofs", "DispatchShiftRightProofs", "DispatchShiftRightTests",
                    "DispatchShiftLeftProofs", "DispatchShiftLeftTests",
                    "ArithmeticShift", "DispatchSignExtendProofs", "DispatchSignExtendTests",
                    "DispatchAndProofs", "DispatchAndTests",
                    "DispatchWordProofs", "DispatchWordTests",
                    "DispatchDefaultProofs", "DispatchDefaultTests",
                    "Recursive", "RecursiveTests", "Normalization", "NormalizationTests",
                    "NormalizationOwnership", "NormalizationOwnershipProofs", "NormalizationOwnershipTests",
                    "NormalizationEffects", "NormalizationEffectTests",
                    "OwnedKeys", "OwnedKeysProgram", "OwnedKeysProofs", "OwnedKeysTests",
                    "InternerControl", "InternerScope", "InternerScopeProofs", "InternerScopeControl",
                    "ScopedRecursive", "InternerScopeTests",
                    "InternerScopeFrames", "ScopedRecursiveFrames", "ScopedFrameTests",
                    "InternerScopeSemantics", "InternerScopePreservation", "ScopedRecursiveSemantics", "ScopedSemanticTests",
                    "ObservedHeap", "ObservedHeapTests", "ObservedStorage", "ObservedStorageTests",
                    "AssemblyClone", "AssemblyCloneProgram", "AssemblyCloneProofs", "AssemblyCloneFixtures", "AssemblyCloneTests",
                    "RepresentativeFrame", "DispatchFrames", "RecursiveFrames", "RecursiveFrameTests",
                    "LocalState", "LocalStateTests", "StorageEffects", "StorageEffectTests",
                    "InsertionEffects", "InsertionEffectTests",
                    "Folding", "FoldingProgram", "FoldingBits", "FoldingProofs", "FoldingTests",
                    "WordMeaning", "Nested", "NestedProgram", "NestedProofs", "NestedTests")] + [
                "lean/Compiler/Validation/" + name + ".lean" for name in ("Normalize", "Graph", "Tests")]:
            data = (ROOT / relative).read_bytes()
            if digest(data) != before[relative]:
                raise ValueError("input changed while retaining source: " + relative)
            target = inputs / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
        require_stable(before, snapshot())
        report["status"] = "passed"
    except (Exception, KeyboardInterrupt) as error:
        report["failure"] = {"kind": type(error).__name__, "message": str(error)}
    finally:
        (output / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": report["status"], "scope": report["scope"], "output": str(output)}))
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    sys.exit(main())
