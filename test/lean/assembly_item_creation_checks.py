#!/usr/bin/env python3
"""Check creation-derived ownership in the actual insertion execution.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import json
import re
from lean_control_matrix import PendingControl
import assembly_clone_query_checks
import assembly_clone_registry_checks
import native_insertion_checks
import expression_invalidation_checks
import assembly_item_deinit_native_checks
import expression_deinit_native_checks
import native_last_value_checks
import native_pop_checks
import native_rollback_checks
import native_outer_cleanup_checks
import native_append_ownership_checks
import native_preparation_checks
import native_preparation_failure_checks
import native_first_ownership_checks
import native_growth_append_checks
import native_growing_ownership_checks
import native_cleanup_correspondence_checks
import native_publication_success_checks
import caller_origin_checks
import caller_publication_completion_checks
import caller_native_insertion_checks
import caller_first_success_checks
import publication_graph_checks
import caller_spare_success_checks
import caller_growing_success_checks
import caller_growing_rollback_checks
import caller_growth_allocation_failure_checks
import caller_transferred_growth_checks
import caller_transferred_allocation_failure_checks
import caller_transferred_preparation_failure_checks
import caller_capacity_checks
import caller_capacity_completion_checks
import caller_custody_checks
import caller_native_routing_checks
import constructor_item_checks
import recursive_child_checks
import constructor_argument_checks
import shift_input_checks
import recursive_nonempty_checks
import algebraic_input_checks
import pair_input_checks
import literal_input_checks
import view_input_checks
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

MODULE = native_insertion_checks.MODULE
NS = 'Compiler.Extraction.AssemblyItem.Creation.'
CLAIMS = [NS + name for name in (
    'layout_captured', 'view_layout_captured', 'create_from_response', 'extend_lookup', 'create_shape', 'create_verified', 'Created.arguments', 'create_oom',
    'Insertion.create_callback', 'Insertion.create_clone_rollback', 'Insertion.clone_oom_release')]
CLAIMS += [NS + 'Insertion.Tests.' + name for name in (
    'initial_valid', 'no_initial_object', 'taken_ready', 'create_result', 'creation_contract', 'clone_result', 'clone_contract',
    'composed_rollback', 'clone_oom_contract', 'publication_rollback', 'physical_rollback', 'append_rollback',
    'clone_oom_cleanup', 'create_oom_cleanup', 'success_keeps_allocations', 'request_oom_keeps_effects',
    'misaligned_rejected', 'overlap_rejected', 'overflow_rejected', 'collision_retains_allocation', 'bad_region_stops',
    'missing_object_rejects', 'repeated_creation_rejects', 'failed_destroy_retains_object', 'invalid_input_skips_request',
    'null_region_rejects', 'source_fault_retains_object', 'transferred_success', 'transferred_append_cleanup',
    'transferred_create_oom', 'transferred_clone_oom', 'insertion_words')]

FIELD = 'Compiler.Extraction.AssemblyItem.Fields.'
CLAIMS += ['Compiler.ZigAir.Memory.recordView_root']
CLAIMS += [FIELD + name for name in (
    'scalar_fields_checked', 'root_view', 'root_field', 'read_from_root', 'read_after_store', 'tag_of_read',
    'instruction_field_checked', 'instruction_after_store', 'instruction_store', 'optional_fields_checked', 'optional_store')]
CLAIMS += [FIELD + 'Tests.' + name for name in (
    'created_contract', 'allocation_not_initialization', 'complete_scalar_readback', 'parent_unchanged',
    'invalid_tags_reject', 'compound_fields_need_initialization', 'padding_rejects', 'readonly_store_rejects', 'wrong_scalar_rejects',
    'nominal_is_not_declaration', 'partial_is_not_declaration', 'wrong_identity_rejects', 'interior_rejects',
    'release_invalidates_fields', 'address_reuse_keeps_history', 'instruction_missing', 'instruction_null',
    'instruction_zero', 'instruction_unknown_opcode', 'instruction_last_opcode', 'instruction_frames_scalars',
    'instruction_dead_alias', 'instruction_reuse_uninitialized', 'integer_optionals_missing', 'all_optional_payloads',
    'integer_optionals_null', 'integer_optionals_zero', 'integer_optionals_high_bits', 'integer_optionals_frame',
    'integer_optionals_no_punning')]

OPTIONAL = 'Compiler.ZigAir.Memory.OptionalScalar.'
CLAIMS += [OPTIONAL + name for name in ('layout_captured', 'byteValue_type', 'byteValue_valid', 'byteValue_typed',
                                      'bytePayload_value', 'read_after_store', 'usize_layout_captured', 'word_layout_captured',
                                      'unsignedValue_type', 'unsignedValue_valid', 'unsignedValue_typed',
                                      'unsignedPayload_value', 'unsigned_read_after_store')]
CLAIMS += [OPTIONAL + 'Tests.' + name for name in (
    'before_valid', 'write_result', 'saved_valid', 'saved_payload', 'missing_is_uninitialized', 'null_is_initialized',
    'zero_is_present', 'largest_is_present', 'overwrite_clears_payload', 'independent_word', 'readonly_rejects',
    'wrong_payload_type', 'wrong_payload_range', 'wrong_optional_type', 'malformed_payload_never_wraps',
    'no_payload_field', 'scalar_punning_rejects', 'interior_rejects', 'unsupported_optional_layouts', 'dead_alias_rejects',
    'array_stride_and_bound')]
CLAIMS += [OPTIONAL + 'Tests.Wide.' + name for name in (
    'write_result', 'every_payload', 'missing_is_uninitialized', 'null_and_zero_differ', 'maximum_values',
    'clear_payload', 'invalid_values', 'wrong_children', 'no_payload_projection', 'readonly_and_dead',
    'unsupported_widths', 'array_stride_and_bounds')]

CLAIMS += [OPTIONAL + 'Tests.Signed.' + name for name in ('captured_layout_and_stride', 'unsupported_widths', 'signed_is_not_unsigned')]
CLAIMS += [FIELD + name for name in ('readTyped_from_root', 'leaf_store', 'Member.geometry', 'member_store')]
CLAIMS += ['Compiler.ZigAir.Memory.Value.leaves_atomic']
CLAIMS += [FIELD + 'MemberTests.' + name for name in (
    'all_member_values', 'missing_compound_members', 'all_verbatim_payloads', 'verbatim_null_empty_and_offset',
    'verbatim_incomplete_wrong_permission_and_range', 'nested_debug_readback',
    'source_descriptors_keep_identity_offset_and_empty', 'debug_frames_neighbors', 'signed_ast_boundaries',
    'source_and_ast_type_confusion_reject', 'no_optional_or_whole_debug_punning', 'readonly_dead_and_borrowed',
    'nonzero_item_view', 'partial_owner_declaration_rejects', 'clearing_preserves_other_members')]

CLAIMS += [FIELD + name for name in (
    'item_record_valid', 'debug_record_valid', 'location_record_valid', 'objectValue_typed',
    'members_complete', 'members_unique', 'Member.offset_injective', 'Member.read_offsets',
    'member_store_frame', 'writeMembers_total', 'assign_total', 'Written.session')]
INITIAL = 'Compiler.Extraction.AssemblyItem.Initializers.'
CLAIMS += [INITIAL + name for name in (
    'debug_typed', 'debug_forwarded', 'construct_typed', 'construct_complete', 'assign_query',
    'constant_typed', 'operation_typed', 'constant_arguments', 'operation_arguments', 'create_initialize')]
CLAIMS += [INITIAL + 'Tests.' + name for name in (
    'debug_valid', 'complete_execution', 'complete_valid', 'every_member', 'complete_record_shape',
    'debug_identity_and_offset', 'all_values', 'complete_frame', 'overwrite_all_fields', 'zero_and_last_opcode',
    'all_constant_words', 'all_operation_bytes', 'malformed_value_rejects', 'complete_owner_required',
    'readonly_and_dead', 'raw_enum_is_not_native_admission', 'graph_query_from_assignment',
    'initial_region', 'actual_creation_and_initialization', 'all_constant_creation', 'all_operation_creation')]

CLONE_FIELDS = 'Compiler.Extraction.AssemblyClone.NativeFields.'
CREATION_FIELDS = NS + 'NativeFields.'
CLAIMS += [FIELD + name for name in ('readTyped_parts', 'readTyped_typed', 'readTyped_frame')]
CLAIMS += ['Compiler.Extraction.AssemblyItem.payload_ne', 'Compiler.Extraction.AssemblyClone.Physical.Reads.frame',
           'Compiler.Extraction.AssemblyClone.Physical.run_duplicate']
CLAIMS += [CLONE_FIELDS + name for name in (
    'Represents.typed', 'Represents.live', 'Represents.frame', 'payload_typed_same', 'values_typed_same',
    'payload_owned_frame', 'payload_reads_frame', 'install_assigned', 'install_unchanged', 'install_total',
    'checkMembers_iff', 'checkSource_iff', 'clone_install')]
CLAIMS += [CREATION_FIELDS + name for name in (
    'finish_assigned', 'finish_failed', 'clone_callback', 'clone_oom', 'represented_after_create', 'create_clone_rollback')]
CLAIMS += [CREATION_FIELDS + 'Tests.' + name for name in (
    'initial_frame', 'initial_valid', 'source_represented', 'complete_execution', 'every_member',
    'source_and_payload_frame', 'borrowed_metadata', 'publication_rollback', 'append_rollback', 'clone_oom_cleanup',
    'source_mismatch_rejects', 'source_fault_keeps_state', 'composed_rollback', 'oom_precedes_payload_reads',
    'failed_assignment_retains_clone', 'absent_and_empty_payloads', 'overwritten_target')]

CLAIMS += assembly_clone_query_checks.CLAIMS
CLAIMS += assembly_clone_registry_checks.CLAIMS
CLAIMS += native_insertion_checks.CLAIMS
CLAIMS += expression_invalidation_checks.CLAIMS
CLAIMS += assembly_item_deinit_native_checks.CLAIMS
CLAIMS += expression_deinit_native_checks.CLAIMS
CLAIMS += native_last_value_checks.CLAIMS
CLAIMS += native_pop_checks.CLAIMS
CLAIMS += native_rollback_checks.CLAIMS
CLAIMS += native_outer_cleanup_checks.CLAIMS
CLAIMS += native_append_ownership_checks.CLAIMS
CLAIMS += native_preparation_checks.CLAIMS
CLAIMS += native_preparation_failure_checks.CLAIMS
CLAIMS += native_first_ownership_checks.CLAIMS
CLAIMS += native_growth_append_checks.CLAIMS
CLAIMS += native_growing_ownership_checks.CLAIMS
CLAIMS += native_cleanup_correspondence_checks.CLAIMS
CLAIMS += native_publication_success_checks.CLAIMS
CLAIMS += caller_origin_checks.CLAIMS
CLAIMS += caller_publication_completion_checks.CLAIMS
CLAIMS += caller_native_insertion_checks.CLAIMS
CLAIMS += caller_first_success_checks.CLAIMS
CLAIMS += publication_graph_checks.CLAIMS
CLAIMS += caller_spare_success_checks.CLAIMS
CLAIMS += caller_growing_success_checks.CLAIMS
CLAIMS += caller_growing_rollback_checks.CLAIMS
CLAIMS += caller_growth_allocation_failure_checks.CLAIMS
CLAIMS += caller_transferred_growth_checks.CLAIMS
CLAIMS += caller_transferred_allocation_failure_checks.CLAIMS
CLAIMS += caller_transferred_preparation_failure_checks.CLAIMS
CLAIMS += caller_capacity_checks.CLAIMS
CLAIMS += caller_capacity_completion_checks.CLAIMS
CLAIMS += caller_custody_checks.CLAIMS
CLAIMS += caller_native_routing_checks.CLAIMS
CLAIMS += constructor_item_checks.CLAIMS
CLAIMS += recursive_child_checks.CLAIMS
CLAIMS += constructor_argument_checks.CLAIMS
CLAIMS += shift_input_checks.CLAIMS
CLAIMS += recursive_nonempty_checks.CLAIMS
CLAIMS += algebraic_input_checks.CLAIMS
CLAIMS += pair_input_checks.CLAIMS
CLAIMS += literal_input_checks.CLAIMS
CLAIMS += view_input_checks.CLAIMS


def audit(output):
    claims = {c['theorem']: set(c['dependencies'])
              for c in json.loads((output / 'audit.json').read_bytes())['claims']}
    clone = 'Compiler.Extraction.AssemblyClone.Physical.'
    required = {
        CLONE_FIELDS + 'Represents.typed': {FIELD + 'readTyped_typed'},
        CLONE_FIELDS + 'Represents.frame': {FIELD + 'readTyped_frame'},
        CLONE_FIELDS + 'payload_owned_frame': {'Compiler.Extraction.AssemblyItem.payload_ne'},
        CLONE_FIELDS + 'payload_reads_frame': {'Compiler.Extraction.AssemblyItem.payload_ne', clone + 'Reads.frame'},
        CLONE_FIELDS + 'install_total': {FIELD + 'assign_total', FIELD + 'Written.session',
            CLONE_FIELDS + 'payload_owned_frame', CLONE_FIELDS + 'payload_reads_frame'},
        CLONE_FIELDS + 'clone_install': {clone + 'run_valid', clone + 'Cloned.item',
            CLONE_FIELDS + 'Represents.typed', CLONE_FIELDS + 'values_typed_same', CLONE_FIELDS + 'install_total'},
        CREATION_FIELDS + 'clone_callback': {CLONE_FIELDS + 'checkSource_iff', CLONE_FIELDS + 'clone_install',
            NS + 'Insertion.operations', CREATION_FIELDS + 'finish_assigned'},
        CREATION_FIELDS + 'represented_after_create': {CLONE_FIELDS + 'Represents.live', CLONE_FIELDS + 'Represents.frame'},
        CREATION_FIELDS + 'create_clone_rollback': {NS + 'create_verified', NS + 'Created.arguments',
            CREATION_FIELDS + 'represented_after_create', CREATION_FIELDS + 'clone_callback',
            clone + 'Cloned.arguments', clone + 'Insertion.last_value_callback'},
        CREATION_FIELDS + 'Tests.composed_rollback': {CREATION_FIELDS + 'create_clone_rollback'},
        FIELD + 'member_store_frame': {'Compiler.ZigAir.Memory.load_disjoint_after_store', FIELD + 'Member.offset_injective'},
        FIELD + 'writeMembers_total': {FIELD + 'member_store', FIELD + 'member_store_frame',
            'Compiler.ZigAir.Memory.store_retains_shape', 'Compiler.ZigAir.Memory.heap_after_store_other'},
        FIELD + 'assign_total': {FIELD + 'writeMembers_total', FIELD + 'members_complete', FIELD + 'root_view'},
        FIELD + 'Written.session': {'Compiler.Extraction.Memory.Arguments.Normalization.represented_frame'},
        INITIAL + 'assign_query': {FIELD + 'assign_total', INITIAL + 'construct_typed', FIELD + 'read_from_root',
            FIELD + 'tag_of_read', OPTIONAL + 'bytePayload_value'},
        INITIAL + 'create_initialize': {NS + 'create_from_response', INITIAL + 'assign_query', FIELD + 'Written.session'},
        INITIAL + 'constant_arguments': {'Compiler.Extraction.Interner.constructorCode'},
        INITIAL + 'operation_arguments': {'Compiler.Extraction.Interner.constructorCode'},
        INITIAL + 'Tests.actual_creation_and_initialization': {INITIAL + 'create_initialize'},
        INITIAL + 'Tests.all_constant_creation': {INITIAL + 'Tests.actual_creation_and_initialization',
            'Compiler.Extraction.Interner.constructorCode'},
        INITIAL + 'Tests.all_operation_creation': {INITIAL + 'Tests.actual_creation_and_initialization',
            'Compiler.Extraction.Interner.constructorCode'},
        FIELD + 'member_store': {FIELD + 'leaf_store', FIELD + 'Member.geometry'},
        FIELD + 'leaf_store': {'Compiler.ZigAir.Memory.store_subobject_total', 'Compiler.ZigAir.Memory.access_subregion',
            'Compiler.ZigAir.Memory.Value.leaves_atomic', 'Compiler.ZigAir.Memory.store_preserves_valid',
            FIELD + 'readTyped_from_root', 'Compiler.ZigAir.Memory.load_alias_after_store'},
        FIELD + 'MemberTests.all_member_values': {FIELD + 'member_store', FIELD + 'Tests.created_contract'},
        FIELD + 'MemberTests.all_verbatim_payloads': {FIELD + 'MemberTests.all_member_values',
            'Compiler.ZigAir.Memory.OptionalObject.payload_value'},
        FIELD + 'instruction_store': {FIELD + 'optional_store'},
        FIELD + 'optional_store': {FIELD + 'read_after_store', FIELD + 'optional_fields_checked',
            'Compiler.ZigAir.Memory.store_subobject_total', 'Compiler.ZigAir.Memory.root_access',
            OPTIONAL + 'unsignedValue_valid', OPTIONAL + 'unsignedPayload_value'},
        FIELD + 'Tests.all_optional_payloads': {FIELD + 'optional_store', FIELD + 'Tests.created_contract'},
        FIELD + 'instruction_after_store': {FIELD + 'read_after_store', OPTIONAL + 'bytePayload_value'},
        OPTIONAL + 'read_after_store': {OPTIONAL + 'unsigned_read_after_store'},
        OPTIONAL + 'unsigned_read_after_store': {'Compiler.ZigAir.Memory.load_alias_after_store', OPTIONAL + 'unsignedPayload_value'},
        OPTIONAL + 'Tests.Wide.every_payload': {OPTIONAL + 'unsigned_read_after_store', OPTIONAL + 'Tests.Wide.write_result',
            'Compiler.ZigAir.Memory.store_preserves_valid'},
        NS + 'create_from_response': {NS + 'create_verified', NS + 'view_layout_captured',
            'Compiler.ZigAir.Memory.RegionAllocation.extend_valid'},
        FIELD + 'root_view': {'Compiler.ZigAir.Memory.recordView_root', NS + 'view_layout_captured'},
        FIELD + 'read_after_store': {FIELD + 'read_from_root', 'Compiler.ZigAir.Memory.store_retains_shape',
            'Compiler.ZigAir.Memory.store_preserves_valid', 'Compiler.ZigAir.Memory.load_alias_after_store'},
        FIELD + 'Tests.created_contract': {NS + 'create_from_response'},
        NS + 'create_verified': {NS + 'create', NS + 'create_shape', 'Compiler.Extraction.AssemblyItem.allocationType',
                               'Compiler.Extraction.AssemblyItem.viewType'},
        NS + 'Insertion.create_callback': {NS + 'create_verified', NS + 'Insertion.operations'},
        NS + 'Insertion.create_clone_rollback': {NS + 'create_verified', NS + 'Created.arguments',
            clone + 'run_valid', clone + 'Cloned.item', clone + 'Cloned.arguments', clone + 'Insertion.last_value_callback',
            'Compiler.Extraction.ExpressionDeinit.Lifetime.run_verified'},
        NS + 'Insertion.clone_oom_release': {NS + 'create_verified', clone + 'run_oom',
            'Compiler.Extraction.AssemblyItem.destroy_verified'},
        NS + 'Insertion.Tests.composed_rollback': {NS + 'Insertion.create_clone_rollback',
            'Compiler.Extraction.Memory.Arguments.Normalization.take_refines'},
        NS + 'Insertion.Tests.insertion_words': {'Compiler.Extraction.Interner.InsertionExecution.verified',
            NS + 'Insertion.Tests.creation_contract', NS + 'Insertion.Tests.clone_contract', NS + 'Insertion.Tests.publication_rollback'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('creation path lost checked dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'creationSuppliesObjectOwnership': True,
            'itemCreationCallbackIntegrated': True, 'nativeAllocatorImplementationVerified': False,
            'completeItemDeclarationBound': True, 'checkedScalarFieldReadbackVerified': True,
            'nativeFieldAssignmentVerified': False, 'instructionOptionalReadVerified': True,
            'integerOptionalReadVerified': True, 'nestedDeclaredMembersVerified': True,
            'completeTypedItemAssignmentVerified': True, 'constructorValuesVerified': True,
            'cloneResultAssignmentIntegrated': True, 'initialSourceFieldsChecked': True,
            'cloneAssignmentDerivesPayloadFrame': True,
            'assignmentDerivesQueryItemRelation': True,
            'cloneQueries': assembly_clone_query_checks.audit(claims),
            'cloneRegistryQueries': assembly_clone_registry_checks.audit(claims),
            'nativeInsertion': native_insertion_checks.audit(claims),
            'expressionInvalidation': expression_invalidation_checks.audit(claims),
            'nativeItemDeinit': assembly_item_deinit_native_checks.audit(claims),
            'nativeExpressionDeinit': expression_deinit_native_checks.audit(claims),
            'nativeLastValue': native_last_value_checks.audit(claims),
            'nativePop': native_pop_checks.audit(claims),
            'nativeRollback': native_rollback_checks.audit(claims),
            'nativeOuterCleanup': native_outer_cleanup_checks.audit(claims),
            'nativeAppendOwnership': native_append_ownership_checks.audit(claims),
            'nativePreparation': native_preparation_checks.audit(claims),
            'nativePreparationFailures': native_preparation_failure_checks.audit(claims),
            'nativeFirstOwnership': native_first_ownership_checks.audit(claims),
            'nativeGrowingAppend': native_growth_append_checks.audit(claims),
            'nativeGrowingOwnership': native_growing_ownership_checks.audit(claims),
            'nativeCleanupCorrespondence': native_cleanup_correspondence_checks.audit(claims),
            'nativePublicationSuccess': native_publication_success_checks.audit(claims),
            'callerOrigin': caller_origin_checks.audit(claims),
            'callerPublicationCompletion': caller_publication_completion_checks.audit(claims),
            'callerNativeInsertion': caller_native_insertion_checks.audit(claims),
            'callerFirstSuccess': caller_first_success_checks.audit(claims),
            'publicationGraph': publication_graph_checks.audit(claims),
            'callerSpareSuccess': caller_spare_success_checks.audit(claims),
            'callerGrowingSuccess': caller_growing_success_checks.audit(claims),
            'callerGrowingRollback': caller_growing_rollback_checks.audit(claims),
            'callerGrowthAllocationFailure': caller_growth_allocation_failure_checks.audit(claims),
            'callerTransferredGrowth': caller_transferred_growth_checks.audit(claims),
            'callerTransferredAllocationFailure': caller_transferred_allocation_failure_checks.audit(claims),
            'callerTransferredPreparationFailure': caller_transferred_preparation_failure_checks.audit(claims),
            'callerCapacity': caller_capacity_checks.audit(claims),
            'callerCapacityCompletion': caller_capacity_completion_checks.audit(claims),
            'callerCustody': caller_custody_checks.audit(claims),
            'callerNativeRouting': caller_native_routing_checks.audit(claims),
            'constructorItem': constructor_item_checks.audit(claims),
            'recursiveChild': recursive_child_checks.audit(claims),
            'constructorArguments': constructor_argument_checks.audit(claims),
            'shiftInputs': shift_input_checks.audit(claims),
            'recursiveNonempty': recursive_nonempty_checks.audit(claims),
            'algebraicInputs': algebraic_input_checks.audit(claims),
            'scalarPairInputs': pair_input_checks.audit(claims),
            'literalInputs': literal_input_checks.audit(claims),
            'viewInputs': view_input_checks.audit(claims),
            'compoundFieldReadbackVerified': True, 'optionalContentsVerified': False, 'universalCallerAdmissionVerified': False}


def controls(output, env, lean):
    directory = ROOT / 'lean/Compiler/Extraction'
    source = ('import Compiler.Extraction.AssemblyCloneInsertionTests\n'
              'import Compiler.ZigAir.MemoryRecordViews\n'
              'import Compiler.ZigAir.MemoryRecordWrites\n'
              'import Compiler.ZigAir.MemoryOptionalScalarTests\n'
              'import Compiler.ZigAir.MemoryOptionalObject\n'
              'import Compiler.ZigAir.MemoryRegionAllocationProofs\n') + '\n'.join(
        without_imports((directory / name).read_text()) for name in (
            'AssemblyItemCreation.lean', 'AssemblyItemFields.lean', 'AssemblyItemFieldTests.lean',
            'AssemblyItemMembers.lean', 'AssemblyItemMemberTests.lean',
            'AssemblyItemCreationInsertion.lean', 'AssemblyItemCreationTests.lean'))
    changes = (
        ('nested-read-partial-owner', 'let .pointer _ root ← recordView state viewType (.pointer (.pointer false false allocationType) address)\n    | .error .malformed', 'let root := address'),
        ('nested-read-rebases-owner', 'root.offset + offset', 'offset'),
        ('nested-read-wrong-offset', 'root.offset + offset', 'root.offset + offset + 8'),
        ('wrong-native-start', 'debug_data_native_locationOffset + source_location_startOffset', 'debug_data_native_locationOffset + source_location_endOffset'),
        ('wrong-origin-source', 'debug_data_origin_locationOffset + source_location_source_nameOffset', 'debug_data_native_locationOffset + source_location_source_nameOffset'),
        ('wrong-ast-id-offset', 'debug_dataOffset + debug_data_ast_idOffset', 'immutable_occurrencesOffset'),
        ('source-name-wrong-selection', 'if origin then .originSource else .nativeSource', 'if origin then .nativeSource else .originSource'),
        ('verbatim-always-null', 'OptionalObject.payload verbatimType ⟨40, 8⟩ value', 'let _ := value; .ok none'),
        ('wrong-pushed-offset', '| .pushed => pushed_valueOffset', '| .pushed => data_valueOffset'),
        ('wrong-immutable-offset', '| .immutable => immutable_occurrencesOffset', '| .immutable => modifier_depthOffset'),
        ('optional-always-null', 'OptionalScalar.unsignedPayload field.bits value', 'let _ := value; .ok none'),
        ('wrong-instruction-offset', '| .instruction => instruction_valueOffset', '| .instruction => data_valueOffset'),
        ('instruction-always-null', 'optional state address .instruction', '.ok none'),
        ('nominal-without-declaration', '⟨base, viewType, [], true, false⟩', '⟨base, allocationType, [], true, false⟩'),
        ('wrong-kind-offset', 'tag state address item_typeOffset itemTagValues',
         'tag state address jump_typeOffset itemTagValues'),
        ('skip-enum-domain', 'if value ∈ values then .ok value else .error .malformed\n', '.ok value\n'),
        ('wrong-field-offset', 'let field ← fieldPointer state item offset', 'let field ← fieldPointer state item 0'),
        ('wrong-request-extent', 'let (response, effects) := request layout before',
         'let (response, effects) := request ⟨1, layout.alignment⟩ before'),
        ('wrong-request-alignment', 'let (response, effects) := request layout before',
         'let (response, effects) := request ⟨layout.bytes, 1⟩ before'),
        ('stack-allocation', '⟨base, viewType, [], true, false⟩', '⟨base, viewType, [], true, true⟩'),
        ('wrong-owner', '{ reached with heap := write before.heap before.memory.nextId (some ⟨allocator, .item item⟩) }',
         '{ reached with heap := write before.heap before.memory.nextId (some ⟨0, .item item⟩) }'),
        ('wrong-registered-key', '{ reached with heap := write before.heap before.memory.nextId (some ⟨allocator, .item item⟩) }',
         '{ reached with heap := write before.heap before.memory.nextId (some ⟨allocator, .item { item with data := item.data + 1 }⟩) }'),
        ('discard-oom-effects', '| none => (.error .outOfMemory, { before with effects })', '| none => (.error .outOfMemory, before)'),
        ('discard-created-memory', 'let reached : Session σ := { before with memory, effects }',
         'let reached : Session σ := { before with effects }'),
        ('discard-collision-memory', '(.error .registryCollision, reached)', '(.error .registryCollision, { before with effects })'),
        ('wrong-object-local', '(.ok true, { reached with object := some object })', '(.ok true, { reached with object := some 0 })'),
        ('creation-oom-is-fault', '| .error .outOfMemory => (.ok false, reached)',
         '| .error .outOfMemory => (.error (.creation .outOfMemory), reached)'),
        ('creation-fault-is-oom', '| .error fault => (.error (.creation fault), reached)', '| .error _ => (.ok false, reached)'),
        ('discard-clone-state', '(result.mapError Fault.insertion, { before with clone := after })',
         '(result.mapError Fault.insertion, before)'),
        ('skip-destroy', 'let (result, memory) := destroy objects allocator object before.clone.execution.memory',
         'let (result, memory) := (Except.ok (), before.clone.execution.memory)'),
        ('clear-failed-destroy', 'object := if result.isOk then none else before.object', 'object := none'),
        ('retain-destroyed-local', 'object := if after.execution.invalidated then none else before.object', 'object := before.object'),
    )
    for name, before, _ in changes:
        if source.count(before) != 1:
            raise ValueError('ambiguous creation mutation: ' + name)
    records = [mutation_check(output, 'item-creation-unchanged', source, True, env, lean)]
    for name, before, after in changes:
        records.append(mutation_check(output, 'item-creation-' + name, source.replace(before, after), False, env, lean))
    return (checked_controls(output, records) + initialization_controls(output, env, lean) +
            clone_field_controls(output, env, lean) + assembly_clone_query_checks.controls(output, env, lean) +
            assembly_clone_registry_checks.controls(output, env, lean) + native_insertion_checks.controls(output, env, lean) +
            expression_invalidation_checks.controls(output, env, lean) + assembly_item_deinit_native_checks.controls(output, env, lean) +
            expression_deinit_native_checks.controls(output, env, lean) + native_last_value_checks.controls(output, env, lean) +
            native_pop_checks.controls(output, env, lean) + native_rollback_checks.controls(output, env, lean) +
            native_outer_cleanup_checks.controls(output, env, lean) +
            native_append_ownership_checks.controls(output, env, lean) + native_preparation_checks.controls(output, env, lean) +
            native_preparation_failure_checks.controls(output, env, lean) + native_first_ownership_checks.controls(output, env, lean) +
            native_growth_append_checks.controls(output, env, lean) + native_growing_ownership_checks.controls(output, env, lean) +
            native_cleanup_correspondence_checks.controls(output, env, lean) + native_publication_success_checks.controls(output, env, lean) + caller_origin_checks.controls(output, env, lean) +
            caller_publication_completion_checks.controls(output, env, lean) + caller_native_insertion_checks.controls(output, env, lean) +
            caller_first_success_checks.controls(output, env, lean) + publication_graph_checks.controls(output, env, lean) +
            caller_spare_success_checks.controls(output, env, lean) + caller_growing_success_checks.controls(output, env, lean) +
            caller_growing_rollback_checks.controls(output, env, lean) +
            caller_growth_allocation_failure_checks.controls(output, env, lean) +
            caller_transferred_growth_checks.controls(output, env, lean) +
            caller_transferred_allocation_failure_checks.controls(output, env, lean) +
            caller_transferred_preparation_failure_checks.controls(output, env, lean) +
            caller_capacity_checks.controls(output, env, lean) +
            caller_capacity_completion_checks.controls(output, env, lean) +
            caller_custody_checks.controls(output, env, lean) +
            caller_native_routing_checks.controls(output, env, lean) +
            constructor_item_checks.controls(output, env, lean) +
            recursive_child_checks.controls(output, env, lean) +
            constructor_argument_checks.controls(output, env, lean) +
            shift_input_checks.controls(output, env, lean) +
            recursive_nonempty_checks.controls(output, env, lean) +
            algebraic_input_checks.controls(output, env, lean) +
            pair_input_checks.controls(output, env, lean) +
            literal_input_checks.controls(output, env, lean) +
            view_input_checks.controls(output, env, lean))


def checked_controls(output, records):
    for record in records:
        if isinstance(record, PendingControl):
            record.checked_by(output, check_control_diagnostic)
        else:
            check_control_diagnostic(output, record)
    return records


def check_control_diagnostic(output, record):
    diagnostic = (output / (record['name'] + '.stdout')).read_text()
    if re.search(r'maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant|failed to synthesize|Invalid field', diagnostic, re.I):
        raise ValueError('creation control hit resource, syntax or elaboration failure: ' + record['name'])
    if not record['expectedAcceptance'] and not re.search(
            r'unsolved goals|Type mismatch|Tactic [^\n]*(?:failed|proved)|Dependent elimination failed|Application type mismatch|omega could not prove the goal', diagnostic, re.I):
        raise ValueError('creation negative control has no semantic proof failure: ' + record['name'])


def initialization_controls(output, env, lean):
    directory = ROOT / 'lean/Compiler/Extraction'
    source = ('import Compiler.Extraction.AssemblyItemMemberTests\n'
              'import Compiler.Extraction.ConstructorProgram\n'
              'import Compiler.Extraction.RepresentativeOperationTests\n') + '\n'.join(
        without_imports((directory / name).read_text()) for name in (
            'AssemblyItemAssignment.lean', 'AssemblyItemQuery.lean', 'AssemblyItemInitializers.lean', 'AssemblyItemInitializationTests.lean'))
    changes = (
        ('omitted-ast-id', '.originStart, .originEnd, .originSource, .astId]', '.originStart, .originEnd, .originSource]'),
        ('duplicate-member', '.originStart, .originEnd, .originSource, .astId]', '.originStart, .originEnd, .originSource, .originSource, .astId]'),
        ('skip-complete-owner', 'let _ ← recordView state viewType (.pointer (.pointer true false allocationType) ⟨id, 0⟩)', 'let _ := ()'),
        ('skip-value-precheck', 'if !(members.all fun selected => (values selected).hasType selected.type) then .error .malformed else', 'if false then .error .malformed else'),
        ('skip-field-store', 'let after ← store state (.pointer (.pointer true false selected.type) ⟨id, selected.offset⟩) (values selected)', 'let after := state'),
        ('wrong-store-lifetime', 'let after ← store state (.pointer (.pointer true false selected.type) ⟨id, selected.offset⟩) (values selected)',
         'let after ← store state (.pointer (.pointer true false selected.type) ⟨0, selected.offset⟩) (values selected)'),
        ('truncate-assignment', 'writeMembers values id rest after', 'writeMembers values id [] after'),
        ('rewind-lifetime', '| [], state => .ok state', '| [], state => .ok { state with nextId := 0 }'),
        ('wrong-kind', 'construct (constructorCode.constantRequest value).item debug',
         'construct { (constructorCode.constantRequest value).item with kind := 1 } debug'),
        ('missing-instruction', '| .instruction => OptionalScalar.byteValue item.instruction', '| .instruction => OptionalScalar.byteValue none'),
        ('wrong-data', 'construct (constructorCode.constantRequest value).item debug',
         'construct { (constructorCode.constantRequest value).item with data := 0 } debug'),
        ('wrong-verbatim-default', '| .verbatim => .optionalObject verbatimType ⟨40, 8⟩ none',
         '| .verbatim => .optionalObject verbatimType ⟨40, 8⟩ (some (.fields []))'),
        ('wrong-pushed-default', '| .pushed => OptionalScalar.unsignedValue 256 none', '| .pushed => OptionalScalar.unsignedValue 256 (some 0)'),
        ('wrong-immutable-default', '| .immutable => OptionalScalar.unsignedValue 64 none', '| .immutable => OptionalScalar.unsignedValue 64 (some 0)'),
        ('wrong-modifier-default', '| .modifier => .scalar (.int false 64 0)', '| .modifier => .scalar (.int false 64 19)'),
        ('wrong-jump-default', '| .jump => .scalar (.int true 32 0)', '| .jump => .scalar (.int true 32 2)'),
        ('wrong-debug-forwarding', '| selected => debug selected', '| selected => if selected = .originSource then debug .nativeSource else debug selected'),
        ('wrong-source-reification', 'values (if origin then .originSource else .nativeSource)', 'values (if origin then .nativeSource else .originSource)'),
        ('swapped-tag-reification', '(item_typeOffset, .leaf (values .kind)), (jump_typeOffset, .leaf (values .jump))',
         '(item_typeOffset, .leaf (values .jump)), (jump_typeOffset, .leaf (values .kind))'),
    )
    for name, before, _ in changes:
        if source.count(before) != 1:
            raise ValueError('ambiguous item initialization mutation: ' + name)
    records = [mutation_check(output, 'item-initialization-unchanged', source, True, env, lean)]
    for name, before, after in changes:
        records.append(mutation_check(output, 'item-initialization-' + name, source.replace(before, after), False, env, lean))
    return checked_controls(output, records)


def clone_field_controls(output, env, lean):
    directory = ROOT / 'lean/Compiler/Extraction'
    source = 'import Compiler.Extraction.AssemblyItemCreationTests\n' + '\n'.join(
        without_imports((directory / name).read_text()) for name in (
            'AssemblyCloneFields.lean', 'AssemblyItemCreationFields.lean', 'AssemblyCloneFieldFixtures.lean'))
    changes = (
        ('ignored-kind-metadata', '| .kind => AssemblyItem.Initializers.construct input.item input.metadata .kind',
         '| .kind => input.metadata .kind'),
        ('ignored-instruction-metadata', '| .instruction => AssemblyItem.Initializers.construct input.item input.metadata .instruction',
         '| .instruction => input.metadata .instruction'),
        ('payload-offset-erased', '⟨payload.data.address, payload.data.offset⟩', '⟨payload.data.address, 0⟩'),
        ('wrong-payload-arity', '(.int false 64 payload.arguments)', '(.int false 64 payload.returns)'),
        ('wrong-payload-lifetime', '⟨payload.data.address, payload.data.offset⟩', '⟨0, payload.data.offset⟩'),
        ('wrong-metadata', '| selected => input.metadata selected',
         '| selected => input.metadata (if selected = .originSource then .nativeSource else selected)'),
        ('wrong-data', '| .data => AssemblyItem.Initializers.construct input.item input.metadata .data',
         '| .data => AssemblyItem.Initializers.construct input.item input.metadata .kind'),
        ('missing-payload', '| .verbatim => verbatimValue input.verbatim', '| .verbatim => verbatimValue none'),
        ('skip-source-tail', 'then checkMembers state source input rest', 'then .ok ()'),
        ('wrong-destination', '(assign (values copied) object before.memory).map (fun memory => { before with memory })',
         '(assign (values copied) 0 before.memory).map (fun memory => { before with memory })'),
        ('skip-assignment', '(assign (values copied) object before.memory).map (fun memory => { before with memory })',
         '.ok before'),
        ('discard-assigned-memory', '(assign (values copied) object before.memory).map (fun memory => { before with memory })',
         '(assign (values copied) object before.memory).map (fun _ => before)'),
        ('callback-skips-assignment', 'finish object result reached', '(result.mapError Fault.base, reached)'),
        ('callback-wrong-object', 'finish object result reached', 'finish 0 result reached'),
        ('assignment-fault-is-oom', '| .error reason => (.error (.assignment reason), reached)',
         '| .error _ => (.ok false, reached)'),
        ('lost-failed-clone-local', '| .error reason => (.error (.assignment reason), reached)',
         '| .error reason => (.error (.assignment reason), { reached with clone := { reached.clone with value := none } })'),
        ('oom-runs-assignment', '| .ok false => (.ok false, reached)',
         '| .ok false => installResult (AssemblyClone.NativeFields.install '
         '⟨{ kind := 1, instruction := none, data := 0 }, fun _ => .scalar (.int false 64 0), none⟩ '
         'object reached.clone.execution.memory) reached'),
    )
    for name, before, _ in changes:
        if source.count(before) != 1:
            raise ValueError('ambiguous clone-field mutation: ' + name)
    # Mutate the adapter proofs and independent initial-field oracle. Full insertion
    # fixtures are separately compiled, audited and freshly replayed via MODULE.
    records = checked_controls(output, [mutation_check(output, 'clone-fields-unchanged', source, True, env, lean)])
    for name, before, after in changes:
        records += checked_controls(output, [mutation_check(output, 'clone-fields-' + name, source.replace(before, after), False, env, lean)])
    return checked_controls(output, records)
