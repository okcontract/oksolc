#!/usr/bin/env python3
"""Audit exact created-item residency through native append and borrowed query.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import borrowed_query_checks

MODULE = 'Compiler.Extraction.AssemblyCloneQueryRegistryTests'
CREATION = 'Compiler.Extraction.AssemblyItem.Creation.'
CLONE = 'Compiler.Extraction.AssemblyClone.'
FIELDS = CLONE + 'NativeFields.'
QUERY = borrowed_query_checks.QUERY
NATIVE = QUERY + 'Native.'
ARRAY = 'Compiler.Extraction.RepresentativeArray.'
CLAIMS = [CREATION + 'create_registered', CREATION + 'Created.registered', CLONE + 'Physical.Cloned.registered']
CLAIMS += [FIELDS + name for name in ('created_resident', 'Installed.spare_registered_query', 'Installed.first_registered_query')]
CLAIMS += [FIELDS + 'QueryTests.' + name for name in ('created_result', 'cloned_result', 'old_rows', 'old_items', 'first_fits')]
CLAIMS += [FIELDS + 'RegistryTests.' + name for name in
           ('created_row', 'ready_registered', 'reached_eq', 'registered_execution', 'accepted_borrow', 'misses', 'exact_key')]
CLAIMS += [NATIVE + name for name in ('observed', 'accepted', 'of_resident')]
CLAIMS += [NATIVE + 'Tests.' + name for name in (
    'session_valid', 'resident', 'all_queries', 'unsorted_native_hit', 'unsorted_accepted_good',
    'wrong_owner_rejected', 'wrong_registry_rejected', 'missing_storage_rejected', 'stack_storage_rejected',
    'readonly_storage_rejected', 'wrong_extent_rejected', 'stale_contents_rejected', 'last_element_rejected',
    'uninitialized_rejected', 'descriptor_does_not_prove_contents', 'faults_and_misses', 'empty_sentinel', 'offset_scope')]


def audit(claims):
    required = {
        CREATION + 'create_registered': {CREATION + 'create_shape'},
        FIELDS + 'created_resident': {CREATION + 'create_registered', CREATION + 'create_verified',
                                     CLONE + 'Physical.run_valid', CLONE + 'Physical.Cloned.registered'},
        NATIVE + 'observed': {QUERY + 'resident_accepted'},
        NATIVE + 'accepted': {NATIVE + 'observed', QUERY + 'accepted_good'},
        NATIVE + 'of_resident': {NATIVE + 'observed', NATIVE + 'accepted'},
        FIELDS + 'Installed.first_registered_query': {FIELDS + 'Installed.first_query',
            ARRAY + 'DescriptorRelation.first_registered', NATIVE + 'of_resident'},
        FIELDS + 'Installed.spare_registered_query': {FIELDS + 'Installed.spare_query',
            ARRAY + 'DescriptorRelation.spare_registered', NATIVE + 'of_resident',
            'Compiler.Extraction.Memory.resident_vector_write'},
        FIELDS + 'RegistryTests.created_row': {FIELDS + 'created_resident', FIELDS + 'QueryTests.installed'},
        FIELDS + 'RegistryTests.registered_execution': {FIELDS + 'RegistryTests.created_row',
            FIELDS + 'Installed.first_registered_query', FIELDS + 'Installed.spare_registered_query'},
        FIELDS + 'RegistryTests.accepted_borrow': {FIELDS + 'RegistryTests.registered_execution', QUERY + 'accepted_good'},
        NATIVE + 'Tests.all_queries': {NATIVE + 'of_resident', ARRAY + 'Operation.Tests.all_ids_and_opcodes'},
        NATIVE + 'Tests.unsorted_accepted_good': {NATIVE + 'Tests.all_queries', QUERY + 'accepted_good'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('clone registry query lost checked dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'createdItemExactResidencyVerified': True,
            'firstAndSpareAppendBorrowedQueriesVerified': True, 'finalGoodIsConclusion': True,
            'completeGraphCorrespondenceVerified': False, 'recursiveConstructorsVerified': False}


def controls(output, env, lean):
    return borrowed_query_checks.controls(output, env, lean)
