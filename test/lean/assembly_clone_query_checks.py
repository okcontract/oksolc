#!/usr/bin/env python3
"""Audit installed-clone queries through reached publication and append.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_operation_arguments
import check_representative_array

MODULE = 'Compiler.Extraction.AssemblyCloneQueryTests'
ITEM = 'Compiler.Extraction.AssemblyItem.Query.'
CLONE = 'Compiler.Extraction.AssemblyClone.NativeFields.'
ARRAY = 'Compiler.Extraction.RepresentativeArray.'
CLAIMS = ['Compiler.Extraction.AssemblyItem.Fields.' + name for name in ('view_frame', 'read_frame')]
CLAIMS += [ITEM + name for name in ('of_members', 'frame', 'no_descriptor', 'publication_frame', 'append_frame')]
CLAIMS += [CLONE + name for name in ('key_fields', 'Installed.query', 'Installed.spare_query', 'Installed.first_query')]
CLAIMS += [ARRAY + 'Append.Execution.' + name for name in
           ('finish_allocation_frame', 'assumeCapacity_allocation_frame', 'run_allocation_frame')]
CLAIMS += [CLONE + 'QueryTests.' + name for name in (
    'initial_frame', 'initial_valid', 'installed', 'installed_query', 'first_queries', 'spare_queries',
    'all_append_outcomes', 'publication_outcomes', 'first_oom_keeps_item', 'partial_descriptor_keeps_item',
    'concrete_queries', 'nested_descriptor_requires_exclusion')]


def audit(claims):
    required = {
        ITEM + 'of_members': {'Compiler.Extraction.AssemblyItem.Fields.read_from_root',
                             'Compiler.Extraction.AssemblyItem.Fields.tag_of_read'},
        ITEM + 'frame': {'Compiler.Extraction.AssemblyItem.Fields.read_frame'},
        ITEM + 'publication_frame': {ARRAY + 'Publication.Registered.storage', ITEM + 'frame',
                                    'Compiler.ZigAir.Memory.Heap.lookup_ne_of_type_ne'},
        ITEM + 'append_frame': {ARRAY + 'Append.Execution.run_allocation_frame', ITEM + 'frame', ITEM + 'no_descriptor',
                               'Compiler.ZigAir.Memory.Heap.lookup_ne_of_type_ne'},
        CLONE + 'Installed.query': {ITEM + 'of_members', CLONE + 'key_fields'},
        CLONE + 'Installed.spare_query': {CLONE + 'Installed.query', ITEM + 'append_frame',
                                         ARRAY + 'DescriptorRelation.spare_append', ARRAY + 'Operation.query'},
        CLONE + 'Installed.first_query': {CLONE + 'Installed.query', ITEM + 'append_frame',
                                         ARRAY + 'DescriptorRelation.first_append', ARRAY + 'Operation.query'},
        CLONE + 'QueryTests.installed': {CLONE + 'clone_install',
                                       'Compiler.Extraction.AssemblyItem.Creation.create_verified',
                                       'Compiler.Extraction.AssemblyClone.Physical.run_duplicate'},
        CLONE + 'QueryTests.first_queries': {CLONE + 'Installed.first_query', CLONE + 'QueryTests.installed'},
        CLONE + 'QueryTests.spare_queries': {CLONE + 'Installed.spare_query', CLONE + 'QueryTests.installed'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('clone query lost checked dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    return {'checkedDependencies': sorted(required), 'installedCloneQueryVerified': True,
            'firstAndSpareAppendQueryVerified': True, 'completeGraphCorrespondenceVerified': False}


def bindings(lib):
    return {name: admission.check(lib) for name, admission in (
        ('append', check_representative_array.append_admission),
        ('publication', check_representative_array.publication_admission),
        ('growth', check_representative_array.growth_admission),
        ('capacity', check_representative_array.capacity_admission))}


def controls(output, env, lean):
    # Reuse the source-bound reader and reached-store controls. The composition
    # fixtures are audited and freshly replayed through the creation gate.
    return check_operation_arguments.controls(output, env, lean) + check_representative_array.controls(
        output, env, lean, names={
            'growing-append-bypasses-capacity', 'growing-append-forges-owner-header',
            'reached-fields-rewind-on-rejection', 'publication-rolls-back-fault',
            'initialize-wrong-lifetime', 'initialize-short-slice'})
