"""Audit captured scalar and argument-slice views consumed by scoped hashing.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
SCALAR = 'Compiler.ZigAir.Memory.ScalarBytes.'
AIR = 'Compiler.ZigAir.ScalarBytesAir.'
KEY = 'Compiler.Extraction.ExpressionMap.HashKey.'
BYTES = 'Compiler.Extraction.ExpressionMap.HashBytes.'
GENERATED = 'Compiler.ZigAir.GeneratedExpressionHashBytes.'
STACK = 'Compiler.ZigAir.Memory.StackFrame.'
SLICE = 'Compiler.ZigAir.SliceBytesAir.'
HASH_SLICE = 'Compiler.Extraction.ExpressionMap.HashSlice.'
WORD = 'Compiler.ZigAir.Memory.WordArray.'
SAVED = 'Compiler.ZigAir.AggregateAir.SavedValue.'
SLICE_GENERATED = 'Compiler.ZigAir.GeneratedExpressionHashSlice.'
ORDERED = BYTES + 'Ordered.'
ORDER_GENERATED = 'Compiler.Extraction.ExpressionMap.GeneratedHashOrder.'
CLAIMS = [SCALAR + n for n in ('locate_integer', 'locateField_integer', 'arrayCast_const',
    'readAt_of_load', 'readAt_same_allocation')]
CLAIMS += [AIR + n for n in ('run_cast', 'view_verified')]
CLAIMS += [KEY + n for n in ('layout', 'cells_valid', 'cells_read', 'create_verified',
    'Binding.extend', 'Binding.access', 'Binding.load', 'Binding.select')]
CLAIMS += [BYTES + n for n in ('Field.program_eq', 'Field.fragment_eq', 'Field.value_eq',
    'Field.locate', 'view_verified', 'read_verified', 'argumentBytes_verified', 'inputs_verified',
    'runRaw_verified', 'run_verified')]
CLAIMS += [BYTES + 'Tests.' + n for n in ('initialized_views', 'little_endian_lanes',
    'padding_and_pointer_rejected', 'stale_and_uninitialized_rejected', 'readonly_view',
    'byte_extent_enforced', 'cast_permissions_and_geometry', 'key_allocation_failure')]
CLAIMS += [STACK + 'old_load']
CLAIMS += [SAVED + n for n in ('verified', 'bindings', 'slice_length')]
CLAIMS += [WORD + 'Represents.' + n for n in ('byte_region', 'byte_cast', 'byte_slice', 'byte_offset_zero', 'extend')]
CLAIMS += [SLICE + n for n in ('generated_body', 'branch_steps', 'compare_steps', 'check_steps', 'choose_steps',
    'subtract_zero', 'bounds_zero', 'make_slice', 'construct_steps', 'advance_steps', 'multiply_four',
    'finish_steps', 'nonempty_verified', 'result_typed', 'verified')]
CLAIMS += [HASH_SLICE + n for n in ('view_verified', 'read_verified', 'bytes_verified')]
CLAIMS += ['Compiler.Extraction.ExpressionMap.HashInput.arguments_read_verified',
    'Compiler.ZigAir.AggregateAir.scalar_arithmetic', 'Compiler.ZigAir.AggregateAir.eval_memory']
CLAIMS += [SLICE + 'Tests.' + n for n in ('readonly_subview', 'empty_unused_pointer',
    'first_allocation_failure', 'second_allocation_failure', 'source_geometry_rejected',
    'multiplication_overflow_rejected', 'empty_storage_has_no_heap_capability')]
CLAIMS += [BYTES + 'Tests.' + n for n in ('empty_helper_allocation_history',
    'slice_result_bytes', 'slice_result_requires_initialized_words')]
CLAIMS += [BYTES + n for n in ('field_images', 'ordered_images')]
CLAIMS += [ORDERED + n for n in ('observe_verified', 'updates_verified', 'run_verified')]
CLAIMS += [ORDERED + 'Tests.' + n for n in ('previous_updates_retained', 'failed_view_cleanup',
    'initialization_precedes_invalid_view', 'view_allocation_failure_retains_prefix')]
DEFINITION_NAMES = [SCALAR + n for n in ('locate', 'locateField', 'locateFields', 'arrayCast', 'arrayToSlice', 'readAt', 'read', 'bytes')]
DEFINITION_NAMES += [AIR + n for n in ('byte', 'castProgram', 'viewCode', 'slice')]
DEFINITION_NAMES += [KEY + n for n in ('cells', 'create', 'Binding')]
DEFINITION_NAMES += [BYTES + n for n in ('Field.slot', 'Field.bits', 'Field.value', 'Field.registers', 'Field.program',
    'Field.fragment', 'Field.address', 'Field.slice', 'Field.image', 'view', 'read', 'argumentBytes', 'inputs', 'runRaw', 'run')]
DEFINITION_NAMES += [GENERATED + n + suffix for n in ('kind', 'instruction', 'data', 'sequence') for suffix in ('', 'View')]
DEFINITION_NAMES += [SLICE_GENERATED + n for n in ('arguments', 'argumentsView')]
DEFINITION_NAMES += [SLICE + 'result', SAVED + 'save']
DEFINITION_NAMES += [WORD + 'View.' + n for n in ('readonlySlice', 'byteSlice')]
DEFINITION_NAMES += [HASH_SLICE + n for n in ('view', 'read', 'bytes')]
DEFINITION_NAMES += ['Compiler.ZigAir.AggregateAir.Register.emptyBytes', 'Compiler.ZigAir.AggregateAir.Prim.copy']
DEFINITION_NAMES += [ORDERED + n for n in ('image', 'observe', 'updates', 'finish', 'run')]
DEFINITION_NAMES += [ORDER_GENERATED + n for n in ('inputs', 'run')]
STATEMENT_NAMES = [BYTES + n for n in ('view_verified', 'read_verified', 'inputs_verified', 'runRaw_verified', 'run_verified')]
STATEMENT_NAMES += [SLICE + 'verified', SAVED + 'verified']
STATEMENT_NAMES += [HASH_SLICE + n for n in ('view_verified', 'read_verified', 'bytes_verified')]
STATEMENT_NAMES += [ORDERED + n for n in ('observe_verified', 'updates_verified', 'run_verified')]
STATEMENT_NAMES += [BYTES + 'ordered_images']
# Reviewed exported terms, never populated or changed by acceptance.
DEFINITIONS = {'Compiler.ZigAir.Memory.ScalarBytes.locate': '897bf30e3330cd4166a471a6c6b026f28f16c1d1ad9e4089a8420882f54fbcd1',
 'Compiler.ZigAir.Memory.ScalarBytes.locateField': '321ed966263457cc54c479921dab4f8e23d57f716a81d003fae86c965d5028d5',
 'Compiler.ZigAir.Memory.ScalarBytes.locateFields': '712c70f3bc491f0667f866a3ff6be8613b996e3184f2da4881f8e0f4ae55dcfe',
 'Compiler.ZigAir.Memory.ScalarBytes.arrayCast': '298b8b5ac8880f402cdd1e1ae970b9ab8e217acb73f72dfc024fb59f7ee06180',
 'Compiler.ZigAir.Memory.ScalarBytes.arrayToSlice': 'edee3a3f6bea6fb2d740eab109059c075c49af90763541c7011d6274b84a0cf1',
 'Compiler.ZigAir.Memory.ScalarBytes.readAt': '75de6876f0734e3f92bebf2131ca0a942a6aa11250c4e581743bbaad1a5ae17e',
 'Compiler.ZigAir.Memory.ScalarBytes.read': 'ba634b74fcfdc58bea0e684f9e71ad9b600b4b33f30f3b892ff559abdeeaf962',
 'Compiler.ZigAir.Memory.ScalarBytes.bytes': 'd42a6d1ca45708626897722aca1461f3e3045854ca0e49b9bbec9f4175320610',
 'Compiler.ZigAir.ScalarBytesAir.byte': '7653efe52109c26c81d07f4570ca09610f357612d9c250da9a8ed1bcdfbbd8d1',
 'Compiler.ZigAir.ScalarBytesAir.castProgram': '44da290ba5ef4c0ac1fd15cad6519ea5d4af452af62bd173122d8d4089fc2420',
 'Compiler.ZigAir.ScalarBytesAir.viewCode': '9d067504a017a59c6d5bd729e728a3f89d1443f2b82c2e524462c1d87e1eee54',
 'Compiler.ZigAir.ScalarBytesAir.slice': 'd42aa4cf39cfc202267316fd62a3b15ae1fa7ca1b65dd0c375e9642100f2de14',
 'Compiler.Extraction.ExpressionMap.HashKey.cells': '7b69f61aa2999fa77420d7421b796dad51bed7a1abf9c06daafb63126e6a59ce',
 'Compiler.Extraction.ExpressionMap.HashKey.create': '83eaa6b33b79c44951919fde6ea7a4617e713bf2819e197fc6a65bda479bf710',
 'Compiler.Extraction.ExpressionMap.HashKey.Binding': '82e419469c2d321f05ea05b059bd4d020e839d2f74dab57eb2d9ee924243312f',
 'Compiler.Extraction.ExpressionMap.HashBytes.Field.slot': 'ac742c217b350be0e8d1e0bbb2c097f91294c16661652a3fbdc09e0d9680a9b3',
 'Compiler.Extraction.ExpressionMap.HashBytes.Field.bits': 'a5d6081af7f235e826ddc388dc711d9d2bc5fa38aeae3f1a7b698f4ca9e1667d',
 'Compiler.Extraction.ExpressionMap.HashBytes.Field.value': '3ad5fbe2c039a2b6318f1fcd60a737a51e54ae426c15831151dee54b53951c39',
 'Compiler.Extraction.ExpressionMap.HashBytes.Field.registers': '7d5a5a21181cee42f1458835d4b8780c3b710abc045a53ff09a4e6cd8ad95ded',
 'Compiler.Extraction.ExpressionMap.HashBytes.Field.program': 'cc200a23af44d28d18f0500f95c77a5cd98279942b5f22439ab464f01ae748e4',
 'Compiler.Extraction.ExpressionMap.HashBytes.Field.fragment': '946e317ae1bdd5b24502c684b5206039f604ed31f2105f4bd04cb4e2aa27c27f',
 'Compiler.Extraction.ExpressionMap.HashBytes.Field.address': '4c5b6f19472c9420e788d7018c7f572ca0141b1e3899fef645e1d53febc674ef',
 'Compiler.Extraction.ExpressionMap.HashBytes.Field.slice': 'b1aa8136e9f6d073a0c9f38cfdd9bcc516c6cba915cd83e3533b2c4f2a2d75fb',
 'Compiler.Extraction.ExpressionMap.HashBytes.Field.image': 'e0012de6d5f2005e633f2909f97251dd9f0871ff63877f99524fe604d980de59',
 'Compiler.Extraction.ExpressionMap.HashBytes.view': '19503587f86577316c2087e7087f7c7783aa96d710217f977c26508c45b1dd42',
 'Compiler.Extraction.ExpressionMap.HashBytes.read': 'd47697046b099356e97ab47ce685e7ea8add1223652986975293254ea664594c',
 'Compiler.Extraction.ExpressionMap.HashBytes.argumentBytes': '9d5dc5d4b2d7ce8e4d5e5fb591df09b5cadf5449889be2f9387f09c4dfea3ad2',
 'Compiler.Extraction.ExpressionMap.HashBytes.inputs': 'b50c185adef24d11c31178a89352ab4030351b8cd622976c500ac94ea985881a',
 'Compiler.Extraction.ExpressionMap.HashBytes.runRaw': '2e4c9242bdfe58f94e88403e53e3e74c1ecd0527998e0bd22dda2eadcbca5ec4',
 'Compiler.Extraction.ExpressionMap.HashBytes.run': '2613cc88fe084409adfeebe4905d1c3105c7d583ff20b374185a6c2dbdb983a7',
 'Compiler.ZigAir.GeneratedExpressionHashBytes.kind': 'b222f1e78cdd9e6b9b757e32edba74fbe11cd1f797661301c589f7c148c0c01d',
 'Compiler.ZigAir.GeneratedExpressionHashBytes.kindView': 'd53a86e23f322fea5b945b70682c89375e47b614bcc5aa4a2fad864f1707439a',
 'Compiler.ZigAir.GeneratedExpressionHashBytes.instruction': '24a235021327d95b002534d59457f6e311ff1cf0b553fe95e6cc002c5ad17f35',
 'Compiler.ZigAir.GeneratedExpressionHashBytes.instructionView': '9a03391c682968bbd43fb3a4efed1f6a40b4dff1dce1fbdbc552074625b364e2',
 'Compiler.ZigAir.GeneratedExpressionHashBytes.data': 'b42064b9be8baa783bc7104f377f30fad644d337012017cd5258818ef1cedbf9',
 'Compiler.ZigAir.GeneratedExpressionHashBytes.dataView': '0d125f38becec69a33c9088029b39c9dc1bcad519e8433e9495a0df2f46caa95',
 'Compiler.ZigAir.GeneratedExpressionHashBytes.sequence': '21024e5f07d569b1c381ff7d02aa7e90e5e581dea6c196b7010dc2c67aaa3a0c',
 'Compiler.ZigAir.GeneratedExpressionHashBytes.sequenceView': '54fb6010ee2a35b64ddf1f43e13cc10a154d0ed3e1115ae632d7623f5f9cda5a',
 'Compiler.ZigAir.GeneratedExpressionHashSlice.arguments': '4ddb78639699b5983f2406d5493d7669d6c0c98e1ab5884bf63b4699c979869d',
 'Compiler.ZigAir.GeneratedExpressionHashSlice.argumentsView': 'a4821620f849312a89007c0fce710b3fb1cf44bb439a6768055883369d5d0955',
 'Compiler.ZigAir.SliceBytesAir.result': '0113c77e9b9ea90ddc5a5919f906eb25287b637ce5ac6f46f983bd74947b59cd',
 'Compiler.ZigAir.AggregateAir.SavedValue.save': '016d9fc89273d673e4685e077b72dcc61f569a471eb4e5d0ef8c666fa045a3c3',
 'Compiler.ZigAir.Memory.WordArray.View.readonlySlice': '21c5ab487146740219714f9473c4edc45fa28fdcdd95dcb30f2e82799a9c26f8',
 'Compiler.ZigAir.Memory.WordArray.View.byteSlice': '2ce5293d2e291bf1c90d93551f3ddc72da8ce02b87ddd1ed8f228bb79255fa39',
 'Compiler.Extraction.ExpressionMap.HashSlice.view': 'a203a2fa2d9be8a329d6805787e47659adb911a39d1b37c6002e48ce9c329f5c',
 'Compiler.Extraction.ExpressionMap.HashSlice.read': 'dac15f5c159cc65d43dbac828622edd8f722b36f7f41377497ed95007d68cb78',
 'Compiler.Extraction.ExpressionMap.HashSlice.bytes': '8769ec94e5c9602532258c0e8cbf0b2ed32addd301550a58c5bdaa497896a59c',
 'Compiler.ZigAir.AggregateAir.Register.emptyBytes': 'effa439ad230aca7f14337a42890f896d9162457cd61ec47ae2d01a43c9d56eb',
 'Compiler.ZigAir.AggregateAir.Prim.copy': 'a7c5b598aeb28df1748340306eb2fc1e11e3815b88cbc1c7439c87c5d934190e',
 'Compiler.Extraction.ExpressionMap.HashBytes.Ordered.image': 'd575809e3f3fe3b68ce21da3c9fad24c4e3fba8ef932b9eb97c5ee92b6d3fd5f',
 'Compiler.Extraction.ExpressionMap.HashBytes.Ordered.observe': '51ca05813fc1504c9dd58008bc78f59a306a45178cc075ddf046212900b1dee4',
 'Compiler.Extraction.ExpressionMap.HashBytes.Ordered.updates': '358e88e73108335303fa7ab2943337a16d8699d5755fd467b927233ead4beff4',
 'Compiler.Extraction.ExpressionMap.HashBytes.Ordered.finish': '24e911773591523014cc77126c8b4579dc2ac83ecf346e299d2d1b59585a2393',
 'Compiler.Extraction.ExpressionMap.HashBytes.Ordered.run': '9ad070a99dc59de30a17f4eccac50009360b37f71c3084f30d8187e7cd560e3c',
 'Compiler.Extraction.ExpressionMap.GeneratedHashOrder.inputs': 'ab036bb235dbb1cf11ec8640a776518437c3a97aba756e61dbf7080357e8f367',
 'Compiler.Extraction.ExpressionMap.GeneratedHashOrder.run': '2f0bb376487ec29bbbf8056223ddc9519994d9c5a70b87eae3ad217ee9decba8'}
STATEMENTS = {'Compiler.Extraction.ExpressionMap.HashBytes.view_verified': '5a0be64a0d784033de8fd2c323d9aa03ca1ee47cc5f06b45e20aff1763f9a470',
 'Compiler.Extraction.ExpressionMap.HashBytes.read_verified': 'fe895502d8ae4dafdb0775c45c8b2101c757d71da4851e0f97ee77ae73e0b019',
 'Compiler.Extraction.ExpressionMap.HashBytes.inputs_verified': 'f7014b75275ebb53461042dfdc3512515521b7c3aa6832a368a524fe6f98adac',
 'Compiler.Extraction.ExpressionMap.HashBytes.runRaw_verified': 'a8dbd9cf5828cb7281b4be901f9060dd530f0aa6159296c4894aafb1f855ac49',
 'Compiler.Extraction.ExpressionMap.HashBytes.run_verified': '498aa3faf517f1452df7cbc1d94da7e4ad8e3c77122cc0b60610b41d29f34899',
 'Compiler.ZigAir.AggregateAir.SavedValue.verified': 'a77b09bf8fcd80d89c14b6a93cebe988f76aaf29eb410c12ec6aad1d10a7fde1',
 'Compiler.ZigAir.SliceBytesAir.verified': 'd40f09f2f30942ca1a9844746d639b772b8d24eb546446cee9d6350cab6492c1',
 'Compiler.Extraction.ExpressionMap.HashSlice.view_verified': '592c83aebcdd4c6ee68ebfc34ad45c20583ee7ed8eb61eefdd849a425fd78504',
 'Compiler.Extraction.ExpressionMap.HashSlice.read_verified': '5508ee59b102216ac9e6336e9f01fd2bca3f3db507f54253d5de66301ec87ec8',
 'Compiler.Extraction.ExpressionMap.HashSlice.bytes_verified': '74d6a5cb2387c294442a3f6960034096c45e9d20d23ba52340426549249eb071',
 'Compiler.Extraction.ExpressionMap.HashBytes.ordered_images': '2049875e0cc6d484367d4895ca3e5c51bfae2b1f57d6bd19f2f5a7a3ab1aff45',
 'Compiler.Extraction.ExpressionMap.HashBytes.Ordered.observe_verified': '165e1da519760cb839d557a0c7912acca86489413109c438209cc7de572f6714',
 'Compiler.Extraction.ExpressionMap.HashBytes.Ordered.updates_verified': '73fbde294fabb563ffb6a0f7e6cc3613159cb482d2072b03fdfe2948a5c677be',
 'Compiler.Extraction.ExpressionMap.HashBytes.Ordered.run_verified': 'bdc222a5c554dd6cdc6250f1c32b7d54110ef03b4c184eece81c60cbf37f3079'}


def audit(rows, digest, require):
    indexed = {row['theorem']: row for row in rows}
    dependencies = {
        AIR + 'run_cast': {SCALAR + 'arrayCast_const'},
        AIR + 'view_verified': {AIR + 'run_cast'},
        BYTES + 'view_verified': {AIR + 'view_verified', KEY + 'Binding.select', BYTES + 'Field.fragment_eq'},
        BYTES + 'read_verified': {BYTES + 'view_verified', SCALAR + 'readAt_of_load', KEY + 'Binding.load'},
        SLICE + 'verified': {SLICE + 'generated_body', SLICE + 'choose_steps', SLICE + 'nonempty_verified', SAVED + 'verified'},
        SLICE + 'nonempty_verified': {SAVED + 'verified', SLICE + 'finish_steps', WORD + 'Represents.byte_cast'},
        HASH_SLICE + 'view_verified': {SLICE + 'verified', KEY + 'Binding.select', KEY + 'Binding.load'},
        HASH_SLICE + 'read_verified': {'Compiler.Extraction.ExpressionMap.HashInput.arguments_read_verified'},
        HASH_SLICE + 'bytes_verified': {HASH_SLICE + 'view_verified', HASH_SLICE + 'read_verified', WORD + 'Represents.extend'},
        BYTES + 'argumentBytes_verified': {HASH_SLICE + 'bytes_verified'},
        BYTES + 'inputs_verified': {BYTES + 'read_verified', BYTES + 'argumentBytes_verified'},
        ORDERED + 'observe_verified': {BYTES + 'read_verified', BYTES + 'argumentBytes_verified'},
        ORDERED + 'updates_verified': {ORDERED + 'observe_verified', 'Compiler.Extraction.WyhashUpdate.update_verified',
            STACK + 'install', 'Compiler.ZigAir.Memory.CellFrame.borrow_eq'},
        ORDERED + 'run_verified': {ORDERED + 'updates_verified', 'Compiler.ZigAir.WyhashCallerInit.run_verified',
            'Compiler.Extraction.WyhashHash.run_digest', 'Compiler.Extraction.WyhashMemory.finish_verified'},
        BYTES + 'runRaw_verified': {KEY + 'create_verified', ORDERED + 'run_verified', BYTES + 'ordered_images', STACK + 'old_load'},
        BYTES + 'run_verified': {BYTES + 'runRaw_verified', STACK + 'cleanup_valid', STACK + 'cleanup_heap'},
    }
    for name, required in dependencies.items():
        require(required <= set(indexed[name]['dependencies']), 'hash byte-view connection missing: ' + name)
    require(set(STATEMENTS) == set(STATEMENT_NAMES), 'incomplete hash byte-view statement pins')
    for name, expected in STATEMENTS.items():
        require(digest(indexed[name]['statement']) == expected, 'changed hash byte-view statement: ' + name)
    return {'capturedScalarByteViewsConsumed': True, 'checkedHashByteViewDependencies': sorted(dependencies),
            'argumentSliceHelperTranslated': True, 'capturedArgumentSliceConsumed': True,
            'capturedCallerOrderConsumed': True, 'updateFinalizationBodiesTranslated': False,
            'completeCallerTranslated': False}


def controls(output, env, lean):
    from check_word_swap import ROOT
    from check_zig_air_proofs import mutation_check, kernel_rejection
    from check_zig_air_memory_proofs import without_imports
    from assembly_item_creation_checks import checked_controls

    model = 'import Compiler.ZigAir.MemoryRecordWrites\n'
    model += without_imports((ROOT / 'lean/Compiler/ZigAir/MemoryScalarBytes.lean').read_text()).split('theorem locate_integer (', 1)[0]
    model += '\nend Compiler.ZigAir.Memory.ScalarBytes\n'
    fixture = '''
namespace ByteViewControl
open Compiler.ZigAir.Memory
 deriving instance DecidableEq for Except
 def state : State := ⟨[(0, ⟨64, .scalar (.int false 32), [(0, .scalar (.int false 32 0x1234))], true, true⟩)], 1, 68⟩
 def source : Value := .pointer (.pointer false false (.scalar (.int false 32))) ⟨0, 0⟩
 def array : Value := .pointer (.pointer false false (.array 4 (.scalar (.int false 8)))) ⟨0, 0⟩
end ByteViewControl
open ByteViewControl Compiler.ZigAir.Memory
'''
    expectations = {
        'wrong-byte-lane': 'ScalarBytes.readAt ByteViewControl.state ⟨0, 1⟩ = .ok 0x12',
        'upgraded-permission': 'ScalarBytes.arrayCast ByteViewControl.state true 4 4 source = .error .readOnly',
        'changed-slice-extent': 'ScalarBytes.arrayToSlice array = .ok (.slice (.slice false (.scalar (.int false 8))) ⟨0, 0⟩ 4)',
    }
    positive = ''.join(f'example : {term} := by decide +kernel\n' for term in expectations.values())
    records = [mutation_check(output, 'hash-byte-view-unchanged', model + fixture + positive, True, env, lean)]
    for name, before, after in (
        ('wrong-byte-lane', '256 ^ (address.offset - base)', '256 ^ 0'),
        ('upgraded-permission', 'writable && !mutable', 'false'),
        ('changed-slice-extent', 'Value.slice (.slice writable child) address count', 'Value.slice (.slice writable child) address (count + 1)'),
    ):
        if model.count(before) != 1:
            raise ValueError('missing or ambiguous hash byte-view mutation: ' + name)
        records.append(mutation_check(output, 'hash-byte-view-' + name,
            model.replace(before, after) + fixture + kernel_rejection(expectations[name]), False, env, lean))
    return checked_controls(output, records) + slice_controls(output, env, lean)


def slice_controls(output, env, lean):
    from check_word_swap import ROOT
    from check_zig_air_proofs import mutation_check, kernel_rejection
    from check_zig_air_memory_proofs import without_imports
    from assembly_item_creation_checks import checked_controls

    model = 'import Compiler.ZigAir.AggregateAirTests\nimport Compiler.ZigAir.AggregateCall\n'
    model += without_imports((ROOT / 'lean/Compiler/ZigAir/GeneratedExpressionHashSlice.lean').read_text())
    fixture = '''
namespace SliceViewControl
open Compiler.ZigAir Compiler.ZigAir.Memory
def caller : State := ⟨[(0, ⟨16, .array 3 (.scalar (.int false 32)),
  [(0, .scalar (.int false 32 99)), (4, .scalar (.int false 32 0x12345678)),
   (8, .scalar (.int false 32 0x90abcdef))], false, false⟩)], 1, 28⟩
def run (state : State) (address : Address) (length : Nat) :=
  GeneratedExpressionHashSlice.arguments.run
    [.value (.slice (.slice false (.scalar (.int false 32))) address length)] state
end SliceViewControl
open SliceViewControl Compiler.ZigAir.Memory
'''
    success = '''run caller ⟨0, 4⟩ 2 =
      (.ok (.value (.slice (.slice false (.scalar (.int false 8))) ⟨0, 4⟩ 8)),
       { caller with nextId := 3, nextAddress := 56 })'''
    empty = 'run caller ⟨999, 3⟩ 0 = (.ok .emptyBytes, { caller with nextId := 2, nextAddress := 48 })'
    failure = '''let before := { caller with nextAddress := addressLimit - 24 }
      run before ⟨0, 4⟩ 2 =
        (.error .outOfMemory, { caller with nextId := 2, nextAddress := addressLimit - 8 })'''
    records = [mutation_check(output, 'hash-slice-unchanged', model + fixture +
        ''.join(f'example : {term} := by decide +kernel\n' for term in (success, empty, failure)), True, env, lean)]
    for name, before, after, term in (
        ('wrong-length', '(.constant (.int false 64 (4)))', '(.constant (.int false 64 (8)))', success),
        ('reversed-empty-branch', '.comparison .eq', '.comparison .ne', empty),
        ('wrong-alignment', '.wordByteCast false true 4', '.wordByteCast false true 8', success),
        ('wrong-offset', '.offsetPointer false (.local 38) (.constant (.scalar (.int false 64 (0))))',
            '.offsetPointer false (.local 38) (.constant (.scalar (.int false 64 (4))))', success),
        ('lost-empty-return', '.ret (.constant .emptyBytes)', '.ret (.local 0)', empty),
    ):
        if model.count(before) != 1:
            raise ValueError('missing or ambiguous argument-slice mutation: ' + name)
        records.append(mutation_check(output, 'hash-slice-' + name,
            model.replace(before, after) + fixture + kernel_rejection(term), False, env, lean))
    return checked_controls(output, records)
