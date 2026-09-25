// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Shared Yul helper generation translated from `YulUtilFunctions.cpp`.

const std = @import("std");
const AST = @import("../ast/ast.zig");
const ASTAnnotations = @import("../ast/ast_annotations.zig");
const CompatibilityIdResolver = @import("../ast/compatibility_id_resolver.zig").CompatibilityIdResolver;
const Types = @import("../ast/types.zig");
const TypeBehavior = @import("../ast/types.zig");
const TypeProviderModule = @import("../ast/type_provider.zig");
const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
const DebugSettings = @import("../interface/debug_settings.zig");
const Yul = @import("../../libyul/ast.zig");
const YulName = @import("../../libyul/yul_name.zig").YulName;
const Generated = @import("../../libyul/generated_code.zig");
const CollectorModule = @import("multi_use_yul_function_collector.zig");
const Numeric = @import("../../libsolutil/numeric.zig");
const Keccak256 = @import("../../libsolutil/keccak256.zig");
const FunctionSelector = @import("../../libsolutil/function_selector.zig");
const PanicCode = @import("../../libsolutil/error_codes.zig").PanicCode;
const AsmParser = @import("../../libyul/asm_parser.zig");
const AsmAnalysis = @import("../../libyul/asm_analysis.zig");
const AsmAnalysisInfo = @import("../../libyul/asm_analysis_info.zig").AsmAnalysisInfo;
const EVMDialectModule = @import("../../libyul/backends/evm/evm_dialect.zig");
const Diagnostics = @import("../../liblangutil/diagnostics.zig");

pub const UtilError = @import("../../libyul/utilities.zig").LiteralError || TypeBehavior.BehaviorError || CollectorModule.CollectorError || error{
    UnsupportedType,
    InvalidType,
    StringTooLong,
};

pub const StorageToMemoryABIEncoder = struct {
    context: *anyopaque,
    generate_fn: *const fn (
        *anyopaque,
        *const Types.Type,
        *const Types.Type,
    ) UtilError![]u8,

    pub fn generate(
        self: StorageToMemoryABIEncoder,
        from_type: *const Types.Type,
        to_type: *const Types.Type,
    ) UtilError![]u8 {
        return self.generate_fn(self.context, from_type, to_type);
    }
};

pub const CalldataToMemoryABIDecoder = struct {
    context: *anyopaque,
    generate_fn: *const fn (
        *anyopaque,
        *const Types.Type,
    ) UtilError![]u8,

    pub fn generate(
        self: CalldataToMemoryABIDecoder,
        to_type: *const Types.Type,
    ) UtilError![]u8 {
        return self.generate_fn(self.context, to_type);
    }
};

pub const YulUtilFunctions = struct {
    allocator: std.mem.Allocator,
    type_provider: *TypeProviderModule.TypeProvider,
    compatibility_ids: CompatibilityIdResolver,
    evm_version: EVMVersion,
    revert_strings: DebugSettings.RevertStrings,
    function_collector: *CollectorModule.MultiUseYulFunctionCollector,
    storage_to_memory_abi_encoder: ?StorageToMemoryABIEncoder = null,
    calldata_to_memory_abi_decoder: ?CalldataToMemoryABIDecoder = null,

    pub fn init(
        allocator: std.mem.Allocator,
        type_provider: *TypeProviderModule.TypeProvider,
        compatibility_ids: CompatibilityIdResolver,
        evm_version: EVMVersion,
        revert_strings: DebugSettings.RevertStrings,
        function_collector: *CollectorModule.MultiUseYulFunctionCollector,
    ) YulUtilFunctions {
        return .{
            .allocator = allocator,
            .type_provider = type_provider,
            .compatibility_ids = compatibility_ids,
            .evm_version = evm_version,
            .revert_strings = revert_strings,
            .function_collector = function_collector,
        };
    }

    pub fn identityFunction(self: *YulUtilFunctions) UtilError![]u8 {
        return self.collectTemplate(
            "identity",
            "\nfunction identity(value) -> ret {\nret := value\n}\n",
        );
    }

    pub fn combineExternalFunctionIdFunction(self: *YulUtilFunctions) UtilError![]u8 {
        const name = "combine_external_function_id";
        if (!(try self.function_collector.beginFunction(name))) return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const shift_32 = try self.shiftLeftFunction(32);
        defer self.allocator.free(shift_32);
        const shift_64 = try self.shiftLeftFunction(64);
        defer self.allocator.free(shift_64);
        const generator = try self.function_collector.generator(self.evm_version);
        try self.function_collector.finishGeneratedFunction(name, try generator.functionDefinition(
            "\nfunction @0(addr, selector) -> combined {\ncombined := @1(or(@2(addr), and(selector, 0xffffffff)))\n}\n",
            .{ name, shift_64, shift_32 },
        ));
        return self.function_collector.copyFunctionName(name);
    }

    pub fn splitExternalFunctionIdFunction(self: *YulUtilFunctions) UtilError![]u8 {
        const name = "split_external_function_id";
        if (!(try self.function_collector.beginFunction(name))) return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        // Preserve dependency request order even though shift_64 occurs first.
        const shift_32 = try self.shiftRightFunction(32);
        defer self.allocator.free(shift_32);
        const shift_64 = try self.shiftRightFunction(64);
        defer self.allocator.free(shift_64);
        const generator = try self.function_collector.generator(self.evm_version);
        try self.function_collector.finishGeneratedFunction(name, try generator.functionDefinition(
            "\nfunction @0(combined) -> addr, selector {\ncombined := @1(combined)\nselector := and(combined, 0xffffffff)\naddr := @2(combined)\n}\n",
            .{ name, shift_64, shift_32 },
        ));
        return self.function_collector.copyFunctionName(name);
    }

    pub fn copyToMemoryFunction(self: *YulUtilFunctions, from_calldata: bool, cleanup: bool) UtilError![]u8 {
        const name = try std.fmt.allocPrint(self.allocator, "copy_{s}_to_memory{s}", .{ if (from_calldata) "calldata" else "memory", if (cleanup) "_with_cleanup" else "" });
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name))) return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const generator = try self.function_collector.generator(self.evm_version);
        var body: Generated.Buffer = .{ .generator = generator };
        if (from_calldata) {
            try body.add("calldatacopy(dst, src, length)\n", .{});
        } else if (self.evm_version.hasMcopy()) {
            try body.add("mcopy(dst, src, length)\n", .{});
        } else {
            try body.add("let i := 0\nfor { } lt(i, length) { i := add(i, 32) }\n{\nmstore(add(dst, i), mload(add(src, i)))\n}\n", .{});
        }
        if (cleanup) try body.add("mstore(add(dst, length), 0)\n", .{});
        try self.function_collector.finishGeneratedFunction(name, try generator.functionDefinition(
            "\nfunction @0(src, dst, length) {\n@1}\n",
            .{ name, body.take() },
        ));
        return self.function_collector.copyFunctionName(name);
    }

    pub fn storeLiteralInMemoryFunction(
        self: *YulUtilFunctions,
        literal: []const u8,
    ) UtilError![]u8 {
        const digest = Keccak256.keccak256(literal);
        const digest_hex = digest.hex();
        const name = try std.fmt.allocPrint(
            self.allocator,
            "store_literal_in_memory_{s}",
            .{&digest_hex},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);

        const generator = try self.function_collector.generator(self.evm_version);
        var stores: Generated.Buffer = .{ .generator = generator };
        var offset: usize = 0;
        while (offset < literal.len) : (offset += 32) {
            const chunk = literal[offset..@min(literal.len, offset + 32)];
            const word = try generator.word(
                chunk,
            );

            try stores.add(
                "mstore(add(memPtr, @0), @1)\n",
                .{ offset, word },
            );
        }
        const code = try generator.functionDefinition(
            "\nfunction @0(memPtr) {\n@1}\n",
            .{ name, stores.take() },
        );

        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn copyLiteralToMemoryFunction(
        self: *YulUtilFunctions,
        literal: []const u8,
    ) UtilError![]u8 {
        const digest = Keccak256.keccak256(literal);
        const digest_hex = digest.hex();
        const name = try std.fmt.allocPrint(
            self.allocator,
            "copy_literal_to_memory_{s}",
            .{&digest_hex},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const allocate = try self.allocateMemoryArrayFunction(
            self.type_provider.stringMemory(),
        );
        defer self.allocator.free(allocate);
        const store = try self.storeLiteralInMemoryFunction(literal);
        defer self.allocator.free(store);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0() -> memPtr {\nmemPtr := @1(@2)\n@3(add(memPtr, 32))\n}\n",
            .{ name, allocate, literal.len, store },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn copyLiteralToStorageFunction(
        self: *YulUtilFunctions,
        literal: []const u8,
    ) UtilError![]u8 {
        const digest = Keccak256.keccak256(literal);
        const digest_hex = digest.hex();
        const name = try std.fmt.allocPrint(
            self.allocator,
            "copy_literal_to_storage_{s}",
            .{&digest_hex},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const bytes_storage = self.type_provider.bytesStorage();
        const byte_length = try self.extractByteArrayLengthFunction();
        defer self.allocator.free(byte_length);
        const cleanup = try self.cleanUpDynamicByteArrayEndSlotsFunction(bytes_storage);
        defer self.allocator.free(cleanup);
        const generator = try self.function_collector.generator(self.evm_version);
        var body: Generated.Buffer = .{ .generator = generator };
        try body.add(
            "let oldLen := @0(sload(slot))\n@1(slot, oldLen, @2)\n",
            .{ byte_length, cleanup, literal.len },
        );
        if (literal.len >= 32) {
            const data_area = try self.arrayDataAreaFunction(bytes_storage);
            defer self.allocator.free(data_area);
            try body.add(
                "sstore(slot, @0)\nlet dstPtr := @1(slot)\n",
                .{ 2 * literal.len + 1, data_area },
            );
            var offset: usize = 0;
            while (offset < literal.len) : (offset += 32) {
                const word = try generator.word(
                    literal[offset..@min(literal.len, offset + 32)],
                );

                try body.add(
                    "sstore(add(dstPtr, @0), @1)\n",
                    .{ offset / 32, word },
                );
            }
        } else {
            const word = try generator.word(
                literal,
            );

            try body.add(
                "sstore(slot, add(@0, @1))\n",
                .{ word, 2 * literal.len },
            );
        }
        const code = try generator.functionDefinition(
            "\nfunction @0(slot) {\n@1}\n",
            .{ name, body.take() },
        );

        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn leftAlignFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "leftAlign_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);

        const generator = try self.function_collector.generator(self.evm_version);
        const body = switch (type_ref.payload) {
            .Address => blk: {
                const uint160 = Types.Type{ .payload = .{ .Integer = .{
                    .bits = 160,
                    .modifier = .Unsigned,
                } } };
                const nested = try self.leftAlignFunction(&uint160);
                defer self.allocator.free(nested);
                break :blk try generator.statements(
                    "aligned := @0(value)",
                    .{nested},
                );
            },
            .Integer => |integer| if (integer.bits == 256)
                try generator.statements("aligned := value", .{})
            else blk: {
                const shift = try self.shiftLeftFunction(256 - integer.bits);
                defer self.allocator.free(shift);
                break :blk try generator.statements(
                    "aligned := @0(value)",
                    .{shift},
                );
            },
            .Bool, .Enum => blk: {
                const uint8 = Types.Type{ .payload = .{ .Integer = .{
                    .bits = 8,
                    .modifier = .Unsigned,
                } } };
                const nested = try self.leftAlignFunction(&uint8);
                defer self.allocator.free(nested);
                break :blk try generator.statements(
                    "aligned := @0(value)",
                    .{nested},
                );
            },
            .FixedBytes => try generator.statements("aligned := value", .{}),
            .Contract => blk: {
                const address = Types.Type{ .payload = .{ .Address = .{
                    .state_mutability = .NonPayable,
                } } };
                const nested = try self.leftAlignFunction(&address);
                defer self.allocator.free(nested);
                break :blk try generator.statements(
                    "aligned := @0(value)",
                    .{nested},
                );
            },
            .UserDefinedValueType => |value| blk: {
                const nested = try self.leftAlignFunction(
                    value.underlying_type orelse return error.InvalidType,
                );
                defer self.allocator.free(nested);
                break :blk try generator.statements(
                    "aligned := @0(value)",
                    .{nested},
                );
            },
            else => return error.UnsupportedType,
        };
        const code = try generator.functionDefinition(
            "\nfunction @0(value) -> aligned {\n@1\n}\n",
            .{ name, body },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn arrayLengthFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        const array = type_ref.asArray() orelse return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "array_length_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);

        const generator = try self.function_collector.generator(self.evm_version);
        var parameters: []const []const u8 = &.{"value"};
        const body = if (!array.isDynamicallySized()) blk: {
            const length = try compactHex(self.allocator, array.length.?);
            defer self.allocator.free(length);
            break :blk try generator.statements(
                "length := @0",
                .{try generator.numberToken(length)},
            );
        } else switch (array.reference.location) {
            .Memory => try generator.statements("length := mload(value)", .{}),
            .Storage => if (array.isByteArrayOrString()) blk: {
                const extract = try self.extractByteArrayLengthFunction();
                defer self.allocator.free(extract);
                break :blk try generator.statements(
                    "length := sload(value)\nlength := @0(length)",
                    .{extract},
                );
            } else try generator.statements("length := sload(value)", .{}),
            .CallData => blk: {
                parameters = &.{ "value", "len" };
                break :blk try generator.statements("length := len", .{});
            },
            .Transient => return error.UnsupportedType,
        };
        const code = try generator.functionDefinition(
            "\nfunction @0(@1) -> length {\n@2\n}\n",
            .{ name, parameters, body },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn extractByteArrayLengthFunction(
        self: *YulUtilFunctions,
    ) UtilError![]u8 {
        const name = "extract_byte_array_length";
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const panic = try self.panicFunction(.storage_encoding_error);
        defer self.allocator.free(panic);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0(data) -> length {\nlength := div(data, 2)\nlet outOfPlaceEncoding := and(data, 1)\nif iszero(outOfPlaceEncoding) {\nlength := and(length, 0x7f)\n}\n\nif eq(outOfPlaceEncoding, lt(length, 32)) {\n@1()\n}\n}\n",
            .{ name, panic },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn arrayAllocationSizeFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        const array = type_ref.asArray() orelse return error.InvalidType;
        if (array.reference.location != .Memory) return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "array_allocation_size_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const panic = try self.panicFunction(.resource_error);
        defer self.allocator.free(panic);
        const round_up = try self.roundUpFunction();
        defer self.allocator.free(round_up);
        const generator = try self.function_collector.generator(self.evm_version);
        var body: Generated.Buffer = .{ .generator = generator };
        try body.add(
            "if gt(length, 0xffffffffffffffff) { @0() }\n",
            .{panic},
        );
        if (array.isByteArrayOrString())
            try body.add("size := @0(length)\n", .{round_up})
        else
            try body.add("size := mul(length, 0x20)\n", .{});
        if (array.isDynamicallySized())
            try body.add("size := add(size, 0x20)\n", .{});
        const code = try generator.functionDefinition(
            "\nfunction @0(length) -> size {\n// Make sure we can allocate memory without overflow\n@1}\n",
            .{ name, body.take() },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn arrayDataAreaFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        const array = type_ref.asArray() orelse return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "array_dataslot_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const generator = try self.function_collector.generator(self.evm_version);
        var dynamic_body: Yul.Block = .{};
        if (array.isDynamicallySized()) dynamic_body = switch (array.reference.location) {
            .Memory => try generator.statements("data := add(ptr, 0x20)\n", .{}),
            .Storage => try generator.statements("mstore(0, ptr)\ndata := keccak256(0, 0x20)\n", .{}),
            .CallData => try generator.statements("", .{}),
            .Transient => return error.UnsupportedType,
        };
        const code = try generator.functionDefinition(
            "\nfunction @0(ptr) -> data {\ndata := ptr\n@1}\n",
            .{ name, dynamic_body },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn arrayConvertLengthToSize(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        const array = switch (type_ref.payload) {
            .Array => |value| value,
            else => return error.InvalidType,
        };
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "array_convert_length_to_size_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const generator = try self.function_collector.generator(self.evm_version);
        const body = switch (array.reference.location) {
            .Storage => blk: {
                const storage_bytes = try TypeBehavior.storageBytes(array.base_type);
                if (storage_bytes == 0 or storage_bytes > 32)
                    return error.InvalidType;
                const storage_size = try TypeBehavior.storageSize(array.base_type);
                const multiply = try self.overflowCheckedIntMulFunction(
                    self.type_provider.uint256().payload.Integer,
                );
                defer self.allocator.free(multiply);
                if (storage_size > 1) {
                    break :blk try generator.statements(
                        "size := length\nsize := @0(@1, length)",
                        .{ multiply, storage_size },
                    );
                }
                break :blk try generator.statements(
                    "size := length\nsize := div(add(length, sub(@0, 1)), @1)",
                    .{ 32 / storage_bytes, 32 / storage_bytes },
                );
            },
            .Memory, .CallData => blk: {
                const stride = if (array.reference.location == .Memory)
                    try TypeBehavior.memoryStride(array)
                else
                    try TypeBehavior.calldataStride(array);
                const multiply = try self.overflowCheckedIntMulFunction(
                    self.type_provider.uint256().payload.Integer,
                );
                defer self.allocator.free(multiply);
                if (array.isByteArrayOrString())
                    break :blk try generator.statements("size := length", .{});
                break :blk try generator.statements(
                    "size := @0(length, @1)",
                    .{ multiply, stride },
                );
            },
            .Transient => return error.UnsupportedTransientReference,
        };
        const code = try generator.functionDefinition(
            "\nfunction @0(length) -> size {\n@1\n}\n",
            .{ name, body },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn longByteArrayStorageIndexAccessNoCheckFunction(
        self: *YulUtilFunctions,
    ) UtilError![]u8 {
        const name = "long_byte_array_index_access_no_checks";
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const data_area = try self.arrayDataAreaFunction(self.type_provider.bytesStorage());
        defer self.allocator.free(data_area);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0(array, index) -> slot, offset {\noffset := sub(31, mod(index, 0x20))\nlet dataArea := @1(array)\nslot := add(dataArea, div(index, 0x20))\n}\n",
            .{ name, data_area },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn storageArrayIndexAccessFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        const array = switch (type_ref.payload) {
            .Array => |value| value,
            else => return error.InvalidType,
        };
        if (array.reference.location != .Storage) return error.InvalidType;
        const storage_bytes = try TypeBehavior.storageBytes(array.base_type);
        if (storage_bytes == 0 or storage_bytes > 32) return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "storage_array_index_access_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const panic = try self.panicFunction(.array_out_of_bounds);
        defer self.allocator.free(panic);
        // Preserve the upstream Whiskers binding order: panic is registered
        // before arrayLen.
        const length = try self.arrayLengthFunction(type_ref);
        defer self.allocator.free(length);
        const data_area = try self.arrayDataAreaFunction(type_ref);
        defer self.allocator.free(data_area);
        const no_checks = try self.longByteArrayStorageIndexAccessNoCheckFunction();
        defer self.allocator.free(no_checks);
        const generator = try self.function_collector.generator(self.evm_version);
        var body: Generated.Buffer = .{ .generator = generator };
        try body.add(
            "let arrayLength := @0(array)\nif iszero(lt(index, arrayLength)) { @1() }\n",
            .{ length, panic },
        );
        if (storage_bytes <= 16) {
            if (array.isByteArrayOrString()) {
                try body.add(
                    "switch lt(arrayLength, 0x20)\ncase 0 { slot, offset := @0(array, index) }\ndefault { offset := sub(31, mod(index, 0x20)) slot := array }\n",
                    .{no_checks},
                );
            } else {
                const items_per_slot = 32 / storage_bytes;
                try body.add(
                    "let dataArea := @0(array)\nslot := add(dataArea, div(index, @1))\noffset := mul(mod(index, @2), @3)\n",
                    .{ data_area, items_per_slot, items_per_slot, storage_bytes },
                );
            }
        } else {
            const storage_size = try TypeBehavior.storageSize(array.base_type);
            try body.add(
                "let dataArea := @0(array)\nslot := add(dataArea, mul(index, @1))\noffset := 0\n",
                .{ data_area, storage_size },
            );
        }
        const code = try generator.functionDefinition(
            "\nfunction @0(array, index) -> slot, offset {\n@1}\n",
            .{ name, body.take() },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn memoryArrayIndexAccessFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        const array = switch (type_ref.payload) {
            .Array => |value| value,
            else => return error.InvalidType,
        };
        if (array.reference.location != .Memory) return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "memory_array_index_access_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const panic = try self.panicFunction(.array_out_of_bounds);
        defer self.allocator.free(panic);
        const length = try self.arrayLengthFunction(type_ref);
        defer self.allocator.free(length);
        const stride = try TypeBehavior.memoryStride(array);
        const generator = try self.function_collector.generator(self.evm_version);
        const dynamic_adjustment = if (array.isDynamicallySized())
            try generator.statements("offset := add(offset, 32)", .{})
        else
            Yul.Block{};
        const code = try generator.functionDefinition(
            "\nfunction @0(baseRef, index) -> addr {\nif iszero(lt(index, @1(baseRef))) { @2() }\nlet offset := mul(index, @3)\n@4\naddr := add(baseRef, offset)\n}\n",
            .{ name, length, panic, stride, dynamic_adjustment },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn calldataArrayIndexAccessFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        const array = switch (type_ref.payload) {
            .Array => |value| value,
            else => return error.InvalidType,
        };
        if (array.reference.location != .CallData) return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "calldata_array_index_access_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const panic = try self.panicFunction(.array_out_of_bounds);
        defer self.allocator.free(panic);
        const stride = try TypeBehavior.calldataStride(array);
        const static_length = if (array.length) |value|
            try compactHex(self.allocator, value)
        else
            try self.allocator.alloc(u8, 0);
        defer self.allocator.free(static_length);
        const generator = try self.function_collector.generator(self.evm_version);
        const parameters: []const []const u8 = if (array.isDynamicallySized()) &.{ "base_ref", "length", "index" } else &.{ "base_ref", "index" };
        const bound = if (array.isDynamicallySized()) try generator.identifier("length") else try generator.numberToken(static_length);
        const dynamic_base = TypeBehavior.isDynamicallyEncoded(array.base_type);
        const dynamic_length = TypeBehavior.isDynamicallySized(array.base_type);
        const returns: []const []const u8 = if (dynamic_length) &.{ "addr", "len" } else &.{"addr"};
        const tail = if (dynamic_base) blk: {
            const access = try self.accessCalldataTailFunction(array.base_type);
            defer self.allocator.free(access);
            break :blk try generator.statements("@0 := @1(base_ref, addr)", .{ returns, access });
        } else Yul.Block{};
        const code = try generator.functionDefinition(
            "\nfunction @0(@1) -> @2 {\nif iszero(lt(index, @3)) { @4() }\naddr := add(base_ref, mul(index, @5))\n@6\n}\n",
            .{ name, parameters, returns, bound, panic, stride, tail },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn calldataArrayIndexRangeAccess(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        const array = switch (type_ref.payload) {
            .Array => |value| value,
            else => return error.InvalidType,
        };
        if (array.reference.location != .CallData or !array.isDynamicallySized())
            return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "calldata_array_index_range_access_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const start_error = try self.revertReasonIfDebugFunction("Slice starts after end");
        defer self.allocator.free(start_error);
        const length_error = try self.revertReasonIfDebugFunction("Slice is greater than length");
        defer self.allocator.free(length_error);
        const stride = try TypeBehavior.calldataStride(array);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0(offset, length, startIndex, endIndex) -> offsetOut, lengthOut {\nif gt(startIndex, endIndex) { @1() }\nif gt(endIndex, length) { @2() }\noffsetOut := add(offset, mul(startIndex, @3))\nlengthOut := sub(endIndex, startIndex)\n}\n",
            .{ name, start_error, length_error, stride },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn accessCalldataTailFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        if (!TypeBehavior.isDynamicallyEncoded(type_ref) or
            !TypeBehavior.dataStoredIn(type_ref, .CallData))
            return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "access_calldata_tail_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const needed_length = try TypeBehavior.calldataEncodedTailSize(type_ref);
        const needed_length_text = try compactHex(self.allocator, needed_length);
        defer self.allocator.free(needed_length_text);
        const dynamic = TypeBehavior.isDynamicallySized(type_ref);
        const stride: u32 = if (dynamic)
            try TypeBehavior.calldataStride(type_ref.payload.Array)
        else
            0;
        const bad_offset = try self.revertReasonIfDebugFunction("Invalid calldata tail offset");
        defer self.allocator.free(bad_offset);
        const bad_length = try self.revertReasonIfDebugFunction("Invalid calldata tail length");
        defer self.allocator.free(bad_length);
        const short_tail = try self.revertReasonIfDebugFunction("Calldata tail too short");
        defer self.allocator.free(short_tail);
        const generator = try self.function_collector.generator(self.evm_version);
        const dynamic_body = if (dynamic)
            try generator.statements(
                "length := calldataload(addr)\nif gt(length, 0xffffffffffffffff) { @0() }\naddr := add(addr, 32)\nif sgt(addr, sub(calldatasize(), mul(length, @1))) { @2() }",
                .{ bad_length, stride, short_tail },
            )
        else
            Yul.Block{};
        const code = try generator.functionDefinition(
            "\nfunction @0(base_ref, ptr_to_tail) -> @1 {\nlet rel_offset_of_tail := calldataload(ptr_to_tail)\nif iszero(slt(rel_offset_of_tail, sub(sub(calldatasize(), base_ref), sub(@2, 1)))) { @3() }\naddr := add(base_ref, rel_offset_of_tail)\n@4\n}\n",
            .{ name, @as([]const []const u8, if (dynamic) &.{ "addr", "length" } else &.{"addr"}), try generator.numberToken(needed_length_text), bad_offset, dynamic_body },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn nextArrayElementFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        const array = type_ref.asArray() orelse return error.InvalidType;
        if (array.isByteArrayOrString()) return error.InvalidType;
        const advance_value: u256 = switch (array.reference.location) {
            .Memory => 32,
            .Storage => blk: {
                if (try TypeBehavior.storageBytes(array.base_type) <= 16)
                    return error.InvalidType;
                break :blk try TypeBehavior.storageSize(array.base_type);
            },
            .CallData => try TypeBehavior.calldataStride(array.*),
            .Transient => return error.UnsupportedType,
        };
        const advance = try compactHex(self.allocator, advance_value);
        defer self.allocator.free(advance);
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "array_nextElement_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0(ptr) -> next {\nnext := add(ptr, @1)\n}\n",
            .{ name, try generator.numberToken(advance) },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn copyArrayFromStorageToMemoryFunction(
        self: *YulUtilFunctions,
        from_type: *const Types.Type,
        to_type: *const Types.Type,
    ) UtilError![]u8 {
        const from = from_type.asArray() orelse return error.InvalidType;
        const to = to_type.asArray() orelse return error.InvalidType;
        if (from.reference.location != .Storage or to.reference.location != .Memory or
            from.isDynamicallySized() != to.isDynamicallySized() or
            (!from.isDynamicallySized() and from.length.? != to.length.?))
            return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, from_type);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "copy_array_from_storage_to_memory_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (try self.function_collector.beginFunction(name)) {
            errdefer self.function_collector.abortFunction(name);
            const generator = try self.function_collector.generator(self.evm_version);
            const code = if (TypeBehavior.isValueType(from.base_type)) value: {
                if (!TypeBehavior.equals(from.base_type, to.base_type))
                    return error.InvalidType;
                if (self.storage_to_memory_abi_encoder) |provider| {
                    const allocate = try self.allocateUnboundedFunction();
                    defer self.allocator.free(allocate);
                    const encode = try provider.generate(from_type, to_type);
                    defer self.allocator.free(encode);
                    const finalize = try self.finalizeAllocationFunction();
                    defer self.allocator.free(finalize);
                    break :value try generator.functionDefinition(
                        "\nfunction @0(slot) -> memPtr {\nmemPtr := @1()\nlet end := @2(slot, memPtr)\n@3(memPtr, sub(end, memPtr))\n}\n",
                        .{ name, allocate, encode, finalize },
                    );
                }

                // Standalone helper tests do not own an ABI provider. Keep the
                // structurally equivalent fallback local to that environment;
                // production IR contexts always take the upstream ABI path.
                const length = try self.arrayLengthFunction(from_type);
                defer self.allocator.free(length);
                const allocate = try self.allocateMemoryArrayFunction(to_type);
                defer self.allocator.free(allocate);
                const index = try self.storageArrayIndexAccessFunction(from_type);
                defer self.allocator.free(index);
                const read = try self.readFromStorageDynamic(
                    from.base_type,
                    true,
                    .Unspecified,
                );
                defer self.allocator.free(read);
                const write = try self.writeToMemoryFunction(to.base_type);
                defer self.allocator.free(write);
                const stack_size = try TypeBehavior.sizeOnStack(from.base_type);
                const values = try generator.indexedNames("item_", stack_size);

                const memory_stride = try TypeBehavior.memoryStride(to.*);
                break :value try generator.functionDefinition(
                    \\function @0(slot) -> memPtr {
                    \\    let length := @1(slot)
                    \\    memPtr := @2(length)
                    \\    let mpos := memPtr
                    \\    @3
                    \\    for { let i := 0 } lt(i, length) { i := add(i, 1) } {
                    \\        let itemSlot, itemOffset := @4(slot, i)
                    \\        let @5 := @6(itemSlot, itemOffset)
                    \\        @7(mpos, @8)
                    \\        mpos := add(mpos, @9)
                    \\    }
                    \\}
                , .{
                    name,
                    length,
                    allocate,
                    if (to.isDynamicallySized()) try generator.statements("mpos := add(mpos, 0x20)", .{}) else Yul.Block{},
                    index,
                    values,
                    read,
                    write,
                    values,
                    memory_stride,
                });
            } else reference: {
                if (from.isByteArrayOrString() or
                    try TypeBehavior.memoryStride(to.*) != 32 or
                    !TypeBehavior.dataStoredIn(to.base_type, .Memory) or
                    !TypeBehavior.dataStoredIn(from.base_type, .Storage))
                    return error.InvalidType;
                const length = try self.arrayLengthFunction(from_type);
                defer self.allocator.free(length);
                const allocate = try self.allocateMemoryArrayFunction(to_type);
                defer self.allocator.free(allocate);
                const data_area = try self.arrayDataAreaFunction(from_type);
                defer self.allocator.free(data_area);
                const conversion = try self.conversionFunction(
                    from.base_type,
                    to.base_type,
                );
                defer self.allocator.free(conversion);
                const storage_size = try TypeBehavior.storageSize(from.base_type);
                break :reference try generator.functionDefinition(
                    \\function @0(slot) -> memPtr {
                    \\    let length := @1(slot)
                    \\    memPtr := @2(length)
                    \\    let mpos := memPtr
                    \\    @3
                    \\    let spos := @4(slot)
                    \\    for { let i := 0 } lt(i, length) { i := add(i, 1) } {
                    \\        mstore(mpos, @5(spos))
                    \\        mpos := add(mpos, 0x20)
                    \\        spos := add(spos, @6)
                    \\    }
                    \\}
                , .{
                    name,
                    length,
                    allocate,
                    if (to.isDynamicallySized()) try generator.statements("mpos := add(mpos, 0x20)", .{}) else Yul.Block{},
                    data_area,
                    conversion,
                    storage_size,
                });
            };

            try self.function_collector.finishGeneratedFunction(name, code);
        }
        return self.function_collector.copyFunctionName(name);
    }

    pub fn copyArrayToStorageFunction(
        self: *YulUtilFunctions,
        from_type: *const Types.Type,
        to_type: *const Types.Type,
    ) UtilError![]u8 {
        const from = from_type.asArray() orelse return error.InvalidType;
        const to = to_type.asArray() orelse return error.InvalidType;
        if (to.reference.location != .Storage) return error.InvalidType;
        if (!to.isDynamicallySized() and
            (from.isDynamicallySized() or from.length.? > to.length.?))
            return error.InvalidType;
        if (from.isByteArrayOrString())
            return self.copyByteArrayToStorageFunction(from_type, to_type);
        if (TypeBehavior.isValueType(to.base_type))
            return self.copyValueArrayToStorageFunction(from_type, to_type);
        if (try TypeBehavior.storageStride(to.*) != 32 or
            TypeBehavior.isValueType(from.base_type))
            return error.InvalidType;

        const from_identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, from_type);
        defer self.allocator.free(from_identifier);
        const to_identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, to_type);
        defer self.allocator.free(to_identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "copy_array_to_storage_from_{s}_to_{s}",
            .{ from_identifier, to_identifier },
        );
        defer self.allocator.free(name);
        if (try self.function_collector.beginFunction(name)) {
            errdefer self.function_collector.abortFunction(name);
            const from_calldata = from.reference.location == .CallData;
            const from_memory = from.reference.location == .Memory;
            const from_storage = from.reference.location == .Storage;
            if (!from_calldata and !from_memory and !from_storage)
                return error.InvalidType;
            const dynamic_calldata = from_calldata and from.isDynamicallySized();
            const length = try self.arrayLengthFunction(from_type);
            defer self.allocator.free(length);
            const resize = try self.resizeArrayFunction(to_type);
            defer self.allocator.free(resize);
            const src_data = try self.arrayDataAreaFunction(from_type);
            defer self.allocator.free(src_data);
            const dst_data = try self.arrayDataAreaFunction(to_type);
            defer self.allocator.free(dst_data);
            const generator = try self.function_collector.generator(self.evm_version);
            const stack_size = try TypeBehavior.sizeOnStack(from.base_type);
            const stack_items = try generator.indexedNames(
                "stackItem_",
                stack_size,
            );

            const update = try self.updateStorageValueFunction(
                from.base_type,
                to.base_type,
                0,
            );
            defer self.allocator.free(update);
            const source_read = if (from_calldata) calldata: {
                if (TypeBehavior.isDynamicallyEncoded(from.base_type)) {
                    const access = try self.accessCalldataTailFunction(from.base_type);
                    defer self.allocator.free(access);
                    break :calldata try generator.statements(
                        "let @0 := @1(value, srcPtr)",
                        .{ stack_items, access },
                    );
                }
                break :calldata try generator.statements(
                    "let @0 := srcPtr",
                    .{stack_items},
                );
            } else if (from_memory) memory: {
                const read = try self.readFromMemoryOrCalldata(
                    from.base_type,
                    false,
                );
                defer self.allocator.free(read);
                break :memory try generator.statements(
                    "let @0 := @1(srcPtr)",
                    .{ stack_items, read },
                );
            } else try generator.statements(
                "let @0 := srcPtr",
                .{stack_items},
            );

            const src_stride: u256 = if (from_calldata)
                try TypeBehavior.calldataStride(from.*)
            else if (from_memory)
                try TypeBehavior.memoryStride(from.*)
            else
                try TypeBehavior.storageSize(from.base_type);
            const destination_size = try TypeBehavior.storageSize(to.base_type);
            const len_name = try generator.name("len");
            const len_names: []const YulName = if (dynamic_calldata) &.{len_name} else &.{};
            const code = try generator.functionDefinition(
                \\function @0(slot, value, @1) {
                \\    @2
                \\    let length := @3(value, @4)
                \\    @5(slot, length)
                \\    let srcPtr := @6(value)
                \\    let elementSlot := @7(slot)
                \\    for { let i := 0 } lt(i, length) { i := add(i, 1) } {
                \\        @8
                \\        @9(elementSlot, @10)
                \\        srcPtr := add(srcPtr, @11)
                \\        elementSlot := add(elementSlot, @12)
                \\    }
                \\}
            , .{
                name,
                len_names,
                if (from_storage) try generator.statements("if eq(slot, value) { leave }", .{}) else Yul.Block{},
                length,
                len_names,
                resize,
                src_data,
                dst_data,
                source_read,
                update,
                stack_items,
                src_stride,
                destination_size,
            });

            try self.function_collector.finishGeneratedFunction(name, code);
        }
        return self.function_collector.copyFunctionName(name);
    }

    pub fn copyByteArrayToStorageFunction(
        self: *YulUtilFunctions,
        from_type: *const Types.Type,
        to_type: *const Types.Type,
    ) UtilError![]u8 {
        const from = from_type.asArray() orelse return error.InvalidType;
        const to = to_type.asArray() orelse return error.InvalidType;
        if (!from.isByteArrayOrString() or !to.isByteArrayOrString() or
            to.reference.location != .Storage)
            return error.InvalidType;
        const from_identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, from_type);
        defer self.allocator.free(from_identifier);
        const to_identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, to_type);
        defer self.allocator.free(to_identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "copy_byte_array_to_storage_from_{s}_to_{s}",
            .{ from_identifier, to_identifier },
        );
        defer self.allocator.free(name);
        if (try self.function_collector.beginFunction(name)) {
            errdefer self.function_collector.abortFunction(name);
            const from_storage = from.reference.location == .Storage;
            const from_calldata = from.reference.location == .CallData;
            const from_memory = from.reference.location == .Memory;
            if (!from_storage and !from_calldata and !from_memory)
                return error.InvalidType;
            const length = try self.arrayLengthFunction(from_type);
            defer self.allocator.free(length);
            const panic = try self.panicFunction(.resource_error);
            defer self.allocator.free(panic);
            const byte_length = try self.extractByteArrayLengthFunction();
            defer self.allocator.free(byte_length);
            const destination_data = try self.arrayDataAreaFunction(to_type);
            defer self.allocator.free(destination_data);
            const source_data = if (from_storage)
                try self.arrayDataAreaFunction(from_type)
            else
                try self.allocator.alloc(u8, 0);
            defer self.allocator.free(source_data);
            const cleanup = try self.cleanUpDynamicByteArrayEndSlotsFunction(to_type);
            defer self.allocator.free(cleanup);
            const mask = try self.maskBytesFunctionDynamic();
            defer self.allocator.free(mask);
            const combine_short = try self.shortByteArrayEncodeUsedAreaSetLengthFunction();
            defer self.allocator.free(combine_short);
            const load = if (from_storage)
                "sload"
            else if (from_calldata)
                "calldataload"
            else
                "mload";
            const generator = try self.function_collector.generator(self.evm_version);
            const source_assignment = if (from_storage)
                try generator.statements(
                    "src := @0(src)",
                    .{source_data},
                )
            else
                Yul.Block{};

            const len_name = try generator.name("len");
            const len_names: []const YulName = if (from_calldata) &.{len_name} else &.{};
            const code = try generator.functionDefinition(
                \\function @0(slot, src, @1) {
                \\    @2
                \\    let newLen := @3(src, @4)
                \\    if gt(newLen, 0xffffffffffffffff) { @5() }
                \\    let oldLen := @6(sload(slot))
                \\    @7(slot, oldLen, newLen)
                \\    let srcOffset := 0
                \\    @8
                \\    switch gt(newLen, 31)
                \\    case 1 {
                \\        let loopEnd := and(newLen, not(0x1f))
                \\        @9
                \\        let dstPtr := @10(slot)
                \\        let i := 0
                \\        for { } lt(i, loopEnd) { i := add(i, 0x20) } {
                \\            sstore(dstPtr, @11(add(src, srcOffset)))
                \\            dstPtr := add(dstPtr, 1)
                \\            srcOffset := add(srcOffset, @12)
                \\        }
                \\        if lt(loopEnd, newLen) {
                \\            let lastValue := @13(add(src, srcOffset))
                \\            sstore(dstPtr, @14(lastValue, and(newLen, 0x1f)))
                \\        }
                \\        sstore(slot, add(mul(newLen, 2), 1))
                \\    }
                \\    default {
                \\        let value := 0
                \\        if newLen { value := @15(add(src, srcOffset)) }
                \\        sstore(slot, @16(value, newLen))
                \\    }
                \\}
            , .{
                name,
                len_names,
                if (from_storage) try generator.statements("if eq(slot, src) { leave }", .{}) else Yul.Block{},
                length,
                len_names,
                panic,
                byte_length,
                cleanup,
                if (from_memory) try generator.statements("srcOffset := 0x20", .{}) else Yul.Block{},
                source_assignment,
                destination_data,
                load,
                @as(u32, if (from_storage) 1 else 0x20),
                load,
                mask,
                load,
                combine_short,
            });

            try self.function_collector.finishGeneratedFunction(name, code);
        }
        return self.function_collector.copyFunctionName(name);
    }

    pub fn copyValueArrayToStorageFunction(
        self: *YulUtilFunctions,
        from_type: *const Types.Type,
        to_type: *const Types.Type,
    ) UtilError![]u8 {
        const from = from_type.asArray() orelse return error.InvalidType;
        const to = to_type.asArray() orelse return error.InvalidType;
        if (!TypeBehavior.isValueType(from.base_type) or
            !TypeBehavior.isValueType(to.base_type) or
            !TypeBehavior.isImplicitlyConvertibleTo(from.base_type, to.base_type) or
            from.isByteArrayOrString() or to.isByteArrayOrString() or
            to.reference.location != .Storage)
            return error.InvalidType;
        const source_storage_stride = try TypeBehavior.storageStride(from.*);
        const destination_storage_stride = try TypeBehavior.storageStride(to.*);
        if (source_storage_stride > destination_storage_stride or
            destination_storage_stride == 0 or destination_storage_stride > 32)
            return error.InvalidType;

        const from_identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, from_type);
        defer self.allocator.free(from_identifier);
        const to_identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, to_type);
        defer self.allocator.free(to_identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "copy_array_to_storage_from_{s}_to_{s}",
            .{ from_identifier, to_identifier },
        );
        defer self.allocator.free(name);
        if (try self.function_collector.beginFunction(name)) {
            errdefer self.function_collector.abortFunction(name);
            const from_calldata = from.reference.location == .CallData;
            const from_storage = from.reference.location == .Storage;
            const from_memory = from.reference.location == .Memory;
            if (!from_calldata and !from_storage and !from_memory)
                return error.InvalidType;
            const dynamic_calldata = from_calldata and from.isDynamicallySized();
            const resize = try self.resizeArrayFunction(to_type);
            defer self.allocator.free(resize);
            const length_function = try self.arrayLengthFunction(from_type);
            defer self.allocator.free(length_function);
            const panic = try self.panicFunction(.resource_error);
            defer self.allocator.free(panic);
            // Upstream registers this reader even when the storage branch does
            // not render it; preserving that request order keeps collector
            // output deterministic across the port.
            const read = try self.readFromMemoryOrCalldata(
                from.base_type,
                from_calldata,
            );
            defer self.allocator.free(read);
            const source_data = try self.arrayDataAreaFunction(from_type);
            defer self.allocator.free(source_data);
            const destination_data = try self.arrayDataAreaFunction(to_type);
            defer self.allocator.free(destination_data);
            const generator = try self.function_collector.generator(self.evm_version);
            const stack_size = try TypeBehavior.sizeOnStack(from.base_type);
            const stack_items = try generator.indexedNames(
                "stackItem_",
                stack_size,
            );

            const items_per_slot: u8 = 32 / destination_storage_stride;
            const multiple_destination_items = items_per_slot > 1;
            var same_type_from_storage = from_storage and
                TypeBehavior.equals(from.base_type, to.base_type);
            if (from.base_type.asFunction()) |from_function| {
                const to_function = to.base_type.asFunction() orelse
                    return error.InvalidType;
                if (!TypeBehavior.functionEqualExcludingStateMutability(
                    from_function.*,
                    to_function.*,
                )) return error.InvalidType;
                same_type_from_storage = from_storage;
            }

            const mask_full = if (same_type_from_storage)
                try self.maskLowerOrderBytesFunction(
                    items_per_slot * destination_storage_stride,
                )
            else
                try self.allocator.alloc(u8, 0);
            defer self.allocator.free(mask_full);
            const mask_bytes = if (same_type_from_storage)
                try self.maskLowerOrderBytesFunctionDynamic()
            else
                try self.allocator.alloc(u8, 0);
            defer self.allocator.free(mask_bytes);
            const extract = if (!same_type_from_storage)
                try self.extractFromStorageValueDynamic(from.base_type)
            else
                try self.allocator.alloc(u8, 0);
            defer self.allocator.free(extract);
            const update_slice = if (!same_type_from_storage)
                try self.updateByteSliceFunctionDynamic(destination_storage_stride)
            else
                try self.allocator.alloc(u8, 0);
            defer self.allocator.free(update_slice);
            const conversion = if (!same_type_from_storage)
                try self.conversionFunction(from.base_type, to.base_type)
            else
                try self.allocator.alloc(u8, 0);
            defer self.allocator.free(conversion);
            const prepare = if (!same_type_from_storage)
                try self.prepareStoreFunction(to.base_type)
            else
                try self.allocator.alloc(u8, 0);
            defer self.allocator.free(prepare);

            const source_advance: u256 = if (from_storage) 1 else if (from_calldata)
                try TypeBehavior.calldataStride(from.*)
            else
                try TypeBehavior.memoryStride(from.*);
            // Full and partial slots contain distinct mutable AST occurrences.
            // Construct each from the same recipe; no prototype tree is retained
            // or traversed just to clone it for the second loop.
            var transfers: [2]Yul.Block = .{ .{}, .{} };
            const transfer_count: usize = if (multiple_destination_items) 2 else 1;
            for (transfers[0..transfer_count], 0..) |*transfer, mode| {
                const partial_slot = mode == 1;
                const update_source = if (from_storage and !same_type_from_storage and source_storage_stride <= 16)
                    try generator.statements(
                        "srcItemIndexInSlot := add(srcItemIndexInSlot, 1) if eq(srcItemIndexInSlot, @0) { srcPtr := add(srcPtr, 1) srcSlotValue := sload(srcPtr) srcItemIndexInSlot := 0 }",
                        .{32 / source_storage_stride},
                    )
                else if (from_storage)
                    try generator.statements("srcPtr := add(srcPtr, 1) srcSlotValue := sload(srcPtr)", .{})
                else
                    try generator.statements("srcPtr := add(srcPtr, @0)", .{source_advance});
                if (same_type_from_storage) {
                    transfer.* = if (partial_slot)
                        try generator.statements("dstSlotValue := @0(srcSlotValue, mul(spill, @1)) @2", .{ mask_bytes, source_storage_stride, update_source })
                    else
                        try generator.statements("dstSlotValue := @0(srcSlotValue) @1", .{ mask_full, update_source });
                } else {
                    const read_item = if (from_storage)
                        try generator.statements("let @0 := @1(@2(srcSlotValue, mul(@3, srcItemIndexInSlot)))", .{ stack_items, conversion, extract, source_storage_stride })
                    else
                        try generator.statements("let @0 := @1(srcPtr)", .{ stack_items, read });
                    const insert_item = if (multiple_destination_items)
                        try generator.statements("dstSlotValue := @0(dstSlotValue, mul(@1, j), itemValue)", .{ update_slice, destination_storage_stride })
                    else
                        try generator.statements("dstSlotValue := itemValue", .{});
                    const item = try generator.statements("@0 let itemValue := @1(@2) @3 @4", .{ read_item, prepare, stack_items, insert_item, update_source });
                    transfer.* = if (multiple_destination_items)
                        try generator.statements("for { let j := 0 } lt(j, @0) { j := add(j, 1) } { @1 }", .{ if (partial_slot) try generator.identifier("spill") else try generator.expression("@0", .{items_per_slot}), item })
                    else
                        try generator.statements("{ @0 }", .{item});
                }
            }
            const spill = if (multiple_destination_items)
                try generator.statements(
                    "let spill := sub(length, mul(fullSlots, @0)) if gt(spill, 0) { let dstSlotValue := 0 @1 sstore(add(dstSlot, fullSlots), dstSlotValue) }",
                    .{ items_per_slot, transfers[1] },
                )
            else
                Yul.Block{};
            const len_name = try generator.name("len");
            const len_names: []const YulName = if (dynamic_calldata) &.{len_name} else &.{};
            const alias_guard = if (from_storage) try generator.statements("if eq(dst, src) { leave }", .{}) else Yul.Block{};
            const source_setup = if (from_storage) try generator.statements("let srcSlotValue := sload(srcPtr) let srcItemIndexInSlot := 0", .{}) else Yul.Block{};
            const code = try generator.functionDefinition(
                \\function @0(dst, src, @1) {
                \\    @2
                \\    let length := @3(src, @1)
                \\    if gt(length, 0xffffffffffffffff) { @4() }
                \\    @5(dst, length)
                \\    let srcPtr := @6(src)
                \\    let dstSlot := @7(dst)
                \\    let fullSlots := div(length, @8)
                \\    @9
                \\    for { let i := 0 } lt(i, fullSlots) { i := add(i, 1) } {
                \\        let dstSlotValue := 0
                \\        @10
                \\        sstore(add(dstSlot, i), dstSlotValue)
                \\    }
                \\    @11
                \\}
            , .{ name, len_names, alias_guard, length_function, panic, resize, source_data, destination_data, items_per_slot, source_setup, transfers[0], spill });
            try self.function_collector.finishGeneratedFunction(name, code);
        }
        return self.function_collector.copyFunctionName(name);
    }

    pub fn copyStructToStorageFunction(
        self: *YulUtilFunctions,
        from_type: *const Types.Type,
        to_type: *const Types.Type,
    ) UtilError![]u8 {
        const from = switch (from_type.payload) {
            .Struct => |value| value,
            else => return error.InvalidType,
        };
        const to = switch (to_type.payload) {
            .Struct => |value| value,
            else => return error.InvalidType,
        };
        if (to.reference.location != .Storage or
            from.declaration != to.declaration)
            return error.InvalidType;
        const from_identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, from_type);
        defer self.allocator.free(from_identifier);
        const to_identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, to_type);
        defer self.allocator.free(to_identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "copy_struct_to_storage_from_{s}_to_{s}",
            .{ from_identifier, to_identifier },
        );
        defer self.allocator.free(name);
        if (try self.function_collector.beginFunction(name)) {
            errdefer self.function_collector.abortFunction(name);
            var from_members = try TypeBehavior.nativeMembersAlloc(
                self.type_provider,
                self.allocator,
                from_type,
                null,
            );
            defer from_members.deinit();
            var to_members = try TypeBehavior.nativeMembersAlloc(
                self.type_provider,
                self.allocator,
                to_type,
                null,
            );
            defer to_members.deinit();
            if (from_members.items.len != to_members.items.len)
                return error.InvalidType;
            const to_offsets = try TypeBehavior.structStorageOffsetsAlloc(
                self.allocator,
                to,
            );
            defer self.allocator.free(to_offsets.offsets);
            const from_storage = from.reference.location == .Storage;
            const from_memory = from.reference.location == .Memory;
            const from_calldata = from.reference.location == .CallData;
            if (!from_storage and !from_memory and !from_calldata)
                return error.InvalidType;
            const generator = try self.function_collector.generator(self.evm_version);
            var body: Generated.Buffer = .{ .generator = generator };
            for (from_members.items, to_members.items, to_offsets.offsets) |
                from_member,
                to_member,
                maybe_to_offset,
            | {
                const member_type = from_member.type_ref;
                if (try TypeBehavior.memoryHeadSize(member_type) != 32)
                    return error.InvalidType;
                const to_offset = maybe_to_offset orelse return error.InvalidType;
                const stack_size = try TypeBehavior.sizeOnStack(member_type);
                const member_values = try generator.indexedNames(
                    "memberValue_",
                    stack_size,
                );

                const member_source_offset: u256 = if (from_calldata)
                    try TypeBehavior.structCalldataOffsetOfMember(
                        from,
                        from_member.name,
                    )
                else if (from_memory)
                    try TypeBehavior.structMemoryOffsetOfMember(
                        from,
                        from_member.name,
                    )
                else
                    (try TypeBehavior.structStorageOffsetOfMember(
                        self.allocator,
                        from,
                        from_member.name,
                    )).slot;
                // Match the eager Whiskers substitution order upstream: the
                // source reader is requested before the storage updater even
                // though both names are rendered later in the member body.
                var calldata_access: ?[]u8 = null;
                defer if (calldata_access) |value| self.allocator.free(value);
                var read: ?[]u8 = null;
                defer if (read) |value| self.allocator.free(value);
                if (from_calldata) {
                    if (TypeBehavior.isDynamicallyEncoded(member_type))
                        calldata_access = try self.accessCalldataTailFunction(member_type);
                    if (TypeBehavior.isValueType(member_type))
                        read = try self.readFromCalldata(member_type);
                } else if (from_memory) {
                    read = try self.readFromMemory(member_type);
                } else if (TypeBehavior.isValueType(member_type)) {
                    const source_offset = try TypeBehavior.structStorageOffsetOfMember(
                        self.allocator,
                        from,
                        from_member.name,
                    );
                    read = try self.readFromStorageValueType(
                        member_type,
                        source_offset.byte_offset,
                        true,
                        .Unspecified,
                    );
                } else {
                    const source_offset = try TypeBehavior.structStorageOffsetOfMember(
                        self.allocator,
                        from,
                        from_member.name,
                    );
                    if (source_offset.byte_offset != 0) return error.InvalidType;
                }
                const update = try self.updateStorageValueFunction(
                    member_type,
                    to_member.type_ref,
                    to_offset.byte_offset,
                );
                defer self.allocator.free(update);
                var member_body: Generated.Buffer = .{ .generator = generator };
                if (from_calldata) {
                    if (calldata_access) |access| {
                        try member_body.add(
                            "let @0 := @1(value, memberSrcPtr)\n",
                            .{ member_values, access },
                        );
                    } else {
                        try member_body.add(
                            "let @0 := memberSrcPtr\n",
                            .{member_values},
                        );
                    }
                    if (read) |read_function| {
                        try member_body.add(
                            "@0 := @1(@2)\n",
                            .{ member_values, read_function, member_values },
                        );
                    }
                } else if (from_memory) {
                    try member_body.add(
                        "let @0 := @1(memberSrcPtr)\n",
                        .{ member_values, read.? },
                    );
                } else {
                    if (read) |read_function| {
                        try member_body.add(
                            "let @0 := @1(memberSrcPtr)\n",
                            .{ member_values, read_function },
                        );
                    } else {
                        try member_body.add(
                            "let @0 := memberSrcPtr\n",
                            .{member_values},
                        );
                    }
                }
                try body.add("{ let memberSlot := add(slot, @0) let memberSrcPtr := add(value, @1) @2 @3(memberSlot, @4) }", .{ to_offset.slot, member_source_offset, member_body.take(), update, member_values });
            }
            const members = body.take();
            const guarded = if (from_storage) try generator.statements("if iszero(eq(slot, value)) { @0 }", .{members}) else members;
            const code = try generator.functionDefinition("function @0(slot, value) { @1 }", .{ name, guarded });
            try self.function_collector.finishGeneratedFunction(name, code);
        }
        return self.function_collector.copyFunctionName(name);
    }

    pub fn bytesToFixedBytesConversionFunction(
        self: *YulUtilFunctions,
        from_type: *const Types.Type,
        to_type: *const Types.Type,
    ) UtilError![]u8 {
        const from = from_type.asArray() orelse return error.InvalidType;
        const fixed = to_type.asFixedBytes() orelse return error.InvalidType;
        if (!from.isByteArray() or !from.isDynamicallySized() or
            fixed.bytes == 0)
            return error.InvalidType;
        const from_identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, from_type);
        defer self.allocator.free(from_identifier);
        const to_identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, to_type);
        defer self.allocator.free(to_identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "convert_bytes_to_fixedbytes_from_{s}_to_{s}",
            .{ from_identifier, to_identifier },
        );
        defer self.allocator.free(name);
        if (try self.function_collector.beginFunction(name)) {
            errdefer self.function_collector.abortFunction(name);
            const from_calldata = from.reference.location == .CallData;
            const from_memory = from.reference.location == .Memory;
            const from_storage = from.reference.location == .Storage;
            if (!from_calldata and !from_memory and !from_storage)
                return error.InvalidType;
            const length = try self.arrayLengthFunction(from_type);
            defer self.allocator.free(length);
            const data_area = try self.arrayDataAreaFunction(from_type);
            defer self.allocator.free(data_area);
            const generator = try self.function_collector.generator(self.evm_version);
            const extract = if (from_calldata) blk: {
                const cleanup = try self.cleanupFunction(to_type);
                defer self.allocator.free(cleanup);
                break :blk try generator.statements(
                    "value := @0(calldataload(dataArea))",
                    .{cleanup},
                );
            } else blk: {
                const read = if (from_storage)
                    try self.readFromStorage(
                        to_type,
                        32 - fixed.bytes,
                        false,
                        .Unspecified,
                    )
                else
                    try self.readFromMemory(to_type);
                defer self.allocator.free(read);
                break :blk try generator.statements(
                    "value := @0(dataArea)",
                    .{read},
                );
            };

            const shift = try self.shiftLeftFunctionDynamic();
            defer self.allocator.free(shift);
            const fixed_bits: usize = @as(usize, fixed.bytes) * 8;
            const mask_shift: std.math.Log2Int(u256) = @intCast(256 - fixed_bits);
            const all_ones: u256 = std.math.maxInt(u256);
            const mask_value = if (fixed_bits == 256)
                all_ones
            else
                all_ones << mask_shift;
            const mask = try compactHex(self.allocator, mask_value);
            defer self.allocator.free(mask);
            const data_area_setup = if (from_memory)
                try generator.statements(
                    "dataArea := @0(array)",
                    .{data_area},
                )
            else if (from_storage)
                try generator.statements(
                    "if gt(length, 31) { dataArea := @0(array) }",
                    .{data_area},
                )
            else
                Yul.Block{};

            const len_name = try generator.name("len");
            const len_names: []const YulName = if (from_calldata) &.{len_name} else &.{};
            const code = try generator.functionDefinition(
                "function @0(array, @1) -> value { let length := @2(array, @1) let dataArea := array @3 @4 if lt(length, @5) { value := and(value, @6(mul(8, sub(@5, length)), @7)) } }",
                .{ name, len_names, length, data_area_setup, extract, fixed.bytes, shift, try generator.numberToken(mask) },
            );
            try self.function_collector.finishGeneratedFunction(name, code);
        }
        return self.function_collector.copyFunctionName(name);
    }

    pub fn conversionFunctionSpecial(
        self: *YulUtilFunctions,
        from_type: *const Types.Type,
        to_type: *const Types.Type,
    ) UtilError![]u8 {
        const from_identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, from_type);
        defer self.allocator.free(from_identifier);
        const to_identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, to_type);
        defer self.allocator.free(to_identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "convert_{s}_to_{s}",
            .{ from_identifier, to_identifier },
        );
        defer self.allocator.free(name);
        if (try self.function_collector.beginFunction(name)) {
            errdefer self.function_collector.abortFunction(name);
            const generator = try self.function_collector.generator(self.evm_version);
            const code = if (from_type.asTuple()) |from_tuple| tuple: {
                const to_tuple = to_type.asTuple() orelse return error.InvalidType;
                if (from_tuple.components.len != to_tuple.components.len)
                    return error.InvalidType;
                var source_stack_size: usize = 0;
                var destination_stack_size: usize = 0;
                var conversions: Generated.Buffer = .{ .generator = generator };
                for (from_tuple.components, to_tuple.components) |maybe_from, maybe_to| {
                    const component_from = maybe_from orelse return error.InvalidType;
                    const from_size = try TypeBehavior.sizeOnStack(component_from);
                    if (maybe_to) |component_to| {
                        const to_size = try TypeBehavior.sizeOnStack(component_to);
                        const converted = try generator.indexedNameRange(
                            "converted",
                            destination_stack_size,
                            destination_stack_size + to_size,
                        );

                        const values = try generator.indexedNameRange(
                            "value",
                            source_stack_size,
                            source_stack_size + from_size,
                        );

                        const conversion = try self.conversionFunction(
                            component_from,
                            component_to,
                        );
                        defer self.allocator.free(conversion);
                        if (to_size == 0)
                            try conversions.add("@0(@1)", .{ conversion, values })
                        else
                            try conversions.add("@0 := @1(@2)", .{ converted, conversion, values });
                        destination_stack_size += to_size;
                    }
                    source_stack_size += from_size;
                }
                const values = try generator.indexedNames(
                    "value",
                    source_stack_size,
                );

                const converted = try generator.indexedNames(
                    "converted",
                    destination_stack_size,
                );

                break :tuple try generator.functionDefinition(
                    "function @0(@1) -> @2 { @3 }",
                    .{ name, values, converted, conversions.take() },
                );
            } else string_literal: {
                const literal = switch (from_type.payload) {
                    .StringLiteral => |value| value.value,
                    else => return error.UnsupportedType,
                };
                switch (to_type.payload) {
                    .FixedBytes => |fixed| {
                        if (literal.len > 32) return error.InvalidType;
                        var aligned_bytes: [32]u8 = @splat(0);
                        @memcpy(aligned_bytes[0..literal.len], literal);
                        var value = std.mem.readInt(u256, &aligned_bytes, .big);
                        if (fixed.bytes < 32) {
                            const mask = ~(@as(u256, std.math.maxInt(u256)) >>
                                @intCast(8 * fixed.bytes));
                            value &= mask;
                        }
                        const word = try Numeric.formatNumberU256Alloc(
                            self.allocator,
                            value,
                        );
                        defer self.allocator.free(word);
                        break :string_literal try generator.functionDefinition(
                            "\nfunction @0() -> converted {\nconverted := @1\n}\n",
                            .{ name, try generator.numberToken(word) },
                        );
                    },
                    .Array => |array| {
                        if (!array.isByteArrayOrString() or
                            array.reference.location != .Memory)
                            return error.InvalidType;
                        const copy = try self.copyLiteralToMemoryFunction(literal);
                        defer self.allocator.free(copy);
                        break :string_literal try generator.functionDefinition(
                            "\nfunction @0() -> converted {\nconverted := @1()\n}\n",
                            .{ name, copy },
                        );
                    },
                    else => return error.InvalidType,
                }
            };

            try self.function_collector.finishGeneratedFunction(name, code);
        }
        return self.function_collector.copyFunctionName(name);
    }

    pub fn arrayConversionFunction(
        self: *YulUtilFunctions,
        from_type: *const Types.Type,
        to_type: *const Types.Type,
    ) UtilError![]u8 {
        const from = from_type.asArray() orelse return error.InvalidType;
        const to = to_type.asArray() orelse return error.InvalidType;
        if (to.reference.location == .CallData and
            (from.reference.location != .CallData or
                !from.isByteArrayOrString() or !to.isByteArrayOrString()))
            return error.InvalidType;
        if (to.reference.location == .Storage and
            (from.reference.location != .Storage or
                (!to.reference.storage_pointer and
                    !(from.isByteArrayOrString() and to.isByteArrayOrString()))))
            return error.InvalidType;
        const from_identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, from_type);
        defer self.allocator.free(from_identifier);
        const to_identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, to_type);
        defer self.allocator.free(to_identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "convert_array_{s}_to_{s}",
            .{ from_identifier, to_identifier },
        );
        defer self.allocator.free(name);
        if (try self.function_collector.beginFunction(name)) {
            errdefer self.function_collector.abortFunction(name);
            const from_dynamic_calldata = from.reference.location == .CallData and
                from.isDynamicallySized();
            const to_dynamic_calldata = to.reference.location == .CallData and
                to.isDynamicallySized();
            const same_representation = TypeBehavior.equals(from_type, to_type) or
                (from.reference.location == .Memory and to.reference.location == .Memory) or
                (from.reference.location == .CallData and to.reference.location == .CallData) or
                to.reference.location == .Storage;
            const generator = try self.function_collector.generator(self.evm_version);
            const body = if (same_representation)
                try generator.statements("converted := value", .{})
            else if (to.reference.location == .Memory and
                from.reference.location == .Storage)
            storage: {
                const copy = try self.copyArrayFromStorageToMemoryFunction(
                    from_type,
                    to_type,
                );
                defer self.allocator.free(copy);
                break :storage try generator.statements(
                    "converted := @0(value)",
                    .{copy},
                );
            } else if (to.reference.location == .Memory and
                from.reference.location == .CallData)
            calldata: {
                const length_expression = if (from.isDynamicallySized())
                    try generator.identifier("length")
                else
                    try generator.expression("@0", .{from.length.?});
                if (self.calldata_to_memory_abi_decoder) |provider| {
                    const decoder = try provider.generate(to_type);
                    defer self.allocator.free(decoder);
                    break :calldata try generator.statements(
                        "// Copy the array to a free position in memory\nconverted :=\n@0(value, @1, calldatasize())",
                        .{ decoder, length_expression },
                    );
                }
                const copy = try self.copyCalldataArrayToMemoryFunction(
                    from_type,
                    to_type,
                );
                defer self.allocator.free(copy);
                break :calldata try generator.statements(
                    "converted := @0(value, @1)",
                    .{ copy, length_expression },
                );
            } else return error.UnsupportedType;

            const output_length_statement = if (to_dynamic_calldata)
                try generator.statements("outLength := @0", .{if (from.isDynamicallySized()) try generator.identifier("length") else try generator.expression("@0", .{from.length.?})})
            else
                Yul.Block{};
            const parameters: []const []const u8 = if (from_dynamic_calldata) &.{ "value", "length" } else &.{"value"};
            const returns: []const []const u8 = if (to_dynamic_calldata) &.{ "converted", "outLength" } else &.{"converted"};
            const code = try generator.functionDefinition(
                "function @0(@1) -> @2 { @3 @4 }",
                .{ name, parameters, returns, body, output_length_statement },
            );
            try self.function_collector.finishGeneratedFunction(name, code);
        }
        return self.function_collector.copyFunctionName(name);
    }

    fn copyCalldataArrayToMemoryFunction(
        self: *YulUtilFunctions,
        from_type: *const Types.Type,
        to_type: *const Types.Type,
    ) UtilError![]u8 {
        const from = from_type.asArray() orelse return error.InvalidType;
        const to = to_type.asArray() orelse return error.InvalidType;
        if (from.reference.location != .CallData or
            to.reference.location != .Memory or
            from.isDynamicallySized() != to.isDynamicallySized())
            return error.InvalidType;
        const from_identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, from_type);
        defer self.allocator.free(from_identifier);
        const to_identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, to_type);
        defer self.allocator.free(to_identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "copy_calldata_array_to_memory_from_{s}_to_{s}",
            .{ from_identifier, to_identifier },
        );
        defer self.allocator.free(name);
        if (try self.function_collector.beginFunction(name)) {
            errdefer self.function_collector.abortFunction(name);
            const allocate = try self.allocateMemoryArrayFunction(to_type);
            defer self.allocator.free(allocate);
            const generator = try self.function_collector.generator(self.evm_version);
            const code = if (from.isByteArrayOrString()) bytes: {
                if (!to.isByteArrayOrString()) return error.InvalidType;
                const copy = try self.copyToMemoryFunction(true, true);
                defer self.allocator.free(copy);
                const short = try self.revertReasonIfDebugFunction(
                    "ABI decoding: byte array data too short",
                );
                defer self.allocator.free(short);
                break :bytes try generator.functionDefinition(
                    \\function @0(offset, length) -> array {
                    \\    if gt(add(offset, length), calldatasize()) { @1() }
                    \\    array := @2(length)
                    \\    @3(offset, add(array, 0x20), length)
                    \\}
                , .{ name, short, allocate, copy });
            } else ordinary: {
                const source_stride = try TypeBehavior.calldataStride(from.*);
                const destination_stride = try TypeBehavior.memoryStride(to.*);
                const source_size = try TypeBehavior.sizeOnStack(from.base_type);
                const destination_size = try TypeBehavior.sizeOnStack(to.base_type);
                if (source_size == 0 or destination_size == 0)
                    return error.UnsupportedType;
                const source_values = try generator.indexedNames(
                    "sourceValue_",
                    source_size,
                );

                const converted_values = try generator.indexedNames(
                    "convertedValue_",
                    destination_size,
                );

                const conversion = try self.conversionFunction(
                    from.base_type,
                    to.base_type,
                );
                defer self.allocator.free(conversion);
                const write = try self.writeToMemoryFunction(to.base_type);
                defer self.allocator.free(write);
                const source = if (TypeBehavior.isDynamicallyEncoded(from.base_type)) dynamic: {
                    const access = try self.accessCalldataTailFunction(from.base_type);
                    defer self.allocator.free(access);
                    break :dynamic try generator.statements(
                        "let @0 := @1(offset, src)",
                        .{ source_values, access },
                    );
                } else if (TypeBehavior.isValueType(from.base_type)) scalar: {
                    const read = try self.readFromCalldata(from.base_type);
                    defer self.allocator.free(read);
                    break :scalar try generator.statements(
                        "let @0 := @1(src)",
                        .{ source_values, read },
                    );
                } else try generator.statements(
                    "let @0 := src",
                    .{source_values},
                );

                const short = try self.revertReasonIfDebugFunction(
                    "ABI decoding: calldata array data too short",
                );
                defer self.allocator.free(short);
                break :ordinary try generator.functionDefinition(
                    \\function @0(offset, length) -> array {
                    \\    let srcEnd := add(offset, mul(length, @1))
                    \\    if or(lt(srcEnd, offset), gt(srcEnd, calldatasize())) { @2() }
                    \\    array := @3(length)
                    \\    let dst := array
                    \\    @4
                    \\    for { let src := offset } lt(src, srcEnd) { src := add(src, @5) } {
                    \\        @6
                    \\        let @7 := @8(@9)
                    \\        @10(dst, @11)
                    \\        dst := add(dst, @12)
                    \\    }
                    \\}
                , .{
                    name,
                    source_stride,
                    short,
                    allocate,
                    if (to.isDynamicallySized()) try generator.statements("dst := add(dst, 0x20)", .{}) else Yul.Block{},
                    source_stride,
                    source,
                    converted_values,
                    conversion,
                    source_values,
                    write,
                    converted_values,
                    destination_stride,
                });
            };

            try self.function_collector.finishGeneratedFunction(name, code);
        }
        return self.function_collector.copyFunctionName(name);
    }

    fn copyCalldataStructToMemoryFunction(
        self: *YulUtilFunctions,
        from_type: *const Types.Type,
        to_type: *const Types.Type,
    ) UtilError![]u8 {
        const from = switch (from_type.payload) {
            .Struct => |value| value,
            else => return error.InvalidType,
        };
        const to = switch (to_type.payload) {
            .Struct => |value| value,
            else => return error.InvalidType,
        };
        if (from.reference.location != .CallData or
            to.reference.location != .Memory or
            from.declaration != to.declaration)
            return error.InvalidType;
        const from_identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, from_type);
        defer self.allocator.free(from_identifier);
        const to_identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, to_type);
        defer self.allocator.free(to_identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "copy_calldata_struct_to_memory_from_{s}_to_{s}",
            .{ from_identifier, to_identifier },
        );
        defer self.allocator.free(name);
        if (try self.function_collector.beginFunction(name)) {
            errdefer self.function_collector.abortFunction(name);
            var source_members = try TypeBehavior.nativeMembersAlloc(
                self.type_provider,
                self.allocator,
                from_type,
                null,
            );
            defer source_members.deinit();
            var target_members = try TypeBehavior.nativeMembersAlloc(
                self.type_provider,
                self.allocator,
                to_type,
                null,
            );
            defer target_members.deinit();
            if (source_members.items.len != target_members.items.len)
                return error.InvalidType;
            const allocate = try self.allocateMemoryStructFunction(to_type);
            defer self.allocator.free(allocate);
            const short = try self.revertReasonIfDebugFunction(
                "ABI decoding: struct data too short",
            );
            defer self.allocator.free(short);
            var head_size: u32 = 0;
            for (source_members.items) |member|
                head_size = std.math.add(
                    u32,
                    head_size,
                    try TypeBehavior.calldataHeadSize(member.type_ref),
                ) catch return error.Overflow;
            const generator = try self.function_collector.generator(self.evm_version);
            var body: Generated.Buffer = .{ .generator = generator };
            for (source_members.items, target_members.items) |source_member, target_member| {
                const source_type = source_member.type_ref;
                const target_type = target_member.type_ref;
                const source_size = try TypeBehavior.sizeOnStack(source_type);
                const target_size = try TypeBehavior.sizeOnStack(target_type);
                if (source_size == 0 or target_size == 0)
                    return error.UnsupportedType;
                const source_values = try generator.indexedNames(
                    "sourceValue_",
                    source_size,
                );

                const converted_values = try generator.indexedNames(
                    "convertedValue_",
                    target_size,
                );

                const calldata_offset = try TypeBehavior.structCalldataOffsetOfMember(
                    from,
                    source_member.name,
                );
                const memory_offset = try TypeBehavior.structMemoryOffsetOfMember(
                    to,
                    target_member.name,
                );
                const source = if (TypeBehavior.isDynamicallyEncoded(source_type)) dynamic: {
                    const access = try self.accessCalldataTailFunction(source_type);
                    defer self.allocator.free(access);
                    break :dynamic try generator.statements(
                        "let @0 := @1(offset, add(offset, @2))",
                        .{ source_values, access, calldata_offset },
                    );
                } else if (TypeBehavior.isValueType(source_type)) scalar: {
                    const read = try self.readFromCalldata(source_type);
                    defer self.allocator.free(read);
                    break :scalar try generator.statements(
                        "let @0 := @1(add(offset, @2))",
                        .{ source_values, read, calldata_offset },
                    );
                } else try generator.statements(
                    "let @0 := add(offset, @1)",
                    .{ source_values, calldata_offset },
                );

                const conversion = try self.conversionFunction(source_type, target_type);
                defer self.allocator.free(conversion);
                const write = try self.writeToMemoryFunction(target_type);
                defer self.allocator.free(write);
                try body.add(
                    "{ @0 let @1 := @2(@3) @4(add(value, @5), @6) }\n",
                    .{
                        source,
                        converted_values,
                        conversion,
                        source_values,
                        write,
                        memory_offset,
                        converted_values,
                    },
                );
            }
            const code = try generator.functionDefinition(
                "function @0(offset) -> value { if gt(add(offset, @1), calldatasize()) { @2() } value := @3() @4 }",
                .{ name, head_size, short, allocate, body.take() },
            );
            try self.function_collector.finishGeneratedFunction(name, code);
        }
        return self.function_collector.copyFunctionName(name);
    }

    pub fn bytesOrStringConcatFunction(
        self: *YulUtilFunctions,
        argument_types: []const *const Types.Type,
        function_kind: Types.FunctionKind,
        packed_encoder_name: []const u8,
    ) UtilError![]u8 {
        if (function_kind != .BytesConcat and function_kind != .StringConcat)
            return error.InvalidType;
        var name: std.ArrayList(u8) = .empty;
        defer name.deinit(self.allocator);
        try name.appendSlice(
            self.allocator,
            if (function_kind == .StringConcat) "string_concat" else "bytes_concat",
        );
        var total_parameters: usize = 0;
        for (argument_types) |argument_type| {
            total_parameters = std.math.add(
                usize,
                total_parameters,
                try TypeBehavior.sizeOnStack(argument_type),
            ) catch return error.Overflow;
            const identifier = try TypeBehavior.compatibilityIdentifierAlloc(
                self.allocator,
                self.compatibility_ids,
                argument_type,
            );
            defer self.allocator.free(identifier);
            try name.print(self.allocator, "_{s}", .{identifier});
        }
        if (try self.function_collector.beginFunction(name.items)) {
            errdefer self.function_collector.abortFunction(name.items);
            const generator = try self.function_collector.generator(self.evm_version);
            const parameters = try generator.indexedNames(
                "param_",
                total_parameters,
            );

            const allocate = try self.allocateUnboundedFunction();
            defer self.allocator.free(allocate);
            const finalize = try self.finalizeAllocationFunction();
            defer self.allocator.free(finalize);
            const code = try generator.functionDefinition(
                "function @0(@1) -> outPtr { outPtr := @2() let dataStart := add(outPtr, 0x20) let dataEnd := @3(dataStart, @1) mstore(outPtr, sub(dataEnd, dataStart)) @4(outPtr, sub(dataEnd, outPtr)) }",
                .{ name.items, parameters, allocate, packed_encoder_name, finalize },
            );
            try self.function_collector.finishGeneratedFunction(name.items, code);
        }
        return self.function_collector.copyFunctionName(name.items);
    }

    pub fn packedHashFunction(
        self: *YulUtilFunctions,
        given_types: []const *const Types.Type,
        target_types: []const *const Types.Type,
        packed_encoder_name: []const u8,
    ) UtilError![]u8 {
        if (given_types.len != target_types.len) return error.InvalidType;
        var name: std.ArrayList(u8) = .empty;
        defer name.deinit(self.allocator);
        try name.appendSlice(self.allocator, "packed_hashed_");
        for (given_types) |type_ref| {
            const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
            defer self.allocator.free(identifier);
            try name.print(self.allocator, "{s}_", .{identifier});
        }
        try name.appendSlice(self.allocator, "_to_");
        for (target_types) |type_ref| {
            const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
            defer self.allocator.free(identifier);
            try name.print(self.allocator, "{s}_", .{identifier});
        }
        if (try self.function_collector.beginFunction(name.items)) {
            errdefer self.function_collector.abortFunction(name.items);
            var stack_size: usize = 0;
            for (given_types) |type_ref|
                stack_size = std.math.add(
                    usize,
                    stack_size,
                    try TypeBehavior.sizeOnStack(type_ref),
                ) catch return error.Overflow;
            const generator = try self.function_collector.generator(self.evm_version);
            const variables = try generator.indexedNameRange(
                "var_",
                1,
                1 + stack_size,
            );

            const allocate = try self.allocateUnboundedFunction();
            defer self.allocator.free(allocate);
            const code = try generator.functionDefinition(
                "function @0(@1) -> hash { let pos := @2() let end := @3(pos, @1) hash := keccak256(pos, sub(end, pos)) }",
                .{ name.items, variables, allocate, packed_encoder_name },
            );
            try self.function_collector.finishGeneratedFunction(name.items, code);
        }
        return self.function_collector.copyFunctionName(name.items);
    }

    /// Generates the scalar conversion used by ABI encoding and UDVT
    /// wrap/unwrap calls. User-defined value types recurse to their underlying
    /// representation exactly as upstream does, retaining the conversion
    /// helper even when both mobile types are identical.
    pub fn conversionFunction(
        self: *YulUtilFunctions,
        from_raw: *const Types.Type,
        to_raw: *const Types.Type,
    ) UtilError![]u8 {
        const from = switch (from_raw.payload) {
            .UserDefinedValueType => |value| value.underlying_type orelse
                return error.UnsupportedType,
            else => from_raw,
        };
        const to = switch (to_raw.payload) {
            .UserDefinedValueType => |value| value.underlying_type orelse
                return error.UnsupportedType,
            else => to_raw,
        };
        const from_category = from.category();
        const to_category = to.category();
        if (from_category == .ArraySlice) {
            const source_array = from.payload.ArraySlice.array_type;
            if (to_category == .FixedBytes)
                return self.bytesToFixedBytesConversionFunction(source_array, to);
            if (to_category != .Array) return error.UnsupportedType;
            const target_array = to.asArray().?;
            if (target_array.reference.location != .CallData)
                return self.arrayConversionFunction(source_array, to);
            const from_identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, from);
            defer self.allocator.free(from_identifier);
            const to_identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, to);
            defer self.allocator.free(to_identifier);
            const name = try std.fmt.allocPrint(
                self.allocator,
                "convert_{s}_to_{s}",
                .{ from_identifier, to_identifier },
            );
            defer self.allocator.free(name);
            if (try self.function_collector.beginFunction(name)) {
                errdefer self.function_collector.abortFunction(name);
                const generator = try self.function_collector.generator(self.evm_version);
                const code = try generator.functionDefinition(
                    "\nfunction @0(offset, length) -> outOffset, outLength {\noutOffset := offset\noutLength := length\n}\n",
                    .{name},
                );

                try self.function_collector.finishGeneratedFunction(name, code);
            }
            return self.function_collector.copyFunctionName(name);
        }
        if (from_category == .Array) {
            if (to_category == .FixedBytes)
                return self.bytesToFixedBytesConversionFunction(from, to);
            if (to_category != .Array) return error.UnsupportedType;
            return self.arrayConversionFunction(from, to);
        }
        if (from_category == .Function) {
            if (to_category != .Function) return error.UnsupportedType;
            const from_function = from.asFunction().?;
            const to_function = to.asFunction().?;
            if (from_function.kind != to_function.kind or
                (from_function.kind != .Internal and
                    from_function.kind != .External) or
                try TypeBehavior.sizeOnStack(from) !=
                    try TypeBehavior.sizeOnStack(to))
                return error.UnsupportedType;
            const from_identifier = try TypeBehavior.compatibilityIdentifierAlloc(
                self.allocator,
                self.compatibility_ids,
                from,
            );
            defer self.allocator.free(from_identifier);
            const to_identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, to);
            defer self.allocator.free(to_identifier);
            const name = try std.fmt.allocPrint(
                self.allocator,
                "convert_{s}_to_{s}",
                .{ from_identifier, to_identifier },
            );
            defer self.allocator.free(name);
            if (!(try self.function_collector.beginFunction(name)))
                return self.function_collector.copyFunctionName(name);
            errdefer self.function_collector.abortFunction(name);
            const generator = try self.function_collector.generator(self.evm_version);
            const code = if (from_function.kind == .External)
                try generator.functionDefinition(
                    "\nfunction @0(addr, functionId) -> outAddr, outFunctionId {\noutAddr := addr\noutFunctionId := functionId\n}\n",
                    .{name},
                )
            else
                try generator.functionDefinition(
                    "\nfunction @0(functionId) -> outFunctionId {\noutFunctionId := functionId\n}\n",
                    .{name},
                );

            try self.function_collector.finishGeneratedFunction(name, code);
            return self.function_collector.copyFunctionName(name);
        }
        if (try TypeBehavior.sizeOnStack(from) != 1 or
            try TypeBehavior.sizeOnStack(to) != 1)
            return self.conversionFunctionSpecial(from, to);
        const supported = switch (from_category) {
            .Address, .Contract => to_category == .Integer or
                to_category == .Address or to_category == .Contract or
                to_category == .Enum or to_category == .FixedBytes,
            .Integer, .RationalNumber => to_category == .Integer or
                to_category == .Address or to_category == .Contract or
                to_category == .Enum or to_category == .FixedBytes,
            .Bool => to_category == .Bool and TypeBehavior.equals(from, to),
            .FixedBytes => to_category == .FixedBytes or
                to_category == .Integer or to_category == .Address,
            .Enum => to_category == .Integer or TypeBehavior.equals(from, to),
            .Struct => to_category == .Struct and
                from.payload.Struct.declaration == to.payload.Struct.declaration,
            .Mapping => TypeBehavior.equals(from, to),
            .TypeType => to_category == .Address,
            else => false,
        };
        if (!supported) return error.UnsupportedType;

        const from_identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, from);
        defer self.allocator.free(from_identifier);
        const to_identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, to);
        defer self.allocator.free(to_identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "convert_{s}_to_{s}",
            .{ from_identifier, to_identifier },
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const generator = try self.function_collector.generator(self.evm_version);

        const body = switch (from_category) {
            .Address, .Contract => blk: {
                const uint160 = Types.Type{ .payload = .{ .Integer = .{
                    .bits = 160,
                    .modifier = .Unsigned,
                } } };
                const convert = try self.conversionFunction(&uint160, to);
                defer self.allocator.free(convert);
                break :blk try generator.statements(
                    "converted := @0(value)",
                    .{convert},
                );
            },
            .Integer, .RationalNumber => blk: {
                if (to_category == .Address or to_category == .Contract) {
                    const uint160 = Types.Type{ .payload = .{ .Integer = .{
                        .bits = 160,
                        .modifier = .Unsigned,
                    } } };
                    const convert = try self.conversionFunction(from, &uint160);
                    defer self.allocator.free(convert);
                    break :blk try generator.statements(
                        "converted := @0(value)",
                        .{convert},
                    );
                }
                const clean_input = try self.cleanupFunction(from);
                defer self.allocator.free(clean_input);
                const clean_output = try self.cleanupFunction(to);
                defer self.allocator.free(clean_output);
                const convert = if (to_category == .FixedBytes) blk_convert: {
                    const bytes = to.payload.FixedBytes.bytes;
                    break :blk_convert try self.shiftLeftFunction(
                        256 - @as(usize, bytes) * 8,
                    );
                } else try self.identityFunction();
                defer self.allocator.free(convert);
                break :blk try generator.statements(
                    "converted := @0(@1(@2(value)))",
                    .{ clean_output, convert, clean_input },
                );
            },
            .Bool, .Enum => blk: {
                const clean = try self.cleanupFunction(from);
                defer self.allocator.free(clean);
                break :blk try generator.statements(
                    "converted := @0(value)",
                    .{clean},
                );
            },
            .FixedBytes => blk: {
                const from_bytes = from.payload.FixedBytes.bytes;
                if (to_category == .Integer) {
                    const integer = Types.Type{ .payload = .{ .Integer = .{
                        .bits = @as(u16, from_bytes) * 8,
                        .modifier = .Unsigned,
                    } } };
                    const shift = try self.shiftRightFunction(
                        256 - @as(usize, from_bytes) * 8,
                    );
                    defer self.allocator.free(shift);
                    const convert = try self.conversionFunction(&integer, to);
                    defer self.allocator.free(convert);
                    break :blk try generator.statements(
                        "converted := @0(@1(value))",
                        .{ convert, shift },
                    );
                }
                if (to_category == .Address) {
                    const uint160 = Types.Type{ .payload = .{ .Integer = .{
                        .bits = 160,
                        .modifier = .Unsigned,
                    } } };
                    const convert = try self.conversionFunction(from, &uint160);
                    defer self.allocator.free(convert);
                    break :blk try generator.statements(
                        "converted := @0(value)",
                        .{convert},
                    );
                }
                if (to_category != .FixedBytes) return error.UnsupportedType;
                const to_bytes = to.payload.FixedBytes.bytes;
                const clean_type = if (to_bytes <= from_bytes) to else from;
                const clean = try self.cleanupFunction(clean_type);
                defer self.allocator.free(clean);
                break :blk try generator.statements(
                    "converted := @0(value)",
                    .{clean},
                );
            },
            .Struct => blk: {
                const from_struct = from.payload.Struct;
                const to_struct = to.payload.Struct;
                if (from_struct.reference.location == to_struct.reference.location and
                    to_struct.reference.isPointer())
                    break :blk try generator.statements("converted := value", .{});
                if (to_struct.reference.location != .Memory or
                    from_struct.reference.location == .Memory)
                    return error.UnsupportedType;
                const read = if (from_struct.reference.location == .Storage)
                    try self.readFromStorage(to, 0, true, .Unspecified)
                else if (from_struct.reference.location == .CallData)
                    if (self.calldata_to_memory_abi_decoder) |provider|
                        try provider.generate(to)
                    else
                        try self.copyCalldataStructToMemoryFunction(from, to)
                else
                    return error.UnsupportedType;
                defer self.allocator.free(read);
                break :blk if (from_struct.reference.location == .CallData and
                    self.calldata_to_memory_abi_decoder != null)
                    try generator.statements(
                        "converted := @0(value, calldatasize())",
                        .{read},
                    )
                else
                    try generator.statements(
                        "converted := @0(value)",
                        .{read},
                    );
            },
            .Mapping => try generator.statements("converted := value", .{}),
            .TypeType => blk: {
                const actual = from.payload.TypeType.actual_type;
                const contract = switch (actual.payload) {
                    .Contract => |value| value,
                    else => return error.InvalidType,
                };
                if (contract.declaration.nodeKind() != .contract_definition or
                    contract.declaration.payload.contract_definition.contract_kind != .Library)
                    return error.InvalidType;
                break :blk try generator.statements("converted := value", .{});
            },
            else => return error.UnsupportedType,
        };

        const code = try generator.functionDefinition(
            "\nfunction @0(value) -> converted {\n@1\n}\n",
            .{ name, body },
        );

        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn shiftLeftFunction(
        self: *YulUtilFunctions,
        bits: usize,
    ) UtilError![]u8 {
        if (bits >= 256) return error.InvalidType;
        const name = try std.fmt.allocPrint(self.allocator, "shift_left_{d}", .{bits});
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const generator = try self.function_collector.generator(self.evm_version);
        const expression = if (self.evm_version.hasBitwiseShifting())
            try generator.expression("shl(@0, value)", .{bits})
        else blk: {
            const factor = try compactHex(self.allocator, @as(u256, 1) << @intCast(bits));
            defer self.allocator.free(factor);
            break :blk try generator.expression("mul(value, @0)", .{try generator.numberToken(factor)});
        };
        try self.function_collector.finishGeneratedFunction(name, try generator.functionDefinition(
            "function @0(value) -> newValue { newValue := @1 }",
            .{ name, expression },
        ));
        return self.function_collector.copyFunctionName(name);
    }

    pub fn shiftRightFunction(
        self: *YulUtilFunctions,
        bits: usize,
    ) UtilError![]u8 {
        if (bits >= 256) return error.InvalidType;
        const name = try std.fmt.allocPrint(
            self.allocator,
            "shift_right_{d}_unsigned",
            .{bits},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const generator = try self.function_collector.generator(self.evm_version);
        const expression = if (self.evm_version.hasBitwiseShifting())
            try generator.expression("shr(@0, value)", .{bits})
        else blk: {
            const factor = try compactHex(self.allocator, @as(u256, 1) << @intCast(bits));
            defer self.allocator.free(factor);
            break :blk try generator.expression("div(value, @0)", .{try generator.numberToken(factor)});
        };
        try self.function_collector.finishGeneratedFunction(name, try generator.functionDefinition(
            "function @0(value) -> newValue { newValue := @1 }",
            .{ name, expression },
        ));
        return self.function_collector.copyFunctionName(name);
    }

    pub fn shiftLeftFunctionDynamic(self: *YulUtilFunctions) UtilError![]u8 {
        return if (self.evm_version.hasBitwiseShifting())
            self.collectTemplate("shift_left_dynamic", "function shift_left_dynamic(bits, value) -> newValue { newValue := shl(bits, value) }")
        else
            self.collectTemplate("shift_left_dynamic", "function shift_left_dynamic(bits, value) -> newValue { newValue := mul(value, exp(2, bits)) }");
    }

    pub fn shiftRightFunctionDynamic(self: *YulUtilFunctions) UtilError![]u8 {
        return if (self.evm_version.hasBitwiseShifting())
            self.collectTemplate("shift_right_unsigned_dynamic", "function shift_right_unsigned_dynamic(bits, value) -> newValue { newValue := shr(bits, value) }")
        else
            self.collectTemplate("shift_right_unsigned_dynamic", "function shift_right_unsigned_dynamic(bits, value) -> newValue { newValue := div(value, exp(2, bits)) }");
    }

    pub fn shiftRightSignedFunctionDynamic(self: *YulUtilFunctions) UtilError![]u8 {
        return if (self.evm_version.hasBitwiseShifting())
            self.collectTemplate("shift_right_signed_dynamic", "function shift_right_signed_dynamic(bits, value) -> result { result := sar(bits, value) }")
        else
            self.collectTemplate("shift_right_signed_dynamic", "function shift_right_signed_dynamic(bits, value) -> result { let divisor := exp(2, bits) let xor_mask := sub(0, slt(value, 0)) result := xor(div(xor(value, xor_mask), divisor), xor_mask) }");
    }

    pub fn typedShiftLeftFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
        amount_type: *const Types.Type,
    ) UtilError![]u8 {
        return self.typedShiftFunction(type_ref, amount_type, false);
    }

    pub fn typedShiftRightFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
        amount_type: *const Types.Type,
    ) UtilError![]u8 {
        return self.typedShiftFunction(type_ref, amount_type, true);
    }

    fn typedShiftFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
        amount_type: *const Types.Type,
        right: bool,
    ) UtilError![]u8 {
        if ((type_ref.category() != .FixedBytes and type_ref.category() != .Integer) or
            amount_type.category() != .Integer or amount_type.payload.Integer.isSigned())
            return error.InvalidType;
        const type_identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(type_identifier);
        const amount_identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, amount_type);
        defer self.allocator.free(amount_identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "shift_{s}_{s}_{s}",
            .{ if (right) "right" else "left", type_identifier, amount_identifier },
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const clean_amount = try self.cleanupFunction(amount_type);
        defer self.allocator.free(clean_amount);
        const cleanup = try self.cleanupFunction(type_ref);
        defer self.allocator.free(cleanup);
        const shift = if (!right)
            try self.shiftLeftFunctionDynamic()
        else if (type_ref.category() == .Integer and type_ref.payload.Integer.isSigned())
            try self.shiftRightSignedFunctionDynamic()
        else
            try self.shiftRightFunctionDynamic();
        defer self.allocator.free(shift);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0(value, bits) -> result {\nbits := @1(bits)\nresult := @2(@3(bits, @4(value)))\n}\n",
            .{ name, clean_amount, cleanup, shift, cleanup },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn maskBytesFunctionDynamic(self: *YulUtilFunctions) UtilError![]u8 {
        const name = "mask_bytes_dynamic";
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const shift = try self.shiftRightFunctionDynamic();
        defer self.allocator.free(shift);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0(data, bytes) -> result {\nlet mask := not(@1(mul(8, bytes), not(0)))\nresult := and(data, mask)\n}\n",
            .{ name, shift },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn maskLowerOrderBytesFunction(
        self: *YulUtilFunctions,
        bytes: usize,
    ) UtilError![]u8 {
        if (bytes > 32) return error.InvalidType;
        const name = try std.fmt.allocPrint(
            self.allocator,
            "mask_lower_order_bytes_{d}",
            .{bytes},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const mask: u256 = if (bytes == 32)
            std.math.maxInt(u256)
        else if (bytes == 0)
            0
        else
            (@as(u256, 1) << @intCast(bytes * 8)) - 1;
        const mask_text = try compactHex(self.allocator, mask);
        defer self.allocator.free(mask_text);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0(data) -> result {\nresult := and(data, @1)\n}\n",
            .{ name, try generator.numberToken(mask_text) },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn maskLowerOrderBytesFunctionDynamic(self: *YulUtilFunctions) UtilError![]u8 {
        const name = "mask_lower_order_bytes_dynamic";
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const shift = try self.shiftLeftFunctionDynamic();
        defer self.allocator.free(shift);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0(data, bytes) -> result {\nlet mask := not(@1(mul(8, bytes), not(0)))\nresult := and(data, mask)\n}\n",
            .{ name, shift },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn divide32CeilFunction(self: *YulUtilFunctions) UtilError![]u8 {
        return self.collectTemplate(
            "divide_by_32_ceil",
            "function divide_by_32_ceil(value) -> result { result := div(add(value, 31), 32) }\n",
        );
    }

    pub fn allocateUnboundedFunction(self: *YulUtilFunctions) UtilError![]u8 {
        return self.collectTemplate(
            "allocate_unbounded",
            "\nfunction allocate_unbounded() -> memPtr {\nmemPtr := mload(64)\n}\n",
        );
    }

    pub fn roundUpFunction(self: *YulUtilFunctions) UtilError![]u8 {
        return self.collectTemplate(
            "round_up_to_mul_of_32",
            "function round_up_to_mul_of_32(value) -> result { result := and(add(value, 31), not(31)) }\n",
        );
    }

    pub fn finalizeAllocationFunction(self: *YulUtilFunctions) UtilError![]u8 {
        const name = "finalize_allocation";
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const round_up = try self.roundUpFunction();
        defer self.allocator.free(round_up);
        const panic = try self.panicFunction(.resource_error);
        defer self.allocator.free(panic);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "function @0(memPtr, size) { let newFreePtr := add(memPtr, @1(size)) if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, memPtr)) { @2() } mstore(64, newFreePtr) }\n",
            .{ name, round_up, panic },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    /// Revert with the complete returndata produced by a failed external call.
    /// This is the returndata-capable branch of upstream's
    /// `forwardingRevertFunction`; the pre-Byzantium branch remains explicit so
    /// callers do not accidentally emit unsupported opcodes for old targets.
    pub fn forwardingRevertFunction(self: *YulUtilFunctions) UtilError![]u8 {
        const forward = self.evm_version.supportsReturndata();
        const name = if (forward) "revert_forward_1" else "revert_forward_0";
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = if (forward) blk: {
            const allocate = try self.allocateUnboundedFunction();
            defer self.allocator.free(allocate);
            break :blk try generator.functionDefinition(
                "\nfunction @0() {\nlet pos := @1()\nreturndatacopy(pos, 0, returndatasize())\nrevert(pos, returndatasize())\n}\n",
                .{ name, allocate },
            );
        } else try generator.functionDefinition(
            "\nfunction @0() {\nrevert(0, 0)\n}\n",
            .{name},
        );

        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn allocationFunction(self: *YulUtilFunctions) UtilError![]u8 {
        const name = "allocate_memory";
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const unbounded = try self.allocateUnboundedFunction();
        defer self.allocator.free(unbounded);
        const finalize = try self.finalizeAllocationFunction();
        defer self.allocator.free(finalize);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "function @0(size) -> memPtr { memPtr := @1() @2(memPtr, size) }\n",
            .{ name, unbounded, finalize },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn zeroMemoryArrayFunction(
        self: *YulUtilFunctions,
        array_type: *const Types.Type,
    ) UtilError![]u8 {
        const array = switch (array_type.payload) {
            .Array => |value| value,
            else => return error.InvalidType,
        };
        if (TypeBehavior.hasSimpleZeroValueInMemory(array.base_type))
            return self.zeroMemoryFunction(array.base_type);
        return self.zeroComplexMemoryArrayFunction(array_type);
    }

    pub fn zeroMemoryFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        if (!TypeBehavior.hasSimpleZeroValueInMemory(type_ref))
            return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "zero_memory_chunk_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name))) return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const generator = try self.function_collector.generator(self.evm_version);
        try self.function_collector.finishGeneratedFunction(name, try generator.functionDefinition(
            "function @0(dataStart, dataSizeInBytes) { calldatacopy(dataStart, calldatasize(), dataSizeInBytes) }",
            .{name},
        ));
        return self.function_collector.copyFunctionName(name);
    }

    pub fn zeroComplexMemoryArrayFunction(
        self: *YulUtilFunctions,
        array_type: *const Types.Type,
    ) UtilError![]u8 {
        const array = switch (array_type.payload) {
            .Array => |value| value,
            else => return error.InvalidType,
        };
        if (TypeBehavior.hasSimpleZeroValueInMemory(array.base_type) or
            try TypeBehavior.memoryStride(array) != 32)
            return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, array_type);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "zero_complex_memory_array_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const zero = try self.zeroValueFunction(array.base_type, false);
        defer self.allocator.free(zero);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0(dataStart, dataSizeInBytes) {\nfor { let i := 0 } lt(i, dataSizeInBytes) { i := add(i, 32) } {\nmstore(add(dataStart, i), @1())\n}\n}\n",
            .{ name, zero },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn allocateMemoryArrayFunction(
        self: *YulUtilFunctions,
        array_type: *const Types.Type,
    ) UtilError![]u8 {
        const array = switch (array_type.payload) {
            .Array => |value| value,
            else => return error.InvalidType,
        };
        if (array.reference.location != .Memory) return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, array_type);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "allocate_memory_array_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const allocation = try self.allocationFunction();
        defer self.allocator.free(allocation);
        // Preserve upstream Whiskers substitution order: allocation is
        // requested before the array-size helper even though allocSize occurs
        // first in the rendered Yul body.
        const allocation_size = try self.arrayAllocationSizeFunction(array_type);
        defer self.allocator.free(allocation_size);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0(length) -> memPtr {\nlet allocSize := @1(length)\nmemPtr := @2(allocSize)\n@3\n}\n",
            .{
                name,
                allocation_size,
                allocation,
                if (array.isDynamicallySized()) try generator.statements("mstore(memPtr, length)", .{}) else Yul.Block{},
            },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn allocateAndInitializeMemoryArrayFunction(
        self: *YulUtilFunctions,
        array_type: *const Types.Type,
    ) UtilError![]u8 {
        const array = switch (array_type.payload) {
            .Array => |value| value,
            else => return error.InvalidType,
        };
        if (array.reference.location != .Memory) return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, array_type);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "allocate_and_zero_memory_array_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const allocate = try self.allocateMemoryArrayFunction(array_type);
        defer self.allocator.free(allocate);
        const allocation_size = try self.arrayAllocationSizeFunction(array_type);
        defer self.allocator.free(allocation_size);
        const zero = try self.zeroMemoryArrayFunction(array_type);
        defer self.allocator.free(zero);
        const generator = try self.function_collector.generator(self.evm_version);
        const dynamic_setup = if (array.isDynamicallySized())
            try generator.statements("dataStart := add(dataStart, 32)\ndataSize := sub(dataSize, 32)", .{})
        else
            Yul.Block{};
        const code = try generator.functionDefinition(
            "\nfunction @0(length) -> memPtr {\nmemPtr := @1(length)\nlet dataStart := memPtr\nlet dataSize := @2(length)\n@3\n@4(dataStart, dataSize)\n}\n",
            .{ name, allocate, allocation_size, dynamic_setup, zero },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn allocateMemoryStructFunction(
        self: *YulUtilFunctions,
        struct_type: *const Types.Type,
    ) UtilError![]u8 {
        const structure = switch (struct_type.payload) {
            .Struct => |value| value,
            else => return error.InvalidType,
        };
        _ = structure;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, struct_type);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "allocate_memory_struct_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const allocation = try self.allocationFunction();
        defer self.allocator.free(allocation);
        const size = try TypeBehavior.memoryDataSize(struct_type);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0() -> memPtr {\nmemPtr := @1(@2)\n}\n",
            .{ name, allocation, size },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn allocateAndInitializeMemoryStructFunction(
        self: *YulUtilFunctions,
        struct_type: *const Types.Type,
    ) UtilError![]u8 {
        const structure = switch (struct_type.payload) {
            .Struct => |value| value,
            else => return error.InvalidType,
        };
        if (structure.reference.location != .Memory) return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, struct_type);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "allocate_and_zero_memory_struct_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const allocate = try self.allocateMemoryStructFunction(struct_type);
        defer self.allocator.free(allocate);
        const members = try TypeBehavior.structMemoryMemberTypesAlloc(
            self.type_provider,
            self.allocator,
            structure,
        );
        defer self.allocator.free(members);
        const generator = try self.function_collector.generator(self.evm_version);
        var stores: Generated.Buffer = .{ .generator = generator };
        for (members) |member| {
            if (try TypeBehavior.memoryHeadSize(member) != 32)
                return error.InvalidType;
            const zero = try self.zeroValueFunction(member, false);
            defer self.allocator.free(zero);
            try stores.add(
                "mstore(offset, @0())\noffset := add(offset, 32)\n",
                .{zero},
            );
        }
        const code = try generator.functionDefinition(
            "\nfunction @0() -> memPtr {\nmemPtr := @1()\nlet offset := memPtr\n@2}\n",
            .{ name, allocate, stores.take() },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn readFromMemoryFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        return self.readFromMemoryOrCalldata(type_ref, false);
    }

    pub fn readFromMemory(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        return self.readFromMemoryOrCalldata(type_ref, false);
    }

    pub fn readFromCalldata(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        return self.readFromMemoryOrCalldata(type_ref, true);
    }

    pub fn readFromMemoryOrCalldata(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
        from_calldata: bool,
    ) UtilError![]u8 {
        if (from_calldata and TypeBehavior.isDynamicallyEncoded(type_ref))
            return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "read_from_{s}{s}",
            .{ if (from_calldata) "calldata" else "memory", identifier },
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = if (type_ref.asReference() != null) blk: {
            if (from_calldata or try TypeBehavior.sizeOnStack(type_ref) != 1)
                return error.InvalidType;
            break :blk try generator.functionDefinition(
                "\nfunction @0(memPtr) -> value {\nvalue := mload(memPtr)\n}\n",
                .{name},
            );
        } else blk: {
            if (!TypeBehavior.isValueType(type_ref)) return error.UnsupportedType;
            const external_function = type_ref.asFunction() != null and
                type_ref.payload.Function.kind == .External;
            const return_variables: []const []const u8 = if (external_function) &.{ "addr", "selector" } else &.{"returnValue"};
            const load = try generator.expression("@0(ptr)", .{if (from_calldata) "calldataload" else "mload"});
            const validate = if (from_calldata) try self.validatorFunction(type_ref, true) else null;
            defer if (validate) |value| self.allocator.free(value);
            const split = if (external_function) try self.splitExternalFunctionIdFunction() else null;
            defer if (split) |value| self.allocator.free(value);
            // solc registers cleanup after validation/splitting even for a
            // calldata read. Its enum/panic helpers can be used later, and
            // their insertion order determines the final bytecode layout.
            const cleanup = try self.cleanupFunction(type_ref);
            defer self.allocator.free(cleanup);
            const post_load = if (from_calldata)
                try generator.statements(
                    "let value := @0\n@1(value)",
                    .{ load, validate.? },
                )
            else
                try generator.statements(
                    "let value := @0(@1)",
                    .{ cleanup, load },
                );

            const result = if (split) |split_name|
                try generator.statements(
                    "addr, selector := @0(value)",
                    .{split_name},
                )
            else
                try generator.statements("returnValue := value", .{});

            break :blk try generator.functionDefinition(
                "\nfunction @0(ptr) -> @1 {\n@2\n@3\n}\n",
                .{ name, return_variables, post_load, result },
            );
        };
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn writeToMemoryFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        if (type_ref.category() == .StringLiteral) return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "write_to_memory_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = if (type_ref.asReference()) |reference| blk: {
            if (reference.location != .Memory) return error.InvalidType;
            break :blk try generator.functionDefinition(
                "\nfunction @0(memPtr, value) {\nmstore(memPtr, value)\n}\n",
                .{name},
            );
        } else if (type_ref.asFunction()) |function| blk: {
            if (function.kind == .External) {
                const combine = try self.combineExternalFunctionIdFunction();
                defer self.allocator.free(combine);
                break :blk try generator.functionDefinition(
                    "\nfunction @0(memPtr, addr, selector) {\nmstore(memPtr, @1(addr, selector))\n}\n",
                    .{ name, combine },
                );
            }
            if (!TypeBehavior.isValueType(type_ref)) return error.UnsupportedType;
            const cleanup = try self.cleanupFunction(type_ref);
            defer self.allocator.free(cleanup);
            break :blk try generator.functionDefinition(
                "\nfunction @0(memPtr, value) {\nmstore(memPtr, @1(value))\n}\n",
                .{ name, cleanup },
            );
        } else blk: {
            if (!TypeBehavior.isValueType(type_ref)) return error.UnsupportedType;
            const cleanup = try self.cleanupFunction(type_ref);
            defer self.allocator.free(cleanup);
            break :blk try generator.functionDefinition(
                "\nfunction @0(memPtr, value) {\nmstore(memPtr, @1(value))\n}\n",
                .{ name, cleanup },
            );
        };
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn mappingIndexAccessFunction(
        self: *YulUtilFunctions,
        mapping_type: *const Types.Type,
        key_type: *const Types.Type,
        packed_encoder_name: ?[]const u8,
    ) UtilError![]u8 {
        const mapping = switch (mapping_type.payload) {
            .Mapping => |value| value,
            else => return error.InvalidType,
        };
        const stack_size = try TypeBehavior.sizeOnStack(key_type);
        const mapping_identifier = try TypeBehavior.compatibilityIdentifierAlloc(
            self.allocator,
            self.compatibility_ids,
            mapping_type,
        );
        defer self.allocator.free(mapping_identifier);
        const key_identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, key_type);
        defer self.allocator.free(key_identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "mapping_index_access_{s}_of_{s}",
            .{ mapping_identifier, key_identifier },
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);

        const generator = try self.function_collector.generator(self.evm_version);
        const code = if (TypeBehavior.isDynamicallySized(mapping.key_type)) dynamic: {
            const keys = try generator.indexedNames("key_", stack_size);
            const encoder = packed_encoder_name orelse return error.InvalidType;
            const uint_type = self.type_provider.uint256();
            const hash = try self.packedHashFunction(
                &.{ key_type, uint_type },
                &.{ mapping.key_type, uint_type },
                encoder,
            );
            defer self.allocator.free(hash);
            break :dynamic try generator.functionDefinition(
                "function @0(slot, @1) -> dataSlot { dataSlot := @2(@1, slot) }",
                .{ name, keys, hash },
            );
        } else static: {
            if (packed_encoder_name != null or stack_size > 1 or
                TypeBehavior.isDynamicallyEncoded(mapping.key_type))
                return error.InvalidType;
            const conversion = try self.conversionFunction(
                key_type,
                mapping.key_type,
            );
            defer self.allocator.free(conversion);
            // Match solc's static-key name. Renaming this parameter can change
            // optimizer name allocation and, subsequently, inlining decisions.
            const key = [_]YulName{try generator.name("key")};
            const keys = key[0..stack_size];
            break :static try generator.functionDefinition(
                "function @0(slot, @1) -> dataSlot { mstore(0, @2(@1)) mstore(0x20, slot) dataSlot := keccak256(0, 0x40) }",
                .{ name, keys, conversion },
            );
        };

        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn cleanupFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        if (type_ref.category() == .UserDefinedValueType) {
            const underlying = type_ref.payload.UserDefinedValueType.underlying_type orelse
                return error.InvalidType;
            return self.cleanupFunction(underlying);
        }
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(self.allocator, "cleanup_{s}", .{identifier});
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);

        const body = try self.cleanupBody(type_ref);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0(value) -> cleaned {\n@1\n}\n",
            .{ name, body },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    fn cleanupBody(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError!Yul.Block {
        const generator = try self.function_collector.generator(self.evm_version);
        return switch (type_ref.payload) {
            .Address => blk: {
                const uint160 = Types.Type{ .payload = .{ .Integer = .{
                    .bits = 160,
                    .modifier = .Unsigned,
                } } };
                const cleanup = try self.cleanupFunction(&uint160);
                defer self.allocator.free(cleanup);
                break :blk generator.statements(
                    "cleaned := @0(value)",
                    .{cleanup},
                );
            },
            .Contract => blk: {
                const address = (try TypeBehavior.encodingType(self.type_provider, type_ref)) orelse
                    return error.InvalidType;
                const cleanup = try self.cleanupFunction(address);
                defer self.allocator.free(cleanup);
                break :blk generator.statements(
                    "cleaned := @0(value)",
                    .{cleanup},
                );
            },
            .Integer => |integer| if (integer.bits == 256)
                generator.statements("cleaned := value", .{})
            else if (integer.isSigned())
                generator.statements(
                    "cleaned := signextend(@0, value)",
                    .{integer.bits / 8 - 1},
                )
            else blk: {
                const mask = (@as(u256, 1) << @intCast(integer.bits)) - 1;
                const rendered = try compactHex(self.allocator, mask);
                defer self.allocator.free(rendered);
                break :blk generator.statements(
                    "cleaned := and(value, @0)",
                    .{try generator.numberToken(rendered)},
                );
            },
            .RationalNumber => generator.statements("cleaned := value", .{}),
            .Bool => generator.statements("cleaned := iszero(iszero(value))", .{}),
            .Function => |function| switch (function.kind) {
                .External => blk: {
                    const bytes24 = Types.Type{ .payload = .{ .FixedBytes = .{ .bytes = 24 } } };
                    const cleanup = try self.cleanupFunction(&bytes24);
                    defer self.allocator.free(cleanup);
                    break :blk generator.statements(
                        "cleaned := @0(value)",
                        .{cleanup},
                    );
                },
                .Internal => generator.statements("cleaned := value", .{}),
                else => error.UnsupportedType,
            },
            .Array, .Struct, .Mapping => if (TypeBehavior.dataStoredIn(type_ref, .Storage))
                generator.statements("cleaned := value", .{})
            else
                error.UnsupportedType,
            .FixedBytes => |fixed| if (fixed.bytes == 32)
                generator.statements("cleaned := value", .{})
            else if (fixed.bytes == 0)
                error.InvalidType
            else blk: {
                const bits: u16 = @as(u16, fixed.bytes) * 8;
                const low_mask = (@as(u256, 1) << @intCast(bits)) - 1;
                const mask = low_mask << @intCast(256 - bits);
                const rendered = try compactHex(self.allocator, mask);
                defer self.allocator.free(rendered);
                break :blk generator.statements(
                    "cleaned := and(value, @0)",
                    .{try generator.numberToken(rendered)},
                );
            },
            .Enum => blk: {
                const validator = try self.validatorFunction(type_ref, false);
                defer self.allocator.free(validator);
                break :blk generator.statements(
                    "cleaned := value @0(value)",
                    .{validator},
                );
            },
            .InaccessibleDynamic => generator.statements("cleaned := 0", .{}),
            else => error.UnsupportedType,
        };
    }

    pub fn cleanupFromStorageFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        if (!TypeBehavior.isValueType(type_ref)) return error.UnsupportedType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "cleanup_from_storage_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);

        const encoding_type = switch (type_ref.payload) {
            .UserDefinedValueType => |value| value.underlying_type orelse
                return error.InvalidType,
            else => type_ref,
        };
        const generator = try self.function_collector.generator(self.evm_version);
        const storage_bytes = try TypeBehavior.storageBytes(encoding_type);
        const expression = if (encoding_type.asInteger()) |integer|
            if (integer.isSigned() and storage_bytes != 32)
                try generator.expression(
                    "signextend(@0, value)",
                    .{storage_bytes - 1},
                )
            else
                try self.storageCleanupExpression(encoding_type, storage_bytes)
        else
            try self.storageCleanupExpression(encoding_type, storage_bytes);
        const code = try generator.functionDefinition(
            "\nfunction @0(value) -> cleaned {\ncleaned := @1\n}\n",
            .{ name, expression },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn extractFromStorageValueDynamicFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "extract_from_storage_value_dynamic{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const shift = try self.shiftRightFunctionDynamic();
        defer self.allocator.free(shift);
        const cleanup = try self.cleanupFromStorageFunction(type_ref);
        defer self.allocator.free(cleanup);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0(slot_value, offset) -> value {\nvalue := @1(@2(mul(offset, 8), slot_value))\n}\n",
            .{ name, cleanup, shift },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn readFromStorageDynamicFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        if (!TypeBehavior.isValueType(type_ref)) return error.UnsupportedType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "read_from_storage_split_dynamic_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const extract = try self.extractFromStorageValueDynamicFunction(type_ref);
        defer self.allocator.free(extract);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0(slot, offset) -> value {\nvalue := @1(sload(slot), offset)\n\n}\n",
            .{ name, extract },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn extractFromStorageValueFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
        offset: u32,
    ) UtilError![]u8 {
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "extract_from_storage_value_offset_{d}_{s}",
            .{ offset, identifier },
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const shift = try self.shiftRightFunction(@as(usize, offset) * 8);
        defer self.allocator.free(shift);
        const cleanup = try self.cleanupFromStorageFunction(type_ref);
        defer self.allocator.free(cleanup);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0(slot_value) -> value {\nvalue := @1(@2(slot_value))\n}\n",
            .{ name, cleanup, shift },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn readFromStorageFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
        offset: u32,
    ) UtilError![]u8 {
        if (!TypeBehavior.isValueType(type_ref)) return error.UnsupportedType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "read_from_storage_split_offset_{d}_{s}",
            .{ offset, identifier },
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const extract = try self.extractFromStorageValueFunction(type_ref, offset);
        defer self.allocator.free(extract);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0(slot) -> value {\nvalue := @1(sload(slot))\n\n}\n",
            .{ name, extract },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn readFromStorage(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
        offset: u32,
        split_function_types: bool,
        location: AST.VariableLocation,
    ) UtilError![]u8 {
        if (TypeBehavior.isValueType(type_ref))
            return self.readFromStorageValueType(
                type_ref,
                offset,
                split_function_types,
                location,
            );
        if (location == .Transient or offset != 0) return error.InvalidType;
        return self.readFromStorageReferenceType(type_ref);
    }

    pub fn readFromStorageDynamic(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
        split_function_types: bool,
        location: AST.VariableLocation,
    ) UtilError![]u8 {
        if (TypeBehavior.isValueType(type_ref))
            return self.readFromStorageValueType(
                type_ref,
                null,
                split_function_types,
                location,
            );
        if (location == .Transient) return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "read_from_storage__dynamic_{s}{s}",
            .{ if (split_function_types) "split_" else "", identifier },
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const panic = try self.panicFunction(.generic);
        defer self.allocator.free(panic);
        const read = try self.readFromStorageReferenceType(type_ref);
        defer self.allocator.free(read);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0(slot, offset) -> value {\nif gt(offset, 0) { @1() }\nvalue := @2(slot)\n}\n",
            .{ name, panic, read },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn readFromStorageValueType(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
        offset: ?u32,
        split_function_types: bool,
        location: AST.VariableLocation,
    ) UtilError![]u8 {
        if (!TypeBehavior.isValueType(type_ref) or
            (location != .Transient and location != .Unspecified))
            return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const offset_name = if (offset) |value|
            try std.fmt.allocPrint(self.allocator, "offset_{d}", .{value})
        else
            try self.allocator.dupe(u8, "dynamic");
        defer self.allocator.free(offset_name);
        const external_split = split_function_types and type_ref.asFunction() != null and
            type_ref.payload.Function.kind == .External;
        const name = try std.fmt.allocPrint(
            self.allocator,
            "read_from_{s}storage_{s}{s}_{s}",
            .{
                if (location == .Transient) "transient_" else "",
                if (split_function_types) "split_" else "",
                offset_name,
                identifier,
            },
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const extract = if (offset) |value|
            try self.extractFromStorageValueFunction(type_ref, value)
        else
            try self.extractFromStorageValueDynamicFunction(type_ref);
        defer self.allocator.free(extract);
        const generator = try self.function_collector.generator(self.evm_version);
        const extracted_call = if (offset == null)
            try generator.expression(
                "@0(@1(slot), offset)",
                .{ extract, if (location == .Transient) "tload" else "sload" },
            )
        else
            try generator.expression(
                "@0(@1(slot))",
                .{ extract, if (location == .Transient) "tload" else "sload" },
            );

        const body = if (external_split) blk: {
            const split = try self.splitExternalFunctionIdFunction();
            defer self.allocator.free(split);
            break :blk try generator.statements(
                "let value := @0\naddr, selector := @1(value)",
                .{ extracted_call, split },
            );
        } else try generator.statements("value := @0", .{extracted_call});

        const code = try generator.functionDefinition(
            "\nfunction @0(@1) -> @2 {\n@3\n}\n",
            .{
                name,
                @as([]const []const u8, if (offset == null) &.{ "slot", "offset" } else &.{"slot"}),
                @as([]const []const u8, if (external_split) &.{ "addr", "selector" } else &.{"value"}),
                body,
            },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn readFromStorageReferenceType(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        if (switch (type_ref.payload) {
            .Array => true,
            else => false,
        }) {
            const array = type_ref.payload.Array;
            if (array.reference.location != .Memory) return error.InvalidType;
            const storage_type = try self.type_provider.withLocationIfReference(
                .Storage,
                type_ref,
                false,
            );
            return self.copyArrayFromStorageToMemoryFunction(storage_type, type_ref);
        }
        const structure = switch (type_ref.payload) {
            .Struct => |value| value,
            else => return error.InvalidType,
        };
        if (structure.reference.location != .Memory) return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "read_from_storage_reference_type_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const members = try TypeBehavior.structMemoryMemberTypesAlloc(
            self.type_provider,
            self.allocator,
            structure,
        );
        defer self.allocator.free(members);
        const offsets = try TypeBehavior.structStorageOffsetsAlloc(
            self.allocator,
            structure,
        );
        defer self.allocator.free(offsets.offsets);
        const generator = try self.function_collector.generator(self.evm_version);
        var body: Generated.Buffer = .{ .generator = generator };
        var memory_offset: u256 = 0;
        for (members, offsets.offsets) |member, maybe_offset| {
            const storage_offset = maybe_offset orelse return error.InvalidType;
            if (!TypeBehavior.isValueType(member) and storage_offset.byte_offset != 0)
                return error.InvalidType;
            const stack_size = try TypeBehavior.sizeOnStack(member);
            if (stack_size == 0) return error.InvalidType;
            const values = try generator.indexedNames(
                "memberValue_",
                stack_size,
            );

            const read = try self.readFromStorage(
                member,
                storage_offset.byte_offset,
                true,
                .Unspecified,
            );
            defer self.allocator.free(read);
            const write = try self.writeToMemoryFunction(member);
            defer self.allocator.free(write);
            try body.add(
                "{ let @0 := @1(add(slot, @2)) @3(add(value, @4), @5) }\n",
                .{ values, read, storage_offset.slot, write, memory_offset, values },
            );
            memory_offset = std.math.add(
                u256,
                memory_offset,
                try TypeBehavior.memoryHeadSize(member),
            ) catch return error.Overflow;
        }
        // solc requests member read/write helpers before the allocator.
        // This declaration order affects optimizer naming and inlining.
        const allocate = try self.allocateMemoryStructFunction(type_ref);
        defer self.allocator.free(allocate);
        const code = try generator.functionDefinition(
            "\nfunction @0(slot) -> value {\nvalue := @1()\n@2}\n",
            .{ name, allocate, body.take() },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn extractFromStorageValue(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
        offset: u32,
    ) UtilError![]u8 {
        return self.extractFromStorageValueFunction(type_ref, offset);
    }

    pub fn extractFromStorageValueDynamic(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        return self.extractFromStorageValueDynamicFunction(type_ref);
    }

    pub fn updateByteSliceFunctionDynamic(
        self: *YulUtilFunctions,
        num_bytes: u8,
    ) UtilError![]u8 {
        return self.updateByteSliceDynamicFunction(num_bytes);
    }

    pub fn updateByteSliceFunction(
        self: *YulUtilFunctions,
        num_bytes: u8,
        shift_bytes: u32,
    ) UtilError![]u8 {
        if (num_bytes > 32 or shift_bytes > 32 or
            @as(u32, num_bytes) + shift_bytes > 32)
            return error.InvalidType;
        const name = try std.fmt.allocPrint(
            self.allocator,
            "update_byte_slice_{d}_shift_{d}",
            .{ num_bytes, shift_bytes },
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const num_bits: usize = @as(usize, num_bytes) * 8;
        const shift_bits: usize = @as(usize, shift_bytes) * 8;
        const low_mask = if (num_bits == 256)
            std.math.maxInt(u256)
        else
            (@as(u256, 1) << @intCast(num_bits)) - 1;
        const mask = low_mask << @intCast(shift_bits);
        const mask_text = try Numeric.formatNumberU256Alloc(self.allocator, mask);
        defer self.allocator.free(mask_text);
        const shift = try self.shiftLeftFunction(shift_bits);
        defer self.allocator.free(shift);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0(value, toInsert) -> result {\nlet mask := @1\ntoInsert := @2(toInsert)\nvalue := and(value, not(mask))\nresult := or(value, and(toInsert, mask))\n}\n",
            .{ name, try generator.numberToken(mask_text), shift },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn updateByteSliceDynamicFunction(
        self: *YulUtilFunctions,
        num_bytes: u8,
    ) UtilError![]u8 {
        if (num_bytes > 32) return error.InvalidType;
        const name = try std.fmt.allocPrint(
            self.allocator,
            "update_byte_slice_dynamic{d}",
            .{num_bytes},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const bits: usize = @as(usize, num_bytes) * 8;
        const mask = if (bits == 256)
            std.math.maxInt(u256)
        else
            (@as(u256, 1) << @intCast(bits)) - 1;
        const mask_text = try Numeric.formatNumberU256Alloc(self.allocator, mask);
        defer self.allocator.free(mask_text);
        const shift = try self.shiftLeftFunctionDynamic();
        defer self.allocator.free(shift);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0(value, shiftBytes, toInsert) -> result {\nlet shiftBits := mul(shiftBytes, 8)\nlet mask := @1(shiftBits, @2)\ntoInsert := @3(shiftBits, toInsert)\nvalue := and(value, not(mask))\nresult := or(value, and(toInsert, mask))\n}\n",
            .{ name, shift, try generator.numberToken(mask_text), shift },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn prepareStoreFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        if (!TypeBehavior.isValueType(type_ref)) return error.UnsupportedType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "prepare_store_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const generator = try self.function_collector.generator(self.evm_version);
        const external_function = type_ref.asFunction() != null and
            type_ref.payload.Function.kind == .External;
        if (external_function) {
            const bytes24 = try self.type_provider.fixedBytes(24);
            const prepare = try self.prepareStoreFunction(bytes24);
            defer self.allocator.free(prepare);
            const combine = try self.combineExternalFunctionIdFunction();
            defer self.allocator.free(combine);
            const code = try generator.functionDefinition(
                "\nfunction @0(addr, selector) -> ret {\nret := @1(@2(addr, selector))\n}\n",
                .{ name, prepare, combine },
            );
            try self.function_collector.finishGeneratedFunction(name, code);
            return self.function_collector.copyFunctionName(name);
        }
        if (try TypeBehavior.sizeOnStack(type_ref) != 1)
            return error.UnsupportedType;
        const expression = if (try TypeBehavior.leftAligned(type_ref)) blk: {
            const bytes = try TypeBehavior.storageBytes(type_ref);
            const shift = try self.shiftRightFunction(256 - @as(usize, bytes) * 8);
            defer self.allocator.free(shift);
            break :blk try generator.expression("@0(value)", .{shift});
        } else try generator.identifier("value");
        const code = try generator.functionDefinition(
            "\nfunction @0(value) -> ret {\nret := @1\n}\n",
            .{ name, expression },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn updateStorageValueFunction(
        self: *YulUtilFunctions,
        from_type: *const Types.Type,
        to_type: *const Types.Type,
        offset: ?u32,
    ) UtilError![]u8 {
        return self.updateStorageValueAtLocationFunction(
            from_type,
            to_type,
            .Unspecified,
            offset,
        );
    }

    pub fn updateStorageValueAtLocationFunction(
        self: *YulUtilFunctions,
        from_type: *const Types.Type,
        to_type: *const Types.Type,
        location: AST.VariableLocation,
        offset: ?u32,
    ) UtilError![]u8 {
        if (location != .Transient and location != .Unspecified)
            return error.InvalidType;
        const from_identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, from_type);
        defer self.allocator.free(from_identifier);
        const to_identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, to_type);
        defer self.allocator.free(to_identifier);
        const offset_part = if (offset) |value|
            try std.fmt.allocPrint(self.allocator, "offset_{d}_", .{value})
        else
            try self.allocator.alloc(u8, 0);
        defer self.allocator.free(offset_part);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "update_{s}storage_value_{s}{s}_to_{s}",
            .{
                if (location == .Transient) "transient_" else "",
                offset_part,
                from_identifier,
                to_identifier,
            },
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);

        const generator = try self.function_collector.generator(self.evm_version);
        const offset_name = try generator.name("offset");
        const offset_names: []const YulName = if (offset == null) &.{offset_name} else &.{};
        const code = if (TypeBehavior.isValueType(to_type)) value: {
            if (!TypeBehavior.isImplicitlyConvertibleTo(from_type, to_type))
                return error.InvalidType;
            const storage_bytes = try TypeBehavior.storageBytes(to_type);
            if (storage_bytes == 0 or storage_bytes > 32) return error.InvalidType;
            const from_size = try TypeBehavior.sizeOnStack(from_type);
            const to_size = try TypeBehavior.sizeOnStack(to_type);
            const from_values = try generator.indexedNames("value_", from_size);

            const to_values = try generator.indexedNames(
                "convertedValue_",
                to_size,
            );

            const update = if (offset) |value_offset|
                try self.updateByteSliceFunction(storage_bytes, value_offset)
            else
                try self.updateByteSliceDynamicFunction(storage_bytes);
            defer self.allocator.free(update);
            const conversion = try self.conversionFunction(from_type, to_type);
            defer self.allocator.free(conversion);
            const prepare = try self.prepareStoreFunction(to_type);
            defer self.allocator.free(prepare);
            break :value try generator.functionDefinition(
                "\nfunction @0(slot, @1, @2) {\nlet @3 := @4(@5)\n@6(slot, @7(@8(slot), @9, @10(@11)))\n}\n",
                .{
                    name,
                    offset_names,
                    from_values,
                    to_values,
                    conversion,
                    from_values,
                    if (location == .Transient) "tstore" else "sstore",
                    update,
                    if (location == .Transient) "tload" else "sload",
                    offset_names,
                    prepare,
                    to_values,
                },
            );
        } else reference: {
            if (location == .Transient) return error.InvalidType;
            const dynamic_offset = offset == null;
            if (offset != null and offset.? != 0) return error.InvalidType;
            // Whiskers evaluates this substitution even when the conditional
            // block that references it is disabled by a static offset.
            const panic = try self.panicFunction(.generic);
            defer self.allocator.free(panic);
            const guard = if (dynamic_offset)
                try generator.statements(
                    "if offset { @0() }",
                    .{panic},
                )
            else
                Yul.Block{};

            if (from_type.category() == .StringLiteral) {
                const target = to_type.asArray() orelse return error.InvalidType;
                if (!target.isByteArrayOrString()) return error.InvalidType;
                const copy = try self.copyLiteralToStorageFunction(
                    from_type.payload.StringLiteral.value,
                );
                defer self.allocator.free(copy);
                break :reference try generator.functionDefinition(
                    "\nfunction @0(slot, @1) {\n@2\n@3(slot)\n}\n",
                    .{ name, offset_names, guard, copy },
                );
            }
            const from_size = try TypeBehavior.sizeOnStack(from_type);
            const values = try generator.indexedNames("value_", from_size);

            const copy = switch (from_type.payload) {
                .Array => self.copyArrayToStorageFunction(from_type, to_type),
                .ArraySlice => |slice| self.copyArrayToStorageFunction(
                    slice.array_type,
                    to_type,
                ),
                .Struct => self.copyStructToStorageFunction(from_type, to_type),
                else => return error.InvalidType,
            };
            const copy_name = try copy;
            defer self.allocator.free(copy_name);
            break :reference try generator.functionDefinition(
                "\nfunction @0(slot, @1, @2) {\n@3\n@4(slot, @5)\n}\n",
                .{
                    name,
                    offset_names,
                    values,
                    guard,
                    copy_name,
                    values,
                },
            );
        };
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn storageSetToZeroFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        return self.storageSetToZeroAtLocationFunction(
            type_ref,
            .Unspecified,
        );
    }

    pub fn storageSetToZeroAtLocationFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
        location: AST.VariableLocation,
    ) UtilError![]u8 {
        if (location != .Transient and location != .Unspecified)
            return error.InvalidType;
        if (!TypeBehavior.isValueType(type_ref) and location == .Transient)
            return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "{s}storage_set_to_zero_{s}",
            .{ if (location == .Transient) "transient_" else "", identifier },
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const generator = try self.function_collector.generator(self.evm_version);
        const body = if (TypeBehavior.isValueType(type_ref)) blk: {
            const stack_size = try TypeBehavior.sizeOnStack(type_ref);
            if (stack_size == 0) return error.UnsupportedType;
            const update = try self.updateStorageValueAtLocationFunction(
                type_ref,
                type_ref,
                location,
                null,
            );
            defer self.allocator.free(update);
            const zero = try self.zeroValueFunction(type_ref, true);
            defer self.allocator.free(zero);
            const values = try generator.indexedNames("zero_", stack_size);

            break :blk try generator.statements(
                "let @0 := @1()\n@2(slot, offset, @3)",
                .{ values, zero, update, values },
            );
        } else switch (type_ref.payload) {
            .Array => blk: {
                const clear = try self.clearStorageArrayFunction(type_ref);
                defer self.allocator.free(clear);
                const panic = try self.panicFunction(.generic);
                defer self.allocator.free(panic);
                break :blk try generator.statements(
                    "if iszero(eq(offset, 0)) { @0() }\n@1(slot)",
                    .{ panic, clear },
                );
            },
            .Struct => blk: {
                const clear = try self.clearStorageStructFunction(type_ref);
                defer self.allocator.free(clear);
                const panic = try self.panicFunction(.generic);
                defer self.allocator.free(panic);
                break :blk try generator.statements(
                    "if iszero(eq(offset, 0)) { @0() }\n@1(slot)",
                    .{ panic, clear },
                );
            },
            else => return error.UnsupportedType,
        };

        const code = try generator.functionDefinition(
            "\nfunction @0(slot, offset) {\n@1\n}\n",
            .{ name, body },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn storageArrayPopFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        const array = type_ref.asArray() orelse return error.InvalidType;
        if (array.reference.location != .Storage or !array.isDynamicallySized() or
            try TypeBehavior.storageBytes(array.base_type) > 32)
            return error.InvalidType;
        if (array.isByteArrayOrString())
            return self.storageByteArrayPopFunction(type_ref);
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(self.allocator, "array_pop_{s}", .{identifier});
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const panic = try self.panicFunction(.empty_array_pop);
        defer self.allocator.free(panic);
        const length = try self.arrayLengthFunction(type_ref);
        defer self.allocator.free(length);
        const index = try self.storageArrayIndexAccessFunction(type_ref);
        defer self.allocator.free(index);
        const generator = try self.function_collector.generator(self.evm_version);
        const clear_statement = if (array.base_type.category() == .Mapping)
            Yul.Block{}
        else blk: {
            const clear = try self.storageSetToZeroFunction(array.base_type);
            defer self.allocator.free(clear);
            break :blk try generator.statements(
                "@0(slot, offset)",
                .{clear},
            );
        };

        const code = try generator.functionDefinition(
            \\function @0(array) {
            \\    let oldLen := @1(array)
            \\    if iszero(oldLen) { @2() }
            \\    let newLen := sub(oldLen, 1)
            \\    let slot, offset := @3(array, newLen)
            \\    @4
            \\    sstore(array, newLen)
            \\}
        , .{ name, length, panic, index, clear_statement });
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn storageByteArrayPopFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        const array = type_ref.asArray() orelse return error.InvalidType;
        if (array.reference.location != .Storage or !array.isDynamicallySized() or
            !array.isByteArrayOrString())
            return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "byte_array_pop_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const extract = try self.extractByteArrayLengthFunction();
        defer self.allocator.free(extract);
        const panic = try self.panicFunction(.empty_array_pop);
        defer self.allocator.free(panic);
        const transit = try self.byteArrayTransitLongToShortFunction(type_ref);
        defer self.allocator.free(transit);
        const encode = try self.shortByteArrayEncodeUsedAreaSetLengthFunction();
        defer self.allocator.free(encode);
        const index = try self.longByteArrayStorageIndexAccessNoCheckFunction();
        defer self.allocator.free(index);
        const clear = try self.storageSetToZeroFunction(array.base_type);
        defer self.allocator.free(clear);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            \\function @0(array) {
            \\    let data := sload(array)
            \\    let oldLen := @1(data)
            \\    if iszero(oldLen) { @2() }
            \\    switch oldLen
            \\    case 32 { @3(array, 31) }
            \\    default {
            \\        let newLen := sub(oldLen, 1)
            \\        switch lt(oldLen, 32)
            \\        case 1 { sstore(array, @4(data, newLen)) }
            \\        default {
            \\            let slot, offset := @5(array, newLen)
            \\            @6(slot, offset)
            \\            sstore(array, sub(data, 2))
            \\        }
            \\    }
            \\}
        , .{ name, extract, panic, transit, encode, index, clear });
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn storageArrayPushFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
        maybe_from_type: ?*const Types.Type,
    ) UtilError![]u8 {
        const array = type_ref.asArray() orelse return error.InvalidType;
        if (array.reference.location != .Storage or !array.isDynamicallySized())
            return error.InvalidType;
        const from_type = maybe_from_type orelse array.base_type;
        if (TypeBehavior.isValueType(from_type) and
            !TypeBehavior.equals(from_type, array.base_type))
            return error.InvalidType;
        const from_identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, from_type);
        defer self.allocator.free(from_identifier);
        const to_identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(to_identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "array_push_from_{s}_to_{s}",
            .{ from_identifier, to_identifier },
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const value_count = try TypeBehavior.sizeOnStack(from_type);
        const generator = try self.function_collector.generator(self.evm_version);
        const values = try generator.indexedNames("value_", value_count);
        const panic = try self.panicFunction(.resource_error);
        defer self.allocator.free(panic);
        const extract = if (array.isByteArrayOrString())
            try self.extractByteArrayLengthFunction()
        else
            try self.allocator.alloc(u8, 0);
        defer self.allocator.free(extract);
        // Upstream binds this Whiskers substitution unconditionally, before
        // indexAccess, even though only the byte-array branch renders it.
        const data_area = try self.arrayDataAreaFunction(type_ref);
        defer self.allocator.free(data_area);
        const index = try self.storageArrayIndexAccessFunction(type_ref);
        defer self.allocator.free(index);
        const store = try self.updateStorageValueFunction(
            from_type,
            array.base_type,
            null,
        );
        defer self.allocator.free(store);
        const shift = try self.shiftLeftFunctionDynamic();
        defer self.allocator.free(shift);
        const body = if (array.isByteArrayOrString()) bytes: {
            if (value_count != 1) return error.InvalidType;
            break :bytes try generator.statements(
                \\let data := sload(array)
                \\let oldLen := @0(data)
                \\if iszero(lt(oldLen, 0x10000000000000000)) { @1() }
                \\switch gt(oldLen, 31)
                \\case 0 {
                \\    let value := byte(0, @2)
                \\    switch oldLen
                \\    case 31 {
                \\        let dataArea := @3(array)
                \\        data := and(data, not(0xff))
                \\        sstore(dataArea, or(and(0xff, value), data))
                \\        sstore(array, 65)
                \\    }
                \\    default {
                \\        data := add(data, 2)
                \\        let shiftBits := mul(8, sub(31, oldLen))
                \\        let valueShifted := @4(shiftBits, and(0xff, value))
                \\        let mask := @5(shiftBits, 0xff)
                \\        data := or(and(data, not(mask)), valueShifted)
                \\        sstore(array, data)
                \\    }
                \\}
                \\default {
                \\    sstore(array, add(data, 2))
                \\    let slot, offset := @6(array, oldLen)
                \\    @7(slot, offset, @8)
                \\}
            , .{
                extract,
                panic,
                values,
                data_area,
                shift,
                shift,
                index,
                store,
                values,
            });
        } else try generator.statements(
            \\let oldLen := sload(array)
            \\if iszero(lt(oldLen, 0x10000000000000000)) { @0() }
            \\sstore(array, add(oldLen, 1))
            \\let slot, offset := @1(array, oldLen)
            \\@2(slot, offset, @3)
        , .{ panic, index, store, values });

        const code = try generator.functionDefinition(
            "\nfunction @0(array, @1) {\n@2}\n",
            .{ name, values, body },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn storageArrayPushZeroFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        const array = type_ref.asArray() orelse return error.InvalidType;
        if (array.reference.location != .Storage or !array.isDynamicallySized() or
            try TypeBehavior.storageBytes(array.base_type) > 32)
            return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "array_push_zero_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const increase = if (array.isByteArrayOrString())
            try self.increaseByteArraySizeFunction(type_ref)
        else
            try self.allocator.alloc(u8, 0);
        defer self.allocator.free(increase);
        const extract = if (array.isByteArrayOrString())
            try self.extractByteArrayLengthFunction()
        else
            try self.allocator.alloc(u8, 0);
        defer self.allocator.free(extract);
        const panic = try self.panicFunction(.resource_error);
        defer self.allocator.free(panic);
        const length = try self.arrayLengthFunction(type_ref);
        defer self.allocator.free(length);
        const index = try self.storageArrayIndexAccessFunction(type_ref);
        defer self.allocator.free(index);
        const generator = try self.function_collector.generator(self.evm_version);
        const body = if (array.isByteArrayOrString()) blk: {
            break :blk try generator.statements(
                "let data := sload(array)\nlet oldLen := @0(data)\n@1(array, data, oldLen, add(oldLen, 1))",
                .{ extract, increase },
            );
        } else blk: {
            break :blk try generator.statements(
                "let oldLen := @0(array)\nif iszero(lt(oldLen, 0x10000000000000000)) { @1() }\nsstore(array, add(oldLen, 1))",
                .{ length, panic },
            );
        };

        const code = try generator.functionDefinition(
            "\nfunction @0(array) -> slot, offset {\n@1\nslot, offset := @2(array, oldLen)\n}\n",
            .{ name, body, index },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn partialClearStorageSlotFunction(self: *YulUtilFunctions) UtilError![]u8 {
        const name = "partial_clear_storage_slot";
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const shift = try self.shiftRightFunctionDynamic();
        defer self.allocator.free(shift);
        const ones = try compactHex(self.allocator, std.math.maxInt(u256));
        defer self.allocator.free(ones);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0(slot, offset) {\nlet mask := @1(mul(8, sub(32, offset)), @2)\nsstore(slot, and(mask, sload(slot)))\n}\n",
            .{ name, shift, try generator.numberToken(ones) },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn clearStorageRangeFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        const storage_bytes = try TypeBehavior.storageBytes(type_ref);
        if (storage_bytes < 32 and !TypeBehavior.isValueType(type_ref))
            return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "clear_storage_range_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const clear_type = if (storage_bytes < 32)
            self.type_provider.uint256()
        else
            type_ref;
        const clear = try self.storageSetToZeroFunction(clear_type);
        defer self.allocator.free(clear);
        const increment = try TypeBehavior.storageSize(type_ref);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0(startSlot, slotCount) {\nfor { let i := 0 } lt(i, slotCount) { i := add(i, @1) } {\n@2(add(startSlot, i), 0)\n}\n}\n",
            .{ name, increment, clear },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn clearStorageArrayFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        const array = switch (type_ref.payload) {
            .Array => |value| value,
            else => return error.InvalidType,
        };
        if (array.reference.location != .Storage) return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "clear_storage_array_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const generator = try self.function_collector.generator(self.evm_version);
        const body = if (array.isDynamicallySized()) blk: {
            const resize = try self.resizeArrayFunction(type_ref);
            defer self.allocator.free(resize);
            break :blk try generator.statements("@0(slot, 0)", .{resize});
        } else if (array.base_type.category() == .Mapping)
            Yul.Block{}
        else blk: {
            const base_bytes = try TypeBehavior.storageBytes(array.base_type);
            const clear_type = if (base_bytes < 32)
                self.type_provider.uint256()
            else
                array.base_type;
            const clear = try self.clearStorageRangeFunction(clear_type);
            defer self.allocator.free(clear);
            const to_size = try self.arrayConvertLengthToSize(type_ref);
            defer self.allocator.free(to_size);
            break :blk try generator.statements(
                "@0(slot, @1(@2))",
                .{ clear, to_size, array.length.? },
            );
        };

        const code = try generator.functionDefinition(
            "\nfunction @0(slot) {\n@1\n}\n",
            .{ name, body },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn clearStorageStructFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        const structure = switch (type_ref.payload) {
            .Struct => |value| value,
            else => return error.InvalidType,
        };
        if (structure.reference.location != .Storage) return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "clear_struct_storage_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        var members = try TypeBehavior.nativeMembersAlloc(
            self.type_provider,
            self.allocator,
            type_ref,
            null,
        );
        defer members.deinit();
        const offsets = try TypeBehavior.structStorageOffsetsAlloc(
            self.allocator,
            structure,
        );
        defer self.allocator.free(offsets.offsets);
        var cleared_slots = std.AutoHashMap(u256, void).init(self.allocator);
        defer cleared_slots.deinit();
        const generator = try self.function_collector.generator(self.evm_version);
        var body: Generated.Buffer = .{ .generator = generator };
        for (members.items, offsets.offsets) |member_entry, maybe_offset| {
            const member = member_entry.type_ref;
            if (member.category() == .Mapping) continue;
            const offset = maybe_offset orelse return error.InvalidType;
            const bytes = try TypeBehavior.storageBytes(member);
            if (bytes < 32) {
                if (cleared_slots.contains(offset.slot)) continue;
                try cleared_slots.put(offset.slot, {});
                try body.add(
                    "sstore(add(slot, @0), 0)\n",
                    .{offset.slot},
                );
            } else {
                if (offset.byte_offset != 0) return error.InvalidType;
                const clear = try self.storageSetToZeroFunction(member);
                defer self.allocator.free(clear);
                try body.add(
                    "@0(add(slot, @1), 0)\n",
                    .{ clear, offset.slot },
                );
            }
        }
        const code = try generator.functionDefinition(
            "\nfunction @0(slot) {\n@1}\n",
            .{ name, body.take() },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn resizeArrayFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        const array = switch (type_ref.payload) {
            .Array => |value| value,
            else => return error.InvalidType,
        };
        if (array.reference.location != .Storage or
            try TypeBehavior.storageBytes(array.base_type) > 32)
            return error.InvalidType;
        if (array.isByteArrayOrString())
            return self.resizeDynamicByteArrayFunction(type_ref);
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(self.allocator, "resize_array_{s}", .{identifier});
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const panic = try self.panicFunction(.resource_error);
        defer self.allocator.free(panic);
        const length = try self.arrayLengthFunction(type_ref);
        defer self.allocator.free(length);
        const clear = if (array.base_type.category() != .Mapping)
            try self.cleanUpStorageArrayEndFunction(type_ref)
        else
            try self.allocator.alloc(u8, 0);
        defer self.allocator.free(clear);
        const generator = try self.function_collector.generator(self.evm_version);
        const clear_statement = if (array.base_type.category() != .Mapping)
            try generator.statements(
                "@0(array, oldLen, newLen)",
                .{clear},
            )
        else
            Yul.Block{};

        const code = try generator.functionDefinition(
            "\nfunction @0(array, newLen) {\nif gt(newLen, 0x10000000000000000) { @1() }\nlet oldLen := @2(array)\n@3\n@4\n}\n",
            .{
                name,
                panic,
                length,
                if (array.isDynamicallySized()) try generator.statements("sstore(array, newLen)", .{}) else Yul.Block{},
                clear_statement,
            },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn cleanUpStorageArrayEndFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        const array = switch (type_ref.payload) {
            .Array => |value| value,
            else => return error.InvalidType,
        };
        const storage_bytes = try TypeBehavior.storageBytes(array.base_type);
        if (array.reference.location != .Storage or array.isByteArrayOrString() or
            array.base_type.category() == .Mapping or storage_bytes == 0 or
            storage_bytes > 32)
            return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "cleanup_storage_array_end_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const to_size = try self.arrayConvertLengthToSize(type_ref);
        defer self.allocator.free(to_size);
        const data_area = try self.arrayDataAreaFunction(type_ref);
        defer self.allocator.free(data_area);
        const clear_range = try self.clearStorageRangeFunction(array.base_type);
        defer self.allocator.free(clear_range);
        const uses_packing = storage_bytes <= 16;
        // Whiskers resolves every substitution in insertion order even when a
        // conditional section is not rendered. Keep the helper request here
        // for unpacked arrays as well so collector order matches upstream.
        const partial = try self.partialClearStorageSlotFunction();
        defer self.allocator.free(partial);
        const generator = try self.function_collector.generator(self.evm_version);
        const packed_body = if (uses_packing)
            try generator.statements(
                "let offset := mul(mod(startIndex, @0), @1)\nif gt(offset, 0) { @2(sub(deleteStart, 1), offset) }",
                .{ 32 / storage_bytes, storage_bytes, partial },
            )
        else
            Yul.Block{};

        const code = try generator.functionDefinition(
            "\nfunction @0(array, len, startIndex) {\nif lt(startIndex, len) {\nlet oldSlotCount := @1(len)\nlet newSlotCount := @2(startIndex)\nlet arrayDataStart := @3(array)\nlet deleteStart := add(arrayDataStart, newSlotCount)\n@4\n@5(deleteStart, sub(oldSlotCount, newSlotCount))\n}\n}\n",
            .{ name, to_size, to_size, data_area, packed_body, clear_range },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn resizeDynamicByteArrayFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        const array = switch (type_ref.payload) {
            .Array => |value| value,
            else => return error.InvalidType,
        };
        if (array.reference.location != .Storage or !array.isByteArrayOrString() or
            !array.isDynamicallySized())
            return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(self.allocator, "resize_array_{s}", .{identifier});
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const extract = try self.extractByteArrayLengthFunction();
        defer self.allocator.free(extract);
        const decrease = try self.decreaseByteArraySizeFunction(type_ref);
        defer self.allocator.free(decrease);
        const increase = try self.increaseByteArraySizeFunction(type_ref);
        defer self.allocator.free(increase);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0(array, newLen) {\nlet data := sload(array)\nlet oldLen := @1(data)\nif gt(newLen, oldLen) { @2(array, data, oldLen, newLen) }\nif lt(newLen, oldLen) { @3(array, data, oldLen, newLen) }\n}\n",
            .{ name, extract, increase, decrease },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn cleanUpDynamicByteArrayEndSlotsFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        const array = switch (type_ref.payload) {
            .Array => |value| value,
            else => return error.InvalidType,
        };
        if (array.reference.location != .Storage or !array.isByteArrayOrString() or
            !array.isDynamicallySized())
            return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "clean_up_bytearray_end_slots_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const data_area = try self.arrayDataAreaFunction(type_ref);
        defer self.allocator.free(data_area);
        const divide = try self.divide32CeilFunction();
        defer self.allocator.free(divide);
        const clear = try self.clearStorageRangeFunction(array.base_type);
        defer self.allocator.free(clear);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0(array, len, startIndex) {\nif gt(len, 31) {\nif gt(len, startIndex) {\nlet dataArea := @1(array)\nlet oldSlotCount := @2(len)\nlet newSlotCount := @3(startIndex)\nif lt(startIndex, 32) { newSlotCount := 0 }\nlet deleteStart := add(dataArea, newSlotCount)\n@4(deleteStart, sub(oldSlotCount, newSlotCount))\n}\n}\n}\n",
            .{ name, data_area, divide, divide, clear },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn shortByteArrayEncodeUsedAreaSetLengthFunction(
        self: *YulUtilFunctions,
    ) UtilError![]u8 {
        const name = "extract_used_part_and_set_length_of_short_byte_array";
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const mask = try self.maskBytesFunctionDynamic();
        defer self.allocator.free(mask);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0(data, len) -> used {\ndata := @1(data, len)\nused := or(data, mul(2, len))\n}\n",
            .{ name, mask },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn byteArrayTransitLongToShortFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        const array = switch (type_ref.payload) {
            .Array => |value| value,
            else => return error.InvalidType,
        };
        if (array.reference.location != .Storage or !array.isByteArrayOrString())
            return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "transit_byte_array_long_to_short_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const data_area = try self.arrayDataAreaFunction(type_ref);
        defer self.allocator.free(data_area);
        const encode = try self.shortByteArrayEncodeUsedAreaSetLengthFunction();
        defer self.allocator.free(encode);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0(array, len) {\nlet dataPos := @1(array)\nlet data := @2(sload(dataPos), len)\nsstore(array, data)\nsstore(dataPos, 0)\n}\n",
            .{ name, data_area, encode },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn increaseByteArraySizeFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        const identifier = try self.storageByteArrayIdentifierAlloc(type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "byte_array_increase_size_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const panic = try self.panicFunction(.resource_error);
        defer self.allocator.free(panic);
        const data_area = try self.arrayDataAreaFunction(type_ref);
        defer self.allocator.free(data_area);
        const encode = try self.shortByteArrayEncodeUsedAreaSetLengthFunction();
        defer self.allocator.free(encode);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            \\function @0(array, data, oldLen, newLen) {
            \\if gt(newLen, 0x10000000000000000) { @1() }
            \\switch lt(oldLen, 32)
            \\case 0 { sstore(array, add(mul(2, newLen), 1)) }
            \\default {
            \\    switch lt(newLen, 32)
            \\    case 0 {
            \\        data := and(not(0xff), data)
            \\        sstore(@2(array), data)
            \\        sstore(array, add(mul(2, newLen), 1))
            \\    }
            \\    default { sstore(array, @3(data, newLen)) }
            \\}
            \\}
        , .{ name, panic, data_area, encode });
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn decreaseByteArraySizeFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        const identifier = try self.storageByteArrayIdentifierAlloc(type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "byte_array_decrease_size_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const divide = try self.divide32CeilFunction();
        defer self.allocator.free(divide);
        const data_area = try self.arrayDataAreaFunction(type_ref);
        defer self.allocator.free(data_area);
        const partial = try self.partialClearStorageSlotFunction();
        defer self.allocator.free(partial);
        const clear = try self.clearStorageRangeFunction(
            type_ref.payload.Array.base_type,
        );
        defer self.allocator.free(clear);
        const transit = try self.byteArrayTransitLongToShortFunction(type_ref);
        defer self.allocator.free(transit);
        const encode = try self.shortByteArrayEncodeUsedAreaSetLengthFunction();
        defer self.allocator.free(encode);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            \\function @0(array, data, oldLen, newLen) {
            \\switch lt(newLen, 32)
            \\case 0 {
            \\    let newSlots := @1(newLen)
            \\    let oldSlots := @2(oldLen)
            \\    let arrayDataStart := @3(array)
            \\    let deleteStart := add(arrayDataStart, newSlots)
            \\    let offset := and(newLen, 0x1f)
            \\    if offset { @4(sub(deleteStart, 1), offset) }
            \\    if gt(oldSlots, newSlots) { @5(deleteStart, sub(oldSlots, newSlots)) }
            \\    sstore(array, or(mul(2, newLen), 1))
            \\}
            \\default {
            \\    switch gt(oldLen, 31)
            \\    case 1 {
            \\        let arrayDataStart := @6(array)
            \\        @7(add(arrayDataStart, 1), sub(@8(oldLen), 1))
            \\        @9(array, newLen)
            \\    }
            \\    default { sstore(array, @10(data, newLen)) }
            \\}
            \\}
        , .{
            name,
            divide,
            divide,
            data_area,
            partial,
            clear,
            data_area,
            clear,
            divide,
            transit,
            encode,
        });
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    fn storageByteArrayIdentifierAlloc(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
    ) UtilError![]u8 {
        const array = switch (type_ref.payload) {
            .Array => |value| value,
            else => return error.InvalidType,
        };
        if (array.reference.location != .Storage or !array.isByteArrayOrString() or
            !array.isDynamicallySized())
            return error.InvalidType;
        return TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
    }

    fn storageCleanupExpression(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
        storage_bytes: u8,
    ) UtilError!Yul.Expression {
        const generator = try self.function_collector.generator(self.evm_version);
        if (storage_bytes == 32) return generator.identifier("value");
        if (try TypeBehavior.leftAligned(type_ref)) {
            const shift = try self.shiftLeftFunction(256 - 8 * @as(usize, storage_bytes));
            defer self.allocator.free(shift);
            return generator.expression("@0(value)", .{shift});
        }
        const bits: std.math.Log2Int(u256) = @intCast(8 * @as(usize, storage_bytes));
        const mask = (@as(u256, 1) << bits) - 1;
        const rendered = try compactHex(self.allocator, mask);
        defer self.allocator.free(rendered);
        return generator.expression("and(value, @0)", .{try generator.numberToken(rendered)});
    }

    pub fn validatorFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
        revert_on_failure: bool,
    ) UtilError![]u8 {
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "validator_{s}_{s}",
            .{ if (revert_on_failure) "revert" else "assert", identifier },
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);

        const generator = try self.function_collector.generator(self.evm_version);
        var panic_code: PanicCode = .generic;
        const condition = switch (type_ref.payload) {
            .Enum => |enum_type| blk: {
                if (enum_type.declaration.nodeKind() != .enum_definition or
                    enum_type.declaration.payload.enum_definition.members.len == 0)
                    return error.InvalidType;
                panic_code = .enum_conversion_error;
                break :blk try generator.expression(
                    "lt(value, @0)",
                    .{enum_type.declaration.payload.enum_definition.members.len},
                );
            },
            .InaccessibleDynamic => try generator.expression("1", .{}),
            .Address,
            .Integer,
            .RationalNumber,
            .Bool,
            .FixedPoint,
            .Function,
            .Array,
            .Struct,
            .Mapping,
            .FixedBytes,
            .Contract,
            .UserDefinedValueType,
            => blk: {
                const cleanup = try self.cleanupFunction(type_ref);
                defer self.allocator.free(cleanup);
                break :blk try generator.expression(
                    "eq(value, @0(value))",
                    .{cleanup},
                );
            },
            else => return error.UnsupportedType,
        };

        const failure = if (revert_on_failure)
            try generator.statements("revert(0, 0)", .{})
        else blk: {
            const panic = try self.panicFunction(panic_code);
            defer self.allocator.free(panic);
            break :blk try generator.statements("@0()", .{panic});
        };

        const code = try generator.functionDefinition(
            "\nfunction @0(value) {\nif iszero(@1) { @2 }\n}\n",
            .{ name, condition, failure },
        );

        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn zeroValueFunction(
        self: *YulUtilFunctions,
        type_ref: *const Types.Type,
        split_function_types: bool,
    ) UtilError![]u8 {
        if (type_ref.category() == .Mapping) return error.UnsupportedType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "zero_value_for_{s}{s}",
            .{ if (split_function_types) "split_" else "", identifier },
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);

        const generator = try self.function_collector.generator(self.evm_version);
        const code = switch (type_ref.payload) {
            .Function => |function| if (function.kind == .External and split_function_types)
                try generator.functionDefinition(
                    "function @0() -> retAddress, retFunction { retAddress := 0 retFunction := 0 }\n",
                    .{name},
                )
            else
                try generator.functionDefinition(
                    "function @0() -> ret { ret := 0 }\n",
                    .{name},
                ),
            .Array => |array| if (array.reference.location == .CallData)
                if (array.isDynamicallySized())
                    try generator.functionDefinition(
                        "function @0() -> offset, length { offset := calldatasize() length := 0 }\n",
                        .{name},
                    )
                else
                    try generator.functionDefinition(
                        "function @0() -> offset { offset := calldatasize() }\n",
                        .{name},
                    )
            else if (array.reference.location == .Memory)
                if (array.isDynamicallySized())
                    try generator.functionDefinition(
                        "function @0() -> ret { ret := 96 }\n",
                        .{name},
                    )
                else blk: {
                    const allocate = try self.allocateAndInitializeMemoryArrayFunction(type_ref);
                    defer self.allocator.free(allocate);
                    break :blk try generator.functionDefinition(
                        "function @0() -> ret { ret := @1(@2) }\n",
                        .{ name, allocate, array.length.? },
                    );
                }
            else
                return error.UnsupportedType,
            .Struct => |structure| if (structure.reference.location == .CallData)
                try generator.functionDefinition(
                    "function @0() -> offset { offset := calldatasize() }\n",
                    .{name},
                )
            else if (structure.reference.location == .Memory) blk: {
                const allocate = try self.allocateAndInitializeMemoryStructFunction(type_ref);
                defer self.allocator.free(allocate);
                break :blk try generator.functionDefinition(
                    "function @0() -> ret { ret := @1() }\n",
                    .{ name, allocate },
                );
            } else return error.UnsupportedType,
            else => if (TypeBehavior.isValueType(type_ref))
                try generator.functionDefinition(
                    "\nfunction @0() -> ret {\nret := 0\n}\n",
                    .{name},
                )
            else
                return error.UnsupportedType,
        };

        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn panicFunction(
        self: *YulUtilFunctions,
        panic_code: PanicCode,
    ) UtilError![]u8 {
        const code_value: u32 = @intCast(@intFromEnum(panic_code));
        const rendered_code = try compactHex(self.allocator, code_value);
        defer self.allocator.free(rendered_code);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "panic_error_{s}",
            .{rendered_code},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const selector = FunctionSelector.selectorFromSignatureU256("Panic(uint256)");
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0() {\nmstore(0, @1)\nmstore(4, @2)\nrevert(0, 0x24)\n}\n",
            .{ name, selector, try generator.numberToken(rendered_code) },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn returnDataSelectorFunction(
        self: *YulUtilFunctions,
    ) UtilError![]u8 {
        if (!self.evm_version.supportsReturndata()) return error.InvalidType;
        const name = "return_data_selector";
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const shift = try self.shiftRightFunction(224);
        defer self.allocator.free(shift);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            \\function @0() -> sig {
            \\    if gt(returndatasize(), 3) {
            \\        returndatacopy(0, 0, 4)
            \\        sig := @1(mload(0))
            \\    }
            \\}
        , .{ name, shift });

        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn tryDecodeErrorMessageFunction(
        self: *YulUtilFunctions,
    ) UtilError![]u8 {
        if (!self.evm_version.supportsReturndata()) return error.InvalidType;
        const name = "try_decode_error_message";
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const allocate = try self.allocateUnboundedFunction();
        defer self.allocator.free(allocate);
        const finalize = try self.finalizeAllocationFunction();
        defer self.allocator.free(finalize);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            \\function @0() -> ret {
            \\    if lt(returndatasize(), 0x44) { leave }
            \\    let data := @1()
            \\    returndatacopy(data, 4, sub(returndatasize(), 4))
            \\    let offset := mload(data)
            \\    if or(gt(offset, 0xffffffffffffffff), gt(add(offset, 0x24), returndatasize())) { leave }
            \\    let msg := add(data, offset)
            \\    let length := mload(msg)
            \\    if gt(length, 0xffffffffffffffff) { leave }
            \\    let end := add(add(msg, 0x20), length)
            \\    if gt(end, add(data, sub(returndatasize(), 4))) { leave }
            \\    @2(data, add(offset, add(0x20, length)))
            \\    ret := msg
            \\}
        , .{ name, allocate, finalize });

        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn tryDecodePanicDataFunction(
        self: *YulUtilFunctions,
    ) UtilError![]u8 {
        if (!self.evm_version.supportsReturndata()) return error.InvalidType;
        return self.collectTemplate("try_decode_panic_data",
            \\function try_decode_panic_data() -> success, data {
            \\    if gt(returndatasize(), 0x23) {
            \\        returndatacopy(0, 4, 0x20)
            \\        success := 1
            \\        data := mload(0)
            \\    }
            \\}
            \\
        );
    }

    pub fn extractReturndataFunction(
        self: *YulUtilFunctions,
    ) UtilError![]u8 {
        const name = "extract_returndata";
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const bytes_memory = self.type_provider.bytesMemory();
        // Preserve upstream Whiskers substitution order: allocateArray is
        // requested before emptyArray even though the zero case renders first.
        const allocate = try self.allocateMemoryArrayFunction(bytes_memory);
        defer self.allocator.free(allocate);
        const empty = try self.zeroValueFunction(bytes_memory, true);
        defer self.allocator.free(empty);
        const generator = try self.function_collector.generator(self.evm_version);
        const body = if (self.evm_version.supportsReturndata())
            try generator.statements(
                \\switch returndatasize()
                \\case 0 { data := @0() }
                \\default {
                \\    data := @1(returndatasize())
                \\    returndatacopy(add(data, 0x20), 0, returndatasize())
                \\}
            , .{ empty, allocate })
        else
            try generator.statements("data := @0()", .{empty});

        const code = try generator.functionDefinition(
            "function @0() -> data {\n@1\n}\n",
            .{ name, body },
        );

        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    /// Constructor-argument copying is kept ABI-agnostic by accepting the
    /// tuple decoder generated by `ABIFunctions` from the orchestration layer.
    pub fn copyConstructorArgumentsToMemoryFunction(
        self: *YulUtilFunctions,
        constructor_id: i64,
        contract_name: []const u8,
        contract_id: i64,
        creation_object_name: []const u8,
        return_parameters: []const []const u8,
        decoder_name: []const u8,
    ) UtilError![]u8 {
        const name = try std.fmt.allocPrint(
            self.allocator,
            "copy_arguments_for_constructor_{d}_object_{s}_{d}",
            .{ constructor_id, contract_name, contract_id },
        );
        defer self.allocator.free(name);
        if (try self.function_collector.beginFunction(name)) {
            errdefer self.function_collector.abortFunction(name);
            const allocate = try self.allocationFunction();
            defer self.allocator.free(allocate);
            const generator = try self.function_collector.generator(self.evm_version);
            const decode_statement = if (return_parameters.len == 0)
                try generator.statements(
                    "@0(memoryDataOffset, add(memoryDataOffset, argSize))",
                    .{decoder_name},
                )
            else
                try generator.statements(
                    "@0 := @1(memoryDataOffset, add(memoryDataOffset, argSize))",
                    .{ return_parameters, decoder_name },
                );

            const code = try generator.functionDefinition(
                \\function @0() -> @1 {
                \\    let programSize := datasize(@2)
                \\    let argSize := sub(codesize(), programSize)
                \\    let memoryDataOffset := @3(argSize)
                \\    codecopy(memoryDataOffset, programSize, argSize)
                \\    @4
                \\}
            , .{
                name,
                return_parameters,
                try generator.string(creation_object_name, .builtin),
                allocate,
                decode_statement,
            });

            try self.function_collector.finishGeneratedFunction(name, code);
        }
        return self.function_collector.copyFunctionName(name);
    }

    pub fn externalCodeFunction(self: *YulUtilFunctions) UtilError![]u8 {
        const name = "external_code_at";
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const allocate = try self.allocateMemoryArrayFunction(
            self.type_provider.bytesMemory(),
        );
        defer self.allocator.free(allocate);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            \\function @0(addr) -> mpos {
            \\    let length := extcodesize(addr)
            \\    mpos := @1(length)
            \\    extcodecopy(addr, add(mpos, 0x20), 0, length)
            \\}
        , .{ name, allocate });

        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn externalFunctionPointersEqualFunction(
        self: *YulUtilFunctions,
    ) UtilError![]u8 {
        const name = "externalFunctionPointersEqualFunction";
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const address_cleanup = try self.cleanupFunction(self.type_provider.address());
        defer self.allocator.free(address_cleanup);
        const uint32_type = try self.type_provider.integer(32, .Unsigned);
        const selector_cleanup = try self.cleanupFunction(uint32_type);
        defer self.allocator.free(selector_cleanup);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            \\function @0(leftAddress, leftSelector, rightAddress, rightSelector) -> result {
            \\    result := and(
            \\        eq(@1(leftAddress), @2(rightAddress)),
            \\        eq(@3(leftSelector), @4(rightSelector))
            \\    )
            \\}
        , .{
            name,
            address_cleanup,
            address_cleanup,
            selector_cleanup,
            selector_cleanup,
        });

        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn requireOrAssertFunction(
        self: *YulUtilFunctions,
        is_assert: bool,
    ) UtilError![]u8 {
        const name = if (is_assert) "assert_helper" else "require_helper";
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const generator = try self.function_collector.generator(self.evm_version);
        const failure = if (is_assert) blk: {
            const panic = try self.panicFunction(.assert);
            defer self.allocator.free(panic);
            break :blk try generator.statements("@0()", .{panic});
        } else try generator.statements("revert(0, 0)", .{});

        const code = try generator.functionDefinition(
            "\nfunction @0(condition) {\nif iszero(condition) { @1 }\n}\n",
            .{ name, failure },
        );

        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    /// Emits the custom-error revert block. The ABI tuple encoder is supplied
    /// explicitly by the caller to keep `YulUtilFunctions` independent from
    /// `ABIFunctions` and avoid a Zig import cycle.
    pub fn revertWithError(
        self: *YulUtilFunctions,
        signature: []const u8,
        parameter_types: []const *const Types.Type,
        argument_names: []const []const u8,
        encoder_name: []const u8,
        pos_variable: ?[]const u8,
        end_variable: ?[]const u8,
    ) UtilError!Yul.Block {
        if ((pos_variable == null) != (end_variable == null))
            return error.InvalidType;
        var static_size: usize = 0;
        var static_value_parameters = true;
        for (parameter_types) |type_ref| {
            if (!TypeBehavior.isValueType(type_ref) or
                TypeBehavior.isDynamicallyEncoded(type_ref))
            {
                static_value_parameters = false;
                break;
            }
            static_size = std.math.add(
                usize,
                static_size,
                try TypeBehavior.calldataEncodedSize(type_ref, true),
            ) catch return error.Overflow;
        }
        const encoded_error_size = std.math.add(usize, static_size, 4) catch
            return error.Overflow;
        const needs_allocation = !static_value_parameters or
            encoded_error_size > 0x80;
        const position = pos_variable orelse "memPtr";
        const end = end_variable orelse "end";
        const allocate = if (needs_allocation)
            try self.allocateUnboundedFunction()
        else
            try self.allocator.alloc(u8, 0);
        defer self.allocator.free(allocate);
        const generator = try self.function_collector.generator(self.evm_version);
        const allocation_expression = if (needs_allocation)
            try generator.expression("@0()", .{allocate})
        else
            try generator.expression("0", .{});
        const selector = FunctionSelector.selectorFromSignatureU256(signature);
        return generator.statements(
            "let @0 := @1 mstore(@0, @2) let @3 := @4(add(@0, 4), @5) revert(@0, sub(@3, @0))",
            .{ position, allocation_expression, selector, end, encoder_name, argument_names },
        );
    }

    pub fn requireOrAssertWithMessageFunction(
        self: *YulUtilFunctions,
        message_type: *const Types.Type,
        argument_names: []const []const u8,
        encoder_name: []const u8,
    ) UtilError![]u8 {
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, message_type);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "require_helper_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (try self.function_collector.beginFunction(name)) {
            errdefer self.function_collector.abortFunction(name);
            const revert = try self.revertWithError(
                "Error(string)",
                &.{self.type_provider.stringMemory()},
                argument_names,
                encoder_name,
                null,
                null,
            );

            const generator = try self.function_collector.generator(self.evm_version);
            const code = try generator.functionDefinition(
                "function @0(condition, @1) { if iszero(condition) { @2 } }",
                .{ name, argument_names, revert },
            );
            try self.function_collector.finishGeneratedFunction(name, code);
        }
        return self.function_collector.copyFunctionName(name);
    }

    pub fn requireWithErrorFunction(
        self: *YulUtilFunctions,
        error_id: i64,
        error_name: []const u8,
        error_signature: []const u8,
        argument_types: []const *const Types.Type,
        parameter_types: []const *const Types.Type,
        argument_names: []const []const u8,
        encoder_name: []const u8,
    ) UtilError![]u8 {
        var name: std.ArrayList(u8) = .empty;
        defer name.deinit(self.allocator);
        try name.print(
            self.allocator,
            "require_helper_t_error_{d}_{s}",
            .{ error_id, error_name },
        );
        for (argument_types) |type_ref| {
            const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
            defer self.allocator.free(identifier);
            try name.print(self.allocator, "_{s}", .{identifier});
        }
        if (try self.function_collector.beginFunction(name.items)) {
            errdefer self.function_collector.abortFunction(name.items);
            const revert = try self.revertWithError(
                error_signature,
                parameter_types,
                argument_names,
                encoder_name,
                null,
                null,
            );

            const generator = try self.function_collector.generator(self.evm_version);
            const code = try generator.functionDefinition(
                "function @0(condition, @1) { if iszero(condition) { @2 } }",
                .{ name.items, argument_names, revert },
            );
            try self.function_collector.finishGeneratedFunction(name.items, code);
        }
        return self.function_collector.copyFunctionName(name.items);
    }

    pub fn revertReasonIfDebugFunction(
        self: *YulUtilFunctions,
        message: []const u8,
    ) UtilError![]u8 {
        const digest = Keccak256.keccak256(message);
        const hex = digest.hex();
        const name = try std.fmt.allocPrint(
            self.allocator,
            "revert_error_{s}",
            .{&hex},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const body = try self.revertReasonIfDebugBody(message);

        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0() {\n@1\n}\n",
            .{ name, body },
        );

        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn revertReasonIfDebugBody(
        self: *YulUtilFunctions,
        message: []const u8,
    ) UtilError!Yul.Block {
        const generator = try self.function_collector.generator(self.evm_version);

        if (@intFromEnum(self.revert_strings) < @intFromEnum(DebugSettings.RevertStrings.Debug) or
            message.len == 0)
            return generator.statements("revert(0, 0)", .{});
        const allocate = try self.allocateUnboundedFunction();
        defer self.allocator.free(allocate);
        var output: Generated.Buffer = .{ .generator = generator };
        try output.add(
            "let start := @0() let pos := start mstore(pos, @1) pos := add(pos, 4) mstore(pos, 0x20) pos := add(pos, 0x20) mstore(pos, @2) pos := add(pos, 0x20) ",
            .{
                allocate,
                FunctionSelector.selectorFromSignatureU256("Error(string)"),
                message.len,
            },
        );
        const words = (message.len + 31) / 32;
        for (0..words) |word_index| {
            var word: [32]u8 = [_]u8{0} ** 32;
            const start = word_index * 32;
            const count = @min(@as(usize, 32), message.len - start);
            @memcpy(word[0..count], message[start .. start + count]);
            const value = std.mem.readInt(u256, &word, .big);
            const rendered = try compactHex(self.allocator, value);
            defer self.allocator.free(rendered);
            try output.add(
                "mstore(add(pos, @0), @1) ",
                .{ word_index * 32, try generator.numberToken(rendered) },
            );
        }
        try output.add(
            "revert(start, @0)",
            .{4 + 32 + 32 + words * 32},
        );
        return output.take();
    }

    pub fn overflowCheckedIntAddFunction(
        self: *YulUtilFunctions,
        integer: Types.IntegerType,
    ) UtilError![]u8 {
        return self.integerBinaryFunction(.checked_add, integer);
    }

    pub fn wrappingIntAddFunction(
        self: *YulUtilFunctions,
        integer: Types.IntegerType,
    ) UtilError![]u8 {
        return self.integerBinaryFunction(.wrapping_add, integer);
    }

    pub fn overflowCheckedIntSubFunction(
        self: *YulUtilFunctions,
        integer: Types.IntegerType,
    ) UtilError![]u8 {
        return self.integerBinaryFunction(.checked_sub, integer);
    }

    pub fn wrappingIntSubFunction(
        self: *YulUtilFunctions,
        integer: Types.IntegerType,
    ) UtilError![]u8 {
        return self.integerBinaryFunction(.wrapping_sub, integer);
    }

    pub fn overflowCheckedIntMulFunction(
        self: *YulUtilFunctions,
        integer: Types.IntegerType,
    ) UtilError![]u8 {
        return self.integerBinaryFunction(.checked_mul, integer);
    }

    pub fn wrappingIntMulFunction(
        self: *YulUtilFunctions,
        integer: Types.IntegerType,
    ) UtilError![]u8 {
        return self.integerBinaryFunction(.wrapping_mul, integer);
    }

    pub fn overflowCheckedIntDivFunction(
        self: *YulUtilFunctions,
        integer: Types.IntegerType,
    ) UtilError![]u8 {
        return self.integerBinaryFunction(.checked_div, integer);
    }

    pub fn wrappingIntDivFunction(
        self: *YulUtilFunctions,
        integer: Types.IntegerType,
    ) UtilError![]u8 {
        return self.integerBinaryFunction(.wrapping_div, integer);
    }

    pub fn intModFunction(
        self: *YulUtilFunctions,
        integer: Types.IntegerType,
    ) UtilError![]u8 {
        return self.integerBinaryFunction(.modulo, integer);
    }

    pub fn overflowCheckedIntExpFunction(
        self: *YulUtilFunctions,
        integer: Types.IntegerType,
        exponent_integer: Types.IntegerType,
    ) UtilError![]u8 {
        if (exponent_integer.isSigned()) return error.InvalidType;
        const type_ref = Types.Type{ .payload = .{ .Integer = integer } };
        const exponent_type = Types.Type{ .payload = .{ .Integer = exponent_integer } };
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, &type_ref);
        defer self.allocator.free(identifier);
        const exponent_identifier = try TypeBehavior.compatibilityIdentifierAlloc(
            self.allocator,
            self.compatibility_ids,
            &exponent_type,
        );
        defer self.allocator.free(exponent_identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "checked_exp_{s}_{s}",
            .{ identifier, exponent_identifier },
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const base_cleanup = try self.cleanupFunction(&type_ref);
        defer self.allocator.free(base_cleanup);
        const exponent_cleanup = try self.cleanupFunction(&exponent_type);
        defer self.allocator.free(exponent_cleanup);
        const exponentiation = if (integer.isSigned())
            try self.overflowCheckedSignedExpFunction()
        else
            try self.overflowCheckedUnsignedExpFunction();
        defer self.allocator.free(exponentiation);
        const maximum = try compactHex(self.allocator, TypeBehavior.integerMax(integer));
        defer self.allocator.free(maximum);
        const minimum = try compactHex(self.allocator, TypeBehavior.integerMin(integer));
        defer self.allocator.free(minimum);
        const generator = try self.function_collector.generator(self.evm_version);
        const call = if (integer.isSigned())
            try generator.statements(
                "power := @0(base, exponent, @1, @2)",
                .{ exponentiation, try generator.numberToken(minimum), try generator.numberToken(maximum) },
            )
        else
            try generator.statements(
                "power := @0(base, exponent, @1)",
                .{ exponentiation, try generator.numberToken(maximum) },
            );
        const code = try generator.functionDefinition(
            "\nfunction @0(base, exponent) -> power {\nbase := @1(base)\nexponent := @2(exponent)\n@3\n}\n",
            .{ name, base_cleanup, exponent_cleanup, call },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn overflowCheckedIntLiteralExpFunction(
        self: *YulUtilFunctions,
        base_type: *const Types.Type,
        exponent_type: Types.IntegerType,
        common_type: Types.IntegerType,
    ) UtilError![]u8 {
        const rational = switch (base_type.payload) {
            .RationalNumber => |value| value,
            else => return error.InvalidType,
        };
        if (exponent_type.isSigned() or common_type.bits != 256)
            return error.InvalidType;
        var base_value = Numeric.BigInt.quotient(
            rational.numerator,
            rational.denominator,
        ) catch return error.InvalidType;
        defer base_value.deinit();
        var reconstructed = Numeric.BigInt.mul(&base_value, rational.denominator);
        defer reconstructed.deinit();
        if (reconstructed.compare(rational.numerator) != .eq or
            base_value.isNegative() != common_type.isSigned())
            return error.InvalidType;

        const exponent_type_ref = Types.Type{ .payload = .{ .Integer = exponent_type } };
        const base_identifier = try TypeBehavior.compatibilityIdentifierAlloc(
            self.allocator,
            self.compatibility_ids,
            base_type,
        );
        defer self.allocator.free(base_identifier);
        const exponent_identifier = try TypeBehavior.compatibilityIdentifierAlloc(
            self.allocator,
            self.compatibility_ids,
            &exponent_type_ref,
        );
        defer self.allocator.free(exponent_identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "checked_exp_{s}_{s}",
            .{ base_identifier, exponent_identifier },
        );
        defer self.allocator.free(name);
        if (try self.function_collector.beginFunction(name)) {
            errdefer self.function_collector.abortFunction(name);
            const needs_check = base_value.compareSigned(0) != .eq and
                base_value.compareSigned(-1) != .eq and
                base_value.compareSigned(1) != .eq;
            var exponent_upper_bound: u16 = 0;
            if (needs_check) {
                var absolute_base = base_value.absolute();
                defer absolute_base.deinit();
                var maximum = if (common_type.isSigned())
                    Numeric.BigInt.fromU256(@as(u256, 1) << 255)
                else
                    Numeric.BigInt.fromU256(std.math.maxInt(u256));
                defer maximum.deinit();
                var power = Numeric.BigInt.initUnsigned(1);
                defer power.deinit();
                while (exponent_upper_bound < 255) {
                    var next = Numeric.BigInt.mul(&power, &absolute_base);
                    if (next.compare(&maximum) == .gt) {
                        next.deinit();
                        break;
                    }
                    power.deinit();
                    power = next;
                    exponent_upper_bound += 1;
                }
            }
            const cleanup = try self.cleanupFunction(&exponent_type_ref);
            defer self.allocator.free(cleanup);
            const panic = if (needs_check)
                try self.panicFunction(.under_overflow)
            else
                try self.allocator.alloc(u8, 0);
            defer self.allocator.free(panic);
            const generator = try self.function_collector.generator(self.evm_version);
            const check = if (needs_check)
                try generator.statements(
                    "if gt(exponent, @0) { @1() }",
                    .{ exponent_upper_bound, panic },
                )
            else
                Yul.Block{};
            const code = try generator.functionDefinition(
                \\function @0(exponent) -> power {
                \\    exponent := @1(exponent)
                \\    @2
                \\    power := exp(@3, exponent)
                \\}
            , .{ name, cleanup, check, base_value.toU256Wrapping() });
            try self.function_collector.finishGeneratedFunction(name, code);
        }
        return self.function_collector.copyFunctionName(name);
    }

    pub fn overflowCheckedUnsignedExpFunction(self: *YulUtilFunctions) UtilError![]u8 {
        const name = "checked_exp_unsigned";
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const panic = try self.panicFunction(.under_overflow);
        defer self.allocator.free(panic);
        const loop = try self.overflowCheckedExpLoopFunction();
        defer self.allocator.free(loop);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            \\function @0(base, exponent, max) -> power {
            \\if iszero(exponent) { power := 1 leave }
            \\if iszero(base) { power := 0 leave }
            \\switch base
            \\case 1 { power := 1 leave }
            \\case 2 {
            \\    if gt(exponent, 255) { @1() }
            \\    power := exp(2, exponent)
            \\    if gt(power, max) { @2() }
            \\    leave
            \\}
            \\if or(and(lt(base, 11), lt(exponent, 78)), and(lt(base, 307), lt(exponent, 32))) {
            \\    power := exp(base, exponent)
            \\    if gt(power, max) { @3() }
            \\    leave
            \\}
            \\power, base := @4(1, base, exponent, max)
            \\if gt(power, div(max, base)) { @5() }
            \\power := mul(power, base)
            \\}
        , .{ name, panic, panic, panic, loop, panic });
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn overflowCheckedSignedExpFunction(self: *YulUtilFunctions) UtilError![]u8 {
        const name = "checked_exp_signed";
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const panic = try self.panicFunction(.under_overflow);
        defer self.allocator.free(panic);
        const loop = try self.overflowCheckedExpLoopFunction();
        defer self.allocator.free(loop);
        const shift = try self.shiftRightFunction(1);
        defer self.allocator.free(shift);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            \\function @0(base, exponent, min, max) -> power {
            \\switch exponent
            \\case 0 { power := 1 leave }
            \\case 1 { power := base leave }
            \\if iszero(base) { power := 0 leave }
            \\power := 1
            \\switch sgt(base, 0)
            \\case 1 { if gt(base, div(max, base)) { @1() } }
            \\case 0 { if slt(base, sdiv(max, base)) { @2() } }
            \\if and(exponent, 1) { power := base }
            \\base := mul(base, base)
            \\exponent := @3(exponent)
            \\power, base := @4(power, base, exponent, max)
            \\if and(sgt(power, 0), gt(power, div(max, base))) { @5() }
            \\if and(slt(power, 0), slt(power, sdiv(min, base))) { @6() }
            \\power := mul(power, base)
            \\}
        , .{ name, panic, panic, shift, loop, panic, panic });
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn overflowCheckedExpLoopFunction(self: *YulUtilFunctions) UtilError![]u8 {
        const name = "checked_exp_helper";
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const panic = try self.panicFunction(.under_overflow);
        defer self.allocator.free(panic);
        const shift = try self.shiftRightFunction(1);
        defer self.allocator.free(shift);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            \\function @0(_power, _base, exponent, max) -> power, base {
            \\power := _power
            \\base := _base
            \\for { } gt(exponent, 1) { } {
            \\    if gt(base, div(max, base)) { @1() }
            \\    if and(exponent, 1) { power := mul(power, base) }
            \\    base := mul(base, base)
            \\    exponent := @2(exponent)
            \\}
            \\}
        , .{ name, panic, shift });
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn wrappingIntExpFunction(
        self: *YulUtilFunctions,
        integer: Types.IntegerType,
        exponent_integer: Types.IntegerType,
    ) UtilError![]u8 {
        if (exponent_integer.isSigned()) return error.InvalidType;
        const type_ref = Types.Type{ .payload = .{ .Integer = integer } };
        const exponent_type = Types.Type{ .payload = .{ .Integer = exponent_integer } };
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, &type_ref);
        defer self.allocator.free(identifier);
        const exponent_identifier = try TypeBehavior.compatibilityIdentifierAlloc(
            self.allocator,
            self.compatibility_ids,
            &exponent_type,
        );
        defer self.allocator.free(exponent_identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "wrapping_exp_{s}_{s}",
            .{ identifier, exponent_identifier },
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const base_cleanup = try self.cleanupFunction(&type_ref);
        defer self.allocator.free(base_cleanup);
        const exponent_cleanup = try self.cleanupFunction(&exponent_type);
        defer self.allocator.free(exponent_cleanup);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0(base, exponent) -> power {\nbase := @1(base)\nexponent := @2(exponent)\npower := @3(exp(base, exponent))\n}\n",
            .{ name, base_cleanup, exponent_cleanup, base_cleanup },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn erc7201(self: *YulUtilFunctions) UtilError![]u8 {
        return self.collectTemplate(
            "erc7201",
            "function erc7201(namespaceIDDataPtr, namespaceIDLength) -> slot { let innerKeccak := keccak256(namespaceIDDataPtr, namespaceIDLength) mstore(0, sub(innerKeccak, 1)) slot := and(keccak256(0, 32), not(0xff)) }\n",
        );
    }

    pub fn decrementCheckedFunction(
        self: *YulUtilFunctions,
        integer: Types.IntegerType,
    ) UtilError![]u8 {
        const type_ref = Types.Type{ .payload = .{ .Integer = integer } };
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, &type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(self.allocator, "decrement_{s}", .{identifier});
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);

        const panic = try self.panicFunction(.under_overflow);
        defer self.allocator.free(panic);
        const cleanup = try self.cleanupFunction(&type_ref);
        defer self.allocator.free(cleanup);
        const minimum = try compactHex(self.allocator, TypeBehavior.integerMin(integer));
        defer self.allocator.free(minimum);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0(value) -> ret {\nvalue := @1(value)\nif eq(value, @2) { @3() }\nret := sub(value, 1)\n}\n",
            .{ name, cleanup, try generator.numberToken(minimum), panic },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn decrementWrappingFunction(
        self: *YulUtilFunctions,
        integer: Types.IntegerType,
    ) UtilError![]u8 {
        return self.integerUnaryWrappingFunction(.decrement, integer);
    }

    pub fn incrementCheckedFunction(
        self: *YulUtilFunctions,
        integer: Types.IntegerType,
    ) UtilError![]u8 {
        const type_ref = Types.Type{ .payload = .{ .Integer = integer } };
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, &type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(self.allocator, "increment_{s}", .{identifier});
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);

        const panic = try self.panicFunction(.under_overflow);
        defer self.allocator.free(panic);
        const cleanup = try self.cleanupFunction(&type_ref);
        defer self.allocator.free(cleanup);
        const maximum = try compactHex(self.allocator, TypeBehavior.integerMax(integer));
        defer self.allocator.free(maximum);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0(value) -> ret {\nvalue := @1(value)\nif eq(value, @2) { @3() }\nret := add(value, 1)\n}\n",
            .{ name, cleanup, try generator.numberToken(maximum), panic },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn incrementWrappingFunction(
        self: *YulUtilFunctions,
        integer: Types.IntegerType,
    ) UtilError![]u8 {
        return self.integerUnaryWrappingFunction(.increment, integer);
    }

    pub fn negateNumberCheckedFunction(
        self: *YulUtilFunctions,
        integer: Types.IntegerType,
    ) UtilError![]u8 {
        if (!integer.isSigned()) return error.InvalidType;
        const type_ref = Types.Type{ .payload = .{ .Integer = integer } };
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, &type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(self.allocator, "negate_{s}", .{identifier});
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);

        const cleanup = try self.cleanupFunction(&type_ref);
        defer self.allocator.free(cleanup);
        const panic = try self.panicFunction(.under_overflow);
        defer self.allocator.free(panic);
        const minimum = try compactHex(self.allocator, TypeBehavior.integerMin(integer));
        defer self.allocator.free(minimum);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0(value) -> ret {\nvalue := @1(value)\nif eq(value, @2) { @3() }\nret := sub(0, value)\n}\n",
            .{ name, cleanup, try generator.numberToken(minimum), panic },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn negateNumberWrappingFunction(
        self: *YulUtilFunctions,
        integer: Types.IntegerType,
    ) UtilError![]u8 {
        if (!integer.isSigned()) return error.InvalidType;
        return self.integerUnaryWrappingFunction(.negate, integer);
    }

    const IntegerUnaryWrappingOperation = enum {
        decrement,
        increment,
        negate,
    };

    fn integerUnaryWrappingFunction(
        self: *YulUtilFunctions,
        operation: IntegerUnaryWrappingOperation,
        integer: Types.IntegerType,
    ) UtilError![]u8 {
        if (operation == .negate and !integer.isSigned()) return error.InvalidType;
        const type_ref = Types.Type{ .payload = .{ .Integer = integer } };
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, &type_ref);
        defer self.allocator.free(identifier);
        const prefix = switch (operation) {
            .decrement => "decrement_wrapping_",
            .increment => "increment_wrapping_",
            .negate => "negate_wrapping_",
        };
        const name = try std.fmt.allocPrint(self.allocator, "{s}{s}", .{ prefix, identifier });
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);

        const cleanup = try self.cleanupFunction(&type_ref);
        defer self.allocator.free(cleanup);
        const generator = try self.function_collector.generator(self.evm_version);
        const expression = switch (operation) {
            .decrement => try generator.expression("sub(value, 1)", .{}),
            .increment => try generator.expression("add(value, 1)", .{}),
            .negate => try generator.expression("sub(0, value)", .{}),
        };
        const code = try generator.functionDefinition(
            "\nfunction @0(value) -> ret {\nret := @1(@2)\n}\n",
            .{ name, cleanup, expression },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    const IntegerBinaryOperation = enum {
        checked_add,
        wrapping_add,
        checked_sub,
        wrapping_sub,
        checked_mul,
        wrapping_mul,
        checked_div,
        wrapping_div,
        modulo,
    };

    fn integerBinaryFunction(
        self: *YulUtilFunctions,
        operation: IntegerBinaryOperation,
        integer: Types.IntegerType,
    ) UtilError![]u8 {
        const type_ref = Types.Type{ .payload = .{ .Integer = integer } };
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, &type_ref);
        defer self.allocator.free(identifier);
        const prefix = switch (operation) {
            .checked_add => "checked_add_",
            .wrapping_add => "wrapping_add_",
            .checked_sub => "checked_sub_",
            .wrapping_sub => "wrapping_sub_",
            .checked_mul => "checked_mul_",
            .wrapping_mul => "wrapping_mul_",
            .checked_div => "checked_div_",
            .wrapping_div => "wrapping_div_",
            .modulo => "mod_",
        };
        const name = try std.fmt.allocPrint(self.allocator, "{s}{s}", .{ prefix, identifier });
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const cleanup = try self.cleanupFunction(&type_ref);
        defer self.allocator.free(cleanup);
        const body = try self.integerBinaryBody(operation, integer, cleanup);
        const result_name = switch (operation) {
            .checked_add, .wrapping_add => "sum",
            .checked_sub, .wrapping_sub => "diff",
            .checked_mul, .wrapping_mul => "product",
            .checked_div, .wrapping_div, .modulo => "r",
        };
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0(x, y) -> @1 {\n@2\n}\n",
            .{ name, result_name, body },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    fn integerBinaryBody(
        self: *YulUtilFunctions,
        operation: IntegerBinaryOperation,
        integer: Types.IntegerType,
        cleanup: []const u8,
    ) UtilError!Yul.Block {
        const generator = try self.function_collector.generator(self.evm_version);
        switch (operation) {
            .wrapping_add => return generator.statements(
                "sum := @0(add(x, y))",
                .{cleanup},
            ),
            .wrapping_sub => return generator.statements(
                "diff := @0(sub(x, y))",
                .{cleanup},
            ),
            .wrapping_mul => return generator.statements(
                "product := @0(mul(x, y))",
                .{cleanup},
            ),
            else => {},
        }

        const panic_overflow = if (operation == .checked_add or
            operation == .checked_sub or operation == .checked_mul)
            try self.panicFunction(.under_overflow)
        else
            try self.panicFunction(.division_by_zero);
        defer self.allocator.free(panic_overflow);
        const maximum = TypeBehavior.integerMax(integer);
        const minimum = TypeBehavior.integerMin(integer);
        const max_text = try compactHex(self.allocator, maximum);
        defer self.allocator.free(max_text);
        const min_text = try compactHex(self.allocator, minimum);
        defer self.allocator.free(min_text);

        return switch (operation) {
            .checked_add => if (integer.isSigned())
                if (integer.bits == 256)
                    generator.statements(
                        "x := @0(x) y := @0(y) sum := add(x, y) if or(and(iszero(slt(x, 0)), slt(sum, y)), and(slt(x, 0), iszero(slt(sum, y)))) { @1() }",
                        .{ cleanup, panic_overflow },
                    )
                else
                    generator.statements(
                        "x := @0(x) y := @0(y) sum := add(x, y) if or(sgt(sum, @1), slt(sum, @2)) { @3() }",
                        .{ cleanup, try generator.numberToken(max_text), try generator.numberToken(min_text), panic_overflow },
                    )
            else if (integer.bits == 256)
                generator.statements(
                    "x := @0(x)\ny := @0(y)\nsum := add(x, y)\n\nif gt(x, sum) { @1() }\n",
                    .{ cleanup, panic_overflow },
                )
            else
                generator.statements(
                    "x := @0(x) y := @0(y) sum := add(x, y) if gt(sum, @1) { @2() }",
                    .{ cleanup, try generator.numberToken(max_text), panic_overflow },
                ),
            .checked_sub => if (integer.isSigned())
                if (integer.bits == 256)
                    generator.statements(
                        "x := @0(x) y := @0(y) diff := sub(x, y) if or(and(iszero(slt(y, 0)), sgt(diff, x)), and(slt(y, 0), slt(diff, x))) { @1() }",
                        .{ cleanup, panic_overflow },
                    )
                else
                    generator.statements(
                        "x := @0(x) y := @0(y) diff := sub(x, y) if or(slt(diff, @1), sgt(diff, @2)) { @3() }",
                        .{ cleanup, try generator.numberToken(min_text), try generator.numberToken(max_text), panic_overflow },
                    )
            else if (integer.bits == 256)
                generator.statements(
                    "x := @0(x) y := @0(y) diff := sub(x, y) if gt(diff, x) { @1() }",
                    .{ cleanup, panic_overflow },
                )
            else
                generator.statements(
                    "x := @0(x) y := @0(y) diff := sub(x, y) if gt(diff, @1) { @2() }",
                    .{ cleanup, try generator.numberToken(max_text), panic_overflow },
                ),
            .checked_mul => if (integer.bits <= 128)
                generator.statements(
                    "x := @0(x) y := @0(y) let product_raw := mul(x, y) product := @0(product_raw) if iszero(eq(product, product_raw)) { @1() }",
                    .{ cleanup, panic_overflow },
                )
            else if (integer.isSigned())
                if (integer.bits == 256)
                    generator.statements(
                        "x := @0(x) y := @0(y) let product_raw := mul(x, y) product := @0(product_raw) if and(slt(x, 0), eq(y, @1)) { @2() } if iszero(or(iszero(x), eq(y, sdiv(product, x)))) { @2() }",
                        .{ cleanup, try generator.numberToken(min_text), panic_overflow },
                    )
                else
                    generator.statements(
                        "x := @0(x) y := @0(y) let product_raw := mul(x, y) product := @0(product_raw) if iszero(or(iszero(x), eq(y, sdiv(product, x)))) { @1() }",
                        .{ cleanup, panic_overflow },
                    )
            else
                generator.statements(
                    "x := @0(x) y := @0(y) let product_raw := mul(x, y) product := @0(product_raw) if iszero(or(iszero(x), eq(y, div(product, x)))) { @1() }",
                    .{ cleanup, panic_overflow },
                ),
            .checked_div, .wrapping_div => blk: {
                const panic_div_zero = panic_overflow;
                // The checked-division template registers both panic helpers,
                // including the unused signed-overflow helper for unsigned x/y.
                const panic_underflow = if (operation == .checked_div)
                    try self.panicFunction(.under_overflow)
                else
                    null;
                defer if (panic_underflow) |value| self.allocator.free(value);
                if (integer.isSigned() and operation == .checked_div) {
                    break :blk generator.statements(
                        "x := @0(x) y := @0(y) if iszero(y) { @1() } if and(eq(x, @2), eq(y, sub(0, 1))) { @3() } r := sdiv(x, y)",
                        .{ cleanup, panic_div_zero, try generator.numberToken(min_text), panic_underflow.? },
                    );
                }
                break :blk generator.statements(
                    "x := @0(x) y := @0(y) if iszero(y) { @1() } r := @2(x, y)",
                    .{ cleanup, panic_div_zero, if (integer.isSigned()) "sdiv" else "div" },
                );
            },
            .modulo => generator.statements(
                "x := @0(x) y := @0(y) if iszero(y) { @1() } r := @2(x, y)",
                .{ cleanup, panic_overflow, if (integer.isSigned()) "smod" else "mod" },
            ),
            else => unreachable,
        };
    }

    fn collectTemplate(self: *YulUtilFunctions, name: []const u8, comptime source: []const u8) UtilError![]u8 {
        if (try self.function_collector.beginFunction(name)) {
            errdefer self.function_collector.abortFunction(name);
            const generator = try self.function_collector.generator(self.evm_version);
            try self.function_collector.finishGeneratedFunction(name, try generator.functionDefinition(source, .{}));
        }
        return self.function_collector.copyFunctionName(name);
    }
};

fn compactHex(allocator: std.mem.Allocator, value: u256) std.mem.Allocator.Error![]u8 {
    return Numeric.toCompactHexWithPrefixAlloc(u256, allocator, value);
}

fn consumeGenerated(
    allocator: std.mem.Allocator,
    generated: []u8,
) !void {
    defer allocator.free(generated);
    try std.testing.expect(generated.len != 0);
}

test "Yul AST scalar helpers are generated once in dependency order" {
    var type_provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer type_provider.deinit();
    var collector = CollectorModule.MultiUseYulFunctionCollector.init(std.testing.allocator);
    defer collector.deinit();
    var utils = YulUtilFunctions.init(
        std.testing.allocator,
        &type_provider,
        CompatibilityIdResolver.legacyNodeIds(),
        EVMVersion.current(),
        .Default,
        &collector,
    );
    const uint256_type = Types.Type{ .payload = .{ .Integer = .{
        .bits = 256,
        .modifier = .Unsigned,
    } } };
    const first = try utils.cleanupFunction(&uint256_type);
    defer std.testing.allocator.free(first);
    const second = try utils.cleanupFunction(&uint256_type);
    defer std.testing.allocator.free(second);
    try std.testing.expectEqualStrings("cleanup_t_uint256", first);
    const checked_add = try utils.overflowCheckedIntAddFunction(
        uint256_type.payload.Integer,
    );
    defer std.testing.allocator.free(checked_add);
    try std.testing.expectEqualStrings("checked_add_t_uint256", checked_add);
    const code = try collector.testFunctionsAlloc();
    defer std.testing.allocator.free(code);
    try std.testing.expectEqual(
        @as(usize, 1),
        std.mem.count(u8, code, "function cleanup_t_uint256("),
    );
    try std.testing.expect(std.mem.find(u8, code, "panic_error_0x11") != null);
    try std.testing.expect(std.mem.find(u8, code, "if gt(x, sum)") != null);
}

test "Yul AST mapping keys retain static and dynamic parameter conventions" {
    const allocator = std.testing.allocator;
    var provider = try TypeProviderModule.TypeProvider.init(allocator);
    defer provider.deinit();
    var collector = CollectorModule.MultiUseYulFunctionCollector.init(allocator);
    defer collector.deinit();
    var utils = YulUtilFunctions.init(
        allocator,
        &provider,
        CompatibilityIdResolver.legacyNodeIds(),
        EVMVersion.current(),
        .Default,
        &collector,
    );
    const integer_mapping = try provider.mapping(provider.uint256(), "", provider.uint256(), "");
    const bytes_mapping = try provider.mapping(try provider.fixedBytes(32), "", provider.uint256(), "");
    const string_mapping = try provider.mapping(provider.stringStorage(), "", provider.uint256(), "");
    const cases = [_]struct {
        mapping: *const Types.Type,
        key: *const Types.Type,
        encoder: ?[]const u8 = null,
        parameters: []const []const u8,
    }{
        .{ .mapping = integer_mapping, .key = provider.uint256(), .parameters = &.{ "slot", "key" } },
        .{ .mapping = bytes_mapping, .key = try provider.stringLiteral("key"), .parameters = &.{"slot"} },
        .{ .mapping = string_mapping, .key = provider.stringMemory(), .encoder = "encode_memory_key", .parameters = &.{ "slot", "key_0" } },
        .{ .mapping = string_mapping, .key = provider.stringCalldata(), .encoder = "encode_calldata_key", .parameters = &.{ "slot", "key_0", "key_1" } },
    };
    for (cases) |case| {
        const name = try utils.mappingIndexAccessFunction(case.mapping, case.key, case.encoder);
        defer allocator.free(name);
        const function = collector.generated.items[collector.generated.items.len - 1];
        try std.testing.expectEqualStrings(name, try function.name.str());
        try std.testing.expectEqual(case.parameters.len, function.parameters.items.len);
        for (case.parameters, function.parameters.items) |expected, actual|
            try std.testing.expectEqualStrings(expected, try actual.name.str());
    }
}

test "Yul AST checked multiplication retains upstream width-specific overflow checks" {
    var type_provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer type_provider.deinit();
    var collector = CollectorModule.MultiUseYulFunctionCollector.init(std.testing.allocator);
    defer collector.deinit();
    var utils = YulUtilFunctions.init(
        std.testing.allocator,
        &type_provider,
        CompatibilityIdResolver.legacyNodeIds(),
        EVMVersion.current(),
        .Default,
        &collector,
    );

    const uint32_tree = try utils.integerBinaryBody(
        .checked_mul,
        .{ .bits = 32, .modifier = .Unsigned },
        "cleanup_t_uint32",
    );
    const uint32_body = try renderArithmeticTestBody(&collector, &uint32_tree);
    defer std.testing.allocator.free(uint32_body);
    try std.testing.expect(std.mem.find(
        u8,
        uint32_body,
        "eq(product, product_raw)",
    ) != null);
    try std.testing.expect(std.mem.find(u8, uint32_body, "div(product, x)") == null);

    const int200_tree = try utils.integerBinaryBody(
        .checked_mul,
        .{ .bits = 200, .modifier = .Signed },
        "cleanup_t_int200",
    );
    const int200_body = try renderArithmeticTestBody(&collector, &int200_tree);
    defer std.testing.allocator.free(int200_body);
    try std.testing.expect(std.mem.find(u8, int200_body, "sdiv(product, x)") != null);
    try std.testing.expect(std.mem.find(u8, int200_body, "if and(slt(x, 0)") == null);

    const int256_tree = try utils.integerBinaryBody(
        .checked_mul,
        .{ .bits = 256, .modifier = .Signed },
        "cleanup_t_int256",
    );
    const int256_body = try renderArithmeticTestBody(&collector, &int256_tree);
    defer std.testing.allocator.free(int256_body);
    try std.testing.expect(std.mem.find(u8, int256_body, "if and(slt(x, 0)") != null);
}

test "Yul AST string literal to fixed bytes conversion emits upstream numeric value" {
    const allocator = std.testing.allocator;
    var type_provider = try TypeProviderModule.TypeProvider.init(allocator);
    defer type_provider.deinit();
    var collector = CollectorModule.MultiUseYulFunctionCollector.init(allocator);
    defer collector.deinit();
    var utils = YulUtilFunctions.init(
        allocator,
        &type_provider,
        CompatibilityIdResolver.legacyNodeIds(),
        EVMVersion.current(),
        .Default,
        &collector,
    );

    const string_zero = try type_provider.stringLiteral("0");
    const bytes1 = try type_provider.fixedBytes(1);
    const conversion = try utils.conversionFunction(string_zero, bytes1);
    defer allocator.free(conversion);
    const code = try collector.testFunctionsAlloc();
    defer allocator.free(code);

    try std.testing.expect(std.mem.find(u8, code, "converted := \"0\"") == null);
    try std.testing.expect(std.mem.find(
        u8,
        code,
        "converted := 0x3000000000000000000000000000000000000000000000000000000000000000",
    ) != null);
}

test "Yul AST panic and empty-message revert helpers match stable names and payloads" {
    var type_provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer type_provider.deinit();
    var collector = CollectorModule.MultiUseYulFunctionCollector.init(std.testing.allocator);
    defer collector.deinit();
    var utils = YulUtilFunctions.init(
        std.testing.allocator,
        &type_provider,
        CompatibilityIdResolver.legacyNodeIds(),
        EVMVersion.current(),
        .Default,
        &collector,
    );
    const panic = try utils.panicFunction(.under_overflow);
    defer std.testing.allocator.free(panic);
    try std.testing.expectEqualStrings("panic_error_0x11", panic);
    const revert = try utils.revertReasonIfDebugFunction("");
    defer std.testing.allocator.free(revert);
    try std.testing.expectEqualStrings(
        "revert_error_c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470",
        revert,
    );
    const code = try collector.testFunctionsAlloc();
    defer std.testing.allocator.free(code);
    try std.testing.expect(std.mem.find(u8, code, "mstore(4, 0x11)") != null);
    try std.testing.expect(std.mem.find(u8, code, "revert(0, 0)") != null);
}

test "Yul AST storage updates accept implicitly convertible rational literal sources" {
    var type_provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer type_provider.deinit();
    var collector = CollectorModule.MultiUseYulFunctionCollector.init(std.testing.allocator);
    defer collector.deinit();
    var utils = YulUtilFunctions.init(
        std.testing.allocator,
        &type_provider,
        CompatibilityIdResolver.legacyNodeIds(),
        EVMVersion.current(),
        .Default,
        &collector,
    );

    const literal = try type_provider.rationalInteger("7", null);
    const update = try utils.updateStorageValueFunction(
        literal,
        type_provider.uint256(),
        0,
    );
    defer std.testing.allocator.free(update);
    try std.testing.expectEqualStrings(
        "update_storage_value_offset_0_t_rational_7_by_1_to_t_uint256",
        update,
    );

    const code = try collector.testFunctionsAlloc();
    defer std.testing.allocator.free(code);
    try std.testing.expect(std.mem.find(
        u8,
        code,
        "let convertedValue_0 := convert_t_rational_7_by_1_to_t_uint256(value_0)",
    ) != null);
}

test "Yul AST reference, packed ABI, and storage helper surface is instantiated" {
    const allocator = std.testing.allocator;
    var type_provider = try TypeProviderModule.TypeProvider.init(allocator);
    defer type_provider.deinit();
    var tree = try AST.Tree.init(allocator, "", "YulUtilMatrix.sol");
    defer tree.deinit();
    const amount = try tree.createNode(.{}, .{ .variable_declaration = .{
        .declaration = .{ .name = "amount" },
    } });
    const amount_annotation = try ASTAnnotations.ensure(&tree, amount);
    amount_annotation.variable_declaration.type_ref = type_provider.uint256();
    const payload = try tree.createNode(.{}, .{ .variable_declaration = .{
        .declaration = .{ .name = "payload" },
    } });
    const payload_annotation = try ASTAnnotations.ensure(&tree, payload);
    payload_annotation.variable_declaration.type_ref = type_provider.bytesStorage();
    const struct_members = try tree.ownSlice(*AST.Node, &.{ amount, payload });
    const struct_declaration = try tree.createNode(.{}, .{ .struct_definition = .{
        .declaration = .{ .name = "Payload" },
        .members = struct_members,
    } });
    const storage_struct = try type_provider.structType(struct_declaration, .Storage);
    const memory_struct = try type_provider.structType(struct_declaration, .Memory);
    const calldata_struct = try type_provider.structType(struct_declaration, .CallData);
    var collector = CollectorModule.MultiUseYulFunctionCollector.init(allocator);
    defer collector.deinit();
    var utils = YulUtilFunctions.init(
        allocator,
        &type_provider,
        CompatibilityIdResolver.legacyNodeIds(),
        EVMVersion.current(),
        .Default,
        &collector,
    );

    const uint8_type = try type_provider.uint(8);
    const uint32_type = try type_provider.uint(32);
    const bytes4_type = try type_provider.fixedBytes(4);
    const bytes8_type = try type_provider.fixedBytes(8);
    const literal = try type_provider.stringLiteral("zig-solidity");
    const negative_two = try type_provider.rationalInteger("-2", null);
    const uint8_memory_array = try type_provider.array(.Memory, uint8_type);
    const uint8_calldata_array = try type_provider.array(.CallData, uint8_type);
    const uint8_storage_array = try type_provider.array(.Storage, uint8_type);
    const fixed_calldata_array = try type_provider.arrayWithLength(.CallData, uint8_type, 3);
    const fixed_storage_array = try type_provider.arrayWithLength(.Storage, uint8_type, 3);
    const nested_memory_array = try type_provider.array(.Memory, uint8_memory_array);
    const nested_storage_array = try type_provider.array(.Storage, uint8_storage_array);
    const external_function = try type_provider.function(
        &.{uint8_type},
        &.{uint32_type},
        &.{"value"},
        &.{"result"},
        .External,
        .View,
        null,
        .{},
    );
    const tuple_from = try type_provider.tupleOfTypes(&.{ uint8_type, bytes4_type });
    const tuple_to = try type_provider.tupleOfTypes(&.{ uint32_type, bytes8_type });

    try consumeGenerated(allocator, try utils.copyLiteralToStorageFunction("zig-solidity"));
    try consumeGenerated(allocator, try utils.overflowCheckedIntLiteralExpFunction(
        negative_two,
        uint8_type.payload.Integer,
        type_provider.int256().payload.Integer,
    ));
    try consumeGenerated(allocator, try utils.storageArrayPopFunction(uint8_storage_array));
    try consumeGenerated(allocator, try utils.storageArrayPushFunction(
        uint8_storage_array,
        null,
    ));
    try consumeGenerated(allocator, try utils.storageArrayPushZeroFunction(
        uint8_storage_array,
    ));
    try consumeGenerated(allocator, try utils.storageArrayPopFunction(
        type_provider.bytesStorage(),
    ));
    try consumeGenerated(allocator, try utils.storageArrayPushFunction(
        type_provider.bytesStorage(),
        null,
    ));
    try consumeGenerated(allocator, try utils.copyValueArrayToStorageFunction(
        uint8_memory_array,
        uint8_storage_array,
    ));
    try consumeGenerated(allocator, try utils.copyValueArrayToStorageFunction(
        fixed_calldata_array,
        fixed_storage_array,
    ));
    try consumeGenerated(allocator, try utils.copyArrayFromStorageToMemoryFunction(
        uint8_storage_array,
        uint8_memory_array,
    ));
    try consumeGenerated(allocator, try utils.copyArrayToStorageFunction(
        nested_memory_array,
        nested_storage_array,
    ));
    try consumeGenerated(allocator, try utils.copyArrayFromStorageToMemoryFunction(
        nested_storage_array,
        nested_memory_array,
    ));
    try consumeGenerated(allocator, try utils.copyStructToStorageFunction(
        memory_struct,
        storage_struct,
    ));
    try consumeGenerated(allocator, try utils.copyStructToStorageFunction(
        calldata_struct,
        storage_struct,
    ));
    try consumeGenerated(allocator, try utils.conversionFunction(
        calldata_struct,
        memory_struct,
    ));
    try consumeGenerated(allocator, try utils.conversionFunction(
        storage_struct,
        memory_struct,
    ));
    try consumeGenerated(allocator, try utils.allocateMemoryStructFunction(memory_struct));
    try consumeGenerated(allocator, try utils.allocateAndInitializeMemoryStructFunction(
        memory_struct,
    ));
    try consumeGenerated(allocator, try utils.clearStorageStructFunction(storage_struct));
    try consumeGenerated(allocator, try utils.storageSetToZeroFunction(storage_struct));
    try consumeGenerated(allocator, try utils.readFromStorageReferenceType(memory_struct));
    try consumeGenerated(allocator, try utils.copyByteArrayToStorageFunction(
        type_provider.bytesMemory(),
        type_provider.bytesStorage(),
    ));
    try consumeGenerated(allocator, try utils.copyByteArrayToStorageFunction(
        type_provider.bytesCalldata(),
        type_provider.bytesStorage(),
    ));
    try consumeGenerated(allocator, try utils.bytesToFixedBytesConversionFunction(
        type_provider.bytesMemory(),
        bytes8_type,
    ));
    try consumeGenerated(allocator, try utils.arrayConversionFunction(
        uint8_calldata_array,
        uint8_memory_array,
    ));
    try consumeGenerated(allocator, try utils.arrayConversionFunction(
        uint8_storage_array,
        uint8_memory_array,
    ));
    try consumeGenerated(allocator, try utils.conversionFunction(tuple_from, tuple_to));
    try consumeGenerated(allocator, try utils.conversionFunction(
        literal,
        type_provider.bytesMemory(),
    ));
    try consumeGenerated(allocator, try utils.prepareStoreFunction(external_function));
    try consumeGenerated(allocator, try utils.writeToMemoryFunction(external_function));
    try consumeGenerated(allocator, try utils.storageSetToZeroFunction(external_function));
    try consumeGenerated(allocator, try utils.storageSetToZeroFunction(uint8_storage_array));
    try consumeGenerated(allocator, try utils.readFromStorageDynamic(
        external_function,
        true,
        .Unspecified,
    ));
    try consumeGenerated(allocator, try utils.readFromMemory(external_function));
    try consumeGenerated(allocator, try utils.readFromCalldata(external_function));

    const concat_types = [_]*const Types.Type{
        literal,
        bytes4_type,
        type_provider.bytesMemory(),
    };
    try consumeGenerated(allocator, try utils.bytesOrStringConcatFunction(
        &concat_types,
        .BytesConcat,
        "test_encode_packed_concat",
    ));
    const packed_types = [_]*const Types.Type{ uint8_type, type_provider.bytesMemory() };
    try consumeGenerated(allocator, try utils.packedHashFunction(
        &packed_types,
        &packed_types,
        "test_encode_packed_hash",
    ));
    try consumeGenerated(allocator, try utils.returnDataSelectorFunction());
    try consumeGenerated(allocator, try utils.tryDecodeErrorMessageFunction());
    try consumeGenerated(allocator, try utils.tryDecodePanicDataFunction());
    try consumeGenerated(allocator, try utils.extractReturndataFunction());
    try consumeGenerated(allocator, try utils.externalCodeFunction());
    try consumeGenerated(allocator, try utils.externalFunctionPointersEqualFunction());
    const revert_block = try utils.revertWithError(
        "Error(string)",
        &.{type_provider.stringMemory()},
        &.{"message"},
        "test_encode_error",
        null,
        null,
    );
    try std.testing.expect(revert_block.statements.items.len != 0);
    try consumeGenerated(allocator, try utils.requireOrAssertWithMessageFunction(
        type_provider.stringMemory(),
        &.{"message"},
        "test_encode_error",
    ));
    try consumeGenerated(allocator, try utils.requireWithErrorFunction(
        7,
        "Failure",
        "Failure(uint256)",
        &.{type_provider.uint256()},
        &.{type_provider.uint256()},
        &.{"value"},
        "test_encode_failure",
    ));
    try consumeGenerated(allocator, try utils.copyConstructorArgumentsToMemoryFunction(
        11,
        "Fixture",
        12,
        "Fixture_12",
        &.{"ret_param_0"},
        "test_decode_constructor",
    ));
    const debug_revert = try utils.revertReasonIfDebugBody("debug");
    try std.testing.expect(debug_revert.statements.items.len != 0);

    try std.testing.expectEqual(collector.requested_functions.count(), collector.generated.items.len);
    const generated = try collector.testFunctionsAlloc();
    defer allocator.free(generated);
    try std.testing.expect(std.mem.find(u8, generated, "function bytes_concat_") != null);
    try std.testing.expect(std.mem.find(u8, generated, "function packed_hashed_") != null);
    try std.testing.expect(std.mem.find(u8, generated, "function array_push_") != null);
    var source: std.ArrayList(u8) = .empty;
    defer source.deinit(allocator);
    try source.appendSlice(allocator,
        \\{
        \\function test_encode_packed_concat(pos, value, bytes_mpos) -> end { end := pos }
        \\function test_encode_packed_hash(pos, value_0, value_1) -> end { end := pos }
        \\function test_encode_error(pos, message) -> end { end := pos }
        \\function test_encode_failure(pos, value) -> end { end := pos }
        \\function test_decode_constructor(start, end) -> value { value := start }
        \\
    );
    try source.appendSlice(allocator, generated);
    try source.appendSlice(allocator, "}\n");
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var dialect = try EVMDialectModule.EVMDialect.init(
        allocator,
        EVMVersion.current(),
        true,
    );
    defer dialect.deinit();
    var parsed = (try AsmParser.Parser.parseSource(
        allocator,
        source.items,
        "yul-util-matrix.yul",
        &reporter,
        dialect.dialect(),
        .{},
    )) orelse return error.TestUnexpectedResult;
    defer parsed.deinit();
    try std.testing.expectEqual(@as(usize, 0), reporter.diagnostics().len);
    var analysis_info = AsmAnalysisInfo.init(allocator);
    defer analysis_info.deinit();
    var analyzer = AsmAnalysis.AsmAnalyzer.init(
        allocator,
        &analysis_info,
        &reporter,
        dialect.dialect(),
        .{},
        .{ .object_paths = &.{"Fixture_12"} },
        AsmAnalysis.instructionValidatorForEVMDialect(&dialect),
    );
    defer analyzer.deinit();
    try std.testing.expect(try analyzer.analyze(parsed.root()));
    try std.testing.expectEqual(@as(usize, 0), reporter.diagnostics().len);
    var printer = @import("../../libyul/asm_printer.zig").AsmPrinter.init(allocator, dialect.dialect(), &.{}, .noneValue(), null);
    const canonical = try printer.renderBlock(parsed.root());
    defer allocator.free(canonical);
    var digest: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(canonical, &digest, .{});
    // Updated from the 5b1255faa baseline for solc's nested copy blocks and
    // typed cleanup dependencies, covered by solidity-array-copy-scopes.json.
    // This checks statement/dependency order, values and literal kinds.
    try std.testing.expectEqualStrings("10b6ca3444702b840465013a9934c9dde1f8665e09b1a350f3b2a10be34a07a7", &std.fmt.bytesToHex(digest, .lower));
}

test "Yul AST scalar helper generation retains structure and published code" {
    const Equality = @import("../../libyul/optimiser/syntactical_equality.zig").SyntacticallyEqual;
    const allocator = std.testing.allocator;
    var types = try TypeProviderModule.TypeProvider.init(allocator);
    defer types.deinit();
    for ([_]EVMVersion{ .init(.Homestead), .init(.Byzantium), .init(.Cancun), .current() }) |version| {
        var collector = CollectorModule.MultiUseYulFunctionCollector.init(allocator);
        defer collector.deinit();
        var utils = YulUtilFunctions.init(allocator, &types, CompatibilityIdResolver.legacyNodeIds(), version, .Default, &collector);
        try consumeGenerated(allocator, try utils.identityFunction());
        try consumeGenerated(allocator, try utils.allocationFunction());
        try consumeGenerated(allocator, try utils.erc7201());
        try consumeGenerated(allocator, try utils.divide32CeilFunction());
        try consumeGenerated(allocator, try utils.extractByteArrayLengthFunction());
        try consumeGenerated(allocator, try utils.maskBytesFunctionDynamic());
        try consumeGenerated(allocator, try utils.maskLowerOrderBytesFunctionDynamic());
        try consumeGenerated(allocator, try utils.typedShiftLeftFunction(types.uint256(), types.uint256()));
        try consumeGenerated(allocator, try utils.typedShiftRightFunction(types.uint256(), types.uint256()));
        try consumeGenerated(allocator, try utils.typedShiftRightFunction(try types.integer(256, .Signed), types.uint256()));
        try consumeGenerated(allocator, try utils.combineExternalFunctionIdFunction());
        try consumeGenerated(allocator, try utils.splitExternalFunctionIdFunction());
        inline for (.{ false, true }) |from_calldata| inline for (.{ false, true }) |cleanup| {
            try consumeGenerated(allocator, try utils.copyToMemoryFunction(from_calldata, cleanup));
        };
        for (collector.generated.items) |entry| {
            var printer = @import("../../libyul/asm_printer.zig").AsmPrinter.init(allocator, collector.dialect.?.dialect(), &.{}, .noneValue(), null);
            const code = try printer.renderFunctionDefinition(&entry);
            defer allocator.free(code);
            const wrapped = try std.fmt.allocPrint(allocator, "{{{s}}}", .{code});
            defer allocator.free(wrapped);
            var errors = Diagnostics.ErrorReporter.init(allocator);
            defer errors.deinit();
            var parsed = (try AsmParser.Parser.parseSource(allocator, wrapped, "helper.yul", &errors, collector.dialect.?.dialect(), .{})).?;
            defer parsed.deinit();
            var equal = Equality.init(allocator);
            defer equal.deinit();
            const statement: Yul.Statement = .{ .function_definition = entry };
            try std.testing.expect(try equal.statement(&statement, &parsed.root().statements.items[0]));
        }
        const code = try collector.testFunctionsAlloc();
        defer allocator.free(code);
        try std.testing.expect(std.mem.startsWith(u8, code, "\nfunction identity(value) -> ret"));
    }
}

fn renderArithmeticTestBody(collector: *CollectorModule.MultiUseYulFunctionCollector, block: *const Yul.Block) ![]u8 {
    var printer = @import("../../libyul/asm_printer.zig").AsmPrinter.init(std.testing.allocator, collector.dialect.?.dialect(), &.{}, .noneValue(), null);
    return printer.renderBlock(block);
}
