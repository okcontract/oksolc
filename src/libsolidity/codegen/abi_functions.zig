// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Yul helpers for ABI encoding and decoding, translated from `ABIFunctions.cpp`.

const std = @import("std");
const Types = @import("../ast/types.zig");
const TypeBehavior = @import("../ast/types.zig");
const TypeProviderModule = @import("../ast/type_provider.zig");
const AST = @import("../ast/ast.zig");
const ASTAnnotations = @import("../ast/ast_annotations.zig");
const CompatibilityIdResolver = @import("../ast/compatibility_id_resolver.zig").CompatibilityIdResolver;
const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
const DebugSettings = @import("../interface/debug_settings.zig");
const CollectorModule = @import("multi_use_yul_function_collector.zig");
const YulUtilFunctionsModule = @import("yul_util_functions.zig");
const Numeric = @import("../../libsolutil/numeric.zig");
const Yul = @import("../../libyul/ast.zig");
const Generated = @import("../../libyul/generated_code.zig");

const interface_uint8 = Types.Type{ .payload = .{ .Integer = .{
    .bits = 8,
    .modifier = .Unsigned,
} } };

pub const ABIError = TypeBehavior.QueryError || YulUtilFunctionsModule.UtilError ||
    CollectorModule.CollectorError || error{
    InvalidTypeList,
    UnsupportedType,
    StringTooLong,
};

pub const EncodingOptions = struct {
    padded: bool = true,
    dynamic_inplace: bool = false,
    encode_function_from_stack: bool = false,
    encode_as_library_types: bool = false,

    pub fn suffixAlloc(
        self: EncodingOptions,
        allocator: std.mem.Allocator,
    ) std.mem.Allocator.Error![]u8 {
        var suffix: std.ArrayList(u8) = .empty;
        errdefer suffix.deinit(allocator);
        if (!self.padded) try suffix.appendSlice(allocator, "_nonPadded");
        if (self.dynamic_inplace) try suffix.appendSlice(allocator, "_inplace");
        if (self.encode_function_from_stack)
            try suffix.appendSlice(allocator, "_fromStack");
        if (self.encode_as_library_types)
            try suffix.appendSlice(allocator, "_library");
        return suffix.toOwnedSlice(allocator);
    }
};

pub const ABIFunctions = struct {
    allocator: std.mem.Allocator,
    type_provider: *TypeProviderModule.TypeProvider,
    compatibility_ids: CompatibilityIdResolver,
    evm_version: EVMVersion,
    revert_strings: DebugSettings.RevertStrings,
    function_collector: *CollectorModule.MultiUseYulFunctionCollector,
    utils: YulUtilFunctionsModule.YulUtilFunctions,

    pub fn init(
        allocator: std.mem.Allocator,
        type_provider: *TypeProviderModule.TypeProvider,
        compatibility_ids: CompatibilityIdResolver,
        evm_version: EVMVersion,
        revert_strings: DebugSettings.RevertStrings,
        function_collector: *CollectorModule.MultiUseYulFunctionCollector,
    ) ABIFunctions {
        return .{
            .allocator = allocator,
            .type_provider = type_provider,
            .compatibility_ids = compatibility_ids,
            .evm_version = evm_version,
            .revert_strings = revert_strings,
            .function_collector = function_collector,
            .utils = YulUtilFunctionsModule.YulUtilFunctions.init(
                allocator,
                type_provider,
                compatibility_ids,
                evm_version,
                revert_strings,
                function_collector,
            ),
        };
    }

    pub fn tupleEncoder(
        self: *ABIFunctions,
        given_types: []const *const Types.Type,
        target_types: []const *const Types.Type,
        encode_as_library_types: bool,
        reversed: bool,
    ) ABIError![]u8 {
        if (given_types.len != target_types.len) return error.InvalidTypeList;
        const options: EncodingOptions = .{
            .padded = true,
            .dynamic_inplace = false,
            .encode_function_from_stack = true,
            .encode_as_library_types = encode_as_library_types,
        };
        const encoded_targets = try self.allocator.alloc(
            *const Types.Type,
            target_types.len,
        );
        defer self.allocator.free(encoded_targets);
        for (target_types, encoded_targets) |target, *encoded|
            encoded.* = try self.fullEncodingType(target, encode_as_library_types);

        const suffix = try options.suffixAlloc(self.allocator);
        defer self.allocator.free(suffix);
        var name: std.ArrayList(u8) = .empty;
        defer name.deinit(self.allocator);
        try name.appendSlice(self.allocator, "abi_encode_tuple_");
        for (given_types) |type_ref| try self.appendIdentifier(&name, type_ref, true);
        try name.appendSlice(self.allocator, "_to_");
        for (encoded_targets) |type_ref|
            try self.appendIdentifier(&name, type_ref, true);
        try name.appendSlice(self.allocator, suffix);
        if (reversed) try name.appendSlice(self.allocator, "_reversed");

        if (!(try self.function_collector.beginFunction(name.items)))
            return self.function_collector.copyFunctionName(name.items);
        errdefer self.function_collector.abortFunction(name.items);

        var stack_size: usize = 0;
        var head_size: usize = 0;
        for (given_types, encoded_targets) |given, target| {
            stack_size = std.math.add(
                usize,
                stack_size,
                try TypeBehavior.sizeOnStack(given),
            ) catch return error.Overflow;
            head_size = std.math.add(
                usize,
                head_size,
                try TypeBehavior.calldataHeadSize(target),
            ) catch return error.Overflow;
        }

        const generator = try self.function_collector.generator(self.evm_version);
        const parameters = try generator.indexedNames("value", stack_size);
        var body: Generated.Buffer = .{ .generator = generator };
        try body.add("tail := add(headStart, @0)", .{head_size});
        var head_position: usize = 0;
        var stack_position: usize = 0;
        for (given_types, encoded_targets) |given, target| {
            const stack_words = try TypeBehavior.sizeOnStack(given);
            const values = parameters[stack_position..][0..stack_words];
            const encoder = try self.abiEncodingFunction(given, target, options);
            defer self.allocator.free(encoder);
            if (TypeBehavior.isDynamicallyEncoded(target))
                try body.add("mstore(add(headStart, @0), sub(tail, headStart)) tail := @1(@2, tail)", .{ head_position, encoder, values })
            else
                try body.add("@0(@1, add(headStart, @2))", .{ encoder, values, head_position });
            head_position += try TypeBehavior.calldataHeadSize(target);
            stack_position += stack_words;
        }
        if (head_position != head_size) return error.InvalidTypeList;
        const code = try generator.functionDefinition(
            "function @0(headStart, @1) -> tail { @2 }",
            .{ name.items, parameters, body.take() },
        );
        if (reversed) std.mem.reverse(Yul.NameWithDebugData, code.parameters.items[1..]);
        try self.function_collector.finishGeneratedFunction(name.items, code);
        return self.function_collector.copyFunctionName(name.items);
    }

    pub fn tupleEncoderReversed(
        self: *ABIFunctions,
        given_types: []const *const Types.Type,
        target_types: []const *const Types.Type,
        encode_as_library_types: bool,
    ) ABIError![]u8 {
        return self.tupleEncoder(
            given_types,
            target_types,
            encode_as_library_types,
            true,
        );
    }

    pub fn tupleEncoderPacked(
        self: *ABIFunctions,
        given_types: []const *const Types.Type,
        target_types: []const *const Types.Type,
        reversed: bool,
    ) ABIError![]u8 {
        if (given_types.len != target_types.len) return error.InvalidTypeList;
        const options: EncodingOptions = .{
            .padded = false,
            .dynamic_inplace = true,
            .encode_function_from_stack = true,
            .encode_as_library_types = false,
        };
        const encoded_targets = try self.allocator.alloc(
            *const Types.Type,
            target_types.len,
        );
        defer self.allocator.free(encoded_targets);
        for (target_types, encoded_targets) |target, *encoded|
            encoded.* = try self.fullEncodingType(target, false);

        const suffix = try options.suffixAlloc(self.allocator);
        defer self.allocator.free(suffix);
        var name: std.ArrayList(u8) = .empty;
        defer name.deinit(self.allocator);
        try name.appendSlice(self.allocator, "abi_encode_tuple_packed_");
        for (given_types) |type_ref| try self.appendIdentifier(&name, type_ref, true);
        try name.appendSlice(self.allocator, "_to_");
        for (encoded_targets) |type_ref|
            try self.appendIdentifier(&name, type_ref, true);
        try name.appendSlice(self.allocator, suffix);
        if (reversed) try name.appendSlice(self.allocator, "_reversed");

        if (!(try self.function_collector.beginFunction(name.items)))
            return self.function_collector.copyFunctionName(name.items);
        errdefer self.function_collector.abortFunction(name.items);

        var stack_size: usize = 0;
        for (given_types) |given|
            stack_size = std.math.add(
                usize,
                stack_size,
                try TypeBehavior.sizeOnStack(given),
            ) catch return error.Overflow;
        const generator = try self.function_collector.generator(self.evm_version);
        const parameters = try generator.indexedNames("value", stack_size);
        var body: Generated.Buffer = .{ .generator = generator };
        var stack_position: usize = 0;
        for (given_types, encoded_targets) |given, target| {
            const stack_words = try TypeBehavior.sizeOnStack(given);
            const values = parameters[stack_position..][0..stack_words];
            const encoder = try self.abiEncodingFunction(given, target, options);
            defer self.allocator.free(encoder);
            if (TypeBehavior.isDynamicallyEncoded(target))
                try body.add("pos := @0(@1, pos)", .{ encoder, values })
            else {
                const encoded_size = try TypeBehavior.calldataEncodedSize(target, false);
                try body.add("@0(@1, pos) pos := add(pos, @2)", .{ encoder, values, encoded_size });
            }
            stack_position += stack_words;
        }
        try body.add("end := pos", .{});
        const code = try generator.functionDefinition(
            "function @0(pos, @1) -> end { @2 }",
            .{ name.items, parameters, body.take() },
        );
        if (reversed) std.mem.reverse(Yul.NameWithDebugData, code.parameters.items[1..]);
        try self.function_collector.finishGeneratedFunction(name.items, code);
        return self.function_collector.copyFunctionName(name.items);
    }

    pub fn tupleEncoderPackedReversed(
        self: *ABIFunctions,
        given_types: []const *const Types.Type,
        target_types: []const *const Types.Type,
    ) ABIError![]u8 {
        return self.tupleEncoderPacked(given_types, target_types, true);
    }

    pub fn tupleDecoder(
        self: *ABIFunctions,
        types: []const *const Types.Type,
        from_memory: bool,
    ) ABIError![]u8 {
        var name: std.ArrayList(u8) = .empty;
        defer name.deinit(self.allocator);
        try name.appendSlice(self.allocator, "abi_decode_tuple_");
        for (types) |type_ref| try self.appendIdentifier(&name, type_ref, false);
        if (from_memory) try name.appendSlice(self.allocator, "_fromMemory");

        if (!(try self.function_collector.beginFunction(name.items)))
            return self.function_collector.copyFunctionName(name.items);
        errdefer self.function_collector.abortFunction(name.items);

        const decoding_types = try self.allocator.alloc(*const Types.Type, types.len);
        defer self.allocator.free(decoding_types);
        for (types, decoding_types) |type_ref, *decoding|
            decoding.* = try self.decodingType(type_ref);

        var return_count: usize = 0;
        var minimum_size: usize = 0;
        for (types, decoding_types) |type_ref, decoding| {
            const size = try TypeBehavior.sizeOnStack(type_ref);
            if (size == 0 or size != try TypeBehavior.sizeOnStack(decoding))
                return error.UnsupportedType;
            return_count = std.math.add(usize, return_count, size) catch return error.Overflow;
            minimum_size = std.math.add(
                usize,
                minimum_size,
                try TypeBehavior.calldataHeadSize(decoding),
            ) catch return error.Overflow;
        }
        const generator = try self.function_collector.generator(self.evm_version);
        const returns = try generator.indexedNames("value", return_count);
        const short_revert = try self.utils.revertReasonIfDebugFunction(
            "ABI decoding: tuple data too short",
        );
        defer self.allocator.free(short_revert);
        var body: Generated.Buffer = .{ .generator = generator };
        try body.add("if slt(sub(dataEnd, headStart), @0) { @1() }", .{ minimum_size, short_revert });
        var head_position: usize = 0;
        var stack_position: usize = 0;
        for (types, decoding_types) |type_ref, decoding| {
            const invalid_offset_revert = try self.utils.revertReasonIfDebugFunction(
                "ABI decoding: invalid tuple offset",
            );
            defer self.allocator.free(invalid_offset_revert);
            const stack_words = try TypeBehavior.sizeOnStack(type_ref);
            const values = returns[stack_position..][0..stack_words];
            const decoder = try self.abiDecodingFunction(type_ref, from_memory, true);
            defer self.allocator.free(decoder);
            if (TypeBehavior.isDynamicallyEncoded(decoding))
                try body.add("{ let offset := @0(add(headStart, @1)) if gt(offset, 0xffffffffffffffff) { @2() } @3 := @4(add(headStart, offset), dataEnd) }", .{ if (from_memory) "mload" else "calldataload", head_position, invalid_offset_revert, values, decoder })
            else
                try body.add("{ let offset := @0 @1 := @2(add(headStart, offset), dataEnd) }", .{ head_position, values, decoder });
            head_position += try TypeBehavior.calldataHeadSize(decoding);
            stack_position += stack_words;
        }
        const code = try generator.functionDefinition("function @0(headStart, dataEnd) -> @1 { @2 }", .{ name.items, returns, body.take() });
        try self.function_collector.finishGeneratedFunction(name.items, code);
        return self.function_collector.copyFunctionName(name.items);
    }

    pub fn abiEncodingFunction(
        self: *ABIFunctions,
        given_type: *const Types.Type,
        target_type_raw: *const Types.Type,
        options: EncodingOptions,
    ) ABIError![]u8 {
        const target_type = try self.fullEncodingType(
            target_type_raw,
            options.encode_as_library_types,
        );
        if (given_type.category() == .StringLiteral)
            return self.abiEncodingFunctionStringLiteral(
                given_type,
                target_type,
                options,
            );
        if (target_type.category() == .Array) {
            const source_type = switch (given_type.payload) {
                .Array => given_type,
                .ArraySlice => |slice| slice.array_type,
                else => return error.InvalidType,
            };
            const source = source_type.asArray() orelse return error.InvalidType;
            return switch (source.reference.location) {
                .CallData => if (source.isByteArrayOrString() or
                    TypeBehavior.equals(source.base_type, self.type_provider.uint256()) or
                    (source.base_type.asFixedBytes() != null and
                        source.base_type.asFixedBytes().?.bytes == 32))
                    self.abiEncodingFunctionCalldataArrayWithoutCleanup(
                        source_type,
                        target_type,
                        options,
                    )
                else
                    self.abiEncodingFunctionSimpleArray(
                        source_type,
                        target_type,
                        options,
                    ),
                .Memory => if (source.isByteArrayOrString())
                    self.abiEncodingFunctionMemoryByteArray(
                        source_type,
                        target_type,
                        options,
                    )
                else
                    self.abiEncodingFunctionSimpleArray(
                        source_type,
                        target_type,
                        options,
                    ),
                .Storage => if (try TypeBehavior.storageBytes(source.base_type) <= 16)
                    self.abiEncodingFunctionCompactStorageArray(
                        source_type,
                        target_type,
                        options,
                    )
                else
                    self.abiEncodingFunctionSimpleArray(
                        source_type,
                        target_type,
                        options,
                    ),
                .Transient => error.UnsupportedType,
            };
        }
        if (target_type.category() == .Struct)
            return self.abiEncodingFunctionStruct(
                given_type,
                target_type,
                options,
            );
        if (given_type.category() == .Function)
            return self.abiEncodingFunctionFunctionType(
                given_type,
                target_type,
                options,
            );

        if (try TypeBehavior.sizeOnStack(given_type) != 1 or
            (!TypeBehavior.isValueType(target_type) and
                !TypeBehavior.dataStoredIn(given_type, .Storage)) or
            TypeBehavior.isDynamicallyEncoded(target_type) or
            try TypeBehavior.calldataEncodedSize(target_type, true) != 32)
            return error.UnsupportedType;
        const name = try self.encodingFunctionNameAlloc(given_type, target_type, options);
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);

        const generator = try self.function_collector.generator(self.evm_version);
        var cleanup_expression = if (TypeBehavior.dataStoredIn(given_type, .Storage)) blk: {
            if (!options.encode_as_library_types or !options.padded or
                options.dynamic_inplace or
                !TypeBehavior.equals(target_type, self.type_provider.uint256()))
                return error.InvalidType;
            break :blk try generator.identifier("value");
        } else if (TypeBehavior.equals(given_type, target_type)) blk: {
            const cleanup = try self.utils.cleanupFunction(given_type);
            defer self.allocator.free(cleanup);
            break :blk try generator.expression(
                "@0(value)",
                .{cleanup},
            );
        } else blk: {
            const conversion = try self.utils.conversionFunction(given_type, target_type);
            defer self.allocator.free(conversion);
            break :blk try generator.expression(
                "@0(value)",
                .{conversion},
            );
        };

        if (!options.padded) {
            const align_function = try self.utils.leftAlignFunction(target_type);
            defer self.allocator.free(align_function);
            const unaligned = cleanup_expression;
            cleanup_expression = try generator.expression(
                "@0(@1)",
                .{ align_function, unaligned },
            );
        }
        const code = try generator.functionDefinition(
            "\nfunction @0(value, pos) {\nmstore(pos, @1)\n}\n",
            .{ name, cleanup_expression },
        );

        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn abiEncodeAndReturnUpdatedPosFunction(
        self: *ABIFunctions,
        given_type: *const Types.Type,
        target_type: *const Types.Type,
        options: EncodingOptions,
    ) ABIError![]u8 {
        const suffix = try options.suffixAlloc(self.allocator);
        defer self.allocator.free(suffix);
        const given_identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, given_type);
        defer self.allocator.free(given_identifier);
        const target_identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, target_type);
        defer self.allocator.free(target_identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "abi_encodeUpdatedPos_{s}_to_{s}{s}",
            .{ given_identifier, target_identifier, suffix },
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const encoder = try self.abiEncodingFunction(given_type, target_type, options);
        defer self.allocator.free(encoder);
        const target_encoding = try self.fullEncodingType(
            target_type,
            options.encode_as_library_types,
        );
        const generator = try self.function_collector.generator(self.evm_version);
        const values = try generator.indexedNames("value", try self.numVariablesForType(given_type, options));
        const code = if (TypeBehavior.isDynamicallyEncoded(target_encoding))
            try generator.functionDefinition("function @0(@1, pos) -> updatedPos { updatedPos := @2(@1, pos) }", .{ name, values, encoder })
        else blk: {
            const size = try TypeBehavior.calldataEncodedSize(target_encoding, options.padded);
            if (size == 0) return error.InvalidType;
            const size_text = try compactHex(self.allocator, size);
            defer self.allocator.free(size_text);
            break :blk try generator.functionDefinition("function @0(@1, pos) -> updatedPos { @2(@1, pos) updatedPos := add(pos, @3) }", .{ name, values, encoder, try generator.numberToken(size_text) });
        };
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn arrayStoreLengthForEncodingFunction(
        self: *ABIFunctions,
        type_ref: *const Types.Type,
        options: EncodingOptions,
    ) ABIError![]u8 {
        const array = type_ref.asArray() orelse return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const suffix = try options.suffixAlloc(self.allocator);
        defer self.allocator.free(suffix);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "array_storeLengthForEncoding_{s}{s}",
            .{ identifier, suffix },
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const generator = try self.function_collector.generator(self.evm_version);
        const body = if (array.isDynamicallySized() and !options.dynamic_inplace)
            try generator.statements("mstore(pos, length) updated_pos := add(pos, 0x20)", .{})
        else
            try generator.statements("updated_pos := pos", .{});
        const code = try generator.functionDefinition(
            "\nfunction @0(pos, length) -> updated_pos {\n@1\n}\n",
            .{ name, body },
        );

        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    fn abiEncodingFunctionCalldataArrayWithoutCleanup(
        self: *ABIFunctions,
        from_type: *const Types.Type,
        to_type: *const Types.Type,
        options: EncodingOptions,
    ) ABIError![]u8 {
        const from = from_type.asArray() orelse return error.InvalidType;
        const to = to_type.asArray() orelse return error.InvalidType;
        if (from.reference.location != .CallData) return error.InvalidType;
        const from_stride = try TypeBehavior.calldataStride(from.*);
        const to_stride = try TypeBehavior.memoryStride(to.*);
        if (@as(u256, from_stride) != to_stride) return error.InvalidType;
        const from_memory = self.type_provider.withLocation(
            from_type,
            .Memory,
            true,
        ) catch |err| return mapProviderError(err);
        const to_memory = self.type_provider.withLocation(
            to_type,
            .Memory,
            true,
        ) catch |err| return mapProviderError(err);
        if (!TypeBehavior.equals(from_memory, to_memory)) return error.InvalidType;

        const name = try self.encodingFunctionNameAlloc(from_type, to_type, options);
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = if (from.isDynamicallySized()) blk: {
            const store_length = try self.arrayStoreLengthForEncodingFunction(
                to_type,
                options,
            );
            defer self.allocator.free(store_length);
            var scale: Generated.Buffer = .{ .generator = generator };
            if (!from.isByteArrayOrString() and from_stride != 1) {
                const maximum = std.math.maxInt(u256) / @as(u256, from_stride);
                const maximum_text = try compactHex(self.allocator, maximum);
                defer self.allocator.free(maximum_text);
                const stride_text = try compactHex(self.allocator, from_stride);
                defer self.allocator.free(stride_text);
                const revert = try self.utils.revertReasonIfDebugFunction(
                    "ABI encoding: array data too long",
                );
                defer self.allocator.free(revert);
                try scale.add(
                    "if gt(length, @0) { @1() }\nlength := mul(length, @2)",
                    .{ try generator.numberToken(maximum_text), revert, try generator.numberToken(stride_text) },
                );
            }
            const copy = try self.utils.copyToMemoryFunction(
                true,
                from.isByteArrayOrString(),
            );
            defer self.allocator.free(copy);
            const length_padded = if (options.padded and from.isByteArrayOrString()) pad: {
                const round = try self.utils.roundUpFunction();
                defer self.allocator.free(round);
                break :pad try generator.expression(
                    "@0(length)",
                    .{round},
                );
            } else try generator.identifier("length");

            break :blk try generator.functionDefinition(
                "\nfunction @0(start, length, pos) -> end {\npos := @1(pos, length)\n@2\n@3(start, pos, length)\nend := add(pos, @4)\n}\n",
                .{
                    name,
                    store_length,
                    scale.take(),
                    copy,
                    length_padded,
                },
            );
        } else blk: {
            if (from_stride != 32) return error.InvalidType;
            const byte_length = std.math.mul(
                u256,
                from.length.?,
                from_stride,
            ) catch return error.Overflow;
            const byte_length_text = try compactHex(self.allocator, byte_length);
            defer self.allocator.free(byte_length_text);
            const copy = try self.utils.copyToMemoryFunction(
                true,
                from.isByteArrayOrString(),
            );
            defer self.allocator.free(copy);
            break :blk try generator.functionDefinition(
                "\nfunction @0(start, pos) {\n@1(start, pos, @2)\n}\n",
                .{ name, copy, try generator.numberToken(byte_length_text) },
            );
        };

        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    fn abiEncodingFunctionMemoryByteArray(
        self: *ABIFunctions,
        from_type: *const Types.Type,
        to_type: *const Types.Type,
        options: EncodingOptions,
    ) ABIError![]u8 {
        const from = from_type.asArray() orelse return error.InvalidType;
        const to = to_type.asArray() orelse return error.InvalidType;
        if (from.reference.location != .Memory or !from.isByteArrayOrString() or
            !to.isByteArrayOrString() or
            from.isDynamicallySized() != to.isDynamicallySized() or
            from.length != to.length)
            return error.InvalidType;
        const name = try self.encodingFunctionNameAlloc(from_type, to_type, options);
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const length_function = try self.utils.arrayLengthFunction(from_type);
        defer self.allocator.free(length_function);
        const store_length = try self.arrayStoreLengthForEncodingFunction(to_type, options);
        defer self.allocator.free(store_length);
        const copy = try self.utils.copyToMemoryFunction(false, true);
        defer self.allocator.free(copy);
        const generator = try self.function_collector.generator(self.evm_version);
        const padded = if (options.padded) blk: {
            const round = try self.utils.roundUpFunction();
            defer self.allocator.free(round);
            break :blk try generator.expression("@0(length)", .{round});
        } else try generator.identifier("length");

        const code = try generator.functionDefinition(
            "\nfunction @0(value, pos) -> end {\nlet length := @1(value)\npos := @2(pos, length)\n@3(add(value, 0x20), pos, length)\nend := add(pos, @4)\n}\n",
            .{ name, length_function, store_length, copy, padded },
        );

        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    fn abiEncodingFunctionSimpleArray(
        self: *ABIFunctions,
        from_type: *const Types.Type,
        to_type: *const Types.Type,
        options: EncodingOptions,
    ) ABIError![]u8 {
        const from = from_type.asArray() orelse return error.InvalidType;
        const to = to_type.asArray() orelse return error.InvalidType;
        if (from.isDynamicallySized() != to.isDynamicallySized() or
            from.length != to.length or from.isByteArrayOrString())
            return error.InvalidType;
        if (from.reference.location == .Storage and
            try TypeBehavior.storageBytes(from.base_type) <= 16)
            return error.InvalidType;
        const name = try self.encodingFunctionNameAlloc(from_type, to_type, options);
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);

        const dynamic = TypeBehavior.isDynamicallyEncoded(to_type);
        const dynamic_base = TypeBehavior.isDynamicallyEncoded(to.base_type);
        const uses_tail = dynamic_base and !options.dynamic_inplace;
        var sub_options = options;
        sub_options.encode_function_from_stack = false;
        sub_options.padded = true;
        const generator = try self.function_collector.generator(self.evm_version);
        const element_count = try self.numVariablesForType(from.base_type, sub_options);
        const element_values = try generator.indexedNames("elementValue", element_count);
        const length_as_argument = from.reference.location == .CallData and
            from.isDynamicallySized();
        const length_declaration = if (length_as_argument)
            Yul.Block{}
        else blk: {
            const length_function = try self.utils.arrayLengthFunction(from_type);
            defer self.allocator.free(length_function);
            break :blk try generator.statements(
                "let length := @0(value)",
                .{length_function},
            );
        };

        const store_length = try self.arrayStoreLengthForEncodingFunction(to_type, options);
        defer self.allocator.free(store_length);
        const data_area = try self.utils.arrayDataAreaFunction(from_type);
        defer self.allocator.free(data_area);
        const encode = try self.abiEncodeAndReturnUpdatedPosFunction(
            from.base_type,
            to.base_type,
            sub_options,
        );
        defer self.allocator.free(encode);
        const access = switch (from.reference.location) {
            .Memory => try generator.expression("mload(srcPtr)", .{}),
            .Storage => if (TypeBehavior.isValueType(from.base_type)) blk: {
                const read = try self.utils.readFromStorage(from.base_type, 0, false, .Unspecified);
                defer self.allocator.free(read);
                break :blk try generator.expression(
                    "@0(srcPtr)",
                    .{read},
                );
            } else try generator.expression("srcPtr", .{}),
            .CallData => blk: {
                const calldata_access = try self.calldataAccessFunction(from.base_type);
                defer self.allocator.free(calldata_access);
                break :blk try generator.expression(
                    "@0(baseRef, srcPtr)",
                    .{calldata_access},
                );
            },
            .Transient => return error.UnsupportedType,
        };

        const next = try self.utils.nextArrayElementFunction(from_type);
        defer self.allocator.free(next);

        const loop_body = if (uses_tail)
            try generator.statements("mstore(pos, sub(tail, headStart)) let @0 := @1 tail := @2(@0, tail) srcPtr := @3(srcPtr) pos := add(pos, 0x20)", .{ element_values, access, encode, next })
        else
            try generator.statements("let @0 := @1 pos := @2(@0, pos) srcPtr := @3(srcPtr)", .{ element_values, access, encode, next });
        const tail_setup = if (uses_tail) try generator.statements("let headStart := pos let tail := add(pos, mul(length, 0x20))", .{}) else Yul.Block{};
        var finish: Generated.Buffer = .{ .generator = generator };
        if (uses_tail) try finish.add("pos := tail", .{});
        if (dynamic) try finish.add("end := pos", .{});
        const length_parameters: []const []const u8 = if (length_as_argument) &.{"length"} else &.{};
        const returns: []const []const u8 = if (dynamic) &.{"end"} else &.{};
        const code = try generator.functionDefinition(
            "function @0(value, @1, pos) -> @2 { @3 pos := @4(pos, length) @5 let baseRef := @6(value) let srcPtr := baseRef for { let i := 0 } lt(i, length) { i := add(i, 1) } { @7 } @8 }",
            .{ name, length_parameters, returns, length_declaration, store_length, tail_setup, data_area, loop_body, finish.take() },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    fn abiEncodingFunctionCompactStorageArray(
        self: *ABIFunctions,
        from_type: *const Types.Type,
        to_type: *const Types.Type,
        options: EncodingOptions,
    ) ABIError![]u8 {
        const from = from_type.asArray() orelse return error.InvalidType;
        const to = to_type.asArray() orelse return error.InvalidType;
        if (from.reference.location != .Storage or
            from.isDynamicallySized() != to.isDynamicallySized() or
            from.length != to.length)
            return error.InvalidType;
        const name = try self.encodingFunctionNameAlloc(from_type, to_type, options);
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);

        const generator = try self.function_collector.generator(self.evm_version);
        const code = if (from.isByteArrayOrString()) blk: {
            if (!to.isByteArrayOrString()) return error.InvalidType;
            const length_function = try self.utils.extractByteArrayLengthFunction();
            defer self.allocator.free(length_function);
            const store_length = try self.arrayStoreLengthForEncodingFunction(to_type, options);
            defer self.allocator.free(store_length);
            const data_area = try self.utils.arrayDataAreaFunction(from_type);
            defer self.allocator.free(data_area);
            break :blk try generator.functionDefinition(
                "\nfunction @0(value, pos) -> ret {\nlet slotValue := sload(value)\nlet length := @1(slotValue)\npos := @2(pos, length)\nswitch and(slotValue, 1)\ncase 0 {\n// short byte array\nmstore(pos, and(slotValue, not(0xff)))\nret := add(pos, mul(@3, iszero(iszero(length))))\n}\ncase 1 {\n// long byte array\nlet dataPos := @4(value)\nlet i := 0\nfor { } lt(i, length) { i := add(i, 0x20) } {\nmstore(add(pos, i), sload(dataPos))\ndataPos := add(dataPos, 1)\n}\nret := add(pos, @5)\n}\n}\n",
                .{
                    name,
                    length_function,
                    store_length,
                    if (options.padded) try generator.expression("0x20", .{}) else try generator.identifier("length"),
                    data_area,
                    if (options.padded) try generator.identifier("i") else try generator.identifier("length"),
                },
            );
        } else blk: {
            const storage_bytes = try TypeBehavior.storageBytes(from.base_type);
            if (storage_bytes == 0 or storage_bytes > 16 or
                TypeBehavior.isDynamicallyEncoded(from.base_type) or
                TypeBehavior.isDynamicallyEncoded(to.base_type) or
                !TypeBehavior.isValueType(from.base_type))
                return error.InvalidType;
            const items_per_slot: usize = 32 / storage_bytes;
            const spill: usize = if (from.length) |length|
                @intCast(length % items_per_slot)
            else
                0;
            const dynamic = TypeBehavior.isDynamicallyEncoded(to_type);
            const length_function = try self.utils.arrayLengthFunction(from_type);
            defer self.allocator.free(length_function);
            const store_length = try self.arrayStoreLengthForEncodingFunction(to_type, options);
            defer self.allocator.free(store_length);
            const data_area = try self.utils.arrayDataAreaFunction(from_type);
            defer self.allocator.free(data_area);
            var sub_options = options;
            sub_options.encode_function_from_stack = false;
            sub_options.padded = true;
            const encode = try self.abiEncodingFunction(
                from.base_type,
                to.base_type,
                sub_options,
            );
            defer self.allocator.free(encode);
            const stride = try compactHex(
                self.allocator,
                try TypeBehavior.calldataStride(to.*),
            );
            defer self.allocator.free(stride);
            var loop_items: Generated.Buffer = .{ .generator = generator };
            var spill_items: Generated.Buffer = .{ .generator = generator };
            for (0..items_per_slot) |index| {
                const extract = try self.utils.extractFromStorageValueFunction(
                    from.base_type,
                    @intCast(index * storage_bytes),
                );
                defer self.allocator.free(extract);
                try loop_items.add(
                    "@0(@1(data), pos)\npos := add(pos, @2)\n",
                    .{ encode, extract, try generator.numberToken(stride) },
                );
                const condition = if (from.isDynamicallySized())
                    try generator.expression("lt(itemCounter, length)", .{})
                else
                    try generator.expression("@0", .{@intFromBool(index < spill)});
                try spill_items.add(
                    "if @0 {\n@1(@2(data), pos)\npos := add(pos, @3)\nitemCounter := add(itemCounter, 1)\n}\n",
                    .{ condition, encode, extract, try generator.numberToken(stride) },
                );
            }
            const use_loop = from.isDynamicallySized() or
                from.length.? >= items_per_slot;
            const use_spill = from.isDynamicallySized() or spill != 0;
            break :blk try generator.functionDefinition(
                "\nfunction @0(value, pos) -> @1 {\nlet length := @2(value)\npos := @3(pos, length)\nlet originalPos := pos\nlet srcPtr := @4(value)\nlet itemCounter := 0\nif @5 {\n// Run the loop over all full slots\nfor { } lt(add(itemCounter, sub(@6, 1)), length)\n{ itemCounter := add(itemCounter, @7) }\n{\nlet data := sload(srcPtr)\n@8 srcPtr := add(srcPtr, 1)\n}\n}\n// Handle the last (not necessarily full) slot specially\nif @9 {\nlet data := sload(srcPtr)\n@10}\n@11\n}\n",
                .{
                    name,
                    @as([]const []const u8, if (dynamic) &.{"end"} else &.{}),
                    length_function,
                    store_length,
                    data_area,
                    @intFromBool(use_loop),
                    items_per_slot,
                    items_per_slot,
                    loop_items.take(),
                    @intFromBool(use_spill),
                    spill_items.take(),
                    if (dynamic) try generator.statements("end := pos", .{}) else Yul.Block{},
                },
            );
        };

        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    fn abiEncodingFunctionStruct(
        self: *ABIFunctions,
        from_type: *const Types.Type,
        to_type: *const Types.Type,
        options: EncodingOptions,
    ) ABIError![]u8 {
        const from = switch (from_type.payload) {
            .Struct => |value| value,
            else => return error.InvalidType,
        };
        const to = switch (to_type.payload) {
            .Struct => |value| value,
            else => return error.InvalidType,
        };
        if (from.declaration != to.declaration or
            to.declaration.nodeKind() != .struct_definition)
            return error.InvalidType;
        const name = try self.encodingFunctionNameAlloc(from_type, to_type, options);
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);

        const members = to.declaration.payload.struct_definition.members;
        const from_member_types = try self.allocator.alloc(*const Types.Type, members.len);
        defer self.allocator.free(from_member_types);
        for (members, from_member_types) |member, *target| {
            const raw = try TypeBehavior.variableDeclarationType(member);
            target.* = self.type_provider.withLocationIfReference(
                from.reference.location,
                raw,
                false,
            ) catch |err| return mapProviderError(err);
        }
        const storage_layout = if (from.reference.location == .Storage)
            try TypeBehavior.computeStorageOffsetsAlloc(
                self.allocator,
                from_member_types,
                0,
            )
        else
            Types.StorageOffsets{};
        defer if (from.reference.location == .Storage)
            self.allocator.free(storage_layout.offsets);

        const dynamic = TypeBehavior.isDynamicallyEncoded(to_type);
        const generator = try self.function_collector.generator(self.evm_version);
        var member_code: Generated.Buffer = .{ .generator = generator };
        var encoding_offset: u256 = 0;
        var previous_slot: ?u256 = null;
        for (members, from_member_types, 0..) |member, member_from, index| {
            if (member.nodeKind() != .variable_declaration) return error.InvalidType;
            const member_name = member.payload.variable_declaration.declaration.name;
            const raw_to = try TypeBehavior.variableDeclarationType(member);
            const localized_to = self.type_provider.withLocationIfReference(
                to.reference.location,
                raw_to,
                false,
            ) catch |err| return mapProviderError(err);
            const member_to = try self.fullEncodingType(
                localized_to,
                options.encode_as_library_types,
            );
            const dynamic_member = TypeBehavior.isDynamicallyEncoded(member_to);
            if (dynamic_member and !dynamic) return error.InvalidType;

            var preprocess: Yul.Block = .{};

            const retrieve = switch (from.reference.location) {
                .Storage => blk: {
                    const location = storage_layout.offsets[index] orelse
                        return error.InvalidType;
                    const relative_slot = location.slot;
                    if (TypeBehavior.isValueType(member_from)) {
                        if (previous_slot == null or previous_slot.? != relative_slot) {
                            const slot_text = try compactHex(self.allocator, relative_slot);
                            defer self.allocator.free(slot_text);
                            preprocess = try generator.statements(
                                "slotValue := sload(add(value, @0))",
                                .{try generator.numberToken(slot_text)},
                            );
                            previous_slot = relative_slot;
                        }
                        const extract = try self.utils.extractFromStorageValueFunction(
                            member_from,
                            location.byte_offset,
                        );
                        defer self.allocator.free(extract);
                        break :blk try generator.expression(
                            "@0(slotValue)",
                            .{extract},
                        );
                    }
                    if (location.byte_offset != 0) return error.InvalidType;
                    const slot_text = try compactHex(self.allocator, relative_slot);
                    defer self.allocator.free(slot_text);
                    break :blk try generator.expression(
                        "add(value, @0)",
                        .{try generator.numberToken(slot_text)},
                    );
                },
                .Memory => blk: {
                    const offset = try TypeBehavior.structMemoryOffsetOfMember(
                        from,
                        member_name,
                    );
                    const text = try compactHex(self.allocator, offset);
                    defer self.allocator.free(text);
                    break :blk try generator.expression(
                        "mload(add(value, @0))",
                        .{try generator.numberToken(text)},
                    );
                },
                .CallData => blk: {
                    const offset = try TypeBehavior.structCalldataOffsetOfMember(
                        from,
                        member_name,
                    );
                    const text = try compactHex(self.allocator, offset);
                    defer self.allocator.free(text);
                    const access = try self.calldataAccessFunction(member_from);
                    defer self.allocator.free(access);
                    break :blk try generator.expression(
                        "@0(value, add(value, @1))",
                        .{ access, try generator.numberToken(text) },
                    );
                },
                .Transient => return error.UnsupportedType,
            };

            var sub_options = options;
            sub_options.encode_function_from_stack = false;
            sub_options.padded = true;
            const member_values = try generator.indexedNames("memberValue", try self.numVariablesForType(member_from, sub_options));
            const encode = if (options.dynamic_inplace) blk: {
                const updated = try self.abiEncodeAndReturnUpdatedPosFunction(
                    member_from,
                    member_to,
                    sub_options,
                );
                defer self.allocator.free(updated);
                break :blk try generator.statements(
                    "pos := @0(@1, pos)",
                    .{ updated, member_values },
                );
            } else if (dynamic_member) blk: {
                const encoder = try self.abiEncodingFunction(
                    member_from,
                    member_to,
                    sub_options,
                );
                defer self.allocator.free(encoder);
                const offset_text = try compactHex(self.allocator, encoding_offset);
                defer self.allocator.free(offset_text);
                break :blk try generator.statements(
                    "mstore(add(pos, @0), sub(tail, pos))\ntail := @1(@2, tail)",
                    .{ try generator.numberToken(offset_text), encoder, member_values },
                );
            } else blk: {
                const encoder = try self.abiEncodingFunction(
                    member_from,
                    member_to,
                    sub_options,
                );
                defer self.allocator.free(encoder);
                const offset_text = try compactHex(self.allocator, encoding_offset);
                defer self.allocator.free(offset_text);
                break :blk try generator.statements(
                    "@0(@1, add(pos, @2))",
                    .{ encoder, member_values, try generator.numberToken(offset_text) },
                );
            };

            if (!options.dynamic_inplace)
                encoding_offset = std.math.add(
                    u256,
                    encoding_offset,
                    try TypeBehavior.calldataHeadSize(member_to),
                ) catch return error.Overflow;
            try member_code.add(
                "{\n@0\nlet @1 := @2\n@3\n}\n",
                .{ preprocess, member_values, retrieve, encode },
            );
        }
        const head_size = try compactHex(self.allocator, encoding_offset);
        defer self.allocator.free(head_size);
        const assign_end = if (dynamic and options.dynamic_inplace)
            try generator.statements("end := pos", .{})
        else if (dynamic)
            try generator.statements("end := tail", .{})
        else
            Yul.Block{};
        const returns: []const []const u8 = if (dynamic) &.{"end"} else &.{};
        const preload = if (from.reference.location == .Storage) try generator.statements("let slotValue := 0", .{}) else Yul.Block{};
        const code = try generator.functionDefinition(
            "function @0(value, pos) -> @1 { let tail := add(pos, @2) @3 @4 @5 }",
            .{ name, returns, try generator.numberToken(head_size), preload, member_code.take(), assign_end },
        );
        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    fn abiEncodingFunctionStringLiteral(
        self: *ABIFunctions,
        from_type: *const Types.Type,
        to_type: *const Types.Type,
        options: EncodingOptions,
    ) ABIError![]u8 {
        const literal = switch (from_type.payload) {
            .StringLiteral => |value| value.value,
            else => return error.InvalidType,
        };
        const name = try self.encodingFunctionNameAlloc(from_type, to_type, options);
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = if (TypeBehavior.isDynamicallySized(to_type)) blk: {
            if (to_type.category() != .Array) return error.InvalidType;
            const store_length = try self.arrayStoreLengthForEncodingFunction(
                to_type,
                options,
            );
            defer self.allocator.free(store_length);
            const store_literal = try self.utils.storeLiteralInMemoryFunction(literal);
            defer self.allocator.free(store_literal);
            const overall_size = if (options.padded)
                ((literal.len + 31) / 32) * 32
            else
                literal.len;
            break :blk try generator.functionDefinition(
                "\nfunction @0(pos) -> end {\npos := @1(pos, @2)\n@3(pos)\nend := add(pos, @4)\n}\n",
                .{ name, store_length, literal.len, store_literal, overall_size },
            );
        } else blk: {
            const fixed = to_type.asFixedBytes() orelse return error.InvalidType;
            if (literal.len > 32 or fixed.bytes < literal.len)
                return error.InvalidType;
            const word = try generator.word(literal);
            break :blk try generator.functionDefinition(
                "\nfunction @0(pos) {\nmstore(pos, @1)\n}\n",
                .{ name, word },
            );
        };

        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    fn abiEncodingFunctionFunctionType(
        self: *ABIFunctions,
        from_type: *const Types.Type,
        to_type: *const Types.Type,
        options: EncodingOptions,
    ) ABIError![]u8 {
        const from = from_type.asFunction() orelse return error.InvalidType;
        const to = to_type.asFunction() orelse return error.InvalidType;
        if (from.kind != .External or to.kind != .External or
            try TypeBehavior.sizeOnStack(from_type) !=
                try TypeBehavior.sizeOnStack(to_type))
            return error.InvalidType;
        const name = try self.encodingFunctionNameAlloc(from_type, to_type, options);
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = if (options.encode_function_from_stack) blk: {
            const combine = try self.utils.combineExternalFunctionIdFunction();
            defer self.allocator.free(combine);
            const conversion = try self.utils.conversionFunction(from_type, to_type);
            defer self.allocator.free(conversion);
            break :blk try generator.functionDefinition(
                "\nfunction @0(addr, function_id, pos) {\naddr, function_id := @1(addr, function_id)\nmstore(pos, @2(addr, function_id))\n}\n",
                .{ name, conversion, combine },
            );
        } else blk: {
            const cleanup = try self.utils.cleanupFunction(to_type);
            defer self.allocator.free(cleanup);
            break :blk try generator.functionDefinition(
                "\nfunction @0(addr_and_function_id, pos) {\nmstore(pos, @1(addr_and_function_id))\n}\n",
                .{ name, cleanup },
            );
        };

        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn abiDecodingFunction(
        self: *ABIFunctions,
        type_ref: *const Types.Type,
        from_memory: bool,
        for_use_on_stack: bool,
    ) ABIError![]u8 {
        const decoding = try self.decodingType(type_ref);
        if (decoding.category() == .Array) {
            const array = decoding.asArray().?;
            if (array.reference.location == .CallData) {
                if (from_memory) return error.InvalidType;
                return self.abiDecodingFunctionCalldataArray(decoding);
            }
            return self.abiDecodingFunctionArray(decoding, from_memory);
        }
        if (decoding.category() == .Struct) {
            const structure = decoding.payload.Struct;
            if (structure.reference.location == .CallData) {
                if (from_memory) return error.InvalidType;
                return self.abiDecodingFunctionCalldataStruct(decoding);
            }
            return self.abiDecodingFunctionStruct(decoding, from_memory);
        }
        if (decoding.category() == .Function)
            return self.abiDecodingFunctionFunctionType(
                decoding,
                from_memory,
                for_use_on_stack,
            );
        if (!TypeBehavior.isValueType(decoding) or
            try TypeBehavior.sizeOnStack(decoding) != 1 or
            TypeBehavior.isDynamicallyEncoded(decoding) or
            try TypeBehavior.calldataEncodedSize(decoding, true) != 32)
            return error.UnsupportedType;
        return self.abiDecodingFunctionValueType(type_ref, from_memory);
    }

    pub fn abiDecodingFunctionValueType(
        self: *ABIFunctions,
        type_ref: *const Types.Type,
        from_memory: bool,
    ) ABIError![]u8 {
        const decoding = try self.decodingType(type_ref);
        if (try TypeBehavior.sizeOnStack(decoding) != 1 or
            !TypeBehavior.isValueType(decoding) or
            TypeBehavior.isDynamicallyEncoded(decoding) or
            try TypeBehavior.calldataEncodedSize(decoding, true) != 32)
            return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "abi_decode_{s}{s}",
            .{ identifier, if (from_memory) "_fromMemory" else "" },
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const validator = try self.utils.validatorFunction(type_ref, true);
        defer self.allocator.free(validator);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0(offset, end) -> value {\nvalue := @1(offset)\n@2(value)\n}\n",
            .{ name, if (from_memory) "mload" else "calldataload", validator },
        );

        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn abiDecodingFunctionArray(
        self: *ABIFunctions,
        type_ref: *const Types.Type,
        from_memory: bool,
    ) ABIError![]u8 {
        const array = type_ref.asArray() orelse return error.InvalidType;
        if (array.reference.location != .Memory) return error.InvalidType;
        const name = try self.decodingFunctionNameAlloc(type_ref, from_memory, false);
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const revert = try self.utils.revertReasonIfDebugFunction(
            "ABI decoding: invalid calldata array offset",
        );
        defer self.allocator.free(revert);
        const available = try self.abiDecodingFunctionArrayAvailableLength(
            type_ref,
            from_memory,
        );
        defer self.allocator.free(available);
        const generator = try self.function_collector.generator(self.evm_version);
        const retrieve_length = if (array.isDynamicallySized())
            try generator.expression(
                "@0(offset)",
                .{if (from_memory) "mload" else "calldataload"},
            )
        else blk: {
            const length = try compactHex(self.allocator, array.length.?);
            defer self.allocator.free(length);
            break :blk try generator.numberToken(length);
        };

        const code = try generator.functionDefinition(
            "\nfunction @0(offset, end) -> array {\nif iszero(slt(add(offset, 0x1f), end)) { @1() }\nlet length := @2\narray := @3(@4, length, end)\n}\n",
            .{
                name,
                revert,
                retrieve_length,
                available,
                if (array.isDynamicallySized()) try generator.expression("add(offset, 0x20)", .{}) else try generator.identifier("offset"),
            },
        );

        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn abiDecodingFunctionArrayAvailableLength(
        self: *ABIFunctions,
        type_ref: *const Types.Type,
        from_memory: bool,
    ) ABIError![]u8 {
        const array = type_ref.asArray() orelse return error.InvalidType;
        if (array.reference.location != .Memory) return error.InvalidType;
        if (array.isByteArrayOrString())
            return self.abiDecodingFunctionByteArrayAvailableLength(
                type_ref,
                from_memory,
            );
        const stride = try TypeBehavior.calldataStride(array.*);
        if (stride == 0) return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "abi_decode_available_length_{s}{s}",
            .{ identifier, if (from_memory) "_fromMemory" else "" },
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const allocate = try self.utils.allocationFunction();
        defer self.allocator.free(allocate);
        const allocation_size = try self.utils.arrayAllocationSizeFunction(type_ref);
        defer self.allocator.free(allocation_size);
        const invalid_stride = try self.utils.revertReasonIfDebugFunction(
            "ABI decoding: invalid calldata array stride",
        );
        defer self.allocator.free(invalid_stride);
        const invalid_offset = try self.utils.revertReasonIfDebugFunction(
            "ABI decoding: invalid calldata array offset",
        );
        defer self.allocator.free(invalid_offset);
        const decoder = try self.abiDecodingFunction(
            array.base_type,
            from_memory,
            false,
        );
        defer self.allocator.free(decoder);
        const stride_text = try compactHex(self.allocator, stride);
        defer self.allocator.free(stride_text);
        const dynamic_base = TypeBehavior.isDynamicallyEncoded(array.base_type);
        const generator = try self.function_collector.generator(self.evm_version);
        const element_position = if (dynamic_base)
            try generator.statements(
                "let innerOffset := @0(src)\nif gt(innerOffset, 0xffffffffffffffff) { @1() }\nlet elementPos := add(offset, innerOffset)",
                .{ if (from_memory) "mload" else "calldataload", invalid_offset },
            )
        else
            try generator.statements("let elementPos := src", .{});

        const code = try generator.functionDefinition(
            "\nfunction @0(offset, length, end) -> array {\narray := @1(@2(length))\nlet dst := array\n@3\nlet srcEnd := add(offset, mul(length, @4))\nif gt(srcEnd, end) {\n@5()\n}\nfor { let src := offset } lt(src, srcEnd) { src := add(src, @6) }\n{\n@7\nmstore(dst, @8(elementPos, end))\ndst := add(dst, 0x20)\n}\n}\n",
            .{
                name,
                allocate,
                allocation_size,
                if (array.isDynamicallySized())
                    try generator.statements("mstore(array, length) dst := add(array, 0x20)", .{})
                else
                    Yul.Block{},
                try generator.numberToken(stride_text),
                invalid_stride,
                try generator.numberToken(stride_text),
                element_position,
                decoder,
            },
        );

        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    fn abiDecodingFunctionCalldataArray(
        self: *ABIFunctions,
        type_ref: *const Types.Type,
    ) ABIError![]u8 {
        const array = type_ref.asArray() orelse return error.InvalidType;
        if (array.reference.location != .CallData) return error.InvalidType;
        const stride = try TypeBehavior.calldataStride(array.*);
        if (stride == 0) return error.InvalidType;
        const name = try self.decodingFunctionNameAlloc(type_ref, false, false);
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const stride_text = try compactHex(self.allocator, stride);
        defer self.allocator.free(stride_text);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = if (array.isDynamicallySized()) blk: {
            const invalid_offset = try self.utils.revertReasonIfDebugFunction(
                "ABI decoding: invalid calldata array offset",
            );
            defer self.allocator.free(invalid_offset);
            const invalid_length = try self.utils.revertReasonIfDebugFunction(
                "ABI decoding: invalid calldata array length",
            );
            defer self.allocator.free(invalid_length);
            const invalid_position = try self.utils.revertReasonIfDebugFunction(
                "ABI decoding: invalid calldata array stride",
            );
            defer self.allocator.free(invalid_position);
            break :blk try generator.functionDefinition(
                "\nfunction @0(offset, end) -> arrayPos, length {\nif iszero(slt(add(offset, 0x1f), end)) { @1() }\nlength := calldataload(offset)\nif gt(length, 0xffffffffffffffff) { @2() }\narrayPos := add(offset, 0x20)\nif gt(add(arrayPos, mul(length, @3)), end) { @4() }\n}\n",
                .{ name, invalid_offset, invalid_length, try generator.numberToken(stride_text), invalid_position },
            );
        } else blk: {
            const length = try compactHex(self.allocator, array.length.?);
            defer self.allocator.free(length);
            const invalid_position = try self.utils.revertReasonIfDebugFunction(
                "ABI decoding: invalid calldata array stride",
            );
            defer self.allocator.free(invalid_position);
            break :blk try generator.functionDefinition(
                "\nfunction @0(offset, end) -> arrayPos {\narrayPos := offset\nif gt(add(arrayPos, mul(@1, @2)), end) { @3() }\n}\n",
                .{ name, try generator.numberToken(length), try generator.numberToken(stride_text), invalid_position },
            );
        };

        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    fn abiDecodingFunctionByteArrayAvailableLength(
        self: *ABIFunctions,
        type_ref: *const Types.Type,
        from_memory: bool,
    ) ABIError![]u8 {
        const array = type_ref.asArray() orelse return error.InvalidType;
        if (array.reference.location != .Memory or !array.isByteArrayOrString())
            return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "abi_decode_available_length_{s}{s}",
            .{ identifier, if (from_memory) "_fromMemory" else "" },
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const invalid_length = try self.utils.revertReasonIfDebugFunction(
            "ABI decoding: invalid byte array length",
        );
        defer self.allocator.free(invalid_length);
        const allocate = try self.utils.allocationFunction();
        defer self.allocator.free(allocate);
        const allocation_size = try self.utils.arrayAllocationSizeFunction(type_ref);
        defer self.allocator.free(allocation_size);
        const copy = try self.utils.copyToMemoryFunction(!from_memory, true);
        defer self.allocator.free(copy);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0(src, length, end) -> array {\narray := @1(@2(length))\nmstore(array, length)\nlet dst := add(array, 0x20)\nif gt(add(src, length), end) { @3() }\n@4(src, dst, length)\n}\n",
            .{ name, allocate, allocation_size, invalid_length, copy },
        );

        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    fn abiDecodingFunctionCalldataStruct(
        self: *ABIFunctions,
        type_ref: *const Types.Type,
    ) ABIError![]u8 {
        const structure = switch (type_ref.payload) {
            .Struct => |value| value,
            else => return error.InvalidType,
        };
        if (structure.reference.location != .CallData) return error.InvalidType;
        const name = try self.decodingFunctionNameAlloc(type_ref, false, false);
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const revert = try self.utils.revertReasonIfDebugFunction(
            "ABI decoding: struct calldata too short",
        );
        defer self.allocator.free(revert);
        const minimum = if (TypeBehavior.isDynamicallyEncoded(type_ref))
            try TypeBehavior.calldataEncodedTailSize(type_ref)
        else
            try TypeBehavior.calldataEncodedSize(type_ref, true);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = try generator.functionDefinition(
            "\nfunction @0(offset, end) -> value {\nif slt(sub(end, offset), @1) { @2() }\nvalue := offset\n}\n",
            .{ name, minimum, revert },
        );

        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn abiDecodingFunctionStruct(
        self: *ABIFunctions,
        type_ref: *const Types.Type,
        from_memory: bool,
    ) ABIError![]u8 {
        const structure = switch (type_ref.payload) {
            .Struct => |value| value,
            else => return error.InvalidType,
        };
        if (structure.reference.location == .CallData or
            structure.declaration.nodeKind() != .struct_definition)
            return error.InvalidType;
        const name = try self.decodingFunctionNameAlloc(type_ref, from_memory, false);
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const revert = try self.utils.revertReasonIfDebugFunction(
            "ABI decoding: struct data too short",
        );
        defer self.allocator.free(revert);
        const allocate = try self.utils.allocationFunction();
        defer self.allocator.free(allocate);
        const memory_size = try TypeBehavior.memoryDataSize(type_ref);
        const memory_size_text = try compactHex(self.allocator, memory_size);
        defer self.allocator.free(memory_size_text);
        const generator = try self.function_collector.generator(self.evm_version);
        var member_code: Generated.Buffer = .{ .generator = generator };
        var head_position: u32 = 0;
        for (structure.declaration.payload.struct_definition.members) |member| {
            if (member.nodeKind() != .variable_declaration) return error.InvalidType;
            const member_name = member.payload.variable_declaration.declaration.name;
            const raw_member = try TypeBehavior.variableDeclarationType(member);
            const member_type = self.type_provider.withLocationIfReference(
                structure.reference.location,
                raw_member,
                false,
            ) catch |err| return mapProviderError(err);
            const decoding = try self.decodingType(member_type);
            const invalid_offset = try self.utils.revertReasonIfDebugFunction(
                "ABI decoding: invalid struct offset",
            );
            defer self.allocator.free(invalid_offset);
            const decoder = try self.abiDecodingFunction(
                member_type,
                from_memory,
                false,
            );
            defer self.allocator.free(decoder);
            const memory_offset = try TypeBehavior.structMemoryOffsetOfMember(
                structure,
                member_name,
            );
            const memory_offset_text = try compactHex(self.allocator, memory_offset);
            defer self.allocator.free(memory_offset_text);
            if (TypeBehavior.isDynamicallyEncoded(decoding))
                try member_code.add(
                    "{ let offset := @0(add(headStart, @1)) if gt(offset, 0xffffffffffffffff) { @2() } mstore(add(value, @3), @4(add(headStart, offset), end)) }",
                    .{
                        if (from_memory) "mload" else "calldataload",
                        head_position,
                        invalid_offset,
                        try generator.numberToken(memory_offset_text),
                        decoder,
                    },
                )
            else
                try member_code.add(
                    "{\nlet offset := @0\nmstore(add(value, @1), @2(add(headStart, offset), end))\n}\n",
                    .{ head_position, try generator.numberToken(memory_offset_text), decoder },
                );
            head_position = std.math.add(
                u32,
                head_position,
                try TypeBehavior.calldataHeadSize(decoding),
            ) catch return error.Overflow;
        }
        const minimum = try compactHex(self.allocator, head_position);
        defer self.allocator.free(minimum);
        const code = try generator.functionDefinition(
            "\nfunction @0(headStart, end) -> value {\nif slt(sub(end, headStart), @1) { @2() }\nvalue := @3(@4)\n@5}\n",
            .{ name, try generator.numberToken(minimum), revert, allocate, try generator.numberToken(memory_size_text), member_code.take() },
        );

        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    fn abiDecodingFunctionFunctionType(
        self: *ABIFunctions,
        type_ref: *const Types.Type,
        from_memory: bool,
        for_use_on_stack: bool,
    ) ABIError![]u8 {
        const function = type_ref.asFunction() orelse return error.InvalidType;
        if (function.kind != .External) return error.InvalidType;
        const name = try self.decodingFunctionNameAlloc(
            type_ref,
            from_memory,
            for_use_on_stack,
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = if (for_use_on_stack) blk: {
            const nested = try self.abiDecodingFunctionFunctionType(
                type_ref,
                from_memory,
                false,
            );
            defer self.allocator.free(nested);
            const split = try self.utils.splitExternalFunctionIdFunction();
            defer self.allocator.free(split);
            break :blk try generator.functionDefinition(
                "\nfunction @0(offset, end) -> addr, function_selector {\naddr, function_selector := @1(@2(offset, end))\n}\n",
                .{ name, split, nested },
            );
        } else blk: {
            const validator = try self.utils.validatorFunction(type_ref, true);
            defer self.allocator.free(validator);
            break :blk try generator.functionDefinition(
                "\nfunction @0(offset, end) -> fun {\nfun := @1(offset)\n@2(fun)\n}\n",
                .{ name, if (from_memory) "mload" else "calldataload", validator },
            );
        };

        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    pub fn calldataAccessFunction(
        self: *ABIFunctions,
        type_ref: *const Types.Type,
    ) ABIError![]u8 {
        if (!TypeBehavior.isValueType(type_ref) and
            !TypeBehavior.dataStoredIn(type_ref, .CallData))
            return error.InvalidType;
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        const name = try std.fmt.allocPrint(
            self.allocator,
            "calldata_access_{s}",
            .{identifier},
        );
        defer self.allocator.free(name);
        if (!(try self.function_collector.beginFunction(name)))
            return self.function_collector.copyFunctionName(name);
        errdefer self.function_collector.abortFunction(name);
        const generator = try self.function_collector.generator(self.evm_version);
        const code = if (TypeBehavior.isDynamicallyEncoded(type_ref)) blk: {
            const tail_size = try TypeBehavior.calldataEncodedTailSize(type_ref);
            if (tail_size <= 1) return error.InvalidType;
            const tail_size_text = try compactHex(self.allocator, tail_size);
            defer self.allocator.free(tail_size_text);
            if (TypeBehavior.isDynamicallySized(type_ref)) {
                const array = type_ref.asArray() orelse return error.InvalidType;
                const stride = try compactHex(
                    self.allocator,
                    try TypeBehavior.calldataStride(array.*),
                );
                defer self.allocator.free(stride);
                const invalid_length = try self.utils.revertReasonIfDebugFunction(
                    "Invalid calldata access length",
                );
                defer self.allocator.free(invalid_length);
                const invalid_stride = try self.utils.revertReasonIfDebugFunction(
                    "Invalid calldata access stride",
                );
                defer self.allocator.free(invalid_stride);
                const invalid_offset = try self.utils.revertReasonIfDebugFunction(
                    "Invalid calldata access offset",
                );
                defer self.allocator.free(invalid_offset);
                break :blk try generator.functionDefinition(
                    "\nfunction @0(base_ref, ptr) -> value, length {\nlet rel_offset_of_tail := calldataload(ptr)\nif iszero(slt(rel_offset_of_tail, sub(sub(calldatasize(), base_ref), sub(@1, 1)))) { @2() }\nvalue := add(rel_offset_of_tail, base_ref)\nlength := calldataload(value)\nvalue := add(value, 0x20)\nif gt(length, 0xffffffffffffffff) { @3() }\nif sgt(value, sub(calldatasize(), mul(length, @4))) { @5() }\n}\n",
                    .{ name, try generator.numberToken(tail_size_text), invalid_offset, invalid_length, try generator.numberToken(stride), invalid_stride },
                );
            }
            const invalid_offset = try self.utils.revertReasonIfDebugFunction(
                "Invalid calldata access offset",
            );
            defer self.allocator.free(invalid_offset);
            break :blk try generator.functionDefinition(
                "\nfunction @0(base_ref, ptr) -> value {\nlet rel_offset_of_tail := calldataload(ptr)\nif iszero(slt(rel_offset_of_tail, sub(sub(calldatasize(), base_ref), sub(@1, 1)))) { @2() }\nvalue := add(rel_offset_of_tail, base_ref)\n}\n",
                .{ name, try generator.numberToken(tail_size_text), invalid_offset },
            );
        } else if (TypeBehavior.isValueType(type_ref)) blk: {
            const decoder = if (type_ref.category() == .Function)
                try self.abiDecodingFunctionFunctionType(type_ref, false, false)
            else
                try self.abiDecodingFunctionValueType(type_ref, false);
            defer self.allocator.free(decoder);
            break :blk try generator.functionDefinition(
                "\nfunction @0(baseRef, ptr) -> value {\nvalue := @1(ptr, add(ptr, 32))\n}\n",
                .{ name, decoder },
            );
        } else switch (type_ref.category()) {
            .Array, .Struct => try generator.functionDefinition(
                "\nfunction @0(baseRef, ptr) -> value {\nvalue := ptr\n}\n",
                .{name},
            ),
            else => return error.InvalidType,
        };

        try self.function_collector.finishGeneratedFunction(name, code);
        return self.function_collector.copyFunctionName(name);
    }

    fn encodingFunctionNameAlloc(
        self: *ABIFunctions,
        given_type: *const Types.Type,
        target_type: *const Types.Type,
        options: EncodingOptions,
    ) ABIError![]u8 {
        const suffix = try options.suffixAlloc(self.allocator);
        defer self.allocator.free(suffix);
        const given_identifier = try TypeBehavior.compatibilityIdentifierAlloc(
            self.allocator,
            self.compatibility_ids,
            given_type,
        );
        defer self.allocator.free(given_identifier);
        const target_identifier = try TypeBehavior.compatibilityIdentifierAlloc(
            self.allocator,
            self.compatibility_ids,
            target_type,
        );
        defer self.allocator.free(target_identifier);
        return std.fmt.allocPrint(
            self.allocator,
            "abi_encode_{s}_to_{s}{s}",
            .{ given_identifier, target_identifier, suffix },
        );
    }

    fn decodingFunctionNameAlloc(
        self: *ABIFunctions,
        type_ref: *const Types.Type,
        from_memory: bool,
        on_stack: bool,
    ) ABIError![]u8 {
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        return std.fmt.allocPrint(
            self.allocator,
            "abi_decode_{s}{s}{s}",
            .{
                identifier,
                if (from_memory) "_fromMemory" else "",
                if (on_stack) "_onStack" else "",
            },
        );
    }

    fn numVariablesForType(
        self: *ABIFunctions,
        type_ref: *const Types.Type,
        options: EncodingOptions,
    ) ABIError!usize {
        _ = self;
        if (type_ref.category() == .Function and
            !options.encode_function_from_stack)
            return 1;
        return TypeBehavior.sizeOnStack(type_ref);
    }

    fn fullEncodingType(
        self: *ABIFunctions,
        type_ref: *const Types.Type,
        in_library_call: bool,
    ) ABIError!*const Types.Type {
        const mobile = switch (type_ref.payload) {
            .StringLiteral => self.type_provider.stringMemory(),
            .ArraySlice => |slice| slice.array_type,
            else => type_ref,
        };
        const interface_type = try self.interfaceType(mobile, in_library_call, 0);
        return self.encodingType(interface_type);
    }

    fn interfaceType(
        self: *ABIFunctions,
        type_ref: *const Types.Type,
        in_library_call: bool,
        depth: usize,
    ) ABIError!*const Types.Type {
        if (depth >= 256) return error.InvalidType;
        return switch (type_ref.payload) {
            .Address,
            .Integer,
            .Bool,
            .FixedPoint,
            .FixedBytes,
            .Enum,
            .InaccessibleDynamic,
            => type_ref,
            .Contract => if (in_library_call)
                type_ref
            else
                self.encodingType(type_ref),
            .UserDefinedValueType => |value| value.underlying_type orelse
                return error.InvalidType,
            .Function => |function| if (function.kind == .External and
                !function.options.gas_set and
                !function.options.value_set and
                !function.options.salt_set and
                !function.options.has_bound_first_argument)
                type_ref
            else
                error.UnsupportedType,
            .Array => |array| blk: {
                if (in_library_call and array.reference.location == .Storage)
                    break :blk type_ref;
                if (array.isByteArrayOrString())
                    break :blk self.type_provider.byteString(
                        .Memory,
                        array.isString(),
                    ) catch |err| return mapProviderError(err);
                const base = try self.interfaceType(
                    array.base_type,
                    in_library_call,
                    depth + 1,
                );
                break :blk self.type_provider.arrayWithLength(
                    .Memory,
                    base,
                    array.length,
                ) catch |err| return mapProviderError(err);
            },
            .Struct => |structure| if (in_library_call and
                structure.reference.location == .Storage)
                type_ref
            else
                self.type_provider.withLocation(type_ref, .Memory, true) catch |err|
                    return mapProviderError(err),
            .Mapping => if (in_library_call) type_ref else error.UnsupportedType,
            else => error.UnsupportedType,
        };
    }

    fn encodingType(
        self: *ABIFunctions,
        type_ref: *const Types.Type,
    ) ABIError!*const Types.Type {
        return switch (type_ref.payload) {
            .Address,
            .Integer,
            .Bool,
            .FixedPoint,
            .FixedBytes,
            .InaccessibleDynamic,
            => type_ref,
            .Contract => (try TypeBehavior.encodingType(self.type_provider, type_ref)) orelse
                error.InvalidType,
            .Enum => &interface_uint8,
            .UserDefinedValueType => |value| value.underlying_type orelse
                return error.InvalidType,
            .Array => |array| if (array.reference.location == .Storage)
                self.type_provider.uint256()
            else
                self.type_provider.withLocation(type_ref, .Memory, true) catch |err|
                    return mapProviderError(err),
            .Struct => |structure| if (structure.reference.location == .Storage)
                self.type_provider.uint256()
            else
                type_ref,
            .Function => |function| if (function.kind == .External and
                !function.options.gas_set and !function.options.value_set)
                type_ref
            else
                error.UnsupportedType,
            .Mapping => self.type_provider.uint256(),
            else => error.UnsupportedType,
        };
    }

    fn decodingType(
        self: *ABIFunctions,
        type_ref: *const Types.Type,
    ) ABIError!*const Types.Type {
        return switch (type_ref.payload) {
            .Array => |array| if (array.reference.location == .Storage)
                self.type_provider.uint256()
            else
                type_ref,
            .Struct => |structure| if (structure.reference.location == .Storage)
                self.type_provider.uint256()
            else
                type_ref,
            .InaccessibleDynamic => self.type_provider.uint256(),
            else => self.encodingType(type_ref),
        };
    }

    fn appendIdentifier(
        self: *ABIFunctions,
        output: *std.ArrayList(u8),
        type_ref: *const Types.Type,
        trailing_underscore: bool,
    ) ABIError!void {
        const identifier = try TypeBehavior.compatibilityIdentifierAlloc(self.allocator, self.compatibility_ids, type_ref);
        defer self.allocator.free(identifier);
        try output.appendSlice(self.allocator, identifier);
        if (trailing_underscore) try output.append(self.allocator, '_');
    }
};

fn compactHex(allocator: std.mem.Allocator, value: anytype) std.mem.Allocator.Error![]u8 {
    return Numeric.toCompactHexWithPrefixAlloc(
        @TypeOf(value),
        allocator,
        value,
    );
}

fn mapProviderError(err: TypeProviderModule.ProviderError) ABIError {
    return switch (err) {
        error.OutOfMemory => error.OutOfMemory,
        error.UnsupportedTransientReference => error.UnsupportedTransientReference,
        else => error.InvalidType,
    };
}

test "Yul AST scalar ABI tuple helpers retain upstream names and checks" {
    var type_provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer type_provider.deinit();
    var collector = CollectorModule.MultiUseYulFunctionCollector.init(std.testing.allocator);
    defer collector.deinit();
    var abi = ABIFunctions.init(
        std.testing.allocator,
        &type_provider,
        CompatibilityIdResolver.legacyNodeIds(),
        EVMVersion.current(),
        .Default,
        &collector,
    );
    const uint_type = Types.Type{ .payload = .{ .Integer = .{
        .bits = 256,
        .modifier = .Unsigned,
    } } };
    const decoder = try abi.tupleDecoder(&.{ &uint_type, &uint_type }, false);
    defer std.testing.allocator.free(decoder);
    try std.testing.expectEqualStrings("abi_decode_tuple_t_uint256t_uint256", decoder);
    const encoder = try abi.tupleEncoder(
        &.{&uint_type},
        &.{&uint_type},
        false,
        false,
    );
    defer std.testing.allocator.free(encoder);
    try std.testing.expectEqualStrings(
        "abi_encode_tuple_t_uint256__to_t_uint256__fromStack",
        encoder,
    );
    try std.testing.expectEqual(collector.requested_functions.count(), collector.generated.items.len);
    const code = try collector.testFunctionsAlloc();
    defer std.testing.allocator.free(code);
    try expectCanonicalHelpers(code, "5f240399f45568a746fea42612c3dd5d99dc48ad609a3685fd6d462098cbbdb9");
    try std.testing.expect(std.mem.find(u8, code, "slt(sub(dataEnd, headStart), 64)") != null);
    try std.testing.expect(std.mem.find(u8, code, "calldataload(offset)") != null);
    try std.testing.expect(std.mem.find(u8, code, "mstore(pos, cleanup_t_uint256(value))") != null);
}

test "Yul AST encoding option suffix order is stable" {
    const suffix = try (EncodingOptions{
        .padded = false,
        .dynamic_inplace = true,
        .encode_function_from_stack = true,
        .encode_as_library_types = true,
    }).suffixAlloc(std.testing.allocator);
    defer std.testing.allocator.free(suffix);
    try std.testing.expectEqualStrings(
        "_nonPadded_inplace_fromStack_library",
        suffix,
    );
}

test "Yul AST composite ABI helpers cover arrays, literals, storage packing, and external functions" {
    var type_provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer type_provider.deinit();
    var collector = CollectorModule.MultiUseYulFunctionCollector.init(std.testing.allocator);
    defer collector.deinit();
    var abi = ABIFunctions.init(
        std.testing.allocator,
        &type_provider,
        CompatibilityIdResolver.legacyNodeIds(),
        EVMVersion.current(),
        .Default,
        &collector,
    );

    const uint8_type = try type_provider.uint(8);
    const uint256_type = type_provider.uint256();
    const calldata_uints = try type_provider.array(.CallData, uint256_type);
    const memory_uints = try type_provider.array(.Memory, uint256_type);
    const nested_memory_uints = try type_provider.array(.Memory, memory_uints);
    const storage_uint8s = try type_provider.array(.Storage, uint8_type);
    const memory_uint8s = try type_provider.array(.Memory, uint8_type);

    const array_encoder = try abi.tupleEncoder(
        &.{ type_provider.bytesCalldata(), calldata_uints },
        &.{ type_provider.bytesMemory(), memory_uints },
        false,
        false,
    );
    defer std.testing.allocator.free(array_encoder);
    const array_decoder = try abi.tupleDecoder(
        &.{ nested_memory_uints, type_provider.bytesMemory() },
        false,
    );
    defer std.testing.allocator.free(array_decoder);
    const calldata_decoder = try abi.tupleDecoder(&.{calldata_uints}, false);
    defer std.testing.allocator.free(calldata_decoder);

    const literal = try type_provider.stringLiteral("zig");
    const packed_encoder = try abi.tupleEncoderPacked(
        &.{ literal, uint8_type },
        &.{ type_provider.bytesMemory(), uint8_type },
        false,
    );
    defer std.testing.allocator.free(packed_encoder);

    const storage_array_encoder = try abi.abiEncodingFunction(
        storage_uint8s,
        memory_uint8s,
        .{ .encode_function_from_stack = true },
    );
    defer std.testing.allocator.free(storage_array_encoder);
    const storage_bytes_encoder = try abi.abiEncodingFunction(
        type_provider.bytesStorage(),
        type_provider.bytesMemory(),
        .{ .encode_function_from_stack = true },
    );
    defer std.testing.allocator.free(storage_bytes_encoder);

    const external_function = try type_provider.function(
        &.{uint256_type},
        &.{uint256_type},
        &.{""},
        &.{""},
        .External,
        .View,
        null,
        .{},
    );
    const function_encoder = try abi.tupleEncoder(
        &.{external_function},
        &.{external_function},
        false,
        false,
    );
    defer std.testing.allocator.free(function_encoder);
    const function_decoder = try abi.tupleDecoder(&.{external_function}, false);
    defer std.testing.allocator.free(function_decoder);

    try std.testing.expectEqual(collector.requested_functions.count(), collector.generated.items.len);
    const code = try collector.testFunctionsAlloc();
    defer std.testing.allocator.free(code);
    try expectCanonicalHelpers(code, "905725869928b98ec2fc3d5acc5cbdb57951ac9b3cd32df203878056cb9cf157");
    try std.testing.expect(std.mem.find(
        u8,
        code,
        "abi_decode_available_length_",
    ) != null);
    try std.testing.expect(std.mem.find(
        u8,
        code,
        "copy_calldata_to_memory_with_cleanup",
    ) != null);
    try std.testing.expect(std.mem.find(
        u8,
        code,
        "extract_from_storage_value_offset_31_t_uint8",
    ) != null);
    try std.testing.expect(std.mem.find(
        u8,
        code,
        "store_literal_in_memory_",
    ) != null);
    try std.testing.expect(std.mem.find(
        u8,
        code,
        "combine_external_function_id",
    ) != null);
    try std.testing.expect(std.mem.find(
        u8,
        code,
        "split_external_function_id",
    ) != null);
}

test "Yul AST struct ABI helpers cover memory, calldata, and storage members" {
    var type_provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer type_provider.deinit();
    var tree = try AST.Tree.init(std.testing.allocator, "", "Struct.sol");
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
    const members = try tree.ownSlice(*AST.Node, &.{ amount, payload });
    const declaration = try tree.createNode(.{}, .{ .struct_definition = .{
        .declaration = .{ .name = "S" },
        .members = members,
    } });

    const storage_struct = try type_provider.structType(declaration, .Storage);
    const memory_struct = try type_provider.structType(declaration, .Memory);
    const calldata_struct = try type_provider.structType(declaration, .CallData);
    var collector = CollectorModule.MultiUseYulFunctionCollector.init(std.testing.allocator);
    defer collector.deinit();
    var abi = ABIFunctions.init(
        std.testing.allocator,
        &type_provider,
        CompatibilityIdResolver.legacyNodeIds(),
        EVMVersion.current(),
        .Default,
        &collector,
    );

    const memory_encoder = try abi.abiEncodingFunction(
        memory_struct,
        memory_struct,
        .{},
    );
    defer std.testing.allocator.free(memory_encoder);
    const calldata_encoder = try abi.abiEncodingFunction(
        calldata_struct,
        memory_struct,
        .{},
    );
    defer std.testing.allocator.free(calldata_encoder);
    const storage_encoder = try abi.abiEncodingFunction(
        storage_struct,
        memory_struct,
        .{},
    );
    defer std.testing.allocator.free(storage_encoder);
    const memory_decoder = try abi.abiDecodingFunctionStruct(memory_struct, false);
    defer std.testing.allocator.free(memory_decoder);
    const memory_input_decoder = try abi.abiDecodingFunctionStruct(memory_struct, true);
    defer std.testing.allocator.free(memory_input_decoder);
    const calldata_decoder = try abi.tupleDecoder(&.{calldata_struct}, false);
    defer std.testing.allocator.free(calldata_decoder);
    const tuple_encoder = try abi.tupleEncoder(
        &.{memory_struct},
        &.{memory_struct},
        false,
        false,
    );
    defer std.testing.allocator.free(tuple_encoder);

    try std.testing.expectEqual(collector.requested_functions.count(), collector.generated.items.len);
    const code = try collector.testFunctionsAlloc();
    defer std.testing.allocator.free(code);
    try expectCanonicalHelpers(code, "ddff1da0e066db1f8021ef6eb110a427b34b780f2cdf9efbb714fa64c06a4921");
    try std.testing.expect(std.mem.find(u8, code, "slotValue := sload") != null);
    try std.testing.expect(std.mem.find(u8, code, "calldata_access_t_bytes_calldata") != null);
    try std.testing.expect(std.mem.find(u8, code, "ABI decoding: invalid struct offset") == null);
    try std.testing.expect(std.mem.find(u8, code, "mstore(add(value,") != null);
}

fn expectCanonicalHelpers(code: []const u8, expected: []const u8) !void {
    const allocator = std.testing.allocator;
    const Errors = @import("../../liblangutil/error_reporter.zig");
    const Parser = @import("../../libyul/asm_parser.zig").Parser;
    const Dialect = @import("../../libyul/backends/evm/evm_dialect.zig").EVMDialect;
    const wrapped = try std.fmt.allocPrint(allocator, "{{{s}}}", .{code});
    defer allocator.free(wrapped);
    var errors = Errors.ErrorReporter.init(allocator);
    defer errors.deinit();
    var dialect = try Dialect.init(allocator, .current(), true);
    defer dialect.deinit();
    var parsed = (try Parser.parseSource(allocator, wrapped, "abi-matrix.yul", &errors, dialect.dialect(), .{})) orelse return error.TestUnexpectedResult;
    defer parsed.deinit();
    try std.testing.expectEqual(@as(usize, 0), errors.diagnostics().len);
    var printer = @import("../../libyul/asm_printer.zig").AsmPrinter.init(allocator, dialect.dialect(), &.{}, .noneValue(), null);
    const canonical = try printer.renderBlock(parsed.root());
    defer allocator.free(canonical);
    var digest: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(canonical, &digest, .{});
    // Normalized legacy ABI helper output at 66608805b, before AST construction.
    try std.testing.expectEqualStrings(expected, &std.fmt.bytesToHex(digest, .lower));
}

test "Yul AST ABI tuples preserve reversed bindings and empty lists" {
    const allocator = std.testing.allocator;
    var types = try TypeProviderModule.TypeProvider.init(allocator);
    defer types.deinit();
    var collector = CollectorModule.MultiUseYulFunctionCollector.init(allocator);
    defer collector.deinit();
    var abi = ABIFunctions.init(allocator, &types, CompatibilityIdResolver.legacyNodeIds(), .current(), .Default, &collector);
    for ([_]bool{ false, true }) |is_packed| {
        const name = if (is_packed)
            try abi.tupleEncoderPacked(&.{ types.uint256(), types.uint256() }, &.{ types.uint256(), types.uint256() }, true)
        else
            try abi.tupleEncoder(&.{ types.uint256(), types.uint256() }, &.{ types.uint256(), types.uint256() }, false, true);
        defer allocator.free(name);
        const function = &collector.generated.items[collector.generated.items.len - 1];
        try std.testing.expectEqualStrings(name, try function.name.str());
        try std.testing.expectEqual(@as(usize, 3), function.parameters.items.len);
        try std.testing.expectEqualStrings(if (is_packed) "pos" else "headStart", try function.parameters.items[0].name.str());
        try std.testing.expectEqualStrings("value1", try function.parameters.items[1].name.str());
        try std.testing.expectEqualStrings("value0", try function.parameters.items[2].name.str());
        // Reversing the entry bindings must not reverse logical tuple order.
        const first_call = function.body.statements.items[if (is_packed) 0 else 1].expression_statement.expression.function_call;
        try std.testing.expectEqualStrings("value0", try first_call.arguments.items[0].identifier.name.str());
        const empty = if (is_packed) try abi.tupleEncoderPacked(&.{}, &.{}, true) else try abi.tupleEncoder(&.{}, &.{}, false, true);
        defer allocator.free(empty);
        const empty_function = &collector.generated.items[collector.generated.items.len - 1];
        try std.testing.expectEqual(@as(usize, 1), empty_function.parameters.items.len);
    }
    const decoder = try abi.tupleDecoder(&.{}, false);
    defer allocator.free(decoder);
    const empty_decoder = &collector.generated.items[collector.generated.items.len - 1];
    try std.testing.expectEqual(@as(usize, 0), empty_decoder.return_variables.items.len);
}
