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
const CommonData = @import("../../libsolutil/common_data.zig");

const interface_address = Types.Type{ .payload = .{ .Address = .{
    .state_mutability = .NonPayable,
} } };
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

        const parameters = try variableListAlloc(
            self.allocator,
            "value",
            stack_size,
            reversed,
        );
        defer self.allocator.free(parameters);
        var code: std.ArrayList(u8) = .empty;
        defer code.deinit(self.allocator);
        try code.print(
            self.allocator,
            "\nfunction {s}(headStart {s}{s}) -> tail {{\ntail := add(headStart, {d})\n",
            .{
                name.items,
                if (parameters.len == 0) "" else ", ",
                parameters,
                head_size,
            },
        );
        var head_position: usize = 0;
        var stack_position: usize = 0;
        for (given_types, encoded_targets) |given, target| {
            const stack_words = try TypeBehavior.sizeOnStack(given);
            const values = try variableRangeAlloc(
                self.allocator,
                "value",
                stack_position,
                stack_position + stack_words,
            );
            defer self.allocator.free(values);
            const encoder = try self.abiEncodingFunction(given, target, options);
            defer self.allocator.free(encoder);
            if (TypeBehavior.isDynamicallyEncoded(target))
                try code.print(
                    self.allocator,
                    "\nmstore(add(headStart, {d}), sub(tail, headStart))\ntail := {s}({s}{s} tail)\n",
                    .{
                        head_position,
                        encoder,
                        values,
                        if (values.len == 0) "" else ", ",
                    },
                )
            else
                try code.print(
                    self.allocator,
                    "\n{s}({s}{s} add(headStart, {d}))\n",
                    .{
                        encoder,
                        values,
                        if (values.len == 0) "" else ", ",
                        head_position,
                    },
                );
            head_position += try TypeBehavior.calldataHeadSize(target);
            stack_position += stack_words;
        }
        if (head_position != head_size) return error.InvalidTypeList;
        try code.appendSlice(self.allocator, "\n}\n");
        try self.function_collector.finishFunction(name.items, code.items);
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
        const parameters = try variableListAlloc(
            self.allocator,
            "value",
            stack_size,
            reversed,
        );
        defer self.allocator.free(parameters);
        var code: std.ArrayList(u8) = .empty;
        defer code.deinit(self.allocator);
        try code.print(
            self.allocator,
            "\nfunction {s}(pos{s}{s}) -> end {{\n",
            .{
                name.items,
                if (parameters.len == 0) "" else ", ",
                parameters,
            },
        );
        var stack_position: usize = 0;
        for (given_types, encoded_targets) |given, target| {
            const stack_words = try TypeBehavior.sizeOnStack(given);
            const values = try variableRangeAlloc(
                self.allocator,
                "value",
                stack_position,
                stack_position + stack_words,
            );
            defer self.allocator.free(values);
            const encoder = try self.abiEncodingFunction(given, target, options);
            defer self.allocator.free(encoder);
            if (TypeBehavior.isDynamicallyEncoded(target))
                try code.print(
                    self.allocator,
                    "\npos := {s}({s}{s} pos)\n",
                    .{ encoder, values, if (values.len == 0) "" else ", " },
                )
            else {
                const encoded_size = try TypeBehavior.calldataEncodedSize(target, false);
                try code.print(
                    self.allocator,
                    "\n{s}({s}{s} pos)\npos := add(pos, {d})\n",
                    .{
                        encoder,
                        values,
                        if (values.len == 0) "" else ", ",
                        encoded_size,
                    },
                );
            }
            stack_position += stack_words;
        }
        try code.appendSlice(self.allocator, "\nend := pos\n}\n");
        try self.function_collector.finishFunction(name.items, code.items);
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
        const returns = try variableListAlloc(
            self.allocator,
            "value",
            return_count,
            false,
        );
        defer self.allocator.free(returns);
        const short_revert = try self.utils.revertReasonIfDebugFunction(
            "ABI decoding: tuple data too short",
        );
        defer self.allocator.free(short_revert);
        var code: std.ArrayList(u8) = .empty;
        defer code.deinit(self.allocator);
        try code.print(
            self.allocator,
            "\nfunction {s}(headStart, dataEnd) {s} {s} {{\nif slt(sub(dataEnd, headStart), {d}) {{ {s}() }}\n",
            .{
                name.items,
                if (returns.len == 0) "" else "->",
                returns,
                minimum_size,
                short_revert,
            },
        );
        var head_position: usize = 0;
        var stack_position: usize = 0;
        for (types, decoding_types) |type_ref, decoding| {
            const invalid_offset_revert = try self.utils.revertReasonIfDebugFunction(
                "ABI decoding: invalid tuple offset",
            );
            defer self.allocator.free(invalid_offset_revert);
            const stack_words = try TypeBehavior.sizeOnStack(type_ref);
            const values = try variableRangeAlloc(
                self.allocator,
                "value",
                stack_position,
                stack_position + stack_words,
            );
            defer self.allocator.free(values);
            const decoder = try self.abiDecodingFunction(type_ref, from_memory, true);
            defer self.allocator.free(decoder);
            if (TypeBehavior.isDynamicallyEncoded(decoding))
                try code.print(
                    self.allocator,
                    "\n{{\n\nlet offset := {s}(add(headStart, {d}))\nif gt(offset, 0xffffffffffffffff) {{ {s}() }}\n\n{s} := {s}(add(headStart, offset), dataEnd)\n}}\n",
                    .{
                        if (from_memory) "mload" else "calldataload",
                        head_position,
                        invalid_offset_revert,
                        values,
                        decoder,
                    },
                )
            else
                try code.print(
                    self.allocator,
                    "\n{{\n\nlet offset := {d}\n\n{s} := {s}(add(headStart, offset), dataEnd)\n}}\n",
                    .{ head_position, values, decoder },
                );
            head_position += try TypeBehavior.calldataHeadSize(decoding);
            stack_position += stack_words;
        }
        try code.appendSlice(self.allocator, "\n}\n");
        try self.function_collector.finishFunction(name.items, code.items);
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

        var cleanup_expression = if (TypeBehavior.dataStoredIn(given_type, .Storage)) blk: {
            if (!options.encode_as_library_types or !options.padded or
                options.dynamic_inplace or
                !TypeBehavior.equals(target_type, self.type_provider.uint256()))
                return error.InvalidType;
            break :blk try self.allocator.dupe(u8, "value");
        } else if (TypeBehavior.equals(given_type, target_type)) blk: {
            const cleanup = try self.utils.cleanupFunction(given_type);
            defer self.allocator.free(cleanup);
            break :blk try std.fmt.allocPrint(
                self.allocator,
                "{s}(value)",
                .{cleanup},
            );
        } else blk: {
            const conversion = try self.utils.conversionFunction(given_type, target_type);
            defer self.allocator.free(conversion);
            break :blk try std.fmt.allocPrint(
                self.allocator,
                "{s}(value)",
                .{conversion},
            );
        };
        defer self.allocator.free(cleanup_expression);
        if (!options.padded) {
            const align_function = try self.utils.leftAlignFunction(target_type);
            defer self.allocator.free(align_function);
            const unaligned = cleanup_expression;
            cleanup_expression = try std.fmt.allocPrint(
                self.allocator,
                "{s}({s})",
                .{ align_function, unaligned },
            );
            self.allocator.free(unaligned);
        }
        const code = try std.fmt.allocPrint(
            self.allocator,
            "\nfunction {s}(value, pos) {{\nmstore(pos, {s})\n}}\n",
            .{ name, cleanup_expression },
        );
        defer self.allocator.free(code);
        try self.function_collector.finishFunction(name, code);
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
        const values = try variableListAlloc(
            self.allocator,
            "value",
            try self.numVariablesForType(given_type, options),
            false,
        );
        defer self.allocator.free(values);
        const code = if (TypeBehavior.isDynamicallyEncoded(target_encoding))
            try std.fmt.allocPrint(
                self.allocator,
                "\nfunction {s}({s}{s}pos) -> updatedPos {{\nupdatedPos := {s}({s}{s}pos)\n}}\n",
                .{
                    name,
                    values,
                    if (values.len == 0) "" else ", ",
                    encoder,
                    values,
                    if (values.len == 0) "" else ", ",
                },
            )
        else blk: {
            const size = try TypeBehavior.calldataEncodedSize(
                target_encoding,
                options.padded,
            );
            if (size == 0) return error.InvalidType;
            const size_text = try compactHex(self.allocator, size);
            defer self.allocator.free(size_text);
            break :blk try std.fmt.allocPrint(
                self.allocator,
                "\nfunction {s}({s}{s}pos) -> updatedPos {{\n{s}({s}{s}pos)\nupdatedPos := add(pos, {s})\n}}\n",
                .{
                    name,
                    values,
                    if (values.len == 0) "" else ", ",
                    encoder,
                    values,
                    if (values.len == 0) "" else ", ",
                    size_text,
                },
            );
        };
        defer self.allocator.free(code);
        try self.function_collector.finishFunction(name, code);
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
        const body = if (array.isDynamicallySized() and !options.dynamic_inplace)
            "mstore(pos, length)\nupdated_pos := add(pos, 0x20)"
        else
            "updated_pos := pos";
        const code = try std.fmt.allocPrint(
            self.allocator,
            "\nfunction {s}(pos, length) -> updated_pos {{\n{s}\n}}\n",
            .{ name, body },
        );
        defer self.allocator.free(code);
        try self.function_collector.finishFunction(name, code);
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
        const readable_from = try TypeBehavior.toStringAlloc(
            self.allocator,
            from_type,
            true,
        );
        defer self.allocator.free(readable_from);
        const readable_to = try TypeBehavior.toStringAlloc(
            self.allocator,
            to_type,
            true,
        );
        defer self.allocator.free(readable_to);
        const code = if (from.isDynamicallySized()) blk: {
            const store_length = try self.arrayStoreLengthForEncodingFunction(
                to_type,
                options,
            );
            defer self.allocator.free(store_length);
            var scale: std.ArrayList(u8) = .empty;
            defer scale.deinit(self.allocator);
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
                try scale.print(
                    self.allocator,
                    "if gt(length, {s}) {{ {s}() }}\nlength := mul(length, {s})",
                    .{ maximum_text, revert, stride_text },
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
                break :pad try std.fmt.allocPrint(
                    self.allocator,
                    "{s}(length)",
                    .{round},
                );
            } else try self.allocator.dupe(u8, "length");
            defer self.allocator.free(length_padded);
            break :blk try std.fmt.allocPrint(
                self.allocator,
                "\n// {s} -> {s}\nfunction {s}(start, length, pos) -> end {{\npos := {s}(pos, length)\n{s}\n{s}(start, pos, length)\nend := add(pos, {s})\n}}\n",
                .{
                    readable_from,
                    readable_to,
                    name,
                    store_length,
                    scale.items,
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
            break :blk try std.fmt.allocPrint(
                self.allocator,
                "\n// {s} -> {s}\nfunction {s}(start, pos) {{\n{s}(start, pos, {s})\n}}\n",
                .{ readable_from, readable_to, name, copy, byte_length_text },
            );
        };
        defer self.allocator.free(code);
        try self.function_collector.finishFunction(name, code);
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
        const padded = if (options.padded) blk: {
            const round = try self.utils.roundUpFunction();
            defer self.allocator.free(round);
            break :blk try std.fmt.allocPrint(self.allocator, "{s}(length)", .{round});
        } else try self.allocator.dupe(u8, "length");
        defer self.allocator.free(padded);
        const code = try std.fmt.allocPrint(
            self.allocator,
            "\nfunction {s}(value, pos) -> end {{\nlet length := {s}(value)\npos := {s}(pos, length)\n{s}(add(value, 0x20), pos, length)\nend := add(pos, {s})\n}}\n",
            .{ name, length_function, store_length, copy, padded },
        );
        defer self.allocator.free(code);
        try self.function_collector.finishFunction(name, code);
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
        const element_count = try self.numVariablesForType(from.base_type, sub_options);
        const element_values = try variableListAlloc(
            self.allocator,
            "elementValue",
            element_count,
            false,
        );
        defer self.allocator.free(element_values);
        const length_as_argument = from.reference.location == .CallData and
            from.isDynamicallySized();
        const length_declaration = if (length_as_argument)
            try self.allocator.alloc(u8, 0)
        else blk: {
            const length_function = try self.utils.arrayLengthFunction(from_type);
            defer self.allocator.free(length_function);
            break :blk try std.fmt.allocPrint(
                self.allocator,
                "let length := {s}(value)",
                .{length_function},
            );
        };
        defer self.allocator.free(length_declaration);
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
            .Memory => try self.allocator.dupe(u8, "mload(srcPtr)"),
            .Storage => if (TypeBehavior.isValueType(from.base_type)) blk: {
                const read = try self.utils.readFromStorageFunction(from.base_type, 0);
                defer self.allocator.free(read);
                break :blk try std.fmt.allocPrint(
                    self.allocator,
                    "{s}(srcPtr)",
                    .{read},
                );
            } else try self.allocator.dupe(u8, "srcPtr"),
            .CallData => blk: {
                const calldata_access = try self.calldataAccessFunction(from.base_type);
                defer self.allocator.free(calldata_access);
                break :blk try std.fmt.allocPrint(
                    self.allocator,
                    "{s}(baseRef, srcPtr)",
                    .{calldata_access},
                );
            },
            .Transient => return error.UnsupportedType,
        };
        defer self.allocator.free(access);
        const next = try self.utils.nextArrayElementFunction(from_type);
        defer self.allocator.free(next);
        const readable_from = try TypeBehavior.toStringAlloc(self.allocator, from_type, true);
        defer self.allocator.free(readable_from);
        const readable_to = try TypeBehavior.toStringAlloc(self.allocator, to_type, true);
        defer self.allocator.free(readable_to);

        var loop_body: std.ArrayList(u8) = .empty;
        defer loop_body.deinit(self.allocator);
        if (uses_tail)
            try loop_body.print(
                self.allocator,
                "mstore(pos, sub(tail, headStart))\nlet {s} := {s}\ntail := {s}({s}, tail)\nsrcPtr := {s}(srcPtr)\npos := add(pos, 0x20)",
                .{ element_values, access, encode, element_values, next },
            )
        else
            try loop_body.print(
                self.allocator,
                "let {s} := {s}\npos := {s}({s}, pos)\nsrcPtr := {s}(srcPtr)",
                .{ element_values, access, encode, element_values, next },
            );
        const tail_setup = if (uses_tail)
            "let headStart := pos\nlet tail := add(pos, mul(length, 0x20))\n"
        else
            "";
        const tail_finish = if (uses_tail) "pos := tail\n" else "";
        const code = try std.fmt.allocPrint(
            self.allocator,
            "\n// {s} -> {s}\nfunction {s}(value{s} pos){s} {{\n{s}\npos := {s}(pos, length)\n{s}let baseRef := {s}(value)\nlet srcPtr := baseRef\nfor {{ let i := 0 }} lt(i, length) {{ i := add(i, 1) }}\n{{\n{s}\n}}\n{s}{s}\n}}\n",
            .{
                readable_from,
                readable_to,
                name,
                if (length_as_argument) ", length," else ",",
                if (dynamic) " -> end" else "",
                length_declaration,
                store_length,
                tail_setup,
                data_area,
                loop_body.items,
                tail_finish,
                if (dynamic) "end := pos" else "",
            },
        );
        defer self.allocator.free(code);
        try self.function_collector.finishFunction(name, code);
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
        const readable_from = try TypeBehavior.toStringAlloc(self.allocator, from_type, true);
        defer self.allocator.free(readable_from);
        const readable_to = try TypeBehavior.toStringAlloc(self.allocator, to_type, true);
        defer self.allocator.free(readable_to);

        const code = if (from.isByteArrayOrString()) blk: {
            if (!to.isByteArrayOrString()) return error.InvalidType;
            const length_function = try self.utils.extractByteArrayLengthFunction();
            defer self.allocator.free(length_function);
            const store_length = try self.arrayStoreLengthForEncodingFunction(to_type, options);
            defer self.allocator.free(store_length);
            const data_area = try self.utils.arrayDataAreaFunction(from_type);
            defer self.allocator.free(data_area);
            break :blk try std.fmt.allocPrint(
                self.allocator,
                "\n// {s} -> {s}\nfunction {s}(value, pos) -> ret {{\nlet slotValue := sload(value)\nlet length := {s}(slotValue)\npos := {s}(pos, length)\nswitch and(slotValue, 1)\ncase 0 {{\n// short byte array\nmstore(pos, and(slotValue, not(0xff)))\nret := add(pos, mul({s}, iszero(iszero(length))))\n}}\ncase 1 {{\n// long byte array\nlet dataPos := {s}(value)\nlet i := 0\nfor {{ }} lt(i, length) {{ i := add(i, 0x20) }} {{\nmstore(add(pos, i), sload(dataPos))\ndataPos := add(dataPos, 1)\n}}\nret := add(pos, {s})\n}}\n}}\n",
                .{
                    readable_from,
                    readable_to,
                    name,
                    length_function,
                    store_length,
                    if (options.padded) "0x20" else "length",
                    data_area,
                    if (options.padded) "i" else "length",
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
            var loop_items: std.ArrayList(u8) = .empty;
            defer loop_items.deinit(self.allocator);
            var spill_items: std.ArrayList(u8) = .empty;
            defer spill_items.deinit(self.allocator);
            for (0..items_per_slot) |index| {
                const extract = try self.utils.extractFromStorageValueFunction(
                    from.base_type,
                    @intCast(index * storage_bytes),
                );
                defer self.allocator.free(extract);
                try loop_items.print(
                    self.allocator,
                    "{s}({s}(data), pos)\npos := add(pos, {s})\n",
                    .{ encode, extract, stride },
                );
                const condition = if (from.isDynamicallySized())
                    "lt(itemCounter, length)"
                else if (index < spill)
                    "1"
                else
                    "0";
                try spill_items.print(
                    self.allocator,
                    "if {s} {{\n{s}({s}(data), pos)\npos := add(pos, {s})\nitemCounter := add(itemCounter, 1)\n}}\n",
                    .{ condition, encode, extract, stride },
                );
            }
            const use_loop = from.isDynamicallySized() or
                from.length.? >= items_per_slot;
            const use_spill = from.isDynamicallySized() or spill != 0;
            break :blk try std.fmt.allocPrint(
                self.allocator,
                "\n// {s} -> {s}\nfunction {s}(value, pos){s} {{\nlet length := {s}(value)\npos := {s}(pos, length)\nlet originalPos := pos\nlet srcPtr := {s}(value)\nlet itemCounter := 0\nif {d} {{\n// Run the loop over all full slots\nfor {{ }} lt(add(itemCounter, sub({d}, 1)), length)\n{{ itemCounter := add(itemCounter, {d}) }}\n{{\nlet data := sload(srcPtr)\n{s}srcPtr := add(srcPtr, 1)\n}}\n}}\n// Handle the last (not necessarily full) slot specially\nif {d} {{\nlet data := sload(srcPtr)\n{s}}}\n{s}\n}}\n",
                .{
                    readable_from,
                    readable_to,
                    name,
                    if (dynamic) " -> end" else "",
                    length_function,
                    store_length,
                    data_area,
                    @intFromBool(use_loop),
                    items_per_slot,
                    items_per_slot,
                    loop_items.items,
                    @intFromBool(use_spill),
                    spill_items.items,
                    if (dynamic) "end := pos" else "",
                },
            );
        };
        defer self.allocator.free(code);
        try self.function_collector.finishFunction(name, code);
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
        var member_code: std.ArrayList(u8) = .empty;
        defer member_code.deinit(self.allocator);
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

            var preprocess = try self.allocator.alloc(u8, 0);
            defer self.allocator.free(preprocess);
            const retrieve = switch (from.reference.location) {
                .Storage => blk: {
                    const location = storage_layout.offsets[index] orelse
                        return error.InvalidType;
                    const relative_slot = location.slot;
                    if (TypeBehavior.isValueType(member_from)) {
                        if (previous_slot == null or previous_slot.? != relative_slot) {
                            self.allocator.free(preprocess);
                            const slot_text = try compactHex(self.allocator, relative_slot);
                            defer self.allocator.free(slot_text);
                            preprocess = try std.fmt.allocPrint(
                                self.allocator,
                                "slotValue := sload(add(value, {s}))",
                                .{slot_text},
                            );
                            previous_slot = relative_slot;
                        }
                        const extract = try self.utils.extractFromStorageValueFunction(
                            member_from,
                            location.byte_offset,
                        );
                        defer self.allocator.free(extract);
                        break :blk try std.fmt.allocPrint(
                            self.allocator,
                            "{s}(slotValue)",
                            .{extract},
                        );
                    }
                    if (location.byte_offset != 0) return error.InvalidType;
                    const slot_text = try compactHex(self.allocator, relative_slot);
                    defer self.allocator.free(slot_text);
                    break :blk try std.fmt.allocPrint(
                        self.allocator,
                        "add(value, {s})",
                        .{slot_text},
                    );
                },
                .Memory => blk: {
                    const offset = try TypeBehavior.structMemoryOffsetOfMember(
                        from,
                        member_name,
                    );
                    const text = try compactHex(self.allocator, offset);
                    defer self.allocator.free(text);
                    break :blk try std.fmt.allocPrint(
                        self.allocator,
                        "mload(add(value, {s}))",
                        .{text},
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
                    break :blk try std.fmt.allocPrint(
                        self.allocator,
                        "{s}(value, add(value, {s}))",
                        .{ access, text },
                    );
                },
                .Transient => return error.UnsupportedType,
            };
            defer self.allocator.free(retrieve);
            var sub_options = options;
            sub_options.encode_function_from_stack = false;
            sub_options.padded = true;
            const member_values = try variableListAlloc(
                self.allocator,
                "memberValue",
                try self.numVariablesForType(member_from, sub_options),
                false,
            );
            defer self.allocator.free(member_values);
            const encode = if (options.dynamic_inplace) blk: {
                const updated = try self.abiEncodeAndReturnUpdatedPosFunction(
                    member_from,
                    member_to,
                    sub_options,
                );
                defer self.allocator.free(updated);
                break :blk try std.fmt.allocPrint(
                    self.allocator,
                    "pos := {s}({s}, pos)",
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
                break :blk try std.fmt.allocPrint(
                    self.allocator,
                    "mstore(add(pos, {s}), sub(tail, pos))\ntail := {s}({s}, tail)",
                    .{ offset_text, encoder, member_values },
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
                break :blk try std.fmt.allocPrint(
                    self.allocator,
                    "{s}({s}, add(pos, {s}))",
                    .{ encoder, member_values, offset_text },
                );
            };
            defer self.allocator.free(encode);
            if (!options.dynamic_inplace)
                encoding_offset = std.math.add(
                    u256,
                    encoding_offset,
                    try TypeBehavior.calldataHeadSize(member_to),
                ) catch return error.Overflow;
            try member_code.print(
                self.allocator,
                "{{\n// {s}\n{s}\nlet {s} := {s}\n{s}\n}}\n",
                .{ member_name, preprocess, member_values, retrieve, encode },
            );
        }
        const readable_from = try TypeBehavior.toStringAlloc(self.allocator, from_type, true);
        defer self.allocator.free(readable_from);
        const readable_to = try TypeBehavior.toStringAlloc(self.allocator, to_type, true);
        defer self.allocator.free(readable_to);
        const head_size = try compactHex(self.allocator, encoding_offset);
        defer self.allocator.free(head_size);
        const assign_end = if (dynamic and options.dynamic_inplace)
            "end := pos"
        else if (dynamic)
            "end := tail"
        else
            "";
        const code = try std.fmt.allocPrint(
            self.allocator,
            "\n// {s} -> {s}\nfunction {s}(value, pos){s} {{\nlet tail := add(pos, {s})\n{s}\n{s}{s}\n}}\n",
            .{
                readable_from,
                readable_to,
                name,
                if (dynamic) " -> end" else "",
                head_size,
                if (from.reference.location == .Storage) "let slotValue := 0" else "",
                member_code.items,
                assign_end,
            },
        );
        defer self.allocator.free(code);
        try self.function_collector.finishFunction(name, code);
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
            break :blk try std.fmt.allocPrint(
                self.allocator,
                "\nfunction {s}(pos) -> end {{\npos := {s}(pos, {d})\n{s}(pos)\nend := add(pos, {d})\n}}\n",
                .{ name, store_length, literal.len, store_literal, overall_size },
            );
        } else blk: {
            const fixed = to_type.asFixedBytes() orelse return error.InvalidType;
            if (literal.len > 32 or fixed.bytes < literal.len)
                return error.InvalidType;
            const word = try CommonData.formatAsStringOrNumberAlloc(
                self.allocator,
                literal,
            );
            defer self.allocator.free(word);
            break :blk try std.fmt.allocPrint(
                self.allocator,
                "\nfunction {s}(pos) {{\nmstore(pos, {s})\n}}\n",
                .{ name, word },
            );
        };
        defer self.allocator.free(code);
        try self.function_collector.finishFunction(name, code);
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
        const code = if (options.encode_function_from_stack) blk: {
            const combine = try self.utils.combineExternalFunctionIdFunction();
            defer self.allocator.free(combine);
            const conversion = try self.utils.conversionFunction(from_type, to_type);
            defer self.allocator.free(conversion);
            break :blk try std.fmt.allocPrint(
                self.allocator,
                "\nfunction {s}(addr, function_id, pos) {{\naddr, function_id := {s}(addr, function_id)\nmstore(pos, {s}(addr, function_id))\n}}\n",
                .{ name, conversion, combine },
            );
        } else blk: {
            const cleanup = try self.utils.cleanupFunction(to_type);
            defer self.allocator.free(cleanup);
            break :blk try std.fmt.allocPrint(
                self.allocator,
                "\nfunction {s}(addr_and_function_id, pos) {{\nmstore(pos, {s}(addr_and_function_id))\n}}\n",
                .{ name, cleanup },
            );
        };
        defer self.allocator.free(code);
        try self.function_collector.finishFunction(name, code);
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
        const code = try std.fmt.allocPrint(
            self.allocator,
            "\nfunction {s}(offset, end) -> value {{\nvalue := {s}(offset)\n{s}(value)\n}}\n",
            .{ name, if (from_memory) "mload" else "calldataload", validator },
        );
        defer self.allocator.free(code);
        try self.function_collector.finishFunction(name, code);
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
        const retrieve_length = if (array.isDynamicallySized())
            try std.fmt.allocPrint(
                self.allocator,
                "{s}(offset)",
                .{if (from_memory) "mload" else "calldataload"},
            )
        else
            try compactHex(self.allocator, array.length.?);
        defer self.allocator.free(retrieve_length);
        const readable = try TypeBehavior.toStringAlloc(self.allocator, type_ref, true);
        defer self.allocator.free(readable);
        const code = try std.fmt.allocPrint(
            self.allocator,
            "\n// {s}\nfunction {s}(offset, end) -> array {{\nif iszero(slt(add(offset, 0x1f), end)) {{ {s}() }}\nlet length := {s}\narray := {s}({s}, length, end)\n}}\n",
            .{
                readable,
                name,
                revert,
                retrieve_length,
                available,
                if (array.isDynamicallySized()) "add(offset, 0x20)" else "offset",
            },
        );
        defer self.allocator.free(code);
        try self.function_collector.finishFunction(name, code);
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
        const readable = try TypeBehavior.toStringAlloc(self.allocator, type_ref, true);
        defer self.allocator.free(readable);
        const dynamic_base = TypeBehavior.isDynamicallyEncoded(array.base_type);
        const element_position = if (dynamic_base)
            try std.fmt.allocPrint(
                self.allocator,
                "let innerOffset := {s}(src)\nif gt(innerOffset, 0xffffffffffffffff) {{ {s}() }}\nlet elementPos := add(offset, innerOffset)",
                .{ if (from_memory) "mload" else "calldataload", invalid_offset },
            )
        else
            try self.allocator.dupe(u8, "let elementPos := src");
        defer self.allocator.free(element_position);
        const code = try std.fmt.allocPrint(
            self.allocator,
            "\n// {s}\nfunction {s}(offset, length, end) -> array {{\narray := {s}({s}(length))\nlet dst := array\n{s}\nlet srcEnd := add(offset, mul(length, {s}))\nif gt(srcEnd, end) {{\n{s}()\n}}\nfor {{ let src := offset }} lt(src, srcEnd) {{ src := add(src, {s}) }}\n{{\n{s}\nmstore(dst, {s}(elementPos, end))\ndst := add(dst, 0x20)\n}}\n}}\n",
            .{
                readable,
                name,
                allocate,
                allocation_size,
                if (array.isDynamicallySized())
                    "mstore(array, length)\ndst := add(array, 0x20)"
                else
                    "",
                stride_text,
                invalid_stride,
                stride_text,
                element_position,
                decoder,
            },
        );
        defer self.allocator.free(code);
        try self.function_collector.finishFunction(name, code);
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
        const readable = try TypeBehavior.toStringAlloc(self.allocator, type_ref, true);
        defer self.allocator.free(readable);
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
            break :blk try std.fmt.allocPrint(
                self.allocator,
                "\n// {s}\nfunction {s}(offset, end) -> arrayPos, length {{\nif iszero(slt(add(offset, 0x1f), end)) {{ {s}() }}\nlength := calldataload(offset)\nif gt(length, 0xffffffffffffffff) {{ {s}() }}\narrayPos := add(offset, 0x20)\nif gt(add(arrayPos, mul(length, {s})), end) {{ {s}() }}\n}}\n",
                .{ readable, name, invalid_offset, invalid_length, stride_text, invalid_position },
            );
        } else blk: {
            const length = try compactHex(self.allocator, array.length.?);
            defer self.allocator.free(length);
            const invalid_position = try self.utils.revertReasonIfDebugFunction(
                "ABI decoding: invalid calldata array stride",
            );
            defer self.allocator.free(invalid_position);
            break :blk try std.fmt.allocPrint(
                self.allocator,
                "\n// {s}\nfunction {s}(offset, end) -> arrayPos {{\narrayPos := offset\nif gt(add(arrayPos, mul({s}, {s})), end) {{ {s}() }}\n}}\n",
                .{ readable, name, length, stride_text, invalid_position },
            );
        };
        defer self.allocator.free(code);
        try self.function_collector.finishFunction(name, code);
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
        const code = try std.fmt.allocPrint(
            self.allocator,
            "\nfunction {s}(src, length, end) -> array {{\narray := {s}({s}(length))\nmstore(array, length)\nlet dst := add(array, 0x20)\nif gt(add(src, length), end) {{ {s}() }}\n{s}(src, dst, length)\n}}\n",
            .{ name, allocate, allocation_size, invalid_length, copy },
        );
        defer self.allocator.free(code);
        try self.function_collector.finishFunction(name, code);
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
        const readable = try TypeBehavior.toStringAlloc(self.allocator, type_ref, true);
        defer self.allocator.free(readable);
        const code = try std.fmt.allocPrint(
            self.allocator,
            "\n// {s}\nfunction {s}(offset, end) -> value {{\nif slt(sub(end, offset), {d}) {{ {s}() }}\nvalue := offset\n}}\n",
            .{ readable, name, minimum, revert },
        );
        defer self.allocator.free(code);
        try self.function_collector.finishFunction(name, code);
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
        var member_code: std.ArrayList(u8) = .empty;
        defer member_code.deinit(self.allocator);
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
                try member_code.print(
                    self.allocator,
                    "{{\n// {s}\nlet offset := {s}(add(headStart, {d}))\nif gt(offset, 0xffffffffffffffff) {{ {s}() }}\nmstore(add(value, {s}), {s}(add(headStart, offset), end))\n}}\n",
                    .{
                        member_name,
                        if (from_memory) "mload" else "calldataload",
                        head_position,
                        invalid_offset,
                        memory_offset_text,
                        decoder,
                    },
                )
            else
                try member_code.print(
                    self.allocator,
                    "{{\n// {s}\nlet offset := {d}\nmstore(add(value, {s}), {s}(add(headStart, offset), end))\n}}\n",
                    .{ member_name, head_position, memory_offset_text, decoder },
                );
            head_position = std.math.add(
                u32,
                head_position,
                try TypeBehavior.calldataHeadSize(decoding),
            ) catch return error.Overflow;
        }
        const minimum = try compactHex(self.allocator, head_position);
        defer self.allocator.free(minimum);
        const readable = try TypeBehavior.toStringAlloc(self.allocator, type_ref, true);
        defer self.allocator.free(readable);
        const code = try std.fmt.allocPrint(
            self.allocator,
            "\n// {s}\nfunction {s}(headStart, end) -> value {{\nif slt(sub(end, headStart), {s}) {{ {s}() }}\nvalue := {s}({s})\n{s}}}\n",
            .{ readable, name, minimum, revert, allocate, memory_size_text, member_code.items },
        );
        defer self.allocator.free(code);
        try self.function_collector.finishFunction(name, code);
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
        const code = if (for_use_on_stack) blk: {
            const nested = try self.abiDecodingFunctionFunctionType(
                type_ref,
                from_memory,
                false,
            );
            defer self.allocator.free(nested);
            const split = try self.utils.splitExternalFunctionIdFunction();
            defer self.allocator.free(split);
            break :blk try std.fmt.allocPrint(
                self.allocator,
                "\nfunction {s}(offset, end) -> addr, function_selector {{\naddr, function_selector := {s}({s}(offset, end))\n}}\n",
                .{ name, split, nested },
            );
        } else blk: {
            const validator = try self.utils.validatorFunction(type_ref, true);
            defer self.allocator.free(validator);
            break :blk try std.fmt.allocPrint(
                self.allocator,
                "\nfunction {s}(offset, end) -> fun {{\nfun := {s}(offset)\n{s}(fun)\n}}\n",
                .{ name, if (from_memory) "mload" else "calldataload", validator },
            );
        };
        defer self.allocator.free(code);
        try self.function_collector.finishFunction(name, code);
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
                break :blk try std.fmt.allocPrint(
                    self.allocator,
                    "\nfunction {s}(base_ref, ptr) -> value, length {{\nlet rel_offset_of_tail := calldataload(ptr)\nif iszero(slt(rel_offset_of_tail, sub(sub(calldatasize(), base_ref), sub({s}, 1)))) {{ {s}() }}\nvalue := add(rel_offset_of_tail, base_ref)\nlength := calldataload(value)\nvalue := add(value, 0x20)\nif gt(length, 0xffffffffffffffff) {{ {s}() }}\nif sgt(value, sub(calldatasize(), mul(length, {s}))) {{ {s}() }}\n}}\n",
                    .{ name, tail_size_text, invalid_offset, invalid_length, stride, invalid_stride },
                );
            }
            const invalid_offset = try self.utils.revertReasonIfDebugFunction(
                "Invalid calldata access offset",
            );
            defer self.allocator.free(invalid_offset);
            break :blk try std.fmt.allocPrint(
                self.allocator,
                "\nfunction {s}(base_ref, ptr) -> value {{\nlet rel_offset_of_tail := calldataload(ptr)\nif iszero(slt(rel_offset_of_tail, sub(sub(calldatasize(), base_ref), sub({s}, 1)))) {{ {s}() }}\nvalue := add(rel_offset_of_tail, base_ref)\n}}\n",
                .{ name, tail_size_text, invalid_offset },
            );
        } else if (TypeBehavior.isValueType(type_ref)) blk: {
            const decoder = if (type_ref.category() == .Function)
                try self.abiDecodingFunctionFunctionType(type_ref, false, false)
            else
                try self.abiDecodingFunctionValueType(type_ref, false);
            defer self.allocator.free(decoder);
            break :blk try std.fmt.allocPrint(
                self.allocator,
                "\nfunction {s}(baseRef, ptr) -> value {{\nvalue := {s}(ptr, add(ptr, 32))\n}}\n",
                .{ name, decoder },
            );
        } else switch (type_ref.category()) {
            .Array, .Struct => try std.fmt.allocPrint(
                self.allocator,
                "\nfunction {s}(baseRef, ptr) -> value {{\nvalue := ptr\n}}\n",
                .{name},
            ),
            else => return error.InvalidType,
        };
        defer self.allocator.free(code);
        try self.function_collector.finishFunction(name, code);
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
            .Contract,
            .Enum,
            .InaccessibleDynamic,
            => type_ref,
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
            .Contract => &interface_address,
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

fn variableListAlloc(
    allocator: std.mem.Allocator,
    prefix: []const u8,
    count: usize,
    reversed: bool,
) std.mem.Allocator.Error![]u8 {
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    for (0..count) |position| {
        if (position != 0) try output.appendSlice(allocator, ", ");
        const index = if (reversed) count - position - 1 else position;
        try output.print(allocator, "{s}{d}", .{ prefix, index });
    }
    return output.toOwnedSlice(allocator);
}

fn variableRangeAlloc(
    allocator: std.mem.Allocator,
    prefix: []const u8,
    start: usize,
    end: usize,
) std.mem.Allocator.Error![]u8 {
    if (end < start) return allocator.alloc(u8, 0);
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    for (start..end) |index| {
        if (index != start) try output.appendSlice(allocator, ", ");
        try output.print(allocator, "{s}{d}", .{ prefix, index });
    }
    return output.toOwnedSlice(allocator);
}

test "scalar ABI tuple helpers retain upstream names and checks" {
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
    const code = try collector.requestedFunctionsAlloc();
    defer std.testing.allocator.free(code);
    try std.testing.expect(std.mem.find(u8, code, "slt(sub(dataEnd, headStart), 64)") != null);
    try std.testing.expect(std.mem.find(u8, code, "calldataload(offset)") != null);
    try std.testing.expect(std.mem.find(u8, code, "mstore(pos, cleanup_t_uint256(value))") != null);
}

test "encoding option suffix order is stable" {
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

test "composite ABI helpers cover arrays, literals, storage packing, and external functions" {
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

    const code = try collector.requestedFunctionsAlloc();
    defer std.testing.allocator.free(code);
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

test "struct ABI helpers cover memory, calldata, and storage members" {
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

    const code = try collector.requestedFunctionsAlloc();
    defer std.testing.allocator.free(code);
    try std.testing.expect(std.mem.find(u8, code, "// amount") != null);
    try std.testing.expect(std.mem.find(u8, code, "// payload") != null);
    try std.testing.expect(std.mem.find(u8, code, "slotValue := sload") != null);
    try std.testing.expect(std.mem.find(u8, code, "calldata_access_t_bytes_calldata") != null);
    try std.testing.expect(std.mem.find(u8, code, "ABI decoding: invalid struct offset") == null);
    try std.testing.expect(std.mem.find(u8, code, "mstore(add(value,") != null);
}
