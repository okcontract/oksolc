// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Versioned EVM Yul dialect with handle-compatible builtin slots.

const std = @import("std");
const AST = @import("../../ast.zig");
const BuiltinHandle = @import("../../builtins.zig").BuiltinHandle;
const Diagnostics = @import("../../../liblangutil/diagnostics.zig");
const EVMVersionModule = @import("../../../liblangutil/evm_version.zig");
const EVMVersion = EVMVersionModule.EVMVersion;
const Version = EVMVersionModule.Version;
const InstructionModule = @import("../../../libevmasm/instruction.zig");
const Instruction = InstructionModule.Instruction;
const EVMBuiltinsModule = @import("evm_builtins.zig");
const BuiltinFunctionForEVM = EVMBuiltinsModule.BuiltinFunctionForEVM;
const Entry = EVMBuiltinsModule.Entry;
const EVMBuiltins = EVMBuiltinsModule.EVMBuiltins;
const YulString = @import("../../yul_string.zig");

pub const AuxiliaryBuiltinHandles = struct {
    add: ?BuiltinHandle = null,
    exp: ?BuiltinHandle = null,
    mul: ?BuiltinHandle = null,
    not_: ?BuiltinHandle = null,
    shl: ?BuiltinHandle = null,
    sub: ?BuiltinHandle = null,
};

pub const verbatim_max_input_slots: usize = 100;
pub const verbatim_max_output_slots: usize = 100;
pub const verbatim_id_offset: usize = verbatim_max_input_slots * verbatim_max_output_slots;

pub const EVMDialect = struct {
    allocator: std.mem.Allocator,
    object_access: bool,
    evm_version: EVMVersion,
    all_builtins: EVMBuiltins,
    builtin_functions_by_name: std.StringHashMap(BuiltinHandle),
    functions: std.ArrayList(?*const BuiltinFunctionForEVM) = .empty,
    verbatim_functions: std.ArrayList(?*BuiltinFunctionForEVM) = .empty,
    verbatim_mutex: std.Io.Mutex = .init,
    reserved: std.StringHashMap(void),
    reserved_names: std.ArrayList([]u8) = .empty,

    discard_function: ?BuiltinHandle = null,
    equality_function: ?BuiltinHandle = null,
    boolean_negation_function: ?BuiltinHandle = null,
    memory_store_function: ?BuiltinHandle = null,
    memory_load_function: ?BuiltinHandle = null,
    storage_store_function: ?BuiltinHandle = null,
    storage_load_function: ?BuiltinHandle = null,
    hash_function: ?BuiltinHandle = null,
    auxiliary_builtin_handles: AuxiliaryBuiltinHandles = .{},

    pub fn init(
        allocator: std.mem.Allocator,
        evm_version: EVMVersion,
        object_access: bool,
    ) !EVMDialect {
        var result: EVMDialect = .{
            .allocator = allocator,
            .object_access = object_access,
            .evm_version = evm_version,
            .all_builtins = try EVMBuiltins.init(allocator),
            .builtin_functions_by_name = std.StringHashMap(BuiltinHandle).init(allocator),
            .reserved = std.StringHashMap(void).init(allocator),
        };
        errdefer result.deinit();

        try result.functions.ensureTotalCapacity(allocator, result.all_builtins.functions().len);
        for (result.all_builtins.entries.items, 0..) |*entry, index| {
            const maybe_builtin: ?*const BuiltinFunctionForEVM = if (builtinAvailable(
                entry,
                evm_version,
                object_access,
            ))
                &entry.builtin
            else
                null;
            result.functions.appendAssumeCapacity(maybe_builtin);
            if (maybe_builtin) |available_builtin| {
                try result.builtin_functions_by_name.put(
                    available_builtin.base.name,
                    .{ .id = index + verbatim_id_offset },
                );
            }
        }

        try result.verbatim_functions.resize(allocator, verbatim_id_offset);
        @memset(result.verbatim_functions.items, null);
        try result.createReservedIdentifiers();

        result.discard_function = result.findBuiltin("pop");
        result.equality_function = result.findBuiltin("eq");
        result.boolean_negation_function = result.findBuiltin("iszero");
        result.memory_store_function = result.findBuiltin("mstore");
        result.memory_load_function = result.findBuiltin("mload");
        result.storage_store_function = result.findBuiltin("sstore");
        result.storage_load_function = result.findBuiltin("sload");
        result.hash_function = result.findBuiltin("keccak256");
        result.auxiliary_builtin_handles = .{
            .add = result.findBuiltin("add"),
            .exp = result.findBuiltin("exp"),
            .mul = result.findBuiltin("mul"),
            .not_ = result.findBuiltin("not"),
            .shl = result.findBuiltin("shl"),
            .sub = result.findBuiltin("sub"),
        };
        return result;
    }

    pub fn deinit(self: *EVMDialect) void {
        for (self.verbatim_functions.items) |maybe_builtin| {
            if (maybe_builtin) |verbatim_builtin| {
                verbatim_builtin.deinit(self.allocator);
                self.allocator.destroy(verbatim_builtin);
            }
        }
        self.verbatim_functions.deinit(self.allocator);
        self.functions.deinit(self.allocator);
        self.builtin_functions_by_name.deinit();
        self.reserved.deinit();
        for (self.reserved_names.items) |name| self.allocator.free(name);
        self.reserved_names.deinit(self.allocator);
        self.all_builtins.deinit();
        self.* = undefined;
    }

    pub fn dialect(self: *const EVMDialect) AST.Dialect {
        return .{ .context = self, .vtable = &dialect_vtable };
    }

    pub fn findBuiltin(self: *const EVMDialect, name: []const u8) ?BuiltinHandle {
        if (self.object_access and std.mem.startsWith(u8, name, "verbatim_")) {
            if (parseVerbatimName(name)) |shape| {
                return @constCast(self).verbatimFunction(shape.arguments, shape.return_variables) catch null;
            }
        }
        return self.builtin_functions_by_name.get(name);
    }

    pub fn builtin(self: *const EVMDialect, handle: BuiltinHandle) ?*const BuiltinFunctionForEVM {
        if (isVerbatimHandle(handle)) {
            mutexLock(@constCast(&self.verbatim_mutex));
            defer mutexUnlock(@constCast(&self.verbatim_mutex));
            return self.verbatim_functions.items[handle.id];
        }
        const index = handle.id -| verbatim_id_offset;
        if (handle.id < verbatim_id_offset or index >= self.functions.items.len) return null;
        return self.functions.items[index];
    }

    pub fn reservedIdentifier(self: *const EVMDialect, name: []const u8) bool {
        if (self.object_access and std.mem.startsWith(u8, name, "verbatim")) return true;
        return self.reserved.contains(name);
    }

    pub fn discardFunctionHandle(self: *const EVMDialect) ?BuiltinHandle {
        return self.discard_function;
    }

    pub fn equalityFunctionHandle(self: *const EVMDialect) ?BuiltinHandle {
        return self.equality_function;
    }

    pub fn booleanNegationFunctionHandle(self: *const EVMDialect) ?BuiltinHandle {
        return self.boolean_negation_function;
    }

    pub fn memoryStoreFunctionHandle(self: *const EVMDialect) ?BuiltinHandle {
        return self.memory_store_function;
    }

    pub fn memoryLoadFunctionHandle(self: *const EVMDialect) ?BuiltinHandle {
        return self.memory_load_function;
    }

    pub fn storageStoreFunctionHandle(self: *const EVMDialect) ?BuiltinHandle {
        return self.storage_store_function;
    }

    pub fn storageLoadFunctionHandle(self: *const EVMDialect) ?BuiltinHandle {
        return self.storage_load_function;
    }

    pub fn hashFunctionHandle(self: *const EVMDialect) ?BuiltinHandle {
        return self.hash_function;
    }

    pub fn auxiliaryBuiltinHandles(self: *const EVMDialect) *const AuxiliaryBuiltinHandles {
        return &self.auxiliary_builtin_handles;
    }

    pub fn evmVersion(self: *const EVMDialect) EVMVersion {
        return self.evm_version;
    }

    pub fn reachableStackDepth(self: *const EVMDialect) usize {
        return self.evm_version.reachableStackDepth();
    }

    pub fn providesObjectAccess(self: *const EVMDialect) bool {
        return self.object_access;
    }

    /// Returns a sorted, allocator-owned outer slice. The names borrow the dialect.
    pub fn builtinFunctionNamesAlloc(
        self: *const EVMDialect,
        allocator: std.mem.Allocator,
    ) std.mem.Allocator.Error![][]const u8 {
        const result = try allocator.alloc([]const u8, self.builtin_functions_by_name.count());
        var iterator = self.builtin_functions_by_name.keyIterator();
        var index: usize = 0;
        while (iterator.next()) |name| : (index += 1) result[index] = name.*;
        std.sort.insertion([]const u8, result, {}, struct {
            fn lessThan(_: void, left: []const u8, right: []const u8) bool {
                return std.mem.order(u8, left, right) == .lt;
            }
        }.lessThan);
        return result;
    }

    pub fn verbatimFunction(
        self: *EVMDialect,
        arguments: usize,
        return_variables: usize,
    ) !BuiltinHandle {
        if (arguments >= verbatim_max_input_slots or return_variables >= verbatim_max_output_slots)
            return error.InvalidVerbatimShape;
        const index = arguments + return_variables * verbatim_max_input_slots;
        mutexLock(&self.verbatim_mutex);
        defer mutexUnlock(&self.verbatim_mutex);
        if (self.verbatim_functions.items[index] == null) {
            const verbatim_builtin = try self.allocator.create(BuiltinFunctionForEVM);
            errdefer self.allocator.destroy(verbatim_builtin);
            verbatim_builtin.* = try EVMBuiltins.createVerbatimFunction(
                self.allocator,
                arguments,
                return_variables,
            );
            self.verbatim_functions.items[index] = verbatim_builtin;
        }
        return .{ .id = index };
    }

    /// Callback-compatible instruction validation for `AsmAnalyzer`.
    pub fn validateInstructionCallback(
        context: ?*anyopaque,
        name: []const u8,
        location: Diagnostics.SourceLocation,
        reporter: *Diagnostics.ErrorReporter,
    ) Diagnostics.ReportError!bool {
        const self: *const EVMDialect = @ptrCast(@alignCast(context orelse return false));
        return self.validateInstructionName(name, location, reporter);
    }

    pub fn instructionValidatorContext(self: *const EVMDialect) ?*anyopaque {
        return @ptrCast(@constCast(self));
    }

    pub fn validateInstructionName(
        self: *const EVMDialect,
        name: []const u8,
        location: Diagnostics.SourceLocation,
        reporter: *Diagnostics.ErrorReporter,
    ) Diagnostics.ReportError!bool {
        const instruction = self.currentDialectInstruction(name) orelse return false;
        const unavailable: ?UnavailableInstruction = switch (instruction) {
            .RETURNDATACOPY => if (!self.evm_version.supportsReturndata())
                .{ .error_id = 7756, .kind = "only available for Byzantium-compatible" }
            else
                null,
            .RETURNDATASIZE => if (!self.evm_version.supportsReturndata())
                .{ .error_id = 4778, .kind = "only available for Byzantium-compatible" }
            else
                null,
            .STATICCALL => if (!self.evm_version.hasStaticCall())
                .{ .error_id = 1503, .kind = "only available for Byzantium-compatible" }
            else
                null,
            .SHL => if (!self.evm_version.hasBitwiseShifting())
                .{ .error_id = 6612, .kind = "only available for Constantinople-compatible" }
            else
                null,
            .SHR => if (!self.evm_version.hasBitwiseShifting())
                .{ .error_id = 7458, .kind = "only available for Constantinople-compatible" }
            else
                null,
            .SAR => if (!self.evm_version.hasBitwiseShifting())
                .{ .error_id = 2054, .kind = "only available for Constantinople-compatible" }
            else
                null,
            .CLZ => if (!self.evm_version.hasCLZ())
                .{ .error_id = 4948, .kind = "only available for Osaka-compatible" }
            else
                null,
            .CREATE2 => if (!self.evm_version.hasCreate2())
                .{ .error_id = 6166, .kind = "only available for Constantinople-compatible" }
            else
                null,
            .EXTCODEHASH => if (!self.evm_version.hasExtCodeHash())
                .{ .error_id = 7110, .kind = "only available for Constantinople-compatible" }
            else
                null,
            .CHAINID => if (!self.evm_version.hasChainID())
                .{ .error_id = 1561, .kind = "only available for Istanbul-compatible" }
            else
                null,
            .SELFBALANCE => if (!self.evm_version.hasSelfBalance())
                .{ .error_id = 7721, .kind = "only available for Istanbul-compatible" }
            else
                null,
            .BASEFEE => if (!self.evm_version.hasBaseFee())
                .{ .error_id = 5430, .kind = "only available for London-compatible" }
            else
                null,
            .BLOBBASEFEE => if (!self.evm_version.hasBlobBaseFee())
                .{ .error_id = 6679, .kind = "only available for Cancun-compatible" }
            else
                null,
            .BLOBHASH => if (!self.evm_version.hasBlobHash())
                .{ .error_id = 8314, .kind = "only available for Cancun-compatible" }
            else
                null,
            .MCOPY => if (!self.evm_version.hasMcopy())
                .{ .error_id = 7755, .kind = "only available for Cancun-compatible" }
            else
                null,
            .TSTORE, .TLOAD => if (!self.evm_version.supportsTransientStorage())
                .{ .error_id = 6243, .kind = "only available for Cancun-compatible" }
            else
                null,
            else => null,
        };
        if (unavailable) |value| {
            const instruction_name = try lowercaseAlloc(
                self.allocator,
                InstructionModule.instructionInfo(instruction, self.evm_version).name,
            );
            defer self.allocator.free(instruction_name);
            const description = try std.fmt.allocPrint(
                self.allocator,
                "The \"{s}\" instruction is {s} VMs (you are currently compiling for \"{s}\").",
                .{ instruction_name, value.kind, self.evm_version.name() },
            );
            defer self.allocator.free(description);
            try reporter.typeError(.{ .value = value.error_id }, location, description);
            return true;
        }
        if (instruction == .PC) {
            try reporter.syntaxError(
                .{ .value = 2450 },
                location,
                "PC instruction is a low-level EVM feature. Because of that PC is disallowed in strict assembly.",
            );
            return true;
        }
        return false;
    }

    fn createReservedIdentifiers(self: *EVMDialect) !void {
        inline for (std.meta.fields(Instruction)) |field| {
            const instruction: Instruction = @enumFromInt(field.value);
            if (!reservedInstructionException(instruction, field.name, self.evm_version))
                try self.putReservedLower(field.name);
        }
        try self.putReservedLower("DIFFICULTY");
        const object_reserved = [_][]const u8{
            "linkersymbol",
            "datasize",
            "dataoffset",
            "datacopy",
            "setimmutable",
            "loadimmutable",
        };
        for (object_reserved) |name| try self.putReservedLower(name);
    }

    fn putReservedLower(self: *EVMDialect, name: []const u8) !void {
        const owned_name = try lowercaseAlloc(self.allocator, name);
        errdefer self.allocator.free(owned_name);
        if (self.reserved.contains(owned_name)) {
            self.allocator.free(owned_name);
            return;
        }
        try self.reserved_names.append(self.allocator, owned_name);
        errdefer _ = self.reserved_names.pop();
        try self.reserved.put(owned_name, {});
    }

    fn currentDialectInstruction(self: *const EVMDialect, name: []const u8) ?Instruction {
        for (self.all_builtins.entries.items) |*entry| {
            const instruction = entry.builtin.instruction orelse continue;
            if (!builtinAvailable(entry, EVMVersion.current(), true)) continue;
            if (std.mem.eql(u8, entry.builtin.base.name, name)) return instruction;
        }
        return null;
    }
};

const UnavailableInstruction = struct {
    error_id: u64,
    kind: []const u8,
};

const VerbatimShape = struct {
    arguments: usize,
    return_variables: usize,
};

fn parseVerbatimName(name: []const u8) ?VerbatimShape {
    const prefix = "verbatim_";
    if (!std.mem.startsWith(u8, name, prefix)) return null;
    const remainder = name[prefix.len..];
    const separator = std.mem.find(u8, remainder, "i_") orelse return null;
    const arguments_text = remainder[0..separator];
    const returns_with_suffix = remainder[separator + 2 ..];
    if (returns_with_suffix.len < 2 or returns_with_suffix[returns_with_suffix.len - 1] != 'o') return null;
    const returns_text = returns_with_suffix[0 .. returns_with_suffix.len - 1];
    if (!canonicalVerbatimNumber(arguments_text) or !canonicalVerbatimNumber(returns_text)) return null;
    return .{
        .arguments = std.fmt.parseUnsigned(usize, arguments_text, 10) catch return null,
        .return_variables = std.fmt.parseUnsigned(usize, returns_text, 10) catch return null,
    };
}

fn canonicalVerbatimNumber(value: []const u8) bool {
    if (value.len == 0 or value.len > 2) return false;
    for (value) |character| if (!std.ascii.isDigit(character)) return false;
    return value.len == 1 or value[0] != '0';
}

fn isVerbatimHandle(handle: BuiltinHandle) bool {
    return handle.id < verbatim_id_offset;
}

fn builtinAvailable(entry: *const Entry, evm_version: EVMVersion, object_access: bool) bool {
    var available = true;
    if (entry.scopes.instruction()) {
        if (entry.scopes.replaced()) {
            available = false;
        } else {
            const instruction = entry.builtin.instruction orelse return false;
            const low_level_control = switch (instruction) {
                .JUMP, .JUMPI, .JUMPDEST => true,
                else => false,
            };
            const alias_unavailable =
                (std.mem.eql(u8, entry.builtin.base.name, "prevrandao") and !evm_version.atLeast(.Paris)) or
                (std.mem.eql(u8, entry.builtin.base.name, "difficulty") and evm_version.atLeast(.Paris));
            available = !low_level_control and
                !InstructionModule.isSwapInstruction(instruction) and
                !InstructionModule.isDupInstruction(instruction) and
                !InstructionModule.isPushInstruction(instruction) and
                evm_version.hasOpcode(@intFromEnum(instruction)) and
                !alias_unavailable;
        }
    }
    return available and (!entry.scopes.requiresObjectAccess() or object_access);
}

fn reservedInstructionException(
    instruction: Instruction,
    name: []const u8,
    evm_version: EVMVersion,
) bool {
    if (instruction == .BASEFEE and !evm_version.atLeast(.London)) return true;
    if (instruction == .BLOBBASEFEE and !evm_version.atLeast(.Cancun)) return true;
    if (instruction == .MCOPY and !evm_version.atLeast(.Cancun)) return true;
    if (instruction == .BLOBHASH and !evm_version.atLeast(.Cancun)) return true;
    if ((instruction == .TSTORE or instruction == .TLOAD) and !evm_version.atLeast(.Cancun)) return true;
    if (instruction == .CLZ and !evm_version.hasCLZ()) return true;
    if (instruction == .PREVRANDAO and std.mem.eql(u8, name, "PREVRANDAO") and !evm_version.atLeast(.Paris))
        return true;
    return false;
}

fn lowercaseAlloc(allocator: std.mem.Allocator, value: []const u8) std.mem.Allocator.Error![]u8 {
    const result = try allocator.dupe(u8, value);
    for (result) |*character| character.* = std.ascii.toLower(character.*);
    return result;
}

fn dialectFromContext(context: ?*const anyopaque) ?*const EVMDialect {
    return @ptrCast(@alignCast(context orelse return null));
}

fn findBuiltinCallback(context: ?*const anyopaque, name: []const u8) ?BuiltinHandle {
    return (dialectFromContext(context) orelse return null).findBuiltin(name);
}

fn builtinCallback(context: ?*const anyopaque, handle: BuiltinHandle) ?*const AST.BuiltinFunction {
    const builtin = (dialectFromContext(context) orelse return null).builtin(handle) orelse return null;
    return &builtin.base;
}

fn reservedIdentifierCallback(context: ?*const anyopaque, name: []const u8) bool {
    return (dialectFromContext(context) orelse return false).reservedIdentifier(name);
}

fn discardFunctionCallback(context: ?*const anyopaque) ?BuiltinHandle {
    return (dialectFromContext(context) orelse return null).discardFunctionHandle();
}

fn equalityFunctionCallback(context: ?*const anyopaque) ?BuiltinHandle {
    return (dialectFromContext(context) orelse return null).equalityFunctionHandle();
}

fn booleanNegationFunctionCallback(context: ?*const anyopaque) ?BuiltinHandle {
    return (dialectFromContext(context) orelse return null).booleanNegationFunctionHandle();
}

fn memoryStoreFunctionCallback(context: ?*const anyopaque) ?BuiltinHandle {
    return (dialectFromContext(context) orelse return null).memoryStoreFunctionHandle();
}

fn memoryLoadFunctionCallback(context: ?*const anyopaque) ?BuiltinHandle {
    return (dialectFromContext(context) orelse return null).memoryLoadFunctionHandle();
}

fn storageStoreFunctionCallback(context: ?*const anyopaque) ?BuiltinHandle {
    return (dialectFromContext(context) orelse return null).storageStoreFunctionHandle();
}

fn storageLoadFunctionCallback(context: ?*const anyopaque) ?BuiltinHandle {
    return (dialectFromContext(context) orelse return null).storageLoadFunctionHandle();
}

fn hashFunctionCallback(context: ?*const anyopaque) ?BuiltinHandle {
    return (dialectFromContext(context) orelse return null).hashFunctionHandle();
}

const dialect_vtable: AST.DialectVTable = .{
    .find_builtin = findBuiltinCallback,
    .builtin = builtinCallback,
    .reserved_identifier = reservedIdentifierCallback,
    .discard_function_handle = discardFunctionCallback,
    .equality_function_handle = equalityFunctionCallback,
    .boolean_negation_function_handle = booleanNegationFunctionCallback,
    .memory_store_function_handle = memoryStoreFunctionCallback,
    .memory_load_function_handle = memoryLoadFunctionCallback,
    .storage_store_function_handle = storageStoreFunctionCallback,
    .storage_load_function_handle = storageLoadFunctionCallback,
    .hash_function_handle = hashFunctionCallback,
};

const version_count = std.meta.fields(Version).len;
var cache_mutex: std.Io.Mutex = .init;
var inline_dialect_cache: [version_count]?*EVMDialect = @splat(null);
var object_dialect_cache: [version_count]?*EVMDialect = @splat(null);
var reset_callback_registered = false;

pub fn strictAssemblyForEVM(evm_version: EVMVersion) !*const EVMDialect {
    return cachedDialect(&inline_dialect_cache, evm_version, false);
}

pub fn strictAssemblyForEVMObjects(evm_version: EVMVersion) !*const EVMDialect {
    return cachedDialect(&object_dialect_cache, evm_version, true);
}

/// Checked counterpart of the upstream `dynamic_cast<EVMDialect const*>`.
pub fn fromDialect(dialect_value: AST.Dialect) ?*const EVMDialect {
    if (dialect_value.vtable != &dialect_vtable) return null;
    return dialectFromContext(dialect_value.context);
}

fn cachedDialect(
    cache: *[version_count]?*EVMDialect,
    evm_version: EVMVersion,
    object_access: bool,
) !*const EVMDialect {
    mutexLock(&cache_mutex);
    defer mutexUnlock(&cache_mutex);
    if (!reset_callback_registered) {
        try (YulString.ResetCallback{ .function = clearDialectCaches }).register();
        reset_callback_registered = true;
    }
    const index: usize = @intCast(@intFromEnum(evm_version.version));
    if (cache[index] == null) {
        const dialect = try std.heap.page_allocator.create(EVMDialect); // zlinter-disable-current-line no_hidden_allocations - process-wide dialect cache has process-wide allocation lifetime
        errdefer std.heap.page_allocator.destroy(dialect); // zlinter-disable-current-line no_hidden_allocations - process-wide dialect cache has process-wide allocation lifetime
        dialect.* = try EVMDialect.init(std.heap.page_allocator, evm_version, object_access);
        cache[index] = dialect;
    }
    return cache[index].?;
}

fn clearDialectCaches(_: ?*anyopaque) void {
    mutexLock(&cache_mutex);
    defer mutexUnlock(&cache_mutex);
    clearDialectCache(&inline_dialect_cache);
    clearDialectCache(&object_dialect_cache);
}

fn clearDialectCache(cache: *[version_count]?*EVMDialect) void {
    for (cache) |*maybe_dialect| {
        if (maybe_dialect.*) |dialect| {
            dialect.deinit();
            std.heap.page_allocator.destroy(dialect); // zlinter-disable-current-line no_hidden_allocations - process-wide dialect cache has process-wide allocation lifetime
            maybe_dialect.* = null;
        }
    }
}

fn mutexLock(mutex: *std.Io.Mutex) void {
    std.Io.Threaded.mutexLock(mutex);
}

fn mutexUnlock(mutex: *std.Io.Mutex) void {
    std.Io.Threaded.mutexUnlock(mutex);
}

test "EVM dialect filters versions without changing compatible handles" {
    const allocator = std.testing.allocator;
    var homestead = try EVMDialect.init(allocator, EVMVersion.init(.Homestead), false);
    defer homestead.deinit();
    var osaka_objects = try EVMDialect.init(allocator, EVMVersion.init(.Osaka), true);
    defer osaka_objects.deinit();

    try std.testing.expect(homestead.findBuiltin("add") != null);
    try std.testing.expect(homestead.findBuiltin("basefee") == null);
    try std.testing.expect(!homestead.reservedIdentifier("basefee"));
    try std.testing.expect(osaka_objects.findBuiltin("basefee") != null);
    try std.testing.expect(osaka_objects.reservedIdentifier("basefee"));
    try std.testing.expectEqual(
        homestead.findBuiltin("add").?.id,
        osaka_objects.findBuiltin("add").?.id,
    );
    try std.testing.expect(osaka_objects.findBuiltin("datasize") != null);
    try std.testing.expect(homestead.findBuiltin("datasize") == null);
}

test "verbatim builtins use the protected handle range and exact grammar" {
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, EVMVersion.current(), true);
    defer dialect.deinit();
    const handle = dialect.findBuiltin("verbatim_2i_3o").?;
    try std.testing.expectEqual(@as(usize, 302), handle.id);
    try std.testing.expectEqualStrings("verbatim_2i_3o", dialect.builtin(handle).?.base.name);
    try std.testing.expect(dialect.findBuiltin("verbatim_02i_3o") == null);
    try std.testing.expect(dialect.findBuiltin("verbatim_100i_0o") == null);
    try std.testing.expect(dialect.reservedIdentifier("verbatim_bad"));
}

test "cached dialect factories are stable until the Yul string repository resets" {
    try YulString.reset();
    const first = try strictAssemblyForEVM(EVMVersion.init(.London));
    const again = try strictAssemblyForEVM(EVMVersion.init(.London));
    const objects = try strictAssemblyForEVMObjects(EVMVersion.init(.London));
    try std.testing.expect(first == again);
    try std.testing.expect(first != objects);
    try std.testing.expect(!first.providesObjectAccess());
    try std.testing.expect(objects.providesObjectAccess());
    try YulString.reset();
}
