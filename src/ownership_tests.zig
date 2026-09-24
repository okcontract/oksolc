// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Focused ownership/failure tests without building the complete compiler facade.
const std = @import("std");
const AST = @import("libyul/ast.zig");
const Parser = @import("libyul/asm_parser.zig").Parser;
const Diagnostics = @import("liblangutil/diagnostics.zig");
const EVMDialect = @import("libyul/backends/evm/evm_dialect.zig").EVMDialect;
const NameCollector = @import("libyul/optimiser/name_collector.zig");
const NameDispenser = @import("libyul/optimiser/name_dispenser.zig").NameDispenser;
const YulName = @import("libyul/yul_name.zig").YulName;
const Context = @import("libyul/optimiser/optimiser_step.zig").OptimiserStepContext;
const Copier = @import("libyul/optimiser/ast_copier.zig").ASTCopier;
const Encoding = @import("libyul/ast_encoding.zig");

test "ownership test inventory" {
    _ = @import("libyul/exceptions.zig");
    _ = @import("libyul/backends/evm/evm_code_transform.zig");
    _ = @import("libyul/backends/evm/evm_object_compiler.zig");
    _ = @import("libyul/backends/evm/optimized_evm_code_transform.zig");
    _ = @import("libyul/optimiser/function_grouper.zig");
    _ = @import("libyul/optimiser/label_id_dispenser.zig");
    _ = @import("libyul/optimiser/function_specializer.zig");
    _ = @import("libyul/optimiser/ssa_reverser.zig");
    _ = @import("libyul/optimiser/full_inliner.zig");
    _ = @import("libyul/optimiser/block_flattener.zig");
    _ = @import("libyul/optimiser/for_loop_init_rewriter.zig");
    _ = @import("libyul/optimiser/optimizer_utilities.zig");
    _ = @import("libyul/optimiser/loop_invariant_code_motion.zig");
    _ = @import("libevmasm/linker_object.zig");
    _ = @import("libevmasm/expression_classes.zig");
    _ = @import("libevmasm/assembly.zig");
    _ = @import("libsolutil/json.zig");
    _ = @import("libsolutil/profiler.zig");
    _ = @import("libyul/yul_stack.zig");
    _ = @import("libyul/generated_object.zig");
    _ = @import("libsolidity/codegen/ir/ir_variable.zig");
    _ = @import("libsolidity/codegen/ir/ir_generation_context.zig");
    _ = @import("libsolidity/interface/artifact_output.zig");
    _ = @import("libyul/backends/evm/control_flow_graph_builder.zig");
}

test "function grouper transfers partition owners across allocation failures" {
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, .current(), true);
    defer dialect.deinit();
    const cases = .{
        "{}",
        "{ let x := \"code\" pop(x) { pop(2) } }",
        "{ function f(a) -> r { r := add(a, 1) } function g(b) { pop(b) } }",
        "{ function f() { pop(\"f\") } pop(1) function g() { pop(\"g\") } function h() {} }",
        "{ pop(1) function f() { pop(\"f\") } let x := 2 pop(x) { pop(3) } }",
        "{ function f() { pop(\"f\") } pop(1) function g() { pop(\"g\") } pop(2) }",
        "{ { pop(1) } function f() { pop(\"f\") } }",
    };
    inline for (cases) |source| {
        var reporter = Diagnostics.ErrorReporter.init(allocator);
        defer reporter.deinit();
        var ast = (try Parser.parseSource(allocator, source, "grouping-ownership.yul", &reporter, dialect.dialect(), .{})).?;
        defer ast.deinit();
        try checkPassOwnership(@import("libyul/optimiser/function_grouper.zig").FunctionGrouper, &ast);
    }
}

test "optimizer debug snapshots have one owner across allocation failures" {
    const Suite = @import("libyul/optimiser/suite.zig").OptimiserSuite;
    const allocator = std.testing.allocator;
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var source = (try Parser.parseSource(allocator, "{ { { let x := 1 pop(x) } } }", "debug-snapshot.yul", &reporter, .{}, .{})).?;
    defer source.deinit();
    const Check = struct {
        fn run(failing: std.mem.Allocator, original: *const AST.AST) !void {
            var copier = Copier.init(failing);
            var ast = try copier.translateBlock(original.root());
            defer ast.deinit(failing);
            var reserved: NameCollector.NameSet = .{};
            defer reserved.deinit(failing);
            var dispenser = try NameDispenser.initFromAst(failing, .{}, &ast, &reserved);
            defer dispenser.deinit();
            var context: Context = .{
                .dialect = .{},
                .dispenser = &dispenser,
                .reserved_identifiers = &reserved,
            };
            var suite = Suite.init(&context, .print_changes);
            try suite.runSequenceNames(&.{ "BlockFlattener", "BlockFlattener" }, &ast);
            try std.testing.expectEqual(@as(usize, 2), ast.statements.items[0].block.statements.items.len);
        }
    };
    try std.testing.checkAllAllocationFailures(allocator, Check.run, .{&source});
}

test "transient optimizer analysis stays within pass scratch lifetime" {
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, .current(), true);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var source = (try Parser.parseSource(allocator,
        \\{ let x_1 := 1 pop(f_1(x_1)) pop(g_2(x_1))
        \\  function f_1(a_1) -> r_1 {
        \\    if a_1 { return(0, 0) } a_1 := 0
        \\    switch a_1 case 1 { a_1 := 1 r_1 := a_1 }
        \\      default { r_1 := 2 }
        \\    leave r_1 := 3
        \\  }
        \\  function g_2(a_2) -> r_2 {
        \\    if a_2 { return(0, 0) } a_2 := 0
        \\    switch a_2 case 1 { a_2 := 1 r_2 := a_2 }
        \\      default { r_2 := 2 }
        \\    leave r_2 := 3
        \\  }
        \\}
    , "transient-ownership.yul", &reporter, dialect.dialect(), .{})).?;
    defer source.deinit();
    inline for (.{
        @import("libyul/optimiser/conditional_simplifier.zig").ConditionalSimplifier,
        @import("libyul/optimiser/conditional_unsimplifier.zig").ConditionalUnsimplifier,
        @import("libyul/optimiser/dead_code_eliminator.zig").DeadCodeEliminator,
        @import("libyul/optimiser/equivalent_function_combiner.zig").EquivalentFunctionCombiner,
        @import("libyul/optimiser/var_name_cleaner.zig").VarNameCleaner,
    }) |Pass| {
        try checkPassOwnership(Pass, &source);
    }
}

test "name simplifier scratch buffers preserve reserved names and collisions" {
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, .current(), true);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var source = (try Parser.parseSource(allocator,
        \\{ let foo := 1 let foo_123 := 2 let a_123 := 3
        \\  let tuple_add := 4 let tuple_bar_memory_ptr_123 := 5
        \\  pop(foo) pop(foo_123) pop(a_123) pop(tuple_add)
        \\  pop(tuple_bar_memory_ptr_123)
        \\  function abi_encode_tuple_x_to_y_1(tuple_arg_123) -> tuple_result_456 {
        \\    tuple_result_456 := tuple_arg_123
        \\  }
        \\  pop(abi_encode_tuple_x_to_y_1(foo))
        \\}
    , "name-scratch.yul", &reporter, dialect.dialect(), .{})).?;
    defer source.deinit();
    try checkPassOwnership(@import("libyul/optimiser/name_simplifier.zig").NameSimplifier, &source);
}

test "block flattener preserves flat buffers and moves nested owners safely" {
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, .current(), true);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    const Pass = @import("libyul/optimiser/block_flattener.zig").BlockFlattener;
    var source = (try Parser.parseSource(allocator,
        \\{ { let x := 1 if x { { pop(x) } }
        \\    switch x case 1 { { pop(x) } } default { pop(2) }
        \\    for { let i := 0 } lt(i, 2) { { i := add(i, 1) } } {
        \\      { if i { continue } break }
        \\    }
        \\    { { pop(f(x)) } }
        \\  }
        \\  function f(a) -> r { { r := a } }
        \\}
    , "flatten-ownership.yul", &reporter, dialect.dialect(), .{})).?;
    defer source.deinit();
    try checkPassOwnership(Pass, &source);

    var copier = Copier.init(allocator);
    var flat = try copier.translateBlock(source.root());
    defer flat.deinit(allocator);
    try Pass.apply(allocator, &flat);
    const hash = try Encoding.hashBlock(&flat);
    const statements = flat.statements.items[0].block.statements.items.ptr;
    const function_body = flat.statements.items[1].function_definition.body.statements.items.ptr;
    var rejecting = std.testing.FailingAllocator.init(allocator, .{ .fail_index = 0 });
    try Pass.apply(rejecting.allocator(), &flat);
    try std.testing.expect(!rejecting.has_induced_failure);
    try std.testing.expectEqual(statements, flat.statements.items[0].block.statements.items.ptr);
    try std.testing.expectEqual(function_body, flat.statements.items[1].function_definition.body.statements.items.ptr);
    try std.testing.expectEqualDeep(hash, try Encoding.hashBlock(&flat));
}

test "for-loop init rewriter transfers nested initializers through allocation failures" {
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, .current(), true);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var source = (try Parser.parseSource(allocator,
        \\{ let before := 1
        \\  for { let i := 0
        \\    for { let j := 0 } lt(j, 2) { j := add(j, 1) } { pop(j) }
        \\    let limit := 2
        \\  } lt(i, limit) { i := add(i, 1) } {
        \\    for { let body_index := 0 } lt(body_index, 2)
        \\      { body_index := add(body_index, 1) } { pop(body_index) }
        \\  }
        \\  if before { for { let branch := 2 } branch { branch := sub(branch, 1) } {} }
        \\  function f(x) -> r {
        \\    for { let local := x } local { local := sub(local, 1) } { r := local }
        \\  }
        \\  pop(f(before))
        \\}
    , "loop-init-ownership.yul", &reporter, dialect.dialect(), .{})).?;
    defer source.deinit();
    const CheckedPass = struct {
        pub const name = "ForLoopInitRewriter";

        pub fn run(context: *Context, ast: *AST.Block) !void {
            const initializer = ast.statements.items[1].for_loop.pre.statements.items[0].variable_declaration.value;
            const condition = ast.statements.items[1].for_loop.condition;
            try @import("libyul/optimiser/for_loop_init_rewriter.zig").ForLoopInitRewriter.run(context, ast);
            try std.testing.expectEqual(@as(usize, 9), ast.statements.items.len);
            try std.testing.expectEqual(initializer, ast.statements.items[1].variable_declaration.value);
            try std.testing.expectEqual(condition, ast.statements.items[5].for_loop.condition);
            try std.testing.expectEqual(@as(usize, 0), ast.statements.items[5].for_loop.pre.statements.items.len);
            try std.testing.expectEqual(@as(usize, 2), ast.statements.items[5].for_loop.body.statements.items.len);
        }
    };
    try checkPassOwnership(CheckedPass, &source);

    const Pass = @import("libyul/optimiser/for_loop_init_rewriter.zig").ForLoopInitRewriter;
    var copier = Copier.init(allocator);
    var rewritten = try copier.translateBlock(source.root());
    defer rewritten.deinit(allocator);
    try Pass.apply(allocator, &rewritten);
    const hash = try Encoding.hashBlock(&rewritten);
    const root_buffer = rewritten.statements.items.ptr;
    const loop_buffer = rewritten.statements.items[5].for_loop.body.statements.items.ptr;
    const function_buffer = rewritten.statements.items[7].function_definition.body.statements.items.ptr;
    var rejecting = std.testing.FailingAllocator.init(allocator, .{ .fail_index = 0, .resize_fail_index = 0 });
    try Pass.apply(rejecting.allocator(), &rewritten);
    try std.testing.expect(!rejecting.has_induced_failure);
    try std.testing.expectEqual(root_buffer, rewritten.statements.items.ptr);
    try std.testing.expectEqual(loop_buffer, rewritten.statements.items[5].for_loop.body.statements.items.ptr);
    try std.testing.expectEqual(function_buffer, rewritten.statements.items[7].function_definition.body.statements.items.ptr);
    try std.testing.expectEqualDeep(hash, try Encoding.hashBlock(&rewritten));
}

test "for-loop init rewriter reserves before moving and reuses sufficient capacity" {
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, .current(), true);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var source = (try Parser.parseSource(allocator,
        \\{ let before := 1
        \\  for { let i := 0 let limit := 2 } lt(i, limit)
        \\    { i := add(i, 1) } { pop(i) }
        \\  pop(before)
        \\  for {} 0 {} {}
        \\}
    , "loop-init-capacity.yul", &reporter, dialect.dialect(), .{})).?;
    defer source.deinit();
    const Pass = @import("libyul/optimiser/for_loop_init_rewriter.zig").ForLoopInitRewriter;
    const ast = &source.root_block;
    ast.statements.shrinkAndFree(allocator, ast.statements.items.len);
    try ast.statements.items[3].for_loop.pre.statements.ensureTotalCapacityPrecise(allocator, 1);
    const hash = try Encoding.hashBlock(ast);
    var failed_growth = std.testing.FailingAllocator.init(allocator, .{ .fail_index = 0, .resize_fail_index = 0 });
    try std.testing.expectError(error.OutOfMemory, Pass.apply(failed_growth.allocator(), ast));
    try std.testing.expectEqualDeep(hash, try Encoding.hashBlock(ast));
    try std.testing.expectEqual(@as(usize, 0), ast.statements.items[3].for_loop.pre.statements.capacity);

    try ast.statements.ensureTotalCapacityPrecise(allocator, 6);
    const root_buffer = ast.statements.items.ptr;
    const body_buffer = ast.statements.items[1].for_loop.body.statements.items.ptr;
    const condition = ast.statements.items[1].for_loop.condition;
    const initializer = ast.statements.items[1].for_loop.pre.statements.items[0].variable_declaration.value;
    var rejecting = std.testing.FailingAllocator.init(allocator, .{ .fail_index = 0, .resize_fail_index = 0 });
    try Pass.apply(rejecting.allocator(), ast);
    try std.testing.expect(!rejecting.has_induced_failure);
    try std.testing.expectEqual(@as(usize, 6), ast.statements.items.len);
    try std.testing.expectEqual(root_buffer, ast.statements.items.ptr);
    try std.testing.expectEqual(body_buffer, ast.statements.items[3].for_loop.body.statements.items.ptr);
    try std.testing.expectEqual(condition, ast.statements.items[3].for_loop.condition);
    try std.testing.expectEqual(initializer, ast.statements.items[1].variable_declaration.value);
    try std.testing.expectEqual(@as(usize, 0), ast.statements.items[3].for_loop.pre.statements.capacity);
    var empty: AST.Block = .{};
    try Pass.apply(rejecting.allocator(), &empty);
    try std.testing.expect(!rejecting.has_induced_failure);
}

test "function specializer fills reserved slots without aliasing original bodies" {
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, .current(), true);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var source = (try Parser.parseSource(allocator,
        \\{ function first(a) -> r { r := add(a, 1) }
        \\  function second(b) -> s { s := first(b) }
        \\  let x := second(2)
        \\  pop(first(3))
        \\  pop(first(x))
        \\}
    , "specializer-slots.yul", &reporter, dialect.dialect(), .{})).?;
    defer source.deinit();
    const CheckedPass = struct {
        pub const name = "FunctionSpecializer";

        pub fn run(context: *Context, ast: *AST.Block) !void {
            try ast.statements.ensureTotalCapacityPrecise(context.dispenser.allocator, 7);
            const root_buffer = ast.statements.items.ptr;
            const first_body = ast.statements.items[0].function_definition.body;
            const second_body = ast.statements.items[1].function_definition.body;
            const first_hash = try Encoding.hashBlock(&first_body);
            const second_hash = try Encoding.hashBlock(&second_body);
            try @import("libyul/optimiser/function_specializer.zig").FunctionSpecializer.run(context, ast);
            try std.testing.expectEqual(root_buffer, ast.statements.items.ptr);
            try std.testing.expectEqual(@as(usize, 7), ast.statements.items.len);
            try std.testing.expectEqual(first_body.statements.items.ptr, ast.statements.items[1].function_definition.body.statements.items.ptr);
            try std.testing.expectEqual(second_body.statements.items.ptr, ast.statements.items[3].function_definition.body.statements.items.ptr);
            try std.testing.expectEqualDeep(first_hash, try Encoding.hashBlock(&ast.statements.items[1].function_definition.body));
            try std.testing.expectEqualDeep(second_hash, try Encoding.hashBlock(&ast.statements.items[3].function_definition.body));
            for ([_]usize{ 0, 2 }) |index| {
                const copy = &ast.statements.items[index].function_definition.body;
                const original = &ast.statements.items[index + 1].function_definition.body;
                try std.testing.expectEqual(@as(usize, 2), copy.statements.items.len);
                try std.testing.expect(copy.statements.items[1].assignment.value != original.statements.items[0].assignment.value);
            }
        }
    };
    try checkPassOwnership(CheckedPass, &source);
}

test "function specializer preserves buffers without AST allocation when no copies are needed" {
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, .current(), true);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var source = (try Parser.parseSource(
        allocator,
        "{ { let x := calldatasize() pop(f(x)) } function f(a) -> r { r := add(a, 1) } }",
        "specializer-unchanged.yul",
        &reporter,
        dialect.dialect(),
        .{},
    )).?;
    defer source.deinit();
    var reserved: NameCollector.NameSet = .{};
    defer reserved.deinit(allocator);
    var dispenser = try NameDispenser.initFromAst(allocator, dialect.dialect(), source.root(), &reserved);
    defer dispenser.deinit();
    var scratch = std.heap.ArenaAllocator.init(allocator);
    defer scratch.deinit();
    var context: Context = .{
        .dialect = dialect.dialect(),
        .dispenser = &dispenser,
        .reserved_identifiers = &reserved,
        .scratch_arena = &scratch,
    };
    const hash = try Encoding.hashBlock(source.root());
    const root_buffer = source.root().statements.items.ptr;
    const body_buffer = source.root().statements.items[1].function_definition.body.statements.items.ptr;
    var rejecting = std.testing.FailingAllocator.init(allocator, .{ .fail_index = 0, .resize_fail_index = 0 });
    dispenser.allocator = rejecting.allocator();
    defer dispenser.allocator = allocator;
    try @import("libyul/optimiser/function_specializer.zig").FunctionSpecializer.run(&context, &source.root_block);
    _ = scratch.reset(.free_all);
    try std.testing.expect(!rejecting.has_induced_failure);
    try std.testing.expectEqual(root_buffer, source.root().statements.items.ptr);
    try std.testing.expectEqual(body_buffer, source.root().statements.items[1].function_definition.body.statements.items.ptr);
    try std.testing.expectEqualDeep(hash, try Encoding.hashBlock(source.root()));
}

test "expression joiner retains moved values beyond scratch lifetime" {
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, .current(), true);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var source = (try Parser.parseSource(allocator,
        \\{ let a := 1 let b := 2 let sum := add(a, b) pop(sum)
        \\  if calldatasize() { let c := 3 pop(c) }
        \\  switch calldatasize() case 0 { let d := 4 pop(d) }
        \\    default { let e := 5 pop(e) }
        \\  for { let i := 0 } lt(i, 2) { i := add(i, 1) } {
        \\    let inner := add(i, 1) pop(inner)
        \\  }
        \\  function f(x_1) -> r_1 { let t := add(x_1, 1) r_1 := t }
        \\  pop(f(7))
        \\}
    , "join-ownership.yul", &reporter, dialect.dialect(), .{})).?;
    defer source.deinit();
    try checkPassOwnership(@import("libyul/optimiser/expression_joiner.zig").ExpressionJoiner, &source);
}

test "full inliner owns partially appended nested bodies on allocation failure" {
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, .current(), true);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var source = (try Parser.parseSource(allocator,
        \\{ { let outer := 3 let result := f(outer) pop(result) }
        \\  function f(arg) -> ret {
        \\    let first := add(arg, 1)
        \\    if arg { let inner := add(first, 2) mstore(0, inner) }
        \\    switch arg case 0 { ret := first }
        \\      default { ret := add(first, 3) }
        \\    for { let index := 0 } lt(index, 2)
        \\      { index := add(index, 1) } { ret := add(ret, index) }
        \\    ret := add(ret, 4)
        \\  }
        \\}
    , "inliner-nested-body.yul", &reporter, dialect.dialect(), .{})).?;
    defer source.deinit();
    const CheckedPass = struct {
        pub const name = "FullInliner";

        pub fn run(context: *Context, ast: *AST.Block) !void {
            const callee = &ast.statements.items[1].function_definition.body;
            const callee_hash = try Encoding.hashBlock(callee);
            const callee_statements = callee.statements.items.ptr;
            const callee_arguments = callee.statements.items[0].variable_declaration.value.?.function_call.arguments.items.ptr;
            try @import("libyul/optimiser/full_inliner.zig").FullInliner.run(context, ast);
            const inlined = ast.statements.items[0].block.statements.items;
            try std.testing.expectEqual(@as(usize, 10), inlined.len);
            try std.testing.expectEqual(callee_statements, callee.statements.items.ptr);
            try std.testing.expectEqualDeep(callee_hash, try Encoding.hashBlock(callee));
            try std.testing.expect(callee_arguments != inlined[3].variable_declaration.value.?.function_call.arguments.items.ptr);
        }
    };
    try checkPassOwnership(CheckedPass, &source);
}

test "full inliner splices empty singleton and growing bodies across allocation failures" {
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, .current(), false);
    defer dialect.deinit();
    inline for (.{ "", "pop(0x03)", "pop(0x03) pop(0x04)" }) |body| {
        var reporter = Diagnostics.ErrorReporter.init(allocator);
        defer reporter.deinit();
        var source = (try Parser.parseSource(
            allocator,
            "{ { f() pop(0x01) f() pop(0x02) f() } function f() { " ++ body ++ " } }",
            "inliner-splice.yul",
            &reporter,
            dialect.dialect(),
            .{},
        )).?;
        defer source.deinit();
        const Check = struct {
            fn run(failing: std.mem.Allocator, input: *const AST.AST, spare: usize, fit: bool) !void {
                var copier = Copier.init(failing);
                var ast = try copier.translateBlock(input.root());
                defer ast.deinit(failing);
                const body_items = input.root().statements.items[1].function_definition.body.statements.items;
                const final_len = 2 + 3 * body_items.len;
                const block = &ast.statements.items[0].block;
                const capacity = (if (fit) @max(block.statements.items.len, final_len) else block.statements.items.len) + spare;
                const storage = try failing.alloc(AST.Statement, capacity);
                const original_len = block.statements.items.len;
                @memcpy(storage[0..original_len], block.statements.items);
                block.statements.deinit(failing);
                block.statements = .{ .items = storage[0..original_len], .capacity = capacity };
                const first_payload = block.statements.items[1].expression_statement.expression.function_call.arguments.items[0].literal.value.string_value.?.ptr;
                const second_payload = block.statements.items[3].expression_statement.expression.function_call.arguments.items[0].literal.value.string_value.?.ptr;
                var reserved: NameCollector.NameSet = .{};
                defer reserved.deinit(failing);
                var dispenser = try NameDispenser.initFromAst(failing, input.dialect().*, &ast, &reserved);
                defer dispenser.deinit();
                var context: Context = .{
                    .dialect = input.dialect().*,
                    .dispenser = &dispenser,
                    .reserved_identifiers = &reserved,
                };
                try @import("libyul/optimiser/full_inliner.zig").FullInliner.run(&context, &ast);
                try std.testing.expectEqual(final_len, block.statements.items.len);
                if (capacity >= final_len + @intFromBool(body_items.len != 0)) {
                    try std.testing.expectEqual(storage.ptr, block.statements.items.ptr);
                    try std.testing.expectEqual(capacity, block.statements.capacity);
                }
                var expected_items: [8]AST.Statement = undefined;
                var next: usize = 0;
                for (input.root().statements.items[0].block.statements.items) |statement| {
                    if (statement.expression_statement.expression.function_call.function_name == .identifier) {
                        for (body_items) |expected| {
                            expected_items[next] = expected;
                            next += 1;
                        }
                    } else {
                        expected_items[next] = statement;
                        next += 1;
                    }
                }
                try std.testing.expectEqual(final_len, next);
                var expected_block = input.root().statements.items[0].block;
                expected_block.statements = .{ .items = expected_items[0..next], .capacity = expected_items.len };
                var expected_statements = [_]AST.Statement{ .{ .block = expected_block }, input.root().statements.items[1] };
                var expected_root = input.root().*;
                expected_root.statements = .{ .items = &expected_statements, .capacity = expected_statements.len };
                try std.testing.expectEqualDeep(try Encoding.hashBlock(&expected_root), try Encoding.hashBlock(&ast));
                try std.testing.expectEqual(first_payload, block.statements.items[body_items.len].expression_statement.expression.function_call.arguments.items[0].literal.value.string_value.?.ptr);
                try std.testing.expectEqual(second_payload, block.statements.items[2 * body_items.len + 1].expression_statement.expression.function_call.arguments.items[0].literal.value.string_value.?.ptr);
            }
        };
        for ([_]usize{ 0, 4 }) |spare| {
            try std.testing.checkAllAllocationFailures(allocator, Check.run, .{ &source, spare, true });
            try std.testing.checkAllAllocationFailures(allocator, Check.run, .{ &source, spare, false });
        }
    }
}

test "structural simplifier releases detached payloads on allocation failure" {
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, .current(), true);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var source = (try Parser.parseSource(allocator,
        \\{ if 1 { let x := 1 let y := add(x, 2)
        \\    if 1 { mstore(0, y) mstore(32, x) }
        \\  }
        \\  switch 2 case 1 { let c := 3 pop(c) }
        \\    case 2 { if 1 { let c := 4 pop(c) } }
        \\    default { let c := 5 pop(c) }
        \\  switch 9 case 0 { pop(10) } default { pop(11) }
        \\  switch 9 case 0 { pop(12) }
        \\  if 0 { let dead := add(1, 2) pop(dead) }
        \\  for { let i := 7 } 0 { i := add(i, 1) } { pop(i) }
        \\  pop(f(8))
        \\  function f(arg) -> result { if 1 { result := add(arg, 1) } }
        \\}
    , "structural-ownership.yul", &reporter, dialect.dialect(), .{})).?;
    defer source.deinit();
    try checkPassOwnership(@import("libyul/optimiser/structural_simplifier.zig").StructuralSimplifier, &source);
}

test "expression splitter retains nested prefixes beyond scratch lifetime" {
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, .current(), true);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var source = (try Parser.parseSource(allocator,
        \\{ { let outer := add(1, mul(2, 3))
        \\    mstore(add(outer, 4), f(add(5, 6)))
        \\    if eq(add(outer, 1), 8) { pop(mul(outer, 2)) }
        \\    switch add(outer, 2) case 0 { pop(add(outer, 3)) }
        \\      default { pop(mul(outer, 4)) }
        \\    for { let i := add(0, 1) } lt(i, add(outer, 2))
        \\      { i := add(i, add(1, 1)) } {
        \\      if eq(i, 3) { continue } pop(add(i, 4))
        \\    }
        \\    pop(memoryguard(64)) pop(linkersymbol("C.sol:Library"))
        \\  }
        \\  function f(arg) -> result { result := add(arg, mul(2, 3)) }
        \\}
    , "split-ownership.yul", &reporter, dialect.dialect(), .{})).?;
    defer source.deinit();
    try checkPassOwnership(@import("libyul/optimiser/expression_splitter.zig").ExpressionSplitter, &source);
}

test "loop-invariant promotion preserves owners beyond scratch lifetime" {
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, .current(), true);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var source = (try Parser.parseSource(allocator,
        \\{ { let outer := 1 let i := 0
        \\    for {} lt(i, 3) { let increment := 1 i := add(i, increment) } {
        \\      let fixed := add(outer, 2) let called := f(fixed)
        \\      let memory := mload(0) let dependent := add(memory, called)
        \\      mstore(0, dependent) let varying := add(i, 1) pop(varying)
        \\    }
        \\  }
        \\  function f(arg) -> result { result := add(arg, 1) }
        \\}
    , "loop-ownership.yul", &reporter, dialect.dialect(), .{})).?;
    defer source.deinit();
    try checkPassOwnership(@import("libyul/optimiser/loop_invariant_code_motion.zig").LoopInvariantCodeMotion, &source);
}

test "SSA transforms preserve transferred nodes through allocation failures" {
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, .current(), true);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var source = (try Parser.parseSource(allocator,
        \\{ let x := 1 let y := 2 let fixed := 7 let vacant
        \\  let tuple_left, tuple_right := pair()
        \\  tuple_left, tuple_right := pair() vacant := 9
        \\  { let inner := 1 inner := 2 pop(inner) }
        \\  if calldatasize() { x := 3 y := 4 }
        \\  for {} lt(x, 10) { x := add(x, 1) } {
        \\    if y { y := add(y, 1) continue } break
        \\  }
        \\  pop(f(x, y)) pop(fixed) pop(vacant) pop(tuple_left) pop(tuple_right)
        \\  function pair() -> first, second { first := 1 second := 2 }
        \\  function f(a, b) -> r {
        \\    a := add(a, b)
        \\    switch b case 0 { b := a } default { a := b }
        \\    r := a
        \\  }
        \\}
    , "ssa-ownership.yul", &reporter, dialect.dialect(), .{})).?;
    defer source.deinit();
    try checkPassOwnership(@import("libyul/optimiser/ssa_transform.zig").SSATransform, &source);
}

fn checkPassOwnership(comptime Pass: type, input: *const AST.AST) !void {
    const Hash = @TypeOf(try Encoding.hashBlock(input.root()));
    const Check = struct {
        fn run(failing: std.mem.Allocator, original: *const AST.AST, separate_scratch: bool, expected: *?Hash) !void {
            var copier = Copier.init(failing);
            var ast = try copier.translateBlock(original.root());
            defer ast.deinit(failing);
            var reserved: NameCollector.NameSet = .{};
            defer reserved.deinit(failing);
            _ = try reserved.insert(failing, try YulName.init("a"));
            var dispenser = try NameDispenser.initFromAst(failing, original.dialect().*, &ast, &reserved);
            defer dispenser.deinit();
            var scratch = std.heap.ArenaAllocator.init(failing);
            defer scratch.deinit();
            var cache = @import("libyul/optimiser/optimiser_step.zig").FunctionAnalysisCache.init(failing);
            defer cache.deinit();
            var context: Context = .{
                .dialect = original.dialect().*,
                .dispenser = &dispenser,
                .reserved_identifiers = &reserved,
                .scratch_arena = if (separate_scratch) &scratch else null,
                .function_analysis_cache = if (separate_scratch) &cache else null,
            };
            if (separate_scratch) _ = try cache.get(scratch.allocator(), context.dialect, &ast);
            try Pass.run(&context, &ast);
            cache.invalidate();
            _ = scratch.reset(.free_all);
            const hash = try Encoding.hashBlock(&ast);
            const Analysis = @import("libyul/asm_analysis.zig");
            const Structure = @import("libyul/object.zig").Structure;
            var shape = try Structure.init(failing, "");
            defer shape.deinit();
            var info = try Analysis.analyzeStrictBlock(failing, original.dialect().*, &ast, &shape, .{});
            defer info.deinit();
            if (expected.*) |value|
                try std.testing.expectEqualDeep(value, hash)
            else
                expected.* = hash;
        }
    };
    // All retained nodes must be destructible with the AST allocator after
    // scratch destruction, including when analysis or publication fails.
    var expected: ?Hash = null;
    try std.testing.checkAllAllocationFailures(std.testing.allocator, Check.run, .{ input, false, &expected });
    try std.testing.checkAllAllocationFailures(std.testing.allocator, Check.run, .{ input, true, &expected });
}

test "unused store passes preserve ownership across branches and loop exits" {
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, .current(), true);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var source = (try Parser.parseSource(allocator,
        \\{ let p := 0 let v := 1 let q := 32 let a := 0
        \\  a := 1 mstore(p, v) sstore(p, v)
        \\  if calldatasize() { a := 2 mstore(q, v) }
        \\  switch calldatasize()
        \\    case 0 { a := 3 sstore(q, v) }
        \\    case 1 { a := 4 mstore(p, a) }
        \\    default { a := 5 mstore(q, a) }
        \\  switch calldatasize() case 2 { a := 6 mstore(p, a) }
        \\  for {} calldatasize() { a := 7 mstore(q, v) } {
        \\    if a { a := 8 sstore(p, a) continue }
        \\    for {} calldatasize() {} {
        \\      a := 9 mstore(p, v) if calldatasize() { continue } break
        \\    }
        \\    a := 10 sstore(q, a) if calldatasize() { break }
        \\  }
        \\  pop(a) pop(mload(p)) pop(sload(q)) pop(f(v))
        \\  function f(x) -> r {
        \\    r := 1 mstore(x, r)
        \\    if x { r := 2 leave }
        \\    r := 3 mstore(x, r)
        \\  }
        \\}
    , "store-ownership.yul", &reporter, dialect.dialect(), .{})).?;
    defer source.deinit();
    inline for (.{
        @import("libyul/optimiser/unused_assign_eliminator.zig").UnusedAssignEliminator,
        @import("libyul/optimiser/unused_store_eliminator.zig").UnusedStoreEliminator,
        @import("libyul/optimiser/rematerialiser.zig").Rematerialiser,
        @import("libyul/optimiser/rematerialiser.zig").LiteralRematerialiser,
        @import("libyul/optimiser/load_resolver.zig").LoadResolver,
        @import("libyul/optimiser/equal_store_eliminator.zig").EqualStoreEliminator,
    }) |Pass| try checkPassOwnership(Pass, &source);
}

test "transient optimizer substitution and reordering preserve retained nodes" {
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, .current(), true);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var source = (try Parser.parseSource(allocator,
        \\{ let x := 0 let x_1 := 7 x := x_1 pop(x)
        \\  let y_1 := 8 let y := y_1 y := 9 pop(y)
        \\  pop(f(2)) pop(f(add(x, y))) pop(g(x))
        \\  function f(a_1) -> r_1 { r_1 := add(a_1, a_1) }
        \\  function g(a_2) -> r_2 { r_2 := f(a_2) }
        \\  function dead() { dead() }
        \\}
    , "substitution-ownership.yul", &reporter, dialect.dialect(), .{})).?;
    defer source.deinit();
    inline for (.{
        @import("libyul/optimiser/expression_inliner.zig").ExpressionInliner,
        @import("libyul/optimiser/ssa_reverser.zig").SSAReverser,
        @import("libyul/optimiser/circular_references_pruner.zig").CircularReferencesPruner,
    }) |Pass| try checkPassOwnership(Pass, &source);
}

test "unused parameter pruning keeps linking functions outside scratch storage" {
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, .current(), true);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var source = (try Parser.parseSource(allocator,
        \\{ let x, y := f(1, 2, 3) pop(x) pop(y) g(4, 5)
        \\  let z, w := none(6, 7) pop(z) pop(w)
        \\  function f(a_1, b_1, c_1) -> r_1, s_1 {
        \\    let t_1 := add(a_1, c_1) r_1 := add(t_1, 1)
        \\  }
        \\  function g(d_1, e_1) { sstore(d_1, 1) sstore(d_1, 2) }
        \\  function none(q_1, q_2) -> t_2, t_3 { pop(1) pop(2) }
        \\}
    , "parameter-ownership.yul", &reporter, dialect.dialect(), .{})).?;
    defer source.deinit();
    try checkPassOwnership(@import("libyul/optimiser/unused_function_parameter_pruner.zig").UnusedFunctionParameterPruner, &source);
}

test "SSA reverser retains unique owners across branches and allocation failures" {
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, .current(), true);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var source = (try Parser.parseSource(allocator,
        \\{ let x := 0 let y := 0
        \\  let first := add(x, 1) x := first
        \\  let second := add(x, 2) let z := second z := 3
        \\  if x { let inner := add(x, 3) y := inner }
        \\  for {} lt(x, 5) { let post := add(x, 1) x := post } {
        \\    switch y case 0 { let branch := add(y, 1) y := branch }
        \\    default { break }
        \\  }
        \\  pop(x) pop(y) pop(z) pop(g(x))
        \\  function g(a) -> r { let v := add(a, 1) r := v }
        \\}
    , "ssa-reversal-ownership.yul", &reporter, dialect.dialect(), .{})).?;
    defer source.deinit();
    try checkPassOwnership(@import("libyul/optimiser/ssa_reverser.zig").SSAReverser, &source);
}
