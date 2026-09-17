// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Optimizer-step registry, abbreviation grammar, fixed-point bracket
//! execution, and whole-object Yul optimization orchestration.

const std = @import("std");
const AST = @import("../ast.zig");
const AsmAnalysis = @import("../asm_analysis.zig");
const AsmPrinter = @import("../asm_printer.zig").AsmPrinter;
const ASTCopier = @import("ast_copier.zig").ASTCopier;
const BlockFlattener = @import("block_flattener.zig").BlockFlattener;
const CircularReferencesPruner = @import("circular_references_pruner.zig").CircularReferencesPruner;
const CommonSubexpressionEliminator = @import("common_subexpression_eliminator.zig").CommonSubexpressionEliminator;
const ConditionalSimplifier = @import("conditional_simplifier.zig").ConditionalSimplifier;
const ConditionalUnsimplifier = @import("conditional_unsimplifier.zig").ConditionalUnsimplifier;
const ConstantOptimiser = @import("../backends/evm/constant_optimiser.zig").ConstantOptimiser;
const ControlFlowSimplifier = @import("control_flow_simplifier.zig").ControlFlowSimplifier;
const DeadCodeEliminator = @import("dead_code_eliminator.zig").DeadCodeEliminator;
const Disambiguator = @import("disambiguator.zig").Disambiguator;
const EqualStoreEliminator = @import("equal_store_eliminator.zig").EqualStoreEliminator;
const EquivalentFunctionCombiner = @import("equivalent_function_combiner.zig").EquivalentFunctionCombiner;
const EVMDialectModule = @import("../backends/evm/evm_dialect.zig");
const EVMMetrics = @import("../backends/evm/evm_metrics.zig");
const ExpressionInliner = @import("expression_inliner.zig").ExpressionInliner;
const ExpressionJoiner = @import("expression_joiner.zig").ExpressionJoiner;
const ExpressionSimplifier = @import("expression_simplifier.zig").ExpressionSimplifier;
const ExpressionSplitter = @import("expression_splitter.zig").ExpressionSplitter;
const ForLoopConditionIntoBody = @import("for_loop_condition_into_body.zig").ForLoopConditionIntoBody;
const ForLoopConditionOutOfBody = @import("for_loop_condition_out_of_body.zig").ForLoopConditionOutOfBody;
const ForLoopInitRewriter = @import("for_loop_init_rewriter.zig").ForLoopInitRewriter;
const FullInliner = @import("full_inliner.zig").FullInliner;
const FunctionGrouper = @import("function_grouper.zig").FunctionGrouper;
const FunctionHoister = @import("function_hoister.zig").FunctionHoister;
const FunctionSpecializer = @import("function_specializer.zig").FunctionSpecializer;
const LoadResolver = @import("load_resolver.zig").LoadResolver;
const LoopInvariantCodeMotion = @import("loop_invariant_code_motion.zig").LoopInvariantCodeMotion;
const Metrics = @import("metrics.zig");
const NameCollector = @import("name_collector.zig");
const NameDispenser = @import("name_dispenser.zig").NameDispenser;
const NameSimplifier = @import("name_simplifier.zig").NameSimplifier;
const Object = @import("../object.zig").Object;
const OptimiserStepModule = @import("optimiser_step.zig");
const FunctionAnalysisCache = OptimiserStepModule.FunctionAnalysisCache;
const OptimiserStepContext = OptimiserStepModule.OptimiserStepContext;
const ProfilerModule = @import("../../libsolutil/profiler.zig");
const Profiler = ProfilerModule.Profiler;
const RematerialiserModule = @import("rematerialiser.zig");
const SSAReverser = @import("ssa_reverser.zig").SSAReverser;
const SSATransform = @import("ssa_transform.zig").SSATransform;
const StackCompressor = @import("stack_compressor.zig").StackCompressor;
const StackLimitEvader = @import("stack_limit_evader.zig").StackLimitEvader;
const StructuralSimplifier = @import("structural_simplifier.zig").StructuralSimplifier;
const SyntacticalEquality = @import("syntactical_equality.zig").SyntacticallyEqual;
const UnusedAssignEliminator = @import("unused_assign_eliminator.zig").UnusedAssignEliminator;
const UnusedFunctionParameterPruner = @import("unused_function_parameter_pruner.zig").UnusedFunctionParameterPruner;
const UnusedPruner = @import("unused_pruner.zig").UnusedPruner;
const UnusedStoreEliminator = @import("unused_store_eliminator.zig").UnusedStoreEliminator;
const VarDeclInitializer = @import("var_decl_initializer.zig").VarDeclInitializer;
const VarNameCleaner = @import("var_name_cleaner.zig").VarNameCleaner;

pub const max_rounds: usize = 12;
pub const non_step_abbreviations = " \n[]:";

pub const Debug = enum {
    none,
    print_step,
    print_changes,
};

pub const StepDescriptor = struct {
    name: []const u8,
    abbreviation: u8,
    run: *const fn (*OptimiserStepContext, *AST.Block) anyerror!void,
    invalid_in_current_environment: *const fn () ?[]const u8,
    preserves_function_analysis: bool,
};

fn stepDescriptor(comptime Step: type, comptime abbreviation: u8) StepDescriptor {
    const Adapter = struct {
        fn run(context: *OptimiserStepContext, ast: *AST.Block) anyerror!void {
            return Step.run(context, ast);
        }

        fn invalid() ?[]const u8 {
            if (@hasDecl(Step, "invalidInCurrentEnvironment"))
                return Step.invalidInCurrentEnvironment();
            return null;
        }
    };
    return .{
        .name = Step.name,
        .abbreviation = abbreviation,
        .run = Adapter.run,
        .invalid_in_current_environment = Adapter.invalid,
        .preserves_function_analysis = if (@hasDecl(Step, "preserves_function_analysis"))
            Step.preserves_function_analysis
        else
            false,
    };
}

const step_descriptors = [_]StepDescriptor{
    stepDescriptor(BlockFlattener, 'f'),
    stepDescriptor(CircularReferencesPruner, 'l'),
    stepDescriptor(CommonSubexpressionEliminator, 'c'),
    stepDescriptor(ConditionalSimplifier, 'C'),
    stepDescriptor(ConditionalUnsimplifier, 'U'),
    stepDescriptor(ControlFlowSimplifier, 'n'),
    stepDescriptor(DeadCodeEliminator, 'D'),
    stepDescriptor(EqualStoreEliminator, 'E'),
    stepDescriptor(EquivalentFunctionCombiner, 'v'),
    stepDescriptor(ExpressionInliner, 'e'),
    stepDescriptor(ExpressionJoiner, 'j'),
    stepDescriptor(ExpressionSimplifier, 's'),
    stepDescriptor(ExpressionSplitter, 'x'),
    stepDescriptor(ForLoopConditionIntoBody, 'I'),
    stepDescriptor(ForLoopConditionOutOfBody, 'O'),
    stepDescriptor(ForLoopInitRewriter, 'o'),
    stepDescriptor(FullInliner, 'i'),
    stepDescriptor(FunctionGrouper, 'g'),
    stepDescriptor(FunctionHoister, 'h'),
    stepDescriptor(FunctionSpecializer, 'F'),
    stepDescriptor(RematerialiserModule.LiteralRematerialiser, 'T'),
    stepDescriptor(LoadResolver, 'L'),
    stepDescriptor(LoopInvariantCodeMotion, 'M'),
    stepDescriptor(UnusedAssignEliminator, 'r'),
    stepDescriptor(UnusedStoreEliminator, 'S'),
    stepDescriptor(RematerialiserModule.Rematerialiser, 'm'),
    stepDescriptor(SSAReverser, 'V'),
    stepDescriptor(SSATransform, 'a'),
    stepDescriptor(StructuralSimplifier, 't'),
    stepDescriptor(UnusedFunctionParameterPruner, 'p'),
    stepDescriptor(UnusedPruner, 'u'),
    stepDescriptor(VarDeclInitializer, 'd'),
};

pub const OptimiserSuite = struct {
    context: *OptimiserStepContext,
    debug: Debug = .none,
    profiler: ?*Profiler = null,

    pub fn init(context: *OptimiserStepContext, debug: Debug) OptimiserSuite {
        return .{ .context = context, .debug = debug };
    }

    pub fn allSteps() []const StepDescriptor {
        return &step_descriptors;
    }

    pub fn stepForAbbreviation(abbreviation: u8) ?*const StepDescriptor {
        for (&step_descriptors) |*step|
            if (step.abbreviation == abbreviation) return step;
        return null;
    }

    pub fn stepForName(name: []const u8) ?*const StepDescriptor {
        for (&step_descriptors) |*step|
            if (std.mem.eql(u8, step.name, name)) return step;
        return null;
    }

    pub fn validateSequence(sequence: []const u8) !void {
        var nesting_level: i16 = 0;
        var colon_delimiters: usize = 0;
        for (sequence) |abbreviation| switch (abbreviation) {
            ' ', '\n' => {},
            '[' => {
                if (nesting_level == std.math.maxInt(i8))
                    return error.OptimizerBracketsNestedTooDeep;
                nesting_level += 1;
            },
            ']' => {
                nesting_level -= 1;
                if (nesting_level < 0) return error.UnbalancedOptimizerBrackets;
            },
            ':' => {
                colon_delimiters += 1;
                if (nesting_level != 0) return error.CleanupDelimiterInsideBrackets;
                if (colon_delimiters > 1) return error.TooManyCleanupDelimiters;
            },
            else => {
                const step = stepForAbbreviation(abbreviation) orelse
                    return error.InvalidOptimizerStep;
                if (step.invalid_in_current_environment() != null)
                    return error.OptimizerStepInvalidInEnvironment;
            },
        };
        if (nesting_level != 0) return error.UnbalancedOptimizerBrackets;
    }

    pub fn isEmptyOptimizerSequence(sequence: []const u8) bool {
        var colons: usize = 0;
        for (sequence) |character| switch (character) {
            ':' => colons += 1,
            ' ', '\n' => {},
            else => return false,
        };
        return colons == 1;
    }

    pub fn runSequence(
        self: *OptimiserSuite,
        sequence: []const u8,
        ast: *AST.Block,
        repeat_until_stable: bool,
    ) anyerror!void {
        try validateSequence(sequence);
        var code_size = if (repeat_until_stable)
            Metrics.CodeSize.codeSizeIncludingFunctions(ast, .{})
        else
            0;
        const collect_rounds = repeat_until_stable and self.context.profiler != null;
        var rounds: usize = 0;
        for (0..max_rounds) |_| {
            if (collect_rounds) rounds += 1;
            try self.runStructuredSequence(sequence, ast);
            if (!repeat_until_stable) break;
            const new_size = Metrics.CodeSize.codeSizeIncludingFunctions(ast, .{});
            if (new_size == code_size) break;
            code_size = new_size;
        }
        if (collect_rounds)
            self.context.recordCounter("Optimizer fixed-point rounds", @intCast(rounds));
    }

    pub fn runSequenceNames(
        self: *OptimiserSuite,
        names: []const []const u8,
        ast: *AST.Block,
    ) anyerror!void {
        var copy: ?AST.Block = null;
        defer if (copy) |*block| block.deinit(self.context.dispenser.allocator);
        if (self.debug == .print_changes) {
            var copier = ASTCopier.init(self.context.dispenser.allocator);
            copy = try copier.translateBlock(ast);
        }

        for (names) |name| {
            const step = stepForName(name) orelse return error.UnknownOptimizerStepName;
            if (self.debug == .print_step)
                std.debug.print("Running {s}\n", .{step.name});
            try self.runStep(step, ast);
            if (self.debug == .print_changes) {
                var equality = SyntacticalEquality.init(self.context.dispenser.allocator);
                defer equality.deinit();
                if (try equality.block(ast, &copy.?)) {
                    std.debug.print("== Running {s} did not cause changes.\n", .{step.name});
                } else {
                    std.debug.print("== Running {s} changed the AST.\n", .{step.name});
                    var printer = AsmPrinter.init(
                        self.context.dispenser.allocator,
                        self.context.dialect,
                        &.{},
                        .{},
                        null,
                    );
                    const rendered = try printer.renderBlock(ast);
                    defer self.context.dispenser.allocator.free(rendered);
                    std.debug.print("{s}\n", .{rendered});
                    copy.?.deinit(self.context.dispenser.allocator);
                    var copier = ASTCopier.init(self.context.dispenser.allocator);
                    copy = try copier.translateBlock(ast);
                }
            }
        }
    }

    fn runStructuredSequence(
        self: *OptimiserSuite,
        sequence: []const u8,
        ast: *AST.Block,
    ) anyerror!void {
        var cursor: usize = 0;
        while (cursor < sequence.len) {
            var opening = cursor;
            while (opening < sequence.len and sequence[opening] != '[') : (opening += 1) {}
            if (opening > cursor) try self.runPlainSequence(sequence[cursor..opening], ast);
            if (opening == sequence.len) return;

            var nesting: usize = 1;
            var closing = opening + 1;
            while (closing < sequence.len and nesting != 0) : (closing += 1) switch (sequence[closing]) {
                '[' => nesting += 1,
                ']' => nesting -= 1,
                else => {},
            };
            if (nesting != 0) return error.UnbalancedOptimizerBrackets;
            const content_end = closing - 1;
            if (content_end > opening + 1)
                try self.runSequence(sequence[opening + 1 .. content_end], ast, true);
            cursor = closing;
        }
    }

    fn runStep(
        self: *OptimiserSuite,
        step: *const StepDescriptor,
        ast: *AST.Block,
    ) anyerror!void {
        defer self.context.resetScratch(step.name);
        defer if (!step.preserves_function_analysis)
            self.context.invalidateFunctionAnalysis();
        const names_before = if (self.context.profiler != null)
            self.context.dispenser.usedNames().count()
        else
            null;
        defer if (names_before) |before| {
            const names_after = self.context.dispenser.usedNames().count();
            if (names_after > before)
                self.context.recordCounter(
                    "Optimizer generated names",
                    names_after - before,
                );
        };
        var probe = ProfilerModule.OptionalProbe.init(self.profiler, step.name);
        defer probe.deinit();
        try step.run(self.context, ast);
    }

    fn runPlainSequence(
        self: *OptimiserSuite,
        sequence: []const u8,
        ast: *AST.Block,
    ) anyerror!void {
        for (sequence) |abbreviation| switch (abbreviation) {
            ' ', '\n' => {},
            ':' => return error.CleanupDelimiterCannotRun,
            else => {
                const step = stepForAbbreviation(abbreviation) orelse
                    return error.InvalidOptimizerStep;
                try self.runStep(step, ast);
            },
        };
    }

    pub fn run(
        meter: ?*const EVMMetrics.GasMeter,
        object: *Object,
        optimize_stack_allocation: bool,
        optimisation_sequence: []const u8,
        optimisation_cleanup_sequence: []const u8,
        expected_executions_per_deployment: ?usize,
        externally_used_identifiers: ?*const NameCollector.NameSet,
    ) anyerror!void {
        return runProfiled(
            meter,
            object,
            optimize_stack_allocation,
            optimisation_sequence,
            optimisation_cleanup_sequence,
            expected_executions_per_deployment,
            externally_used_identifiers,
            null,
        );
    }

    pub fn runProfiled(
        meter: ?*const EVMMetrics.GasMeter,
        object: *Object,
        optimize_stack_allocation: bool,
        optimisation_sequence: []const u8,
        optimisation_cleanup_sequence: []const u8,
        expected_executions_per_deployment: ?usize,
        externally_used_identifiers: ?*const NameCollector.NameSet,
        profiler: ?*Profiler,
    ) anyerror!void {
        const allocator = object.allocator;
        const code = object.code() orelse return error.MissingObjectCode;
        const analysis_info = if (object.analysis_info) |*info| info else return error.MissingAnalysisInfo;
        const dialect = code.dialect().*;
        const evm_dialect = EVMDialectModule.fromDialect(dialect);
        const uses_optimized_code_generator = optimize_stack_allocation and
            evm_dialect != null and
            evm_dialect.?.evmVersion().canOverchargeGasForCall() and
            evm_dialect.?.providesObjectAccess();

        var reserved_identifiers = if (externally_used_identifiers) |identifiers|
            try identifiers.clone(allocator)
        else
            NameCollector.NameSet{};
        defer reserved_identifiers.deinit(allocator);
        var ast_root: AST.Block = undefined;
        {
            var probe = ProfilerModule.OptionalProbe.init(profiler, "Disambiguator");
            defer probe.deinit();
            var disambiguator = try Disambiguator.init(
                allocator,
                dialect,
                analysis_info,
                &reserved_identifiers,
            );
            defer disambiguator.deinit();
            ast_root = try disambiguator.translateBlock(code.root());
        }
        var ast_root_owned = true;
        defer if (ast_root_owned) ast_root.deinit(allocator);

        var dispenser = try NameDispenser.initFromAst(
            allocator,
            dialect,
            &ast_root,
            &reserved_identifiers,
        );
        defer dispenser.deinit();
        var scratch_arena = std.heap.ArenaAllocator.init(std.heap.smp_allocator);
        defer scratch_arena.deinit();
        var function_analysis_cache = FunctionAnalysisCache.init(std.heap.smp_allocator);
        defer function_analysis_cache.deinit();
        var context: OptimiserStepContext = .{
            .dialect = dialect,
            .dispenser = &dispenser,
            .reserved_identifiers = &reserved_identifiers,
            .expected_executions_per_deployment = expected_executions_per_deployment,
            .profiler = profiler,
            .scratch_arena = &scratch_arena,
            .function_analysis_cache = &function_analysis_cache,
        };
        var suite = OptimiserSuite.init(&context, .none);
        suite.profiler = profiler;

        try suite.runSequence("hgfo", &ast_root, false);
        try suite.runSequence(optimisation_sequence, &ast_root, false);
        const stack_compressor_max_iterations: usize = 16;
        try suite.runSequence("g", &ast_root, false);

        if (!uses_optimized_code_generator) {
            var probe = ProfilerModule.OptionalProbe.init(profiler, "StackCompressor");
            defer probe.deinit();
            object.replaceCode(AST.AST.init(allocator, dialect, ast_root), null);
            ast_root = .{};
            var compressed = try StackCompressor.run(
                allocator,
                object,
                optimize_stack_allocation,
                stack_compressor_max_iterations,
            );
            ast_root = compressed.ast;
            compressed.ast = .{};
        }

        try suite.runSequence(optimisation_cleanup_sequence, &ast_root, false);
        try suite.runSequence("g", &ast_root, false);

        if (evm_dialect) |evm| {
            const gas_meter = meter orelse return error.MissingGasMeter;
            {
                var probe = ProfilerModule.OptionalProbe.init(profiler, "ConstantOptimiser");
                defer probe.deinit();
                var constant_optimiser = ConstantOptimiser.init(allocator, evm, gas_meter);
                defer constant_optimiser.deinit();
                try constant_optimiser.run(&ast_root);
            }

            if (uses_optimized_code_generator) {
                {
                    var probe = ProfilerModule.OptionalProbe.init(profiler, "StackCompressor");
                    defer probe.deinit();
                    object.replaceCode(AST.AST.init(allocator, dialect, ast_root), null);
                    ast_root = .{};
                    var compressed = try StackCompressor.run(
                        allocator,
                        object,
                        optimize_stack_allocation,
                        stack_compressor_max_iterations,
                    );
                    ast_root = compressed.ast;
                    compressed.ast = .{};
                }
                if (evm.providesObjectAccess()) {
                    var probe = ProfilerModule.OptionalProbe.init(profiler, "StackLimitEvader");
                    defer probe.deinit();
                    object.replaceCode(AST.AST.init(allocator, dialect, ast_root), null);
                    ast_root = .{};
                    ast_root = try StackLimitEvader.runObject(&context, object);
                }
            } else if (evm.providesObjectAccess() and optimize_stack_allocation) {
                var probe = ProfilerModule.OptionalProbe.init(profiler, "StackLimitEvader");
                defer probe.deinit();
                object.replaceCode(AST.AST.init(allocator, dialect, ast_root), null);
                ast_root = .{};
                ast_root = try StackLimitEvader.runObject(&context, object);
            }
        }

        try dispenser.reset(&ast_root);
        {
            var probe = ProfilerModule.OptionalProbe.init(profiler, "NameSimplifier");
            defer probe.deinit();
            try NameSimplifier.run(&context, &ast_root);
        }
        {
            var probe = ProfilerModule.OptionalProbe.init(profiler, "VarNameCleaner");
            defer probe.deinit();
            try VarNameCleaner.run(&context, &ast_root);
        }

        object.replaceCode(AST.AST.init(allocator, dialect, ast_root), null);
        ast_root = .{};
        ast_root_owned = false;
        {
            var probe = ProfilerModule.OptionalProbe.init(profiler, "AsmAnalysis");
            defer probe.deinit();
            var structure = try object.summarizeStructure();
            defer structure.deinit();
            object.analysis_info = try AsmAnalysis.analyzeStrictBlock(
                allocator,
                dialect,
                object.code().?.root(),
                &structure,
                if (evm_dialect) |evm|
                    AsmAnalysis.instructionValidatorForEVMDialect(evm)
                else
                    .{},
            );
        }
    }
};

test "optimizer sequence grammar and nested fixed-point execution" {
    try OptimiserSuite.validateSequence("dhfoDgvulfnTUtnIf[xa[r]EscLMcCTU]jmul[jul] VcTOcul jmul");
    try std.testing.expectError(
        error.UnbalancedOptimizerBrackets,
        OptimiserSuite.validateSequence("[d"),
    );
    try std.testing.expectError(
        error.InvalidOptimizerStep,
        OptimiserSuite.validateSequence("?"),
    );
    try std.testing.expect(OptimiserSuite.isEmptyOptimizerSequence(" \n: \n"));
    try std.testing.expect(!OptimiserSuite.isEmptyOptimizerSequence("u:"));
}

test "whole-object optimizer suite preserves analyzed ownership" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
    const Parser = @import("../asm_parser.zig").Parser;

    const allocator = std.testing.allocator;
    var dialect = try EVMDialectModule.EVMDialect.init(allocator, EVMVersion.current(), true);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    const parsed = (try Parser.parseSource(
        allocator,
        "{ mstore(0x40, memoryguard(0x80)) let x := add(1, 2) pop(x) }",
        "suite.yul",
        &reporter,
        dialect.dialect(),
        .{},
    )).?;
    const object = try Object.create(allocator, "");
    defer object.destroy();
    object.debug_data = .{};
    object.setCode(parsed, null);
    var structure = try object.summarizeStructure();
    defer structure.deinit();
    object.analysis_info = try AsmAnalysis.analyzeStrictBlock(
        allocator,
        dialect.dialect(),
        object.code().?.root(),
        &structure,
        AsmAnalysis.instructionValidatorForEVMDialect(&dialect),
    );
    var meter = EVMMetrics.GasMeter.initUnsigned(&dialect, true, 200);
    defer meter.deinit();
    var profiler = Profiler.init(allocator, std.testing.io);
    defer profiler.deinit();
    try OptimiserSuite.runProfiled(&meter, object, false, "u", "", null, null, &profiler);
    try std.testing.expect(object.code() != null);
    try std.testing.expect(object.analysis_info != null);
    try std.testing.expect(profiler.metricsFor(UnusedPruner.name) != null);
}
