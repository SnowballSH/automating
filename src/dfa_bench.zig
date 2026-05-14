//! DFA benchmark for the public optimized `DFA` implementation.

const std = @import("std");
const automating = @import("root.zig");

const DFA = automating.dfa_tools.DFA;

const random_seed: u64 = 0xDFA_BEEE;
const bench_rounds = 15;

const BenchKind = enum {
    random,
    worst_case,
};

const BenchCase = struct {
    name: []const u8,
    kind: BenchKind,
    states: usize,
    alphabet: usize,
    input_len: usize,
};

const BenchData = struct {
    delta_compact: []DFA.State,
    input: []DFA.Symbol,
    accepting: std.DynamicBitSetUnmanaged,
    padded_alphabet: usize,
};

const BenchResult = struct {
    final_state: DFA.State,
    accepted_count: usize,
    ns: u128,
};

const bench_cases = [_]BenchCase{
    .{
        .name = "random non-power-of-two alphabet",
        .kind = .random,
        .states = 8192,
        .alphabet = 257,
        .input_len = 8_000_000,
    },
    .{
        .name = "random power-of-two alphabet",
        .kind = .random,
        .states = 8192,
        .alphabet = 256,
        .input_len = 8_000_000,
    },
    .{
        .name = "worst-case row sweep",
        .kind = .worst_case,
        .states = 131_072,
        .alphabet = 32,
        .input_len = 12_000_000,
    },
};

pub fn main(_: std.process.Init) !void {
    const allocator = std.heap.smp_allocator;

    std.debug.print("DFA benchmark\n", .{});
    std.debug.print("rounds: {d}\n", .{bench_rounds});
    std.debug.print("seed: 0x{x}\n\n", .{random_seed});

    for (bench_cases) |case| {
        try runCase(allocator, case);
    }
}

/// Allocates case data, constructs the DFA, and reports timing results.
fn runCase(allocator: std.mem.Allocator, case: BenchCase) !void {
    var data = try prepareCase(allocator, case);
    defer freeBenchData(allocator, &data);

    const dfa = DFA.init(case.states, case.alphabet, data.delta_compact, 0, data.accepting);
    const result = benchDFA(&dfa, data.input);

    printCaseHeader(case, data.padded_alphabet);
    printResult("public DFA", result, case.input_len);
    std.debug.print("\n", .{});
}

/// Allocates and fills all data needed by a benchmark case.
fn prepareCase(allocator: std.mem.Allocator, case: BenchCase) !BenchData {
    const padded_alphabet = DFA.paddedAlphabetSize(case.alphabet);
    const compact_table_len = try std.math.mul(usize, case.states, padded_alphabet);

    const delta_compact = try allocator.alloc(DFA.State, compact_table_len);
    errdefer allocator.free(delta_compact);

    const input = try allocator.alloc(DFA.Symbol, case.input_len);
    errdefer allocator.free(input);

    var accepting = try std.DynamicBitSetUnmanaged.initEmpty(allocator, case.states);
    errdefer accepting.deinit(allocator);

    var data = BenchData{
        .delta_compact = delta_compact,
        .input = input,
        .accepting = accepting,
        .padded_alphabet = padded_alphabet,
    };

    switch (case.kind) {
        .random => fillRandomCase(case, &data),
        .worst_case => fillWorstCase(case, &data),
    }

    return data;
}

/// Releases all allocations owned by `BenchData`.
fn freeBenchData(allocator: std.mem.Allocator, data: *BenchData) void {
    allocator.free(data.delta_compact);
    allocator.free(data.input);
    data.accepting.deinit(allocator);
}

/// Fills a randomized transition graph and randomized input stream.
fn fillRandomCase(case: BenchCase, data: *BenchData) void {
    var prng = std.Random.DefaultPrng.init(random_seed ^ case.states ^ case.alphabet);
    const random = prng.random();

    for (0..case.states) |state| {
        const row_base = state * data.padded_alphabet;

        for (0..case.alphabet) |symbol| {
            data.delta_compact[row_base + symbol] = @intCast(random.uintLessThan(usize, case.states));
        }

        for (case.alphabet..data.padded_alphabet) |symbol| {
            data.delta_compact[row_base + symbol] = 0;
        }
    }

    for (data.input) |*symbol| {
        symbol.* = @intCast(random.uintLessThan(usize, case.alphabet));
    }

    fillAccepting(case, data);
}

/// Fills a row-sweeping graph intended to defeat locality in the transition table.
fn fillWorstCase(case: BenchCase, data: *BenchData) void {
    const stride = nearestOddStride(case.states / 2 + 1);

    for (0..case.states) |state| {
        const row_base = state * data.padded_alphabet;

        for (0..case.alphabet) |symbol| {
            data.delta_compact[row_base + symbol] = @intCast((state + stride + symbol * 17) % case.states);
        }

        for (case.alphabet..data.padded_alphabet) |symbol| {
            data.delta_compact[row_base + symbol] = 0;
        }
    }

    for (data.input, 0..) |*symbol, i| {
        symbol.* = @intCast((i * 13) % case.alphabet);
    }

    fillAccepting(case, data);
}

/// Returns an odd stride so a power-of-two state count walks every cache region.
fn nearestOddStride(value: usize) usize {
    return value | 1;
}

/// Marks a dense deterministic subset of states as accepting.
///
/// Three quarters of states are accepting. That keeps the benchmark from
/// repeatedly reporting zero accepted runs while still exercising both accepting
/// and rejecting states in the generated automata.
fn fillAccepting(case: BenchCase, data: *BenchData) void {
    for (0..case.states) |state| {
        if (state & 3 != 3) {
            data.accepting.set(state);
        }
    }
}

/// Times repeated full-input runs through the public DFA interface.
fn benchDFA(dfa: *const DFA, input: []const DFA.Symbol) BenchResult {
    const start = nowNs();
    var final_state: DFA.State = 0;
    var accepted_count: usize = 0;

    for (0..bench_rounds) |_| {
        final_state = dfa.processFromState(input, 0);
        accepted_count += @intFromBool(dfa.isAccepting(final_state));
    }

    std.mem.doNotOptimizeAway(final_state);
    std.mem.doNotOptimizeAway(accepted_count);

    return .{
        .final_state = final_state,
        .accepted_count = accepted_count,
        .ns = nowNs() - start,
    };
}

/// Returns a monotonic timestamp in nanoseconds.
fn nowNs() u128 {
    var ts: std.c.timespec = undefined;
    if (std.c.clock_gettime(.MONOTONIC, &ts) != 0) {
        @panic("clock_gettime failed");
    }

    return @as(u128, @intCast(ts.sec)) * std.time.ns_per_s + @as(u128, @intCast(ts.nsec));
}

/// Prints a case label and the dimensions that affect DFA memory access.
fn printCaseHeader(case: BenchCase, padded_alphabet: usize) void {
    const padded_table_len = case.states * padded_alphabet;
    std.debug.print("{s}\n", .{case.name});
    std.debug.print("  states={d} alphabet={d} padded_alphabet={d} table_entries={d} input_len={d}\n", .{
        case.states,
        case.alphabet,
        padded_alphabet,
        padded_table_len,
        case.input_len,
    });
}

/// Prints elapsed time and throughput for one implementation.
fn printResult(label: []const u8, result: BenchResult, input_len: usize) void {
    std.debug.print("  {s}: {d:.3} ms, {d:.1} M transitions/s, final={d}, accepted_count={d}\n", .{
        label,
        nsToMillis(result.ns),
        @as(f64, @floatFromInt(input_len * bench_rounds)) / nsToSeconds(result.ns) / 1_000_000.0,
        result.final_state,
        result.accepted_count,
    });
}

/// Converts nanoseconds to milliseconds for display.
fn nsToMillis(ns: u128) f64 {
    return @as(f64, @floatFromInt(ns)) / @as(f64, @floatFromInt(std.time.ns_per_ms));
}

/// Converts nanoseconds to seconds for throughput calculations.
fn nsToSeconds(ns: u128) f64 {
    return @as(f64, @floatFromInt(ns)) / @as(f64, @floatFromInt(std.time.ns_per_s));
}
