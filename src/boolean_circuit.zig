//! A boolean circuit is a directed acyclic graph of gates over the field
//! GF(2). It has the form C = (n, G, O), where
//! - n is the number of input wires (Booleans).
//! - G = (g_0, g_1, ..., g_{m-1}) is a list of gates in topological order;
//!   gate g_i defines the value of wire `n + i`. Each gate is a tuple
//!   (kind, a, b) with `kind in {NOT, AND, OR, XOR, NAND, NOR}` and
//!   `a, b in {0, ..., n + i - 1}` (and `b` is ignored when kind is NOT).
//! - O = (o_0, ..., o_{k-1}) is a list of output wire indices,
//!   `o_j in {0, ..., n + m - 1}`.
//!
//! Wire `i` carries a Boolean value `w_i in {false, true}`. The first `n`
//! wires are the inputs; subsequent wires are computed by applying each
//! gate to its referenced wires in topological order. The circuit's outputs
//! are `(w_{o_0}, ..., w_{o_{k-1}})`.
//!
//! This module also exposes `compileToTuringMachine`, which produces a
//! `TuringMachine` whose language is `{ x in {0,1}^n | C(x) = 1 }` for
//! single-output circuits, using only the `Nfa`-style bit-tape and standard
//! state-walking subroutines (no advanced libraries or algorithms).

const std = @import("std");
const tm_mod = @import("turing_machine.zig");
pub const TuringMachine = tm_mod.TuringMachine;

const State = TuringMachine.State;
const Symbol = TuringMachine.Symbol;
const Transition = TuringMachine.Transition;
const Direction = TuringMachine.Direction;

/// Tape symbols used by the compiled Turing machine: `Sigma = {zero, one}`
/// and `Gamma = Sigma cup {blank}`. Wire `i` is stored at tape position `i`.
const zero: Symbol = 0;
const one: Symbol = 1;
const blank: Symbol = 2;
const tape_alphabet_size: usize = 3;
const input_alphabet_size: usize = 2;

/// DAG-encoded boolean circuit.
pub const BooleanCircuit = struct {
    pub const WireId = u32;

    pub const GateKind = enum(u8) { not, and_, or_, xor, nand, nor };

    pub const Gate = struct {
        kind: GateKind,
        a: WireId,
        b: WireId,
    };

    num_inputs: u32,
    gates: []const Gate,
    outputs: []const WireId,

    /// Creates a new BooleanCircuit, borrowing `gates` and `outputs`.
    ///
    /// REQUIRES:
    /// - `num_inputs + gates.len <= maxInt(WireId)`.
    /// - For every gate `g_i`: `g_i.a < num_inputs + i`, and if `g_i.kind`
    ///   is binary then `g_i.b < num_inputs + i`.
    /// - For every output wire `w in outputs`: `w < num_inputs + gates.len`.
    pub fn init(num_inputs: u32, gates: []const Gate, outputs: []const WireId) BooleanCircuit {
        const c = BooleanCircuit{
            .num_inputs = num_inputs,
            .gates = gates,
            .outputs = outputs,
        };
        std.debug.assert(c.isCircuit());
        return c;
    }

    /// REQUIRES:
    /// - `self` is a readable BooleanCircuit value.
    ///
    /// ENSURES:
    /// - Returns `true` iff `self` is well-formed under the topological-order
    ///   and wire-range invariants documented on `init`.
    fn isCircuit(self: *const BooleanCircuit) bool {
        const total = std.math.add(usize, self.num_inputs, self.gates.len) catch return false;
        if (total > std.math.maxInt(WireId)) return false;

        for (self.gates, 0..) |gate, i| {
            const limit: WireId = @intCast(@as(usize, self.num_inputs) + i);
            if (gate.a >= limit) return false;
            if (isBinary(gate.kind) and gate.b >= limit) return false;
        }

        for (self.outputs) |w| {
            if (w >= total) return false;
        }
        return true;
    }

    /// Returns the total number of wires `n + m`.
    pub inline fn numWires(self: *const BooleanCircuit) usize {
        return @as(usize, self.num_inputs) + self.gates.len;
    }

    /// Evaluates the circuit on `inputs` and returns a freshly-allocated
    /// list of output values.
    ///
    /// REQUIRES:
    /// - `inputs.len == num_inputs`.
    /// - `allocator` can serve `numWires()` Booleans of scratch and
    ///   `outputs.len` Booleans of result.
    ///
    /// ENSURES:
    /// - On success, returns a slice `out` with `out.len == outputs.len`
    ///   such that `out[j] = w_{outputs[j]}` under the standard semantics.
    /// - On allocation failure, returns `error.OutOfMemory`.
    /// - The caller owns the returned slice.
    pub fn evaluate(
        self: *const BooleanCircuit,
        allocator: std.mem.Allocator,
        inputs: []const bool,
    ) std.mem.Allocator.Error![]bool {
        std.debug.assert(inputs.len == self.num_inputs);

        const wires = try allocator.alloc(bool, self.numWires());
        defer allocator.free(wires);

        @memcpy(wires[0..self.num_inputs], inputs);
        for (self.gates, 0..) |gate, i| {
            const a = wires[gate.a];
            const b = if (isBinary(gate.kind)) wires[gate.b] else false;
            wires[self.num_inputs + i] = applyGate(gate.kind, a, b);
        }

        const result = try allocator.alloc(bool, self.outputs.len);
        for (self.outputs, 0..) |w, i| result[i] = wires[w];
        return result;
    }
};

inline fn isBinary(kind: BooleanCircuit.GateKind) bool {
    return kind != .not;
}

inline fn applyGate(kind: BooleanCircuit.GateKind, a: bool, b: bool) bool {
    return switch (kind) {
        .not => !a,
        .and_ => a and b,
        .or_ => a or b,
        .xor => a != b,
        .nand => !(a and b),
        .nor => !(a or b),
    };
}

inline fn boolSymbol(value: bool) Symbol {
    return if (value) one else zero;
}

pub const CompileError = std.mem.Allocator.Error || error{
    NotSingleOutput,
    CircuitTooLarge,
};

const SparseTransition = struct {
    from: State,
    sym: Symbol,
    t: Transition,
};

const Builder = struct {
    allocator: std.mem.Allocator,
    state_count: usize = 0,
    transitions: std.ArrayList(SparseTransition) = .empty,

    fn deinit(self: *Builder) void {
        self.transitions.deinit(self.allocator);
    }

    fn newState(self: *Builder) CompileError!State {
        if (self.state_count >= std.math.maxInt(State)) return error.CircuitTooLarge;
        const s: State = @intCast(self.state_count);
        self.state_count += 1;
        return s;
    }

    fn addTransition(self: *Builder, from: State, sym: Symbol, t: Transition) CompileError!void {
        try self.transitions.append(self.allocator, .{ .from = from, .sym = sym, .t = t });
    }

    /// For every tape symbol, transition `from -> next` rewriting the symbol
    /// in place and stepping in `dir`.
    fn addPassthrough(self: *Builder, from: State, next: State, dir: Direction) CompileError!void {
        try self.addTransition(from, zero, .{ .next = next, .write = zero, .dir = dir });
        try self.addTransition(from, one, .{ .next = next, .write = one, .dir = dir });
        try self.addTransition(from, blank, .{ .next = next, .write = blank, .dir = dir });
    }

    /// For every tape symbol, transition `from -> next` overwriting the cell
    /// with `write` and staying in place.
    fn addWrite(self: *Builder, from: State, next: State, write: Symbol) CompileError!void {
        try self.addTransition(from, zero, .{ .next = next, .write = write, .dir = .stay });
        try self.addTransition(from, one, .{ .next = next, .write = write, .dir = .stay });
        try self.addTransition(from, blank, .{ .next = next, .write = write, .dir = .stay });
    }

    /// Walks `count` cells in `dir`, threading `entry -> ... -> exit`.
    /// `count == 0` collapses to a single `.stay` no-op step.
    fn walk(self: *Builder, entry: State, count: usize, dir: Direction, exit: State) CompileError!void {
        if (count == 0) {
            try self.addPassthrough(entry, exit, .stay);
            return;
        }
        var cur = entry;
        var remaining = count;
        while (remaining > 1) : (remaining -= 1) {
            const nxt = try self.newState();
            try self.addPassthrough(cur, nxt, dir);
            cur = nxt;
        }
        try self.addPassthrough(cur, exit, dir);
    }

    fn walkBetween(self: *Builder, entry: State, from_pos: usize, to_pos: usize, exit: State) CompileError!void {
        if (to_pos > from_pos) {
            try self.walk(entry, to_pos - from_pos, .right, exit);
        } else if (to_pos < from_pos) {
            try self.walk(entry, from_pos - to_pos, .left, exit);
        } else {
            try self.walk(entry, 0, .stay, exit);
        }
    }

    /// Adds a prologue that requires `tape[0..n]` to be in `{zero, one}` and
    /// `tape[n]` to be `blank`, then walks the head back to position 0 in
    /// `home`. Any other tape pattern transitions to `reject`.
    fn addArityGuard(self: *Builder, entry: State, n: usize, reject: State, home: State) CompileError!void {
        var scan = entry;
        for (0..n) |_| {
            const next = try self.newState();
            try self.addTransition(scan, zero, .{ .next = next, .write = zero, .dir = .right });
            try self.addTransition(scan, one, .{ .next = next, .write = one, .dir = .right });
            try self.addTransition(scan, blank, .{ .next = reject, .write = blank, .dir = .stay });
            scan = next;
        }
        const ok = try self.newState();
        try self.addTransition(scan, blank, .{ .next = ok, .write = blank, .dir = .stay });
        try self.addTransition(scan, zero, .{ .next = reject, .write = zero, .dir = .stay });
        try self.addTransition(scan, one, .{ .next = reject, .write = one, .dir = .stay });
        try self.walk(ok, n, .left, home);
    }

    fn build(
        self: *Builder,
        start: State,
        accept: State,
        reject: State,
    ) CompileError!TuringMachine.Owned {
        const padded = TuringMachine.paddedAlphabetSize(tape_alphabet_size);
        const delta = try self.allocator.alloc(Transition, self.state_count * padded);
        errdefer self.allocator.free(delta);

        // Default every cell to "go to reject without changing the tape" so any
        // unspecified transition fails closed.
        for (0..self.state_count) |q| {
            for (0..padded) |sym| {
                delta[q * padded + sym] = .{
                    .next = reject,
                    .write = @intCast(sym),
                    .dir = .stay,
                };
            }
        }

        for (self.transitions.items) |edge| {
            delta[@as(usize, edge.from) * padded + @as(usize, edge.sym)] = edge.t;
        }

        return .{
            .machine = TuringMachine.init(
                self.state_count,
                tape_alphabet_size,
                input_alphabet_size,
                blank,
                delta,
                start,
                accept,
                reject,
            ),
            .delta = delta,
        };
    }
};

/// Compiles `circuit` into an equivalent single-tape Turing machine.
///
/// REQUIRES:
/// - `circuit.outputs.len == 1`.
/// - `circuit.numWires()` is small enough that the resulting state count
///   fits in `TuringMachine.State`.
///
/// ENSURES:
/// - On success, returns a `TuringMachine.Owned` `M` whose accepted language
///   is exactly `{ x in {zero, one}^{circuit.num_inputs} | C(x) = 1 }`:
///   - For `x in {zero, one}^{circuit.num_inputs}`, `M.run(x)` halts in
///     `q_accept` iff `circuit.evaluate(x)[0] = true`, and in `q_reject`
///     otherwise.
///   - For inputs of any other length, `M.run(x)` halts in `q_reject`.
/// - On invalid output count, returns `error.NotSingleOutput`.
/// - On state-index overflow, returns `error.CircuitTooLarge`.
/// - On allocation failure, returns `error.OutOfMemory`.
/// - The caller owns the returned `Owned` and must call `deinit`.
pub fn compileToTuringMachine(
    allocator: std.mem.Allocator,
    circuit: *const BooleanCircuit,
) CompileError!TuringMachine.Owned {
    if (circuit.outputs.len != 1) return error.NotSingleOutput;

    var builder = Builder{ .allocator = allocator };
    defer builder.deinit();

    const start = try builder.newState();
    const accept = try builder.newState();
    const reject = try builder.newState();

    const home = try builder.newState();
    try builder.addArityGuard(start, circuit.num_inputs, reject, home);

    var current = home;
    for (circuit.gates, 0..) |gate, gate_idx| {
        const target = circuit.num_inputs + gate_idx;
        const exit = try builder.newState();
        try compileGate(&builder, gate, target, current, exit, reject);
        current = exit;
    }

    const final_read = try builder.newState();
    try builder.walk(current, circuit.outputs[0], .right, final_read);
    try builder.addTransition(final_read, zero, .{ .next = reject, .write = zero, .dir = .stay });
    try builder.addTransition(final_read, one, .{ .next = accept, .write = one, .dir = .stay });
    try builder.addTransition(final_read, blank, .{ .next = reject, .write = blank, .dir = .stay });

    return builder.build(start, accept, reject);
}

fn compileGate(
    b: *Builder,
    gate: BooleanCircuit.Gate,
    target: usize,
    entry: State,
    exit: State,
    reject: State,
) CompileError!void {
    if (!isBinary(gate.kind)) {
        try compileUnary(b, gate, target, entry, exit, reject);
    } else {
        try compileBinary(b, gate, target, entry, exit, reject);
    }
}

fn compileUnary(
    b: *Builder,
    gate: BooleanCircuit.Gate,
    target: usize,
    entry: State,
    exit: State,
    reject: State,
) CompileError!void {
    const arrived_a = try b.newState();
    try b.walk(entry, gate.a, .right, arrived_a);

    const got_a0 = try b.newState();
    const got_a1 = try b.newState();
    try b.addTransition(arrived_a, zero, .{ .next = got_a0, .write = zero, .dir = .stay });
    try b.addTransition(arrived_a, one, .{ .next = got_a1, .write = one, .dir = .stay });
    try b.addTransition(arrived_a, blank, .{ .next = reject, .write = blank, .dir = .stay });

    const at_target_a0 = try b.newState();
    const at_target_a1 = try b.newState();
    try b.walkBetween(got_a0, gate.a, target, at_target_a0);
    try b.walkBetween(got_a1, gate.a, target, at_target_a1);

    const home_walk = try b.newState();
    const out0 = boolSymbol(applyGate(gate.kind, false, false));
    const out1 = boolSymbol(applyGate(gate.kind, true, false));
    try b.addWrite(at_target_a0, home_walk, out0);
    try b.addWrite(at_target_a1, home_walk, out1);

    try b.walk(home_walk, target, .left, exit);
}

fn compileBinary(
    b: *Builder,
    gate: BooleanCircuit.Gate,
    target: usize,
    entry: State,
    exit: State,
    reject: State,
) CompileError!void {
    const arrived_a = try b.newState();
    try b.walk(entry, gate.a, .right, arrived_a);

    const got_a0 = try b.newState();
    const got_a1 = try b.newState();
    try b.addTransition(arrived_a, zero, .{ .next = got_a0, .write = zero, .dir = .stay });
    try b.addTransition(arrived_a, one, .{ .next = got_a1, .write = one, .dir = .stay });
    try b.addTransition(arrived_a, blank, .{ .next = reject, .write = blank, .dir = .stay });

    const arrived_b_a0 = try b.newState();
    const arrived_b_a1 = try b.newState();
    try b.walkBetween(got_a0, gate.a, gate.b, arrived_b_a0);
    try b.walkBetween(got_a1, gate.a, gate.b, arrived_b_a1);

    const got_a0_b0 = try b.newState();
    const got_a0_b1 = try b.newState();
    const got_a1_b0 = try b.newState();
    const got_a1_b1 = try b.newState();
    try b.addTransition(arrived_b_a0, zero, .{ .next = got_a0_b0, .write = zero, .dir = .stay });
    try b.addTransition(arrived_b_a0, one, .{ .next = got_a0_b1, .write = one, .dir = .stay });
    try b.addTransition(arrived_b_a0, blank, .{ .next = reject, .write = blank, .dir = .stay });
    try b.addTransition(arrived_b_a1, zero, .{ .next = got_a1_b0, .write = zero, .dir = .stay });
    try b.addTransition(arrived_b_a1, one, .{ .next = got_a1_b1, .write = one, .dir = .stay });
    try b.addTransition(arrived_b_a1, blank, .{ .next = reject, .write = blank, .dir = .stay });

    const at_target_a0_b0 = try b.newState();
    const at_target_a0_b1 = try b.newState();
    const at_target_a1_b0 = try b.newState();
    const at_target_a1_b1 = try b.newState();
    try b.walkBetween(got_a0_b0, gate.b, target, at_target_a0_b0);
    try b.walkBetween(got_a0_b1, gate.b, target, at_target_a0_b1);
    try b.walkBetween(got_a1_b0, gate.b, target, at_target_a1_b0);
    try b.walkBetween(got_a1_b1, gate.b, target, at_target_a1_b1);

    const home_walk = try b.newState();
    const out00 = boolSymbol(applyGate(gate.kind, false, false));
    const out01 = boolSymbol(applyGate(gate.kind, false, true));
    const out10 = boolSymbol(applyGate(gate.kind, true, false));
    const out11 = boolSymbol(applyGate(gate.kind, true, true));
    try b.addWrite(at_target_a0_b0, home_walk, out00);
    try b.addWrite(at_target_a0_b1, home_walk, out01);
    try b.addWrite(at_target_a1_b0, home_walk, out10);
    try b.addWrite(at_target_a1_b1, home_walk, out11);

    try b.walk(home_walk, target, .left, exit);
}

test "BooleanCircuit - evaluate computes NOT, AND, OR, XOR" {
    const allocator = std.testing.allocator;
    const Gate = BooleanCircuit.Gate;

    const not_gates = [_]Gate{
        .{ .kind = .not, .a = 0, .b = 0 },
    };
    const not_outputs = [_]BooleanCircuit.WireId{1};
    const not_circuit = BooleanCircuit.init(1, &not_gates, &not_outputs);

    const not_0 = try not_circuit.evaluate(allocator, &[_]bool{false});
    defer allocator.free(not_0);
    try std.testing.expectEqual(true, not_0[0]);

    const not_1 = try not_circuit.evaluate(allocator, &[_]bool{true});
    defer allocator.free(not_1);
    try std.testing.expectEqual(false, not_1[0]);

    const and_gates = [_]Gate{.{ .kind = .and_, .a = 0, .b = 1 }};
    const and_outputs = [_]BooleanCircuit.WireId{2};
    const and_circuit = BooleanCircuit.init(2, &and_gates, &and_outputs);

    const cases = [_]struct { a: bool, b: bool, kind: BooleanCircuit.GateKind, expected: bool }{
        .{ .a = false, .b = false, .kind = .and_, .expected = false },
        .{ .a = false, .b = true, .kind = .and_, .expected = false },
        .{ .a = true, .b = false, .kind = .and_, .expected = false },
        .{ .a = true, .b = true, .kind = .and_, .expected = true },
    };

    for (cases) |c| {
        const out = try and_circuit.evaluate(allocator, &[_]bool{ c.a, c.b });
        defer allocator.free(out);
        try std.testing.expectEqual(c.expected, out[0]);
    }

    const xor_gates = [_]Gate{
        .{ .kind = .or_, .a = 0, .b = 1 },
        .{ .kind = .nand, .a = 0, .b = 1 },
        .{ .kind = .and_, .a = 2, .b = 3 },
    };
    const xor_outputs = [_]BooleanCircuit.WireId{4};
    const xor_circuit = BooleanCircuit.init(2, &xor_gates, &xor_outputs);

    const xor_cases = [_]struct { a: bool, b: bool, expected: bool }{
        .{ .a = false, .b = false, .expected = false },
        .{ .a = false, .b = true, .expected = true },
        .{ .a = true, .b = false, .expected = true },
        .{ .a = true, .b = true, .expected = false },
    };
    for (xor_cases) |c| {
        const out = try xor_circuit.evaluate(allocator, &[_]bool{ c.a, c.b });
        defer allocator.free(out);
        try std.testing.expectEqual(c.expected, out[0]);
    }
}

test "BooleanCircuit - evaluate computes a half-adder with two outputs" {
    const allocator = std.testing.allocator;
    const Gate = BooleanCircuit.Gate;

    // sum = a XOR b (wire 2), carry = a AND b (wire 3).
    const gates = [_]Gate{
        .{ .kind = .xor, .a = 0, .b = 1 },
        .{ .kind = .and_, .a = 0, .b = 1 },
    };
    const outputs = [_]BooleanCircuit.WireId{ 2, 3 };
    const circuit = BooleanCircuit.init(2, &gates, &outputs);

    const cases = [_]struct { a: bool, b: bool, sum: bool, carry: bool }{
        .{ .a = false, .b = false, .sum = false, .carry = false },
        .{ .a = false, .b = true, .sum = true, .carry = false },
        .{ .a = true, .b = false, .sum = true, .carry = false },
        .{ .a = true, .b = true, .sum = false, .carry = true },
    };

    for (cases) |c| {
        const out = try circuit.evaluate(allocator, &[_]bool{ c.a, c.b });
        defer allocator.free(out);
        try std.testing.expectEqual(c.sum, out[0]);
        try std.testing.expectEqual(c.carry, out[1]);
    }
}

test "BooleanCircuit - isCircuit rejects forward references and OOB outputs" {
    const Gate = BooleanCircuit.Gate;

    const forward_ref = BooleanCircuit{
        .num_inputs = 1,
        .gates = &[_]Gate{.{ .kind = .and_, .a = 0, .b = 1 }},
        .outputs = &[_]BooleanCircuit.WireId{1},
    };
    try std.testing.expect(!forward_ref.isCircuit());

    const oob_output = BooleanCircuit{
        .num_inputs = 2,
        .gates = &[_]Gate{.{ .kind = .or_, .a = 0, .b = 1 }},
        .outputs = &[_]BooleanCircuit.WireId{99},
    };
    try std.testing.expect(!oob_output.isCircuit());

    const ok = BooleanCircuit{
        .num_inputs = 2,
        .gates = &[_]Gate{.{ .kind = .or_, .a = 0, .b = 1 }},
        .outputs = &[_]BooleanCircuit.WireId{2},
    };
    try std.testing.expect(ok.isCircuit());
}

fn expectCompiledMatches(
    allocator: std.mem.Allocator,
    circuit: *const BooleanCircuit,
    inputs: []const bool,
) !void {
    var owned = try compileToTuringMachine(allocator, circuit);
    defer owned.deinit(allocator);

    const sym_buf = try allocator.alloc(Symbol, inputs.len);
    defer allocator.free(sym_buf);
    for (inputs, 0..) |bit, i| sym_buf[i] = boolSymbol(bit);

    var result = try owned.machine.run(allocator, sym_buf, 100_000);
    defer result.deinit(allocator);

    const expected = try circuit.evaluate(allocator, inputs);
    defer allocator.free(expected);

    const expected_outcome: TuringMachine.Outcome = if (expected[0]) .accept else .reject;
    try std.testing.expectEqual(expected_outcome, result.outcome);
}

fn expectCompiledRejects(
    allocator: std.mem.Allocator,
    circuit: *const BooleanCircuit,
    input: []const Symbol,
) !void {
    var owned = try compileToTuringMachine(allocator, circuit);
    defer owned.deinit(allocator);

    var result = try owned.machine.run(allocator, input, 100_000);
    defer result.deinit(allocator);

    try std.testing.expectEqual(TuringMachine.Outcome.reject, result.outcome);
}

fn enumerateInputs(
    allocator: std.mem.Allocator,
    circuit: *const BooleanCircuit,
) !void {
    const n = circuit.num_inputs;
    const buf = try allocator.alloc(bool, n);
    defer allocator.free(buf);

    const total = @as(usize, 1) << @intCast(n);
    for (0..total) |encoded| {
        for (0..n) |i| {
            buf[i] = ((encoded >> @intCast(i)) & 1) == 1;
        }
        try expectCompiledMatches(allocator, circuit, buf);
    }
}

test "compileToTuringMachine - NOT" {
    const allocator = std.testing.allocator;
    const gates = [_]BooleanCircuit.Gate{.{ .kind = .not, .a = 0, .b = 0 }};
    const outputs = [_]BooleanCircuit.WireId{1};
    const circuit = BooleanCircuit.init(1, &gates, &outputs);

    try enumerateInputs(allocator, &circuit);
}

test "compileToTuringMachine - no-gate circuit returns the chosen input bit" {
    const allocator = std.testing.allocator;
    const empty_gates: []const BooleanCircuit.Gate = &.{};
    for ([_]BooleanCircuit.WireId{ 0, 1 }) |output_wire| {
        const outputs = [_]BooleanCircuit.WireId{output_wire};
        const circuit = BooleanCircuit.init(2, empty_gates, &outputs);
        try enumerateInputs(allocator, &circuit);
    }
}

test "compileToTuringMachine - rejects non-arity inputs" {
    const allocator = std.testing.allocator;

    const not_gates = [_]BooleanCircuit.Gate{.{ .kind = .not, .a = 0, .b = 0 }};
    const not_outputs = [_]BooleanCircuit.WireId{1};
    const not_circuit = BooleanCircuit.init(1, &not_gates, &not_outputs);
    try expectCompiledRejects(allocator, &not_circuit, &[_]Symbol{});
    try expectCompiledRejects(allocator, &not_circuit, &[_]Symbol{ one, zero });

    const and_gates = [_]BooleanCircuit.Gate{.{ .kind = .and_, .a = 0, .b = 1 }};
    const and_outputs = [_]BooleanCircuit.WireId{2};
    const and_circuit = BooleanCircuit.init(2, &and_gates, &and_outputs);
    try expectCompiledRejects(allocator, &and_circuit, &[_]Symbol{one});
    try expectCompiledRejects(allocator, &and_circuit, &[_]Symbol{ one, zero, one });
}

test "compileToTuringMachine - AND, OR, NAND, NOR over 2 inputs" {
    const allocator = std.testing.allocator;
    const kinds = [_]BooleanCircuit.GateKind{ .and_, .or_, .nand, .nor };
    for (kinds) |kind| {
        const gates = [_]BooleanCircuit.Gate{.{ .kind = kind, .a = 0, .b = 1 }};
        const outputs = [_]BooleanCircuit.WireId{2};
        const circuit = BooleanCircuit.init(2, &gates, &outputs);
        try enumerateInputs(allocator, &circuit);
    }
}

test "compileToTuringMachine - XOR built from OR, NAND, AND" {
    const allocator = std.testing.allocator;
    const gates = [_]BooleanCircuit.Gate{
        .{ .kind = .or_, .a = 0, .b = 1 },
        .{ .kind = .nand, .a = 0, .b = 1 },
        .{ .kind = .and_, .a = 2, .b = 3 },
    };
    const outputs = [_]BooleanCircuit.WireId{4};
    const circuit = BooleanCircuit.init(2, &gates, &outputs);

    try enumerateInputs(allocator, &circuit);
}

test "compileToTuringMachine - 3-input majority (full truth table)" {
    const allocator = std.testing.allocator;
    // majority(a, b, c) = (a&b) | (a&c) | (b&c)
    const gates = [_]BooleanCircuit.Gate{
        .{ .kind = .and_, .a = 0, .b = 1 }, // wire 3
        .{ .kind = .and_, .a = 0, .b = 2 }, // wire 4
        .{ .kind = .and_, .a = 1, .b = 2 }, // wire 5
        .{ .kind = .or_, .a = 3, .b = 4 }, // wire 6
        .{ .kind = .or_, .a = 5, .b = 6 }, // wire 7
    };
    const outputs = [_]BooleanCircuit.WireId{7};
    const circuit = BooleanCircuit.init(3, &gates, &outputs);

    try enumerateInputs(allocator, &circuit);
}

test "compileToTuringMachine - NotSingleOutput when outputs.len != 1" {
    const allocator = std.testing.allocator;
    const gates = [_]BooleanCircuit.Gate{
        .{ .kind = .xor, .a = 0, .b = 1 },
        .{ .kind = .and_, .a = 0, .b = 1 },
    };
    const outputs = [_]BooleanCircuit.WireId{ 2, 3 };
    const circuit = BooleanCircuit.init(2, &gates, &outputs);

    try std.testing.expectError(error.NotSingleOutput, compileToTuringMachine(allocator, &circuit));
}
