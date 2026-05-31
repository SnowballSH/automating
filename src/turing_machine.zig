//! A deterministic single-tape Turing machine is a 7-tuple
//! M = (Q, Sigma, Gamma, delta, q_0, q_accept, q_reject), where
//! - Q is the set of states, a non-empty finite set
//! - Sigma is the input alphabet, a non-empty finite set
//! - Gamma is the tape alphabet, with Sigma subseteq Gamma and a
//!   distinguished blank symbol b in Gamma \ Sigma
//! - delta: (Q \ {q_accept, q_reject}) x Gamma -> Q x Gamma x {L, R, S}
//!   is the transition function. The `S` (stay) move keeps the head in
//!   place and is included for compiler convenience.
//! - q_0 in Q is the start state
//! - q_accept in Q is the accepting halt state
//! - q_reject in Q is the rejecting halt state, with q_accept != q_reject.
//!
//! The tape is a one-dimensional array indexed by Z, pre-filled with the
//! blank symbol. On entering q_accept or q_reject the machine halts. From
//! any other state q with current symbol s, it writes delta(q, s).write,
//! moves the head per delta(q, s).dir, and transitions to delta(q, s).next.

const std = @import("std");

/// Deterministic single-tape Turing machine with a compact transition table.
///
/// The TuringMachine borrows its transition table. The caller owns the
/// allocation and controls whether it is static, stack-backed, or heap-backed.
///
/// States and tape symbols are dense zero-based ranges. For `n` states and
/// `m` tape symbols, `delta` is an `n * paddedAlphabetSize(m)` table whose
/// `(q, s)` cell is the `Transition` taken on reading `s` in `q`. Cells for
/// `q in {q_accept, q_reject}` and for symbols `m..paddedAlphabetSize(m)-1`
/// are padding and never read during a run.
pub const TuringMachine = struct {
    pub const State = u32;
    pub const Symbol = u32;
    pub const Direction = enum(u2) { left, right, stay };

    pub const Transition = struct {
        next: State,
        write: Symbol,
        dir: Direction,
    };

    pub const Outcome = enum { accept, reject, step_limit };

    pub const RunResult = struct {
        outcome: Outcome,
        steps: u64,
        tape: []Symbol,
        tape_min: i64,
        head: i64,

        /// Returns the symbol written at absolute tape position `pos`, or
        /// `blank` if `pos` is outside the materialized tape range.
        pub fn at(self: *const RunResult, pos: i64, blank: Symbol) Symbol {
            if (pos < self.tape_min) return blank;
            const idx_i64 = pos - self.tape_min;
            if (idx_i64 < 0) return blank;
            const idx: usize = @intCast(idx_i64);
            if (idx >= self.tape.len) return blank;
            return self.tape[idx];
        }

        pub fn deinit(self: *RunResult, allocator: std.mem.Allocator) void {
            allocator.free(self.tape);
            self.* = undefined;
        }
    };

    pub const Owned = struct {
        machine: TuringMachine,
        delta: []Transition,

        /// REQUIRES:
        /// - `self` was constructed with `allocator`-owned `delta` storage.
        /// - `deinit` has not already been called for `self`.
        ///
        /// ENSURES:
        /// - All heap storage owned by `self` is released.
        /// - `self` is no longer usable.
        pub fn deinit(self: *Owned, allocator: std.mem.Allocator) void {
            allocator.free(self.delta);
            self.* = undefined;
        }
    };

    state_size: State,
    tape_alphabet_size: Symbol,
    input_alphabet_size: Symbol,
    blank: Symbol,
    delta: []const Transition,
    start_state: State,
    accept_state: State,
    reject_state: State,
    alphabet_shift: u6,

    /// Creates a new TuringMachine.
    ///
    /// The TuringMachine borrows `delta`; the caller keeps ownership and must
    /// keep it alive for at least as long as the machine is used.
    ///
    /// REQUIRES:
    /// - `1 <= state_size <= maxInt(State)`.
    /// - `1 <= input_alphabet_size < tape_alphabet_size <= maxInt(Symbol)`.
    /// - `input_alphabet_size <= blank < tape_alphabet_size`.
    /// - `delta.len = state_size * paddedAlphabetSize(tape_alphabet_size)`.
    /// - `start_state, accept_state, reject_state in Q`.
    /// - `accept_state != reject_state`.
    /// - For every `q in Q \ {accept_state, reject_state}` and `s in Gamma`,
    ///   `delta[q, s].next in Q` and `delta[q, s].write in Gamma`.
    ///
    /// ENSURES:
    /// - Returns a TuringMachine `M = (Q, Sigma, Gamma, delta, q_0,
    ///   q_accept, q_reject)` borrowing `delta`.
    /// - `Q = {0, ..., state_size - 1}`,
    ///   `Sigma = {0, ..., input_alphabet_size - 1}`,
    ///   `Gamma = {0, ..., tape_alphabet_size - 1}`.
    pub fn init(
        state_size: usize,
        tape_alphabet_size: usize,
        input_alphabet_size: usize,
        blank: Symbol,
        delta: []const Transition,
        start_state: State,
        accept_state: State,
        reject_state: State,
    ) TuringMachine {
        std.debug.assert(state_size > 0);
        std.debug.assert(tape_alphabet_size > 0);
        std.debug.assert(input_alphabet_size > 0);
        std.debug.assert(state_size <= std.math.maxInt(State));
        std.debug.assert(tape_alphabet_size <= std.math.maxInt(Symbol));

        const padded = paddedAlphabetSize(tape_alphabet_size);
        const tm = TuringMachine{
            .state_size = @intCast(state_size),
            .tape_alphabet_size = @intCast(tape_alphabet_size),
            .input_alphabet_size = @intCast(input_alphabet_size),
            .blank = blank,
            .delta = delta,
            .start_state = start_state,
            .accept_state = accept_state,
            .reject_state = reject_state,
            .alphabet_shift = @intCast(std.math.log2_int(usize, padded)),
        };

        std.debug.assert(tm.isTuringMachine());
        return tm;
    }

    /// REQUIRES:
    /// - `self` is a readable TuringMachine value.
    ///
    /// ENSURES:
    /// - Returns `true` iff `self` represents a Turing machine
    ///   `M = (Q, Sigma, Gamma, delta, q_0, q_accept, q_reject)` that
    ///   satisfies the structural invariants documented on `init`.
    fn isTuringMachine(self: *const TuringMachine) bool {
        if (self.state_size == 0) return false;
        if (self.tape_alphabet_size == 0) return false;
        if (self.input_alphabet_size == 0) return false;
        if (self.input_alphabet_size >= self.tape_alphabet_size) return false;
        if (self.blank < self.input_alphabet_size) return false;
        if (self.blank >= self.tape_alphabet_size) return false;
        if (self.start_state >= self.state_size) return false;
        if (self.accept_state >= self.state_size) return false;
        if (self.reject_state >= self.state_size) return false;
        if (self.accept_state == self.reject_state) return false;

        const padded = paddedAlphabetSize(@intCast(self.tape_alphabet_size));
        if (self.alphabet_shift != @as(u6, @intCast(std.math.log2_int(usize, padded)))) return false;
        const expected_len = std.math.mul(usize, @intCast(self.state_size), padded) catch return false;
        if (self.delta.len != expected_len) return false;

        for (0..self.state_size) |q_usize| {
            const q: State = @intCast(q_usize);
            if (q == self.accept_state or q == self.reject_state) continue;
            for (0..self.tape_alphabet_size) |sym_usize| {
                const t = self.next(q, @intCast(sym_usize));
                if (t.next >= self.state_size) return false;
                if (t.write >= self.tape_alphabet_size) return false;
            }
        }
        return true;
    }

    /// Returns the power-of-two row stride required for an alphabet.
    /// This is the smallest power of two that can hold all symbols.
    ///
    /// REQUIRES:
    /// - `1 <= alphabet_size <= maxInt(Symbol)`.
    ///
    /// ENSURES:
    /// - Returns the unique integer `p` such that `p` is a power of two,
    ///   `alphabet_size <= p`, and for every power of two `r < p`,
    ///   `r < alphabet_size`.
    pub inline fn paddedAlphabetSize(alphabet_size: usize) usize {
        std.debug.assert(alphabet_size > 0);
        std.debug.assert(alphabet_size <= std.math.maxInt(Symbol));
        return std.math.ceilPowerOfTwoAssert(usize, alphabet_size);
    }

    /// Returns the transition prescribed by delta for `(state, symbol)`.
    ///
    /// REQUIRES:
    /// - `state in Q \ {accept_state, reject_state}`.
    /// - `symbol in Gamma`.
    pub inline fn next(self: *const TuringMachine, state: State, symbol: Symbol) Transition {
        std.debug.assert(state < self.state_size);
        std.debug.assert(symbol < self.tape_alphabet_size);
        const base = (@as(usize, @intCast(state)) << self.alphabet_shift) + @as(usize, @intCast(symbol));
        return self.delta[base];
    }

    /// Runs the machine on `input` for at most `max_steps` transitions.
    ///
    /// REQUIRES:
    /// - For every `i`, `input[i] in Sigma`.
    /// - `allocator` can serve the tape and the materialized result.
    ///
    /// ENSURES:
    /// - On success, returns a `RunResult` whose `outcome` is:
    ///   - `.accept` if the run halted in `q_accept`,
    ///   - `.reject` if it halted in `q_reject`,
    ///   - `.step_limit` if it exceeded `max_steps` non-halt transitions.
    /// - `tape` contains the symbols at absolute positions
    ///   `tape_min..tape_min + tape.len - 1`, and `head` is the final
    ///   absolute head position. The materialized range covers all positions
    ///   ever read or written, and at minimum the final head position.
    /// - The caller owns `tape` and must call `deinit`.
    pub fn run(
        self: *const TuringMachine,
        allocator: std.mem.Allocator,
        input: []const Symbol,
        max_steps: u64,
    ) std.mem.Allocator.Error!RunResult {
        var tape: Tape = .{ .blank = self.blank };
        defer tape.deinit(allocator);

        for (input, 0..) |sym, i| {
            std.debug.assert(sym < self.input_alphabet_size);
            try tape.write(allocator, @intCast(i), sym);
        }

        var state = self.start_state;
        var head: i64 = 0;
        var steps: u64 = 0;
        var outcome: Outcome = undefined;

        while (true) {
            if (state == self.accept_state) {
                outcome = .accept;
                break;
            }
            if (state == self.reject_state) {
                outcome = .reject;
                break;
            }
            if (steps >= max_steps) {
                outcome = .step_limit;
                break;
            }
            const sym = tape.read(head);
            const t = self.next(state, sym);
            try tape.write(allocator, head, t.write);
            switch (t.dir) {
                .left => head -= 1,
                .right => head += 1,
                .stay => {},
            }
            state = t.next;
            steps += 1;
        }

        const finalized = try tape.finalize(allocator, head);
        return .{
            .outcome = outcome,
            .steps = steps,
            .tape = finalized.tape,
            .tape_min = finalized.tape_min,
            .head = head,
        };
    }
};

const Tape = struct {
    blank: TuringMachine.Symbol,
    right: std.ArrayList(TuringMachine.Symbol) = .empty,
    left: std.ArrayList(TuringMachine.Symbol) = .empty,

    fn deinit(self: *Tape, allocator: std.mem.Allocator) void {
        self.right.deinit(allocator);
        self.left.deinit(allocator);
    }

    fn read(self: *const Tape, pos: i64) TuringMachine.Symbol {
        if (pos >= 0) {
            const idx: usize = @intCast(pos);
            return if (idx < self.right.items.len) self.right.items[idx] else self.blank;
        } else {
            const idx: usize = @intCast(-pos - 1);
            return if (idx < self.left.items.len) self.left.items[idx] else self.blank;
        }
    }

    fn write(self: *Tape, allocator: std.mem.Allocator, pos: i64, sym: TuringMachine.Symbol) !void {
        if (pos >= 0) {
            const idx: usize = @intCast(pos);
            while (self.right.items.len <= idx) try self.right.append(allocator, self.blank);
            self.right.items[idx] = sym;
        } else {
            const idx: usize = @intCast(-pos - 1);
            while (self.left.items.len <= idx) try self.left.append(allocator, self.blank);
            self.left.items[idx] = sym;
        }
    }

    fn finalize(
        self: *Tape,
        allocator: std.mem.Allocator,
        head: i64,
    ) !struct { tape: []TuringMachine.Symbol, tape_min: i64 } {
        if (head >= 0) {
            const idx: usize = @intCast(head);
            while (self.right.items.len <= idx) try self.right.append(allocator, self.blank);
        } else {
            const idx: usize = @intCast(-head - 1);
            while (self.left.items.len <= idx) try self.left.append(allocator, self.blank);
        }

        const total = self.left.items.len + self.right.items.len;
        const buf = try allocator.alloc(TuringMachine.Symbol, total);
        for (self.left.items, 0..) |sym, i| {
            buf[self.left.items.len - 1 - i] = sym;
        }
        @memcpy(buf[self.left.items.len..], self.right.items);
        const tape_min: i64 = -@as(i64, @intCast(self.left.items.len));
        return .{ .tape = buf, .tape_min = tape_min };
    }
};

fn fillHaltRows(buf: []TuringMachine.Transition) void {
    for (buf) |*t| t.* = .{ .next = 0, .write = 0, .dir = .stay };
}

test "TuringMachine - L = {s in {0,1}* | even length} accepts and rejects" {
    const allocator = std.testing.allocator;
    const Symbol = TuringMachine.Symbol;
    const Transition = TuringMachine.Transition;

    const blank: Symbol = 2;
    var delta = [_]Transition{
        .{ .next = 1, .write = 0, .dir = .right },
        .{ .next = 1, .write = 1, .dir = .right },
        .{ .next = 2, .write = blank, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .right },
        .{ .next = 0, .write = 1, .dir = .right },
        .{ .next = 3, .write = blank, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .stay },
    };

    const tm = TuringMachine.init(4, 3, 2, blank, &delta, 0, 2, 3);

    const cases = [_]struct { input: []const Symbol, accept: bool }{
        .{ .input = &[_]Symbol{}, .accept = true },
        .{ .input = &[_]Symbol{0}, .accept = false },
        .{ .input = &[_]Symbol{ 1, 0 }, .accept = true },
        .{ .input = &[_]Symbol{ 0, 1, 0 }, .accept = false },
        .{ .input = &[_]Symbol{ 1, 1, 0, 0 }, .accept = true },
    };

    for (cases) |c| {
        var result = try tm.run(allocator, c.input, 100);
        defer result.deinit(allocator);
        try std.testing.expectEqual(
            if (c.accept) TuringMachine.Outcome.accept else .reject,
            result.outcome,
        );
    }
}

test "TuringMachine - L = {0^n 1^n | n >= 0}" {
    const allocator = std.testing.allocator;
    const Symbol = TuringMachine.Symbol;
    const State = TuringMachine.State;
    const Transition = TuringMachine.Transition;

    // Symbols: 0=0, 1=1, 2=X (crossed 0), 3=Y (crossed 1), 4=blank.
    const blank: Symbol = 4;
    const x: Symbol = 2;
    const y: Symbol = 3;

    // States: 0=q_find_zero, 1=q_seek_one, 2=q_return, 3=q_verify, 4=q_accept,
    //         5=q_reject. Padded alphabet size = 8.
    const padded: usize = 8;
    var delta: [6 * padded]Transition = undefined;
    fillHaltRows(&delta);

    const set = struct {
        fn at(buf: []Transition, st: State, sym: Symbol, t: Transition) void {
            buf[@as(usize, st) * padded + @as(usize, sym)] = t;
        }
    }.at;

    // q_find_zero: scan left-to-right looking for the next unmarked 0.
    set(&delta, 0, 0, .{ .next = 1, .write = x, .dir = .right });
    set(&delta, 0, 1, .{ .next = 5, .write = 1, .dir = .stay });
    set(&delta, 0, x, .{ .next = 0, .write = x, .dir = .right });
    set(&delta, 0, y, .{ .next = 3, .write = y, .dir = .right });
    set(&delta, 0, blank, .{ .next = 4, .write = blank, .dir = .stay });

    // q_seek_one: scan right looking for the next unmarked 1.
    set(&delta, 1, 0, .{ .next = 1, .write = 0, .dir = .right });
    set(&delta, 1, 1, .{ .next = 2, .write = y, .dir = .left });
    set(&delta, 1, x, .{ .next = 5, .write = x, .dir = .stay });
    set(&delta, 1, y, .{ .next = 1, .write = y, .dir = .right });
    set(&delta, 1, blank, .{ .next = 5, .write = blank, .dir = .stay });

    // q_return: scan left back to the leftmost crossed 0, then step right.
    set(&delta, 2, 0, .{ .next = 2, .write = 0, .dir = .left });
    set(&delta, 2, 1, .{ .next = 5, .write = 1, .dir = .stay });
    set(&delta, 2, x, .{ .next = 0, .write = x, .dir = .right });
    set(&delta, 2, y, .{ .next = 2, .write = y, .dir = .left });
    set(&delta, 2, blank, .{ .next = 5, .write = blank, .dir = .stay });

    // q_verify: ensure the remaining tape contains only Ys before the blank.
    set(&delta, 3, 0, .{ .next = 5, .write = 0, .dir = .stay });
    set(&delta, 3, 1, .{ .next = 5, .write = 1, .dir = .stay });
    set(&delta, 3, x, .{ .next = 5, .write = x, .dir = .stay });
    set(&delta, 3, y, .{ .next = 3, .write = y, .dir = .right });
    set(&delta, 3, blank, .{ .next = 4, .write = blank, .dir = .stay });

    const tm = TuringMachine.init(6, 5, 2, blank, &delta, 0, 4, 5);

    const accepts = [_][]const Symbol{
        &[_]Symbol{},
        &[_]Symbol{ 0, 1 },
        &[_]Symbol{ 0, 0, 1, 1 },
        &[_]Symbol{ 0, 0, 0, 1, 1, 1 },
    };
    const rejects = [_][]const Symbol{
        &[_]Symbol{0},
        &[_]Symbol{1},
        &[_]Symbol{ 0, 1, 0 },
        &[_]Symbol{ 1, 0 },
        &[_]Symbol{ 0, 0, 1 },
        &[_]Symbol{ 0, 1, 1 },
    };

    for (accepts) |w| {
        var r = try tm.run(allocator, w, 1024);
        defer r.deinit(allocator);
        try std.testing.expectEqual(TuringMachine.Outcome.accept, r.outcome);
    }
    for (rejects) |w| {
        var r = try tm.run(allocator, w, 1024);
        defer r.deinit(allocator);
        try std.testing.expectEqual(TuringMachine.Outcome.reject, r.outcome);
    }
}

test "TuringMachine - binary increment writes successor and accepts" {
    const allocator = std.testing.allocator;
    const Symbol = TuringMachine.Symbol;
    const Transition = TuringMachine.Transition;

    const blank: Symbol = 2;
    // States: 0=scan_right, 1=carry, 2=accept, 3=reject.
    var delta = [_]Transition{
        .{ .next = 0, .write = 0, .dir = .right },
        .{ .next = 0, .write = 1, .dir = .right },
        .{ .next = 1, .write = blank, .dir = .left },
        .{ .next = 0, .write = 0, .dir = .stay },
        .{ .next = 2, .write = 1, .dir = .stay },
        .{ .next = 1, .write = 0, .dir = .left },
        .{ .next = 2, .write = 1, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .stay },
    };

    const tm = TuringMachine.init(4, 3, 2, blank, &delta, 0, 2, 3);

    {
        var r = try tm.run(allocator, &[_]Symbol{ 1, 0, 1, 1 }, 64);
        defer r.deinit(allocator);
        try std.testing.expectEqual(TuringMachine.Outcome.accept, r.outcome);
        try std.testing.expectEqual(@as(Symbol, 1), r.at(0, blank));
        try std.testing.expectEqual(@as(Symbol, 1), r.at(1, blank));
        try std.testing.expectEqual(@as(Symbol, 0), r.at(2, blank));
        try std.testing.expectEqual(@as(Symbol, 0), r.at(3, blank));
    }

    {
        var r = try tm.run(allocator, &[_]Symbol{ 1, 1, 1 }, 64);
        defer r.deinit(allocator);
        try std.testing.expectEqual(TuringMachine.Outcome.accept, r.outcome);
        try std.testing.expectEqual(@as(Symbol, 1), r.at(-1, blank));
        try std.testing.expectEqual(@as(Symbol, 0), r.at(0, blank));
        try std.testing.expectEqual(@as(Symbol, 0), r.at(1, blank));
        try std.testing.expectEqual(@as(Symbol, 0), r.at(2, blank));
    }

    {
        var r = try tm.run(allocator, &[_]Symbol{0}, 64);
        defer r.deinit(allocator);
        try std.testing.expectEqual(TuringMachine.Outcome.accept, r.outcome);
        try std.testing.expectEqual(@as(Symbol, 1), r.at(0, blank));
    }
}

test "TuringMachine - run reports step_limit when machine does not halt" {
    const allocator = std.testing.allocator;
    const Symbol = TuringMachine.Symbol;
    const Transition = TuringMachine.Transition;

    const blank: Symbol = 2;
    // q0 self-loops on every symbol, never reaching accept/reject.
    var delta = [_]Transition{
        .{ .next = 0, .write = 0, .dir = .right },
        .{ .next = 0, .write = 1, .dir = .right },
        .{ .next = 0, .write = blank, .dir = .right },
        .{ .next = 0, .write = 0, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .stay },
    };

    const tm = TuringMachine.init(3, 3, 2, blank, &delta, 0, 1, 2);

    var r = try tm.run(allocator, &[_]Symbol{ 0, 1 }, 16);
    defer r.deinit(allocator);
    try std.testing.expectEqual(TuringMachine.Outcome.step_limit, r.outcome);
    try std.testing.expectEqual(@as(u64, 16), r.steps);
}

test "TuringMachine - representation invariants" {
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(TuringMachine.State));
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(TuringMachine.Symbol));
    try std.testing.expectEqual(@as(usize, 4), TuringMachine.paddedAlphabetSize(3));
    try std.testing.expectEqual(@as(usize, 8), TuringMachine.paddedAlphabetSize(5));
    try std.testing.expectEqual(@as(usize, 256), TuringMachine.paddedAlphabetSize(256));
}

test "TuringMachine - isTuringMachine rejects malformed representations" {
    const Symbol = TuringMachine.Symbol;
    const Transition = TuringMachine.Transition;

    const blank: Symbol = 2;
    var delta = [_]Transition{
        .{ .next = 1, .write = 0, .dir = .right },    .{ .next = 1, .write = 1, .dir = .right },
        .{ .next = 2, .write = blank, .dir = .stay }, .{ .next = 0, .write = 0, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .right },    .{ .next = 0, .write = 1, .dir = .right },
        .{ .next = 3, .write = blank, .dir = .stay }, .{ .next = 0, .write = 0, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .stay },     .{ .next = 0, .write = 0, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .stay },     .{ .next = 0, .write = 0, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .stay },     .{ .next = 0, .write = 0, .dir = .stay },
        .{ .next = 0, .write = 0, .dir = .stay },     .{ .next = 0, .write = 0, .dir = .stay },
    };

    const ok = TuringMachine.init(4, 3, 2, blank, &delta, 0, 2, 3);
    try std.testing.expect(ok.isTuringMachine());

    const same_accept_reject = TuringMachine{
        .state_size = 4,
        .tape_alphabet_size = 3,
        .input_alphabet_size = 2,
        .blank = blank,
        .delta = &delta,
        .start_state = 0,
        .accept_state = 2,
        .reject_state = 2,
        .alphabet_shift = 2,
    };
    try std.testing.expect(!same_accept_reject.isTuringMachine());

    const blank_in_input = TuringMachine{
        .state_size = 4,
        .tape_alphabet_size = 3,
        .input_alphabet_size = 2,
        .blank = 1,
        .delta = &delta,
        .start_state = 0,
        .accept_state = 2,
        .reject_state = 3,
        .alphabet_shift = 2,
    };
    try std.testing.expect(!blank_in_input.isTuringMachine());

    const sigma_not_subset = TuringMachine{
        .state_size = 4,
        .tape_alphabet_size = 3,
        .input_alphabet_size = 3,
        .blank = blank,
        .delta = &delta,
        .start_state = 0,
        .accept_state = 2,
        .reject_state = 3,
        .alphabet_shift = 2,
    };
    try std.testing.expect(!sigma_not_subset.isTuringMachine());

    var bad_target_delta = delta;
    bad_target_delta[0] = .{ .next = 9, .write = 0, .dir = .right };
    const bad_target = TuringMachine{
        .state_size = 4,
        .tape_alphabet_size = 3,
        .input_alphabet_size = 2,
        .blank = blank,
        .delta = &bad_target_delta,
        .start_state = 0,
        .accept_state = 2,
        .reject_state = 3,
        .alphabet_shift = 2,
    };
    try std.testing.expect(!bad_target.isTuringMachine());
}
