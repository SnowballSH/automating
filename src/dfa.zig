//! A deterministic finite automaton (DFA) is a 5-tuple
//! M = (Q, Sigma, delta, q0, F), where
//! - Q is the set of states, a non-empty finite set
//! - Sigma is the alphabet, a non-empty finite set
//! - delta is the transition function Q x Sigma -> Q
//! - q0 is the start state, an element of Q
//! - F is the set of accepting states, a subset of Q.

const std = @import("std");

/// The following struct implements an optimized DFA.
///
/// The table uses a compact `u32` state representation. On a 64-bit target this
/// halves transition-table bandwidth compared with `usize`, which matters
/// because DFA execution is usually one dependent table load per input symbol.
///
/// Each logical row is padded from `alphabetSize` to the next power of two.
/// Padded cells are never addressed by valid input symbols; they exist so the
/// row base can be computed as `state << alphabetShift` instead of
/// `state * alphabetSize`. That removes a multiply from the transition hot path
/// and leaves a single add after the shift.
///
/// The DFA borrows its transition table and accepting-state bitset. The caller
/// owns both allocations and controls whether the table is static, stack-backed,
/// or heap-backed.
///
/// Assumptions: if we have n states and m logical symbols, then:
/// 1. Q is simply {0, 1, 2, ..., n-1}
/// 2. Sigma is simply {0, 1, 2, ..., m-1}
/// 3. delta is a n by paddedAlphabetSize(m) table, each live cell containing a state
/// 4. q0 is an integer in {0, 1, 2, ..., n-1}
/// 5. F is a bitset of length n.
pub const DFA = struct {
    /// Compact state identifier used by the transition table.
    pub const State = u32;

    /// Compact alphabet symbol identifier used by input streams.
    pub const Symbol = u32;

    stateSize: State,
    alphabetSize: State,
    delta: []const State,
    q0: State,
    F: std.DynamicBitSetUnmanaged,
    alphabetShift: u6,

    /// Creates a new optimized DFA.
    ///
    /// `alphabetSize` is the logical number of symbols accepted by `next`,
    /// `processFromState`, and `process`. `delta` must contain one row per
    /// state, and each row must have `paddedAlphabetSize(alphabetSize)` cells.
    /// Cells at symbols `alphabetSize..paddedAlphabetSize(alphabetSize)-1` are
    /// padding and are never read for valid input.
    ///
    /// The DFA borrows `delta` and `F`; callers keep ownership of both and must
    /// keep them alive for at least as long as the DFA is used.
    pub fn init(stateSize: usize, alphabetSize: usize, delta: []const State, q0: State, F: std.DynamicBitSetUnmanaged) DFA {
        validate(stateSize, alphabetSize, delta, q0, F);

        return DFA{
            .stateSize = @intCast(stateSize),
            .alphabetSize = @intCast(alphabetSize),
            .delta = delta,
            .q0 = q0,
            .F = F,
            .alphabetShift = powerOfTwoShift(paddedAlphabetSize(alphabetSize)),
        };
    }

    /// Verifies that constructor inputs fit the compact DFA representation.
    fn validate(stateSize: usize, alphabetSize: usize, delta: []const State, q0: State, F: std.DynamicBitSetUnmanaged) void {
        const padded_size = paddedAlphabetSize(alphabetSize);

        std.debug.assert(stateSize > 0);
        std.debug.assert(alphabetSize > 0);
        std.debug.assert(stateSize <= std.math.maxInt(State));
        std.debug.assert(alphabetSize <= std.math.maxInt(Symbol));
        std.debug.assert(delta.len == (std.math.mul(usize, stateSize, padded_size) catch unreachable));
        std.debug.assert(q0 < stateSize);
        std.debug.assert(F.capacity() >= stateSize);
    }

    /// Returns the power-of-two row stride required for an alphabet.
    ///
    /// Callers use this when allocating or statically declaring `delta`.
    /// For example, a DFA with `3` logical symbols must provide rows of `4`
    /// cells, while a DFA with `256` symbols already has rows of `256` cells.
    pub fn paddedAlphabetSize(alphabetSize: usize) usize {
        std.debug.assert(alphabetSize > 0);
        std.debug.assert(alphabetSize <= std.math.maxInt(Symbol));
        return std.math.ceilPowerOfTwoAssert(usize, alphabetSize);
    }

    /// Returns log2(value), assuming `value` is a non-zero power of two.
    fn powerOfTwoShift(value: usize) u6 {
        std.debug.assert(value > 0);
        std.debug.assert((value & (value - 1)) == 0);
        return @intCast(@ctz(value));
    }

    /// Converts a compact state or symbol into a host-sized slice index.
    inline fn indexOf(value: anytype) usize {
        return @intCast(value);
    }

    /// Returns the first transition-table index for a state's row.
    inline fn rowBase(self: *const DFA, state: State) usize {
        return indexOf(state) << self.alphabetShift;
    }

    /// Checks a symbol in debug builds and returns it as a host-sized index.
    inline fn checkedSymbolIndex(self: *const DFA, symbol: Symbol) usize {
        std.debug.assert(symbol < self.alphabetSize);
        return indexOf(symbol);
    }

    /// Returns the state advanced by the symbol.
    pub inline fn next(self: *const DFA, currentState: State, symbol: Symbol) State {
        std.debug.assert(currentState < self.stateSize);
        return self.delta[self.rowBase(currentState) + self.checkedSymbolIndex(symbol)];
    }

    /// Checks if a state is accepting.
    pub inline fn isAccepting(self: *const DFA, state: State) bool {
        std.debug.assert(state < self.stateSize);
        return self.F.isSet(indexOf(state));
    }

    /// Processes a list of symbols in order from `startState`.
    pub fn processFromState(self: *const DFA, symbols: []const Symbol, startState: State) State {
        std.debug.assert(startState < self.stateSize);

        var cur_state = startState;
        const shift = self.alphabetShift;
        for (symbols) |symbol| {
            const cur_index = indexOf(cur_state);
            const symbol_index = self.checkedSymbolIndex(symbol);
            cur_state = self.delta[(cur_index << shift) + symbol_index];
        }

        return cur_state;
    }

    /// Processes a list of symbols in order from q0 and returns
    /// whether or not the DFA accepts the input.
    pub fn process(self: *const DFA, symbols: []const Symbol) bool {
        return self.isAccepting(self.processFromState(symbols, self.q0));
    }
};

// Unit Tests

test "DFA - L = {s in {0,1}* | s ends in 1}" {
    const allocator = std.testing.allocator;

    // Alphabet: {0, 1}
    // States: 0 (last was '0' or start), 1 (last was '1')
    const delta = [_]DFA.State{
        0, 1, // State 0 transitions: 0 -> 0, 1 -> 1
        0, 1, // State 1 transitions: 0 -> 0, 1 -> 1
    };

    var F = try std.DynamicBitSetUnmanaged.initEmpty(allocator, 2);
    defer F.deinit(allocator);
    F.set(1); // State 1 is our only accepting state

    const dfa = DFA.init(2, 2, &delta, 0, F);

    try std.testing.expect(!dfa.isAccepting(0));
    try std.testing.expect(dfa.isAccepting(1));

    try std.testing.expectEqual(@as(DFA.State, 1), dfa.next(0, 1));
    try std.testing.expectEqual(@as(DFA.State, 0), dfa.next(1, 0));

    const accept_input = [_]DFA.Symbol{ 0, 1, 1 };
    try std.testing.expect(dfa.process(&accept_input));

    const single_accept = [_]DFA.Symbol{1};
    try std.testing.expect(dfa.process(&single_accept));

    const reject_input = [_]DFA.Symbol{ 1, 0, 1, 0 };
    try std.testing.expect(!dfa.process(&reject_input));

    const trivial_reject = [_]DFA.Symbol{};
    try std.testing.expect(!dfa.process(&trivial_reject));
}

test "DFA - L = {s in {0,1}* | # of 1s in s is a multiple of 3}" {
    const allocator = std.testing.allocator;

    // Alphabet: {0, 1}
    // States track the count of '1's modulo 3.
    // States: 0 (mod 3 == 0), 1 (mod 3 == 1), 2 (mod 3 == 2)
    const delta = [_]DFA.State{
        0, 1, // State 0: '0' -> 0, '1' -> 1
        1, 2, // State 1: '0' -> 1, '1' -> 2
        2, 0, // State 2: '0' -> 2, '1' -> 0
    };

    var F = try std.DynamicBitSetUnmanaged.initEmpty(allocator, 3);
    defer F.deinit(allocator);
    F.set(0); // Accept iff the number of 1s is a multiple of 3

    const dfa = DFA.init(3, 2, &delta, 0, F);

    const ones = [_]DFA.Symbol{ 1, 1 };
    try std.testing.expectEqual(@as(DFA.State, 0), dfa.processFromState(&ones, 1));

    const zeros = [_]DFA.Symbol{0};
    try std.testing.expectEqual(@as(DFA.State, 2), dfa.processFromState(&zeros, 2));

    const input_accept = [_]DFA.Symbol{ 1, 0, 1, 0, 1 };
    try std.testing.expect(dfa.process(&input_accept));

    const input_accept_2 = [_]DFA.Symbol{1} ** 2025;
    try std.testing.expect(dfa.process(&input_accept_2));

    const input_reject = [_]DFA.Symbol{ 1, 0, 1 };
    try std.testing.expect(!dfa.process(&input_reject));

    const trivial_accept = [_]DFA.Symbol{};
    try std.testing.expect(dfa.process(&trivial_accept));
}

test "DFA - Single State Automaton" {
    const allocator = std.testing.allocator;

    // A machine with 1 state that accepts everything
    const delta = [_]DFA.State{ 0, 0, 0, 0 }; // 3 live symbols plus 1 padded cell

    var F = try std.DynamicBitSetUnmanaged.initEmpty(allocator, 1);
    defer F.deinit(allocator);
    F.set(0);

    const dfa = DFA.init(1, 3, &delta, 0, F);

    const input = [_]DFA.Symbol{ 2, 0, 1, 2, 2 };

    try std.testing.expectEqual(@as(DFA.State, 0), dfa.processFromState(&input, 0));
    try std.testing.expect(dfa.process(&input));
}

test "DFA - representation uses compact state and symbol indexes" {
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(DFA.State));
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(DFA.Symbol));
    try std.testing.expectEqual(@as(usize, 4), DFA.paddedAlphabetSize(3));
    try std.testing.expectEqual(@as(usize, 256), DFA.paddedAlphabetSize(256));
}

test "DFA - Pseudo-Random Graph Stress Test" {
    const allocator = std.testing.allocator;
    const N: usize = 251;
    const M: usize = 15251;
    const padded_M = DFA.paddedAlphabetSize(M);

    const delta = try allocator.alloc(DFA.State, N * padded_M);
    defer allocator.free(delta);

    // PRNG
    var prng_state: usize = 15251;
    for (0..N) |state| {
        const row_base = state * padded_M;
        for (0..M) |symbol| {
            prng_state = prng_state *% 1103515245 +% 12345;
            delta[row_base + symbol] = @intCast(prng_state % N);
        }
        for (M..padded_M) |symbol| {
            delta[row_base + symbol] = 0;
        }
    }

    var F = try std.DynamicBitSetUnmanaged.initEmpty(allocator, N);
    defer F.deinit(allocator);

    for (0..N) |i| {
        prng_state = prng_state *% 1103515245 +% 12345;
        if (prng_state % 7 == 0) {
            F.set(i);
        }
    }

    const dfa = DFA.init(N, M, delta, 0, F);

    const input_len = 15251;
    const input = try allocator.alloc(DFA.Symbol, input_len);
    defer allocator.free(input);

    for (0..input_len) |i| {
        prng_state = prng_state *% 1103515245 +% 12345;
        input[i] = @intCast(prng_state % M);
    }

    var expected_state: DFA.State = 0;
    for (input) |sym| {
        const expected_index: usize = @intCast(expected_state);
        const symbol_index: usize = @intCast(sym);
        expected_state = delta[expected_index * padded_M + symbol_index];
    }

    const actual_state = dfa.processFromState(input, 0);

    try std.testing.expectEqual(expected_state, actual_state);
    try std.testing.expectEqual(F.isSet(expected_state), dfa.process(input));
}

test "DFA - padded rows support non-power-of-two alphabets" {
    const allocator = std.testing.allocator;

    const delta = [_]DFA.State{
        1, 0, 2, 0,
        2, 1, 0, 0,
        0, 2, 1, 0,
    };

    var F = try std.DynamicBitSetUnmanaged.initEmpty(allocator, 3);
    defer F.deinit(allocator);
    F.set(2);

    const dfa = DFA.init(3, 3, &delta, 0, F);

    try std.testing.expectEqual(@as(DFA.State, 1), dfa.next(1, 1));

    const input = [_]DFA.Symbol{ 0, 2, 2 };
    try std.testing.expectEqual(@as(DFA.State, 2), dfa.processFromState(&input, 0));
    try std.testing.expect(dfa.process(&input));
}
