//! A deterministic finite automaton (DFA) is a 5-tuple
//! M = (Q, Sigma, delta, q0, F), where
//! - Q is the set of states, a non-empty finite set
//! - Sigma is the alphabet, a non-empty finite set
//! - delta is the transition function Q x Sigma -> Q
//! - q0 is the start state, an element of Q
//! - F is the set of accepting states, a subset of Q.

const std = @import("std");

/// The following struct implements an optimized DFA.
/// Assumptions: if we have n states and m symbols, then:
/// 1. Q is simply {0, 1, 2, ..., n-1}
/// 2. Sigma is simply {0, 1, 2, ..., m-1}
/// 3. delta is a n by m table, each cell containing a state
/// 4. q0 is an integer in {0, 1, 2, ..., n-1}
/// 5. F is a bitset of length n.
pub const DFA = struct {
    stateSize: usize,
    alphabetSize: usize,
    delta: []usize,
    q0: usize,
    F: std.DynamicBitSetUnmanaged,

    /// Creates a new optimized DFA.
    pub fn init(stateSize: usize, alphabetSize: usize, delta: []usize, q0: usize, F: std.DynamicBitSetUnmanaged) DFA {
        std.debug.assert(delta.len == stateSize * alphabetSize);
        std.debug.assert(q0 < stateSize);
        std.debug.assert(F.capacity() >= stateSize);

        return DFA{
            .stateSize = stateSize,
            .alphabetSize = alphabetSize,
            .delta = delta,
            .q0 = q0,
            .F = F,
        };
    }

    /// Returns the state advanced by the symbol.
    pub inline fn next(self: DFA, currentState: usize, symbol: usize) usize {
        return self.delta[currentState * self.alphabetSize + symbol];
    }

    /// Checks if a state is accepting.
    pub inline fn isAccepting(self: DFA, state: usize) bool {
        return self.F.isSet(state);
    }

    /// Processes a list of symbols in order from `startState`.
    pub fn processFromState(self: DFA, symbols: []usize, startState: usize) usize {
        var curState = startState;
        for (symbols) |symbol| {
            curState = self.next(curState, symbol);
        }
        return curState;
    }

    /// Processes a list of symbols in order from q0 and returns
    /// whether or not the DFA accepts the input.
    pub fn process(self: DFA, symbols: []usize) bool {
        return self.isAccepting(self.processFromState(symbols, self.q0));
    }
};

// Unit Tests

test "DFA - L = {s in {0,1}* | s ends in 1}" {
    const allocator = std.testing.allocator;

    // Alphabet: {0, 1}
    // States: 0 (last was '0' or start), 1 (last was '1')
    var delta = [_]usize{
        0, 1, // State 0 transitions: 0 -> 0, 1 -> 1
        0, 1, // State 1 transitions: 0 -> 0, 1 -> 1
    };

    var F = try std.DynamicBitSetUnmanaged.initEmpty(allocator, 2);
    defer F.deinit(allocator);
    F.set(1); // State 1 is our only accepting state

    const dfa = DFA.init(2, 2, &delta, 0, F);

    try std.testing.expect(!dfa.isAccepting(0));
    try std.testing.expect(dfa.isAccepting(1));

    try std.testing.expectEqual(@as(usize, 1), dfa.next(0, 1));
    try std.testing.expectEqual(@as(usize, 0), dfa.next(1, 0));

    var accept_input = [_]usize{ 0, 1, 1 };
    try std.testing.expect(dfa.process(&accept_input));

    var single_accept = [_]usize{1};
    try std.testing.expect(dfa.process(&single_accept));

    var reject_input = [_]usize{ 1, 0, 1, 0 };
    try std.testing.expect(!dfa.process(&reject_input));

    var trivial_reject = [_]usize{};
    try std.testing.expect(!dfa.process(&trivial_reject));
}

test "DFA - L = {s in {0,1}* | # of 1s in s is a multiple of 3}" {
    const allocator = std.testing.allocator;

    // Alphabet: {0, 1}
    // States track the count of '1's modulo 3.
    // States: 0 (mod 3 == 0), 1 (mod 3 == 1), 2 (mod 3 == 2)
    var delta = [_]usize{
        0, 1, // State 0: '0' -> 0, '1' -> 1
        1, 2, // State 1: '0' -> 1, '1' -> 2
        2, 0, // State 2: '0' -> 2, '1' -> 0
    };

    var F = try std.DynamicBitSetUnmanaged.initEmpty(allocator, 3);
    defer F.deinit(allocator);
    F.set(0); // Accept iff the number of 1s is a multiple of 3

    const dfa = DFA.init(3, 2, &delta, 0, F);

    var ones = [_]usize{ 1, 1 };
    try std.testing.expectEqual(@as(usize, 0), dfa.processFromState(&ones, 1));

    var zeros = [_]usize{0};
    try std.testing.expectEqual(@as(usize, 2), dfa.processFromState(&zeros, 2));

    var input_accept = [_]usize{ 1, 0, 1, 0, 1 };
    try std.testing.expect(dfa.process(&input_accept));

    var input_accept_2 = [_]usize{1} ** 2025;
    try std.testing.expect(dfa.process(&input_accept_2));

    var input_reject = [_]usize{ 1, 0, 1 };
    try std.testing.expect(!dfa.process(&input_reject));

    var trivial_accept = [_]usize{};
    try std.testing.expect(dfa.process(&trivial_accept));
}

test "DFA - Single State Automaton" {
    const allocator = std.testing.allocator;

    // A machine with 1 state that accepts everything
    var delta = [_]usize{ 0, 0, 0 }; // State 0 transitions to 0 for all 3 symbols

    var F = try std.DynamicBitSetUnmanaged.initEmpty(allocator, 1);
    defer F.deinit(allocator);
    F.set(0);

    const dfa = DFA.init(1, 3, &delta, 0, F);

    var input = [_]usize{ 2, 0, 1, 2, 2 };

    try std.testing.expectEqual(@as(usize, 0), dfa.processFromState(&input, 0));
    try std.testing.expect(dfa.process(&input));
}

test "DFA - Pseudo-Random Graph Stress Test" {
    const allocator = std.testing.allocator;
    const N: usize = 251;
    const M: usize = 15251;

    var delta = try allocator.alloc(usize, N * M);
    defer allocator.free(delta);

    // PRNG
    var prng_state: usize = 15251;
    for (0..N * M) |i| {
        prng_state = prng_state *% 1103515245 +% 12345;
        delta[i] = prng_state % N;
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
    var input = try allocator.alloc(usize, input_len);
    defer allocator.free(input);

    for (0..input_len) |i| {
        prng_state = prng_state *% 1103515245 +% 12345;
        input[i] = prng_state % M;
    }

    var expected_state: usize = 0;
    for (input) |sym| {
        expected_state = delta[expected_state * M + sym];
    }

    const actual_state = dfa.processFromState(input, 0);

    try std.testing.expectEqual(expected_state, actual_state);
    try std.testing.expectEqual(F.isSet(expected_state), dfa.process(input));
}
