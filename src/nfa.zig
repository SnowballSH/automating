//! A nondeterministic finite automaton (Nfa) is a 5-tuple
//! M = (Q, Sigma, delta, start_state, accepting), where
//! - Q is the set of states, a non-empty finite set
//! - Sigma is the alphabet, a non-empty finite set
//! - delta is the transition function Q x Sigma -> 2^Q
//! - start_state is the start state, an element of Q
//! - accepting is the set of accepting states, a subset of Q.
//!
//! This module also models epsilon-NFAs by allowing an optional epsilon
//! transition function `epsilon: Q -> 2^Q`. A word `w in Sigma*` is accepted
//! iff there is some run that consumes `w` and ends in an accepting state,
//! where each step is either a symbol transition (consuming one input) or an
//! epsilon transition (consuming none).

const std = @import("std");
const dfa_mod = @import("dfa.zig");
pub const Dfa = dfa_mod.Dfa;

/// Nondeterministic finite automaton with bit-packed transition tables.
///
/// The Nfa borrows its transition tables and accepting-state bitset. The
/// caller owns all storage and controls whether the buffers are static,
/// stack-backed, or heap-backed.
///
/// States and symbols are dense zero-based ranges. For `n` states and
/// `w = ceilDiv(n, bits(Word))` words per state-set:
/// - `delta` is an `n * paddedAlphabetSize(m) * w` array of `Word`s. Cell
///   `(q, a)` is the bit-packed set `delta(q, a) subseteq Q`. Cells at
///   symbols `alphabet_size..paddedAlphabetSize(alphabet_size)-1` are padding
///   and are never read for in-range input.
/// - `epsilon`, when present, is an `n * w` array of `Word`s. Row `q` is the
///   bit-packed set of states reachable from `q` by a single epsilon
///   transition. `null` is equivalent to an all-zero epsilon table but skips
///   the epsilon-closure pass entirely.
/// - `accepting` is a bitset with exactly `n` bits.
pub const Nfa = struct {
    pub const State = u32;
    pub const Symbol = u32;
    pub const Word = usize;
    pub const word_bits: u32 = @bitSizeOf(Word);

    pub const ToDfaError = std.mem.Allocator.Error || error{
        TooManyStates,
        TransitionTableTooLarge,
    };

    pub const Owned = struct {
        nfa: Nfa,
        delta: []Word,
        epsilon: ?[]Word,

        /// REQUIRES:
        /// - `self` was constructed with `allocator`-owned storage.
        /// - `deinit` has not already been called for `self`.
        ///
        /// ENSURES:
        /// - All heap storage owned by `self` is released.
        /// - `self` is no longer usable.
        pub fn deinit(self: *Owned, allocator: std.mem.Allocator) void {
            self.nfa.accepting.deinit(allocator);
            allocator.free(self.delta);
            if (self.epsilon) |eps| allocator.free(eps);
            self.* = undefined;
        }
    };

    state_size: State,
    alphabet_size: Symbol,
    state_words: u32,
    delta: []const Word,
    epsilon: ?[]const Word,
    start_state: State,
    accepting: std.DynamicBitSetUnmanaged,
    alphabet_shift: u6,

    /// Creates a new Nfa.
    ///
    /// `alphabet_size` is the logical number of symbols. `delta` must contain
    /// one bit-packed cell of `stateWords(state_size)` words per `(state,
    /// symbol)` pair, where each cell is the subset `delta(state, symbol)`.
    /// `epsilon`, when non-null, must contain one bit-packed row of
    /// `stateWords(state_size)` words per state, where row `q` is the set of
    /// states reachable from `q` by a single epsilon transition.
    ///
    /// The Nfa borrows `delta`, `epsilon`, and `accepting`; callers keep
    /// ownership of all three and must keep them alive for at least as long
    /// as the Nfa is used.
    ///
    /// REQUIRES:
    /// - `1 <= state_size <= maxInt(State)`.
    /// - `1 <= alphabet_size <= maxInt(Symbol)`.
    /// - `delta.len = state_size * paddedAlphabetSize(alphabet_size) * stateWords(state_size)`.
    /// - If `epsilon != null`, `epsilon.?.len = state_size * stateWords(state_size)`.
    /// - `start_state in {0, ..., state_size - 1}`.
    /// - `accepting.capacity() = state_size`.
    /// - For every cell of `delta` and row of `epsilon`, all set bits at
    ///   positions `>= state_size` are zero.
    ///
    /// ENSURES:
    /// - Returns an Nfa `N = (Q, Sigma, delta, start_state, accepting)` with
    ///   optional epsilon transitions.
    /// - `Q = {0, ..., state_size - 1}` and `Sigma = {0, ..., alphabet_size - 1}`.
    /// - `N` borrows `delta`, `epsilon`, and `accepting`.
    pub fn init(
        state_size: usize,
        alphabet_size: usize,
        delta: []const Word,
        epsilon: ?[]const Word,
        start_state: State,
        accepting: std.DynamicBitSetUnmanaged,
    ) Nfa {
        std.debug.assert(state_size > 0);
        std.debug.assert(alphabet_size > 0);
        std.debug.assert(state_size <= std.math.maxInt(State));
        std.debug.assert(alphabet_size <= std.math.maxInt(Symbol));

        const padded = paddedAlphabetSize(alphabet_size);
        const nfa = Nfa{
            .state_size = @intCast(state_size),
            .alphabet_size = @intCast(alphabet_size),
            .state_words = @intCast(stateWords(state_size)),
            .delta = delta,
            .epsilon = epsilon,
            .start_state = start_state,
            .accepting = accepting,
            .alphabet_shift = @intCast(std.math.log2_int(usize, padded)),
        };

        std.debug.assert(nfa.isNfa());
        return nfa;
    }

    /// REQUIRES:
    /// - `self` is a readable `Nfa` value.
    ///
    /// ENSURES:
    /// - Returns `true` iff `self` represents an Nfa
    ///   `N = (Q, Sigma, delta, start_state, accepting)` with non-empty finite
    ///   `Q` and `Sigma`, `start_state in Q`, `accepting subseteq Q`,
    ///   well-formed table sizes, and every transition target in `Q`.
    fn isNfa(self: *const Nfa) bool {
        if (self.state_size == 0) return false;
        if (self.alphabet_size == 0) return false;
        if (self.accepting.capacity() != @as(usize, @intCast(self.state_size))) return false;
        if (self.start_state >= self.state_size) return false;

        const padded = paddedAlphabetSize(@intCast(self.alphabet_size));
        if (self.alphabet_shift != @as(u6, @intCast(std.math.log2_int(usize, padded)))) return false;
        if (self.state_words != stateWords(@intCast(self.state_size))) return false;

        const sw: usize = @intCast(self.state_words);
        const expected_delta_len = blk: {
            const cells = std.math.mul(usize, @intCast(self.state_size), padded) catch return false;
            break :blk std.math.mul(usize, cells, sw) catch return false;
        };
        if (self.delta.len != expected_delta_len) return false;
        if (self.epsilon) |eps| {
            const expected_eps_len = std.math.mul(usize, @intCast(self.state_size), sw) catch return false;
            if (eps.len != expected_eps_len) return false;
        }

        const tail_mask = stateTailMask(@intCast(self.state_size));
        for (0..self.state_size) |q| {
            const qq: State = @intCast(q);
            for (0..self.alphabet_size) |a| {
                const row = self.next(qq, @intCast(a));
                if (sw > 0 and (row[sw - 1] & ~tail_mask) != 0) return false;
            }
            if (self.epsilonNext(qq)) |row| {
                if (sw > 0 and (row[sw - 1] & ~tail_mask) != 0) return false;
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
    ///   `alphabet_size <= p`, and for every power of two `r < p`, `r < alphabet_size`.
    pub inline fn paddedAlphabetSize(alphabet_size: usize) usize {
        std.debug.assert(alphabet_size > 0);
        std.debug.assert(alphabet_size <= std.math.maxInt(Symbol));
        return std.math.ceilPowerOfTwoAssert(usize, alphabet_size);
    }

    /// Returns the number of `Word`s required to represent a state-set bitset.
    ///
    /// REQUIRES:
    /// - `1 <= state_size <= maxInt(State)`.
    ///
    /// ENSURES:
    /// - Returns `ceilDiv(state_size, bits(Word))`.
    pub inline fn stateWords(state_size: usize) usize {
        std.debug.assert(state_size > 0);
        return (state_size + word_bits - 1) / word_bits;
    }

    /// Sets the bit at `position` in `words`.
    ///
    /// REQUIRES:
    /// - `position / bits(Word) < words.len`.
    pub inline fn setBit(words: []Word, position: usize) void {
        const shift: std.math.Log2Int(Word) = @intCast(position % word_bits);
        words[position / word_bits] |= @as(Word, 1) << shift;
    }

    /// Returns whether `position` is set in `words`.
    pub inline fn testBit(words: []const Word, position: usize) bool {
        const shift: std.math.Log2Int(Word) = @intCast(position % word_bits);
        return (words[position / word_bits] >> shift) & 1 != 0;
    }

    /// Bitwise-ORs `src` into `dst`. `dst` and `src` must have the same length.
    pub inline fn unionInto(dst: []Word, src: []const Word) void {
        std.debug.assert(dst.len == src.len);
        for (dst, src) |*d, s| d.* |= s;
    }

    /// Returns whether `a` and `b` share any set bit. Lengths must match.
    pub inline fn intersectsAny(a: []const Word, b: []const Word) bool {
        std.debug.assert(a.len == b.len);
        for (a, b) |x, y| {
            if (x & y != 0) return true;
        }
        return false;
    }

    /// Mask of valid bits within the last `Word` of a `state_size`-bit set.
    inline fn stateTailMask(state_size: usize) Word {
        const bits_in_last: u32 = if (state_size % word_bits == 0) word_bits else @intCast(state_size % word_bits);
        if (bits_in_last == word_bits) return std.math.maxInt(Word);
        return (@as(Word, 1) << @intCast(bits_in_last)) - 1;
    }

    inline fn cellBase(self: *const Nfa, state: State, symbol: Symbol) usize {
        std.debug.assert(state < self.state_size);
        std.debug.assert(symbol < self.alphabet_size);
        const sw: usize = @intCast(self.state_words);
        return ((@as(usize, @intCast(state)) << self.alphabet_shift) + @as(usize, @intCast(symbol))) * sw;
    }

    inline fn epsilonBase(self: *const Nfa, state: State) usize {
        std.debug.assert(state < self.state_size);
        return @as(usize, @intCast(state)) * @as(usize, @intCast(self.state_words));
    }

    /// Returns the bit-packed set `delta(state, symbol) subseteq Q`.
    ///
    /// REQUIRES:
    /// - `state in Q`.
    /// - `symbol in Sigma`.
    pub inline fn next(self: *const Nfa, state: State, symbol: Symbol) []const Word {
        const base = self.cellBase(state, symbol);
        return self.delta[base .. base + self.state_words];
    }

    /// Returns the bit-packed set of states reachable from `state` by a single
    /// epsilon transition, or `null` if this Nfa has no epsilon transitions.
    ///
    /// REQUIRES:
    /// - `state in Q`.
    pub inline fn epsilonNext(self: *const Nfa, state: State) ?[]const Word {
        const eps = self.epsilon orelse return null;
        const base = self.epsilonBase(state);
        return eps[base .. base + self.state_words];
    }

    /// Checks if a state is accepting.
    ///
    /// REQUIRES:
    /// - `state in Q`.
    ///
    /// ENSURES:
    /// - Returns `true` iff `state in accepting`.
    pub inline fn isAccepting(self: *const Nfa, state: State) bool {
        std.debug.assert(state < self.state_size);
        return self.accepting.isSet(@intCast(state));
    }

    /// Updates `set` to its epsilon-closure in place: the smallest superset
    /// such that for every `q in set` and every `p in epsilon(q)`, `p in set`.
    ///
    /// REQUIRES:
    /// - `set.len = state_words`.
    fn epsilonClosureInPlace(self: *const Nfa, set: []Word) void {
        std.debug.assert(set.len == self.state_words);
        if (self.epsilon == null) return;

        var changed = true;
        while (changed) {
            changed = false;
            for (set, 0..) |word, wi| {
                var bits = word;
                while (bits != 0) {
                    const lsb: u32 = @ctz(bits);
                    bits &= bits - 1;
                    const q: State = @intCast(wi * word_bits + lsb);
                    const row = self.epsilonNext(q).?;
                    for (set, row) |*d, s| {
                        const old = d.*;
                        d.* |= s;
                        if (d.* != old) changed = true;
                    }
                }
            }
        }
    }

    /// Processes a list of symbols and returns whether some run accepts.
    ///
    /// REQUIRES:
    /// - For every `i`, `symbols[i] in Sigma`.
    /// - `allocator` can serve two `state_words`-sized scratch buffers.
    ///
    /// ENSURES:
    /// - On success, returns `true` iff some sequence of (epsilon and symbol)
    ///   transitions starting at `start_state` consumes `symbols` in order
    ///   and ends in an accepting state.
    /// - Returns `error.OutOfMemory` if scratch allocation fails.
    pub fn process(self: *const Nfa, allocator: std.mem.Allocator, symbols: []const Symbol) std.mem.Allocator.Error!bool {
        const sw: usize = @intCast(self.state_words);
        var current = try allocator.alloc(Word, sw);
        defer allocator.free(current);
        var next_buf = try allocator.alloc(Word, sw);
        defer allocator.free(next_buf);

        @memset(current, 0);
        setBit(current, self.start_state);
        self.epsilonClosureInPlace(current);

        for (symbols) |symbol| {
            std.debug.assert(symbol < self.alphabet_size);
            @memset(next_buf, 0);
            for (current, 0..) |word, wi| {
                var bits = word;
                while (bits != 0) {
                    const lsb: u32 = @ctz(bits);
                    bits &= bits - 1;
                    const q: State = @intCast(wi * word_bits + lsb);
                    unionInto(next_buf, self.next(q, symbol));
                }
            }
            self.epsilonClosureInPlace(next_buf);
            std.mem.swap([]Word, &current, &next_buf);
        }

        for (current, 0..) |word, wi| {
            var bits = word;
            while (bits != 0) {
                const lsb: u32 = @ctz(bits);
                bits &= bits - 1;
                const q: State = @intCast(wi * word_bits + lsb);
                if (self.accepting.isSet(q)) return true;
            }
        }
        return false;
    }

    /// Builds an equivalent Dfa via the subset construction.
    ///
    /// Each Dfa state corresponds to an epsilon-closed reachable subset of
    /// `Q`; only reachable subsets are materialized. The Dfa start state is
    /// the epsilon-closure of `{start_state}`.
    ///
    /// REQUIRES:
    /// - `allocator` can allocate the returned tables and intermediate
    ///   bookkeeping.
    ///
    /// ENSURES:
    /// - On success, returns a Dfa `D` such that for every `w in Sigma*`,
    ///   `w in L(D)` iff `w in L(self)`.
    /// - If the reachable subset count exceeds `maxInt(Dfa.State)`, returns
    ///   `error.TooManyStates`. If the resulting transition table cannot be
    ///   sized, returns `error.TransitionTableTooLarge`.
    /// - On allocation failure, returns `error.OutOfMemory`.
    /// - The caller owns the returned Dfa storage and must call `deinit`.
    pub fn toDfa(self: *const Nfa, allocator: std.mem.Allocator) ToDfaError!Dfa.Owned {
        const padded = paddedAlphabetSize(@intCast(self.alphabet_size));
        const sw: usize = @intCast(self.state_words);

        var arena = std.heap.ArenaAllocator.init(allocator);
        defer arena.deinit();
        const aalloc = arena.allocator();

        const Context = struct {
            pub fn hash(_: @This(), key: []const Word) u64 {
                return std.hash.Wyhash.hash(0, std.mem.sliceAsBytes(key));
            }
            pub fn eql(_: @This(), a: []const Word, b: []const Word) bool {
                return std.mem.eql(Word, a, b);
            }
        };
        var map = std.HashMap([]const Word, Dfa.State, Context, std.hash_map.default_max_load_percentage).init(allocator);
        defer map.deinit();

        var subsets: std.ArrayList([]const Word) = .empty;
        defer subsets.deinit(allocator);

        var dfa_delta: std.ArrayList(Dfa.State) = .empty;
        errdefer dfa_delta.deinit(allocator);

        const acc_words = try aalloc.alloc(Word, sw);
        @memset(acc_words, 0);
        for (0..self.state_size) |q| {
            if (self.accepting.isSet(q)) setBit(acc_words, q);
        }

        const scratch = try aalloc.alloc(Word, sw);

        {
            const start = try aalloc.alloc(Word, sw);
            @memset(start, 0);
            setBit(start, self.start_state);
            self.epsilonClosureInPlace(start);
            try map.put(start, 0);
            try subsets.append(allocator, start);
        }

        var processed: usize = 0;
        while (processed < subsets.items.len) {
            const cur = subsets.items[processed];
            processed += 1;

            for (0..self.alphabet_size) |sym_usize| {
                const sym: Symbol = @intCast(sym_usize);
                @memset(scratch, 0);
                for (cur, 0..) |word, wi| {
                    var bits = word;
                    while (bits != 0) {
                        const lsb: u32 = @ctz(bits);
                        bits &= bits - 1;
                        const q: State = @intCast(wi * word_bits + lsb);
                        unionInto(scratch, self.next(q, sym));
                    }
                }
                self.epsilonClosureInPlace(scratch);

                const target = if (map.get(scratch)) |idx| idx else blk: {
                    const new_set = try aalloc.alloc(Word, sw);
                    @memcpy(new_set, scratch);
                    if (subsets.items.len > std.math.maxInt(Dfa.State)) return error.TooManyStates;
                    const idx: Dfa.State = @intCast(subsets.items.len);
                    try map.put(new_set, idx);
                    try subsets.append(allocator, new_set);
                    break :blk idx;
                };
                try dfa_delta.append(allocator, target);
            }
            for (self.alphabet_size..padded) |_| {
                try dfa_delta.append(allocator, 0);
            }
        }

        const total = subsets.items.len;
        _ = std.math.mul(usize, total, padded) catch return error.TransitionTableTooLarge;

        const delta_slice = try dfa_delta.toOwnedSlice(allocator);
        errdefer allocator.free(delta_slice);

        var accepting = try std.DynamicBitSetUnmanaged.initEmpty(allocator, total);
        errdefer accepting.deinit(allocator);

        for (subsets.items, 0..) |subset, idx| {
            if (intersectsAny(subset, acc_words)) accepting.set(idx);
        }

        return .{
            .dfa = Dfa.init(total, @intCast(self.alphabet_size), delta_slice, 0, accepting),
            .delta = delta_slice,
        };
    }
};

fn expectNfaLanguage(
    allocator: std.mem.Allocator,
    nfa: *const Nfa,
    alphabet_size: usize,
    max_len: usize,
    predicate: *const fn ([]const Nfa.Symbol) bool,
) !void {
    const input = try allocator.alloc(Nfa.Symbol, max_len);
    defer allocator.free(input);

    for (0..max_len + 1) |len| {
        const word_count = std.math.pow(usize, alphabet_size, len);
        for (0..word_count) |encoded| {
            var remaining = encoded;
            for (0..len) |i| {
                input[i] = @intCast(remaining % alphabet_size);
                remaining /= alphabet_size;
            }
            const word = input[0..len];
            try std.testing.expectEqual(predicate(word), try nfa.process(allocator, word));
        }
    }
}

fn endsInOne(symbols: []const Nfa.Symbol) bool {
    return symbols.len > 0 and symbols[symbols.len - 1] == 1;
}

fn contains01(symbols: []const Nfa.Symbol) bool {
    if (symbols.len < 2) return false;
    var i: usize = 0;
    while (i + 1 < symbols.len) : (i += 1) {
        if (symbols[i] == 0 and symbols[i + 1] == 1) return true;
    }
    return false;
}

fn evenLength(symbols: []const Nfa.Symbol) bool {
    return symbols.len % 2 == 0;
}

fn alwaysAccept(_: []const Nfa.Symbol) bool {
    return true;
}

test "Nfa - L = {s in {0,1}* | s ends in 1}" {
    const allocator = std.testing.allocator;

    // 2-state NFA: state 0 self-loops on 0/1; on '1' also moves to state 1.
    // delta(0, 0) = {0}, delta(0, 1) = {0, 1}
    // delta(1, 0) = {},  delta(1, 1) = {}
    const delta = [_]Nfa.Word{
        0b01, 0b11,
        0b00, 0b00,
    };

    var accepting = try std.DynamicBitSetUnmanaged.initEmpty(allocator, 2);
    defer accepting.deinit(allocator);
    accepting.set(1);

    const nfa = Nfa.init(2, 2, &delta, null, 0, accepting);

    try std.testing.expect(!nfa.isAccepting(0));
    try std.testing.expect(nfa.isAccepting(1));

    const accept_input = [_]Nfa.Symbol{ 0, 1, 1 };
    try std.testing.expect(try nfa.process(allocator, &accept_input));

    const reject_input = [_]Nfa.Symbol{ 1, 0, 1, 0 };
    try std.testing.expect(!try nfa.process(allocator, &reject_input));

    const empty_input = [_]Nfa.Symbol{};
    try std.testing.expect(!try nfa.process(allocator, &empty_input));

    try expectNfaLanguage(allocator, &nfa, 2, 8, endsInOne);
}

test "Nfa - L = {s in {0,1}* | s contains 01}" {
    const allocator = std.testing.allocator;

    // Classic 3-state NFA for "contains 01".
    // delta(0, 0) = {0, 1}, delta(0, 1) = {0}
    // delta(1, 0) = {},     delta(1, 1) = {2}
    // delta(2, 0) = {2},    delta(2, 1) = {2}
    const delta = [_]Nfa.Word{
        0b011, 0b001,
        0b000, 0b100,
        0b100, 0b100,
    };

    var accepting = try std.DynamicBitSetUnmanaged.initEmpty(allocator, 3);
    defer accepting.deinit(allocator);
    accepting.set(2);

    const nfa = Nfa.init(3, 2, &delta, null, 0, accepting);

    const accept_a = [_]Nfa.Symbol{ 0, 1 };
    const accept_b = [_]Nfa.Symbol{ 1, 0, 1, 1 };
    const reject_a = [_]Nfa.Symbol{ 1, 0, 0 };
    const reject_b = [_]Nfa.Symbol{};

    try std.testing.expect(try nfa.process(allocator, &accept_a));
    try std.testing.expect(try nfa.process(allocator, &accept_b));
    try std.testing.expect(!try nfa.process(allocator, &reject_a));
    try std.testing.expect(!try nfa.process(allocator, &reject_b));

    try expectNfaLanguage(allocator, &nfa, 2, 6, contains01);
}

test "Nfa - epsilon transitions accept the (00)* language" {
    const allocator = std.testing.allocator;

    // 4 states. Start q0, accept via epsilon to q3 (also via two-zero loop).
    // Transitions:
    //   q0 -ε-> q3 (accept empty)
    //   q0 -0-> q1
    //   q1 -0-> q2
    //   q2 -ε-> q0
    // Accepting: {q3}
    const delta = [_]Nfa.Word{
        0b0010, 0b0000, // q0
        0b0100, 0b0000, // q1
        0b0000, 0b0000, // q2
        0b0000, 0b0000, // q3
    };
    const epsilon = [_]Nfa.Word{
        0b1000, // q0 -> {q3}
        0b0000,
        0b0001, // q2 -> {q0}
        0b0000,
    };

    var accepting = try std.DynamicBitSetUnmanaged.initEmpty(allocator, 4);
    defer accepting.deinit(allocator);
    accepting.set(3);

    const nfa = Nfa.init(4, 2, &delta, &epsilon, 0, accepting);

    try std.testing.expect(try nfa.process(allocator, &[_]Nfa.Symbol{}));
    try std.testing.expect(try nfa.process(allocator, &[_]Nfa.Symbol{ 0, 0 }));
    try std.testing.expect(try nfa.process(allocator, &[_]Nfa.Symbol{ 0, 0, 0, 0 }));
    try std.testing.expect(!try nfa.process(allocator, &[_]Nfa.Symbol{0}));
    try std.testing.expect(!try nfa.process(allocator, &[_]Nfa.Symbol{ 0, 0, 0 }));
    try std.testing.expect(!try nfa.process(allocator, &[_]Nfa.Symbol{ 0, 1 }));
}

test "Nfa - padded rows support non-power-of-two alphabets" {
    const allocator = std.testing.allocator;

    // 2-state NFA over 3 symbols (padded to stride 4).
    // L = strings over {0,1,2} of even length.
    // delta(0, *) = {1}, delta(1, *) = {0}; padding cell ignored.
    const delta = [_]Nfa.Word{
        0b10, 0b10, 0b10, 0b00,
        0b01, 0b01, 0b01, 0b00,
    };

    var accepting = try std.DynamicBitSetUnmanaged.initEmpty(allocator, 2);
    defer accepting.deinit(allocator);
    accepting.set(0);

    const nfa = Nfa.init(2, 3, &delta, null, 0, accepting);

    try std.testing.expect(try nfa.process(allocator, &[_]Nfa.Symbol{}));
    try std.testing.expect(try nfa.process(allocator, &[_]Nfa.Symbol{ 0, 2 }));
    try std.testing.expect(try nfa.process(allocator, &[_]Nfa.Symbol{ 1, 0, 2, 1 }));
    try std.testing.expect(!try nfa.process(allocator, &[_]Nfa.Symbol{2}));
    try std.testing.expect(!try nfa.process(allocator, &[_]Nfa.Symbol{ 0, 1, 2 }));

    try expectNfaLanguage(allocator, &nfa, 3, 5, evenLength);
}

test "Nfa - representation uses compact state and symbol indexes" {
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(Nfa.State));
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(Nfa.Symbol));
    try std.testing.expectEqual(@as(usize, 4), Nfa.paddedAlphabetSize(3));
    try std.testing.expectEqual(@as(usize, 256), Nfa.paddedAlphabetSize(256));
    try std.testing.expectEqual(@as(usize, 1), Nfa.stateWords(1));
    try std.testing.expectEqual(@as(usize, 1), Nfa.stateWords(@bitSizeOf(Nfa.Word)));
    try std.testing.expectEqual(@as(usize, 2), Nfa.stateWords(@bitSizeOf(Nfa.Word) + 1));
}

test "Nfa - isNfa rejects malformed representations" {
    const allocator = std.testing.allocator;

    const delta = [_]Nfa.Word{
        0b01, 0b11,
        0b00, 0b00,
    };

    var accepting = try std.DynamicBitSetUnmanaged.initEmpty(allocator, 2);
    defer accepting.deinit(allocator);
    accepting.set(1);

    const ok = Nfa.init(2, 2, &delta, null, 0, accepting);
    try std.testing.expect(ok.isNfa());

    const bad_target_delta = [_]Nfa.Word{
        0b01, 0b111, // bit 2 references a non-existent state.
        0b00, 0b00,
    };
    const bad_target = Nfa{
        .state_size = 2,
        .alphabet_size = 2,
        .state_words = 1,
        .delta = &bad_target_delta,
        .epsilon = null,
        .start_state = 0,
        .accepting = accepting,
        .alphabet_shift = 1,
    };
    try std.testing.expect(!bad_target.isNfa());

    const bad_shift = Nfa{
        .state_size = 2,
        .alphabet_size = 2,
        .state_words = 1,
        .delta = &delta,
        .epsilon = null,
        .start_state = 0,
        .accepting = accepting,
        .alphabet_shift = 0,
    };
    try std.testing.expect(!bad_shift.isNfa());

    var wrong_size_accepting = try std.DynamicBitSetUnmanaged.initEmpty(allocator, 3);
    defer wrong_size_accepting.deinit(allocator);
    const bad_accepting_set = Nfa{
        .state_size = 2,
        .alphabet_size = 2,
        .state_words = 1,
        .delta = &delta,
        .epsilon = null,
        .start_state = 0,
        .accepting = wrong_size_accepting,
        .alphabet_shift = 1,
    };
    try std.testing.expect(!bad_accepting_set.isNfa());
}

test "Nfa - toDfa preserves language for plain Nfa" {
    const allocator = std.testing.allocator;

    // contains 01
    const delta = [_]Nfa.Word{
        0b011, 0b001,
        0b000, 0b100,
        0b100, 0b100,
    };
    var accepting = try std.DynamicBitSetUnmanaged.initEmpty(allocator, 3);
    defer accepting.deinit(allocator);
    accepting.set(2);

    const nfa = Nfa.init(3, 2, &delta, null, 0, accepting);

    var owned = try nfa.toDfa(allocator);
    defer owned.deinit(allocator);

    try expectDfaLanguage(allocator, &owned.dfa, 2, 6, contains01);
}

test "Nfa - toDfa preserves language for epsilon Nfa" {
    const allocator = std.testing.allocator;

    // (00)* via epsilon transitions, same machine as the epsilon test.
    const delta = [_]Nfa.Word{
        0b0010, 0b0000,
        0b0100, 0b0000,
        0b0000, 0b0000,
        0b0000, 0b0000,
    };
    const epsilon = [_]Nfa.Word{
        0b1000,
        0b0000,
        0b0001,
        0b0000,
    };
    var accepting = try std.DynamicBitSetUnmanaged.initEmpty(allocator, 4);
    defer accepting.deinit(allocator);
    accepting.set(3);

    const nfa = Nfa.init(4, 2, &delta, &epsilon, 0, accepting);

    var owned = try nfa.toDfa(allocator);
    defer owned.deinit(allocator);

    try std.testing.expect(owned.dfa.process(&[_]Dfa.Symbol{}));
    try std.testing.expect(owned.dfa.process(&[_]Dfa.Symbol{ 0, 0 }));
    try std.testing.expect(owned.dfa.process(&[_]Dfa.Symbol{ 0, 0, 0, 0 }));
    try std.testing.expect(!owned.dfa.process(&[_]Dfa.Symbol{0}));
    try std.testing.expect(!owned.dfa.process(&[_]Dfa.Symbol{ 0, 0, 0 }));
    try std.testing.expect(!owned.dfa.process(&[_]Dfa.Symbol{ 0, 1 }));
}

fn expectDfaLanguage(
    allocator: std.mem.Allocator,
    d: *const Dfa,
    alphabet_size: usize,
    max_len: usize,
    predicate: *const fn ([]const Dfa.Symbol) bool,
) !void {
    const input = try allocator.alloc(Dfa.Symbol, max_len);
    defer allocator.free(input);

    for (0..max_len + 1) |len| {
        const word_count = std.math.pow(usize, alphabet_size, len);
        for (0..word_count) |encoded| {
            var remaining = encoded;
            for (0..len) |i| {
                input[i] = @intCast(remaining % alphabet_size);
                remaining /= alphabet_size;
            }
            const word = input[0..len];
            try std.testing.expectEqual(predicate(word), d.process(word));
        }
    }
}
