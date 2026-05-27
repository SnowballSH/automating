//! A deterministic finite automaton (Dfa) is a 5-tuple
//! M = (Q, Sigma, delta, start_state, accepting), where
//! - Q is the set of states, a non-empty finite set
//! - Sigma is the alphabet, a non-empty finite set
//! - delta is the transition function Q x Sigma -> Q
//! - start_state is the start state, an element of Q
//! - accepting is the set of accepting states, a subset of Q.

const std = @import("std");

/// Deterministic finite automaton with a compact transition table.
///
/// The Dfa borrows its transition table and accepting-state bitset. The caller
/// owns both allocations and controls whether the table is static, stack-backed,
/// or heap-backed.
///
/// States and symbols are dense zero-based ranges. For `n` states and `m`
/// symbols, `delta` is an `n * paddedAlphabetSize(m)` table and `accepting` is a bitset
/// with exactly `n` bits.
pub const Dfa = struct {
    pub const State = u32;
    pub const Symbol = u32;
    pub const ProductError = std.mem.Allocator.Error || error{
        IncompatibleAlphabets,
        TooManyStates,
        TransitionTableTooLarge,
    };

    pub const Owned = struct {
        dfa: Dfa,
        delta: []State,

        /// REQUIRES:
        /// - `self` was returned by `unionWith` or `intersectWith` using `allocator`.
        /// - `deinit` has not already been called for `self`.
        ///
        /// ENSURES:
        /// - All heap storage owned by `self` is released.
        /// - `self` is no longer usable.
        pub fn deinit(self: *Owned, allocator: std.mem.Allocator) void {
            self.dfa.accepting.deinit(allocator);
            allocator.free(self.delta);
            self.* = undefined;
        }
    };

    state_size: State,
    alphabet_size: Symbol,
    delta: []const State,
    start_state: State,
    accepting: std.DynamicBitSetUnmanaged,
    alphabet_shift: u6,

    /// Creates a new Dfa.
    ///
    /// `alphabet_size` is the logical number of symbols accepted by `next`,
    /// `processFromState`, and `process`. `delta` must contain one row per
    /// state, and each row must have `paddedAlphabetSize(alphabet_size)` cells.
    /// Cells at symbols `alphabet_size..paddedAlphabetSize(alphabet_size)-1` are
    /// padding and are never read for in-range input.
    ///
    /// The Dfa borrows `delta` and `accepting`; callers keep ownership of both and must
    /// keep them alive for at least as long as the Dfa is used.
    ///
    /// REQUIRES:
    /// - `1 <= state_size <= maxInt(State)`.
    /// - `1 <= alphabet_size <= maxInt(Symbol)`.
    /// - `delta.len = state_size * paddedAlphabetSize(alphabet_size)`.
    /// - `start_state in {0, ..., state_size - 1}`.
    /// - `accepting.capacity() = state_size`.
    /// - For every `q in Q` and `a in Sigma`, `delta[q, a] in Q`.
    ///
    /// ENSURES:
    /// - Returns a Dfa `D = (Q, Sigma, delta, start_state, accepting)`.
    /// - `Q = {0, ..., state_size - 1}` and `Sigma = {0, ..., alphabet_size - 1}`.
    /// - `D` borrows `delta` and `accepting`.
    pub fn init(state_size: usize, alphabet_size: usize, delta: []const State, start_state: State, accepting: std.DynamicBitSetUnmanaged) Dfa {
        std.debug.assert(state_size > 0);
        std.debug.assert(alphabet_size > 0);
        std.debug.assert(state_size <= std.math.maxInt(State));
        std.debug.assert(alphabet_size <= std.math.maxInt(Symbol));

        const dfa = Dfa{
            .state_size = @intCast(state_size),
            .alphabet_size = @intCast(alphabet_size),
            .delta = delta,
            .start_state = start_state,
            .accepting = accepting,
            .alphabet_shift = @intCast(std.math.log2_int(usize, paddedAlphabetSize(alphabet_size))),
        };

        std.debug.assert(dfa.isDfa());
        return dfa;
    }

    /// REQUIRES:
    /// - `self` is a readable `Dfa` value.
    ///
    /// ENSURES:
    /// - Returns `true` iff `self` represents a Dfa
    ///   `D = (Q, Sigma, delta, start_state, accepting)` with non-empty finite `Q` and `Sigma`,
    ///   `start_state in Q`, `accepting subseteq Q`, and total transition function
    ///   `delta: Q x Sigma -> Q`.
    fn isDfa(self: *const Dfa) bool {
        if (self.state_size == 0) return false;
        if (self.alphabet_size == 0) return false;
        if (self.accepting.capacity() != @as(usize, @intCast(self.state_size))) return false;
        if (self.start_state >= self.state_size) return false;

        const padded_size = paddedAlphabetSize(@intCast(self.alphabet_size));
        if (self.alphabet_shift != @as(u6, @intCast(std.math.log2_int(usize, padded_size)))) return false;

        const expected_delta_len = std.math.mul(usize, @intCast(self.state_size), padded_size) catch return false;
        if (self.delta.len != expected_delta_len) return false;

        for (0..self.state_size) |state| {
            const row_start = state << self.alphabet_shift;
            for (0..self.alphabet_size) |symbol| {
                if (self.delta[row_start + symbol] >= self.state_size) return false;
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

    /// Returns the first transition-table index for a state's row.
    ///
    /// REQUIRES:
    /// - `self.isDfa() = true`.
    /// - `state in Q`.
    ///
    /// ENSURES:
    /// - Returns `state * paddedAlphabetSize(self.alphabet_size)`.
    inline fn rowBase(self: *const Dfa, state: State) usize {
        std.debug.assert(state < self.state_size);
        return @as(usize, @intCast(state)) << self.alphabet_shift;
    }

    /// Checks a symbol in debug builds and returns it as a host-sized index.
    ///
    /// REQUIRES:
    /// - `self.isDfa() = true`.
    /// - `symbol in Sigma`.
    ///
    /// ENSURES:
    /// - Returns the `usize` integer equal to `symbol`.
    inline fn checkedSymbolIndex(self: *const Dfa, symbol: Symbol) usize {
        std.debug.assert(symbol < self.alphabet_size);
        return @intCast(symbol);
    }

    /// Returns the state advanced by the symbol.
    ///
    /// REQUIRES:
    /// - `current_state in Q`.
    /// - `symbol in Sigma`.
    ///
    /// ENSURES:
    /// - Returns `delta(current_state, symbol)`.
    pub inline fn next(self: *const Dfa, current_state: State, symbol: Symbol) State {
        std.debug.assert(current_state < self.state_size);
        return self.delta[self.rowBase(current_state) + self.checkedSymbolIndex(symbol)];
    }

    /// Checks if a state is accepting.
    ///
    /// REQUIRES:
    /// - `state in Q`.
    ///
    /// ENSURES:
    /// - Returns `true` iff `state in accepting`.
    pub inline fn isAccepting(self: *const Dfa, state: State) bool {
        std.debug.assert(state < self.state_size);
        return self.accepting.isSet(@intCast(state));
    }

    /// Processes a list of symbols in order from `start_state`.
    ///
    /// REQUIRES:
    /// - `start_state in Q`.
    /// - For every `i`, `symbols[i] in Sigma`.
    ///
    /// ENSURES:
    /// - Returns `deltaHat(start_state, symbols)`, where
    ///   `deltaHat(q, []) = q` and
    ///   `deltaHat(q, aw) = deltaHat(delta(q, a), w)`.
    pub fn processFromState(self: *const Dfa, symbols: []const Symbol, start_state: State) State {
        std.debug.assert(start_state < self.state_size);

        var cur_state = start_state;
        for (symbols) |symbol| {
            cur_state = self.next(cur_state, symbol);
        }

        return cur_state;
    }

    /// Processes a list of symbols from start_state and returns whether the Dfa accepts it.
    ///
    /// REQUIRES:
    /// - For every `i`, `symbols[i] in Sigma`.
    ///
    /// ENSURES:
    /// - Returns `true` iff `deltaHat(start_state, symbols) in accepting`.
    pub fn process(self: *const Dfa, symbols: []const Symbol) bool {
        return self.isAccepting(self.processFromState(symbols, self.start_state));
    }

    /// REQUIRES:
    /// - `left in Q_left`.
    /// - `right in Q_right`.
    /// - `|Q_left| * |Q_right| <= maxInt(State)`.
    /// - `right_state_size = |Q_right|`.
    ///
    /// ENSURES:
    /// - Returns the dense product-state index for `(left, right)`.
    inline fn pairState(left: State, right: State, right_state_size: usize) State {
        std.debug.assert(right_state_size > 0);
        std.debug.assert(@as(usize, @intCast(right)) < right_state_size);

        const row_offset = std.math.mul(usize, @intCast(left), right_state_size) catch {
            std.debug.assert(false);
            unreachable;
        };
        const pair_index = std.math.add(usize, row_offset, @intCast(right)) catch {
            std.debug.assert(false);
            unreachable;
        };
        std.debug.assert(pair_index <= std.math.maxInt(State));
        return @intCast(pair_index);
    }

    inline fn acceptEither(left_accepts: bool, right_accepts: bool) bool {
        return left_accepts or right_accepts;
    }

    inline fn acceptBoth(left_accepts: bool, right_accepts: bool) bool {
        return left_accepts and right_accepts;
    }

    /// Builds a Dfa over the Cartesian-product transition function.
    ///
    /// REQUIRES:
    /// - `Sigma_1 = Sigma_2`.
    /// - `|Q_1| * |Q_2| <= maxInt(State)`.
    /// - `|Q_1| * |Q_2| * paddedAlphabetSize(|Sigma_1|) <= maxInt(usize)`.
    /// - `allocator` can allocate the returned transition table and accepting set.
    ///
    /// ENSURES:
    /// - If `Sigma_1 != Sigma_2`, returns `error.IncompatibleAlphabets`.
    /// - If the product state set or transition table is too large, returns
    ///   `error.TooManyStates` or `error.TransitionTableTooLarge`.
    /// - If allocation fails, returns `error.OutOfMemory`.
    /// - Otherwise, returns `D` with `Q_D = Q_1 x Q_2`, `q0_D = (q0_1, q0_2)`, and
    ///   `delta_D((p, q), a) = (delta_1(p, a), delta_2(q, a))`.
    /// - `(p, q) in F_D` iff `accepts(p in F_1, q in F_2)`.
    /// - The caller owns the returned Dfa storage and must call `deinit`.
    fn product(self: *const Dfa, allocator: std.mem.Allocator, other: *const Dfa, comptime accepts: anytype) ProductError!Owned {
        if (self.alphabet_size != other.alphabet_size) return error.IncompatibleAlphabets;

        const left_state_size: usize = @intCast(self.state_size);
        const right_state_size: usize = @intCast(other.state_size);
        const product_state_size = std.math.mul(usize, left_state_size, right_state_size) catch return error.TooManyStates;
        if (product_state_size > std.math.maxInt(State)) return error.TooManyStates;

        const padded_size = paddedAlphabetSize(@intCast(self.alphabet_size));
        const delta_len = std.math.mul(usize, product_state_size, padded_size) catch return error.TransitionTableTooLarge;

        const delta = try allocator.alloc(State, delta_len);
        var accepting = std.DynamicBitSetUnmanaged.initEmpty(allocator, product_state_size) catch |err| {
            allocator.free(delta);
            return err;
        };

        for (0..left_state_size) |left_usize| {
            const left: State = @intCast(left_usize);
            for (0..right_state_size) |right_usize| {
                const right: State = @intCast(right_usize);
                const product_state = pairState(left, right, right_state_size);
                const product_row_start = @as(usize, @intCast(product_state)) * padded_size;

                for (0..self.alphabet_size) |symbol_usize| {
                    const symbol: Symbol = @intCast(symbol_usize);
                    delta[product_row_start + symbol_usize] = pairState(
                        self.next(left, symbol),
                        other.next(right, symbol),
                        right_state_size,
                    );
                }
                @memset(delta[product_row_start + @as(usize, @intCast(self.alphabet_size)) .. product_row_start + padded_size], 0);

                accepting.setValue(
                    @intCast(product_state),
                    accepts(self.isAccepting(left), other.isAccepting(right)),
                );
            }
        }

        return .{
            .dfa = Dfa.init(
                product_state_size,
                @intCast(self.alphabet_size),
                delta,
                pairState(self.start_state, other.start_state, right_state_size),
                accepting,
            ),
            .delta = delta,
        };
    }

    /// Returns the union of two Dfa languages.
    ///
    /// REQUIRES:
    /// - `Sigma_1 = Sigma_2`.
    /// - `|Q_1| * |Q_2| <= maxInt(State)`.
    /// - `|Q_1| * |Q_2| * paddedAlphabetSize(|Sigma_1|) <= maxInt(usize)`.
    ///
    /// ENSURES:
    /// - On success, returns a Dfa `D` such that for every `w in Sigma*`,
    ///   `w in L(D)` iff `w in L(self) or w in L(other)`.
    /// - If the product cannot be constructed, returns `ProductError`.
    /// - The caller owns the returned Dfa storage and must call `deinit`.
    pub fn unionWith(self: *const Dfa, allocator: std.mem.Allocator, other: *const Dfa) ProductError!Owned {
        return self.product(allocator, other, acceptEither);
    }

    /// Returns the intersection of two Dfa languages.
    ///
    /// REQUIRES:
    /// - `Sigma_1 = Sigma_2`.
    /// - `|Q_1| * |Q_2| <= maxInt(State)`.
    /// - `|Q_1| * |Q_2| * paddedAlphabetSize(|Sigma_1|) <= maxInt(usize)`.
    ///
    /// ENSURES:
    /// - On success, returns a Dfa `D` such that for every `w in Sigma*`,
    ///   `w in L(D)` iff `w in L(self) and w in L(other)`.
    /// - If the product cannot be constructed, returns `ProductError`.
    /// - The caller owns the returned Dfa storage and must call `deinit`.
    pub fn intersectWith(self: *const Dfa, allocator: std.mem.Allocator, other: *const Dfa) ProductError!Owned {
        return self.product(allocator, other, acceptBoth);
    }
};

fn expectLanguageUpToLength(
    allocator: std.mem.Allocator,
    dfa: *const Dfa,
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
            try std.testing.expectEqual(predicate(word), dfa.process(word));
        }
    }
}

fn endsInOne(symbols: []const Dfa.Symbol) bool {
    return symbols.len > 0 and symbols[symbols.len - 1] == 1;
}

fn onesMultipleOf3(symbols: []const Dfa.Symbol) bool {
    var ones: usize = 0;
    for (symbols) |symbol| {
        if (symbol == 1) ones += 1;
    }
    return ones % 3 == 0;
}

fn endsInOneAndOnesMultipleOf3(symbols: []const Dfa.Symbol) bool {
    return endsInOne(symbols) and onesMultipleOf3(symbols);
}

fn endsInOneOrOnesMultipleOf3(symbols: []const Dfa.Symbol) bool {
    return endsInOne(symbols) or onesMultipleOf3(symbols);
}

fn endsInTwo(symbols: []const Dfa.Symbol) bool {
    return symbols.len > 0 and symbols[symbols.len - 1] == 2;
}

fn containsOne(symbols: []const Dfa.Symbol) bool {
    for (symbols) |symbol| {
        if (symbol == 1) return true;
    }
    return false;
}

fn endsInTwoAndContainsOne(symbols: []const Dfa.Symbol) bool {
    return endsInTwo(symbols) and containsOne(symbols);
}

fn endsInTwoOrContainsOne(symbols: []const Dfa.Symbol) bool {
    return endsInTwo(symbols) or containsOne(symbols);
}

fn alwaysAccept(_: []const Dfa.Symbol) bool {
    return true;
}

fn ternaryPaddedLanguage(symbols: []const Dfa.Symbol) bool {
    var sum: usize = 0;
    for (symbols) |symbol| {
        sum += switch (symbol) {
            0 => 1,
            1 => 0,
            2 => 2,
            else => unreachable,
        };
    }
    return sum % 3 == 2;
}

test "Dfa - L = {s in {0,1}* | s ends in 1}" {
    const allocator = std.testing.allocator;

    const delta = [_]Dfa.State{
        0, 1,
        0, 1,
    };

    var accepting = try std.DynamicBitSetUnmanaged.initEmpty(allocator, 2);
    defer accepting.deinit(allocator);
    accepting.set(1);

    const dfa = Dfa.init(2, 2, &delta, 0, accepting);

    try std.testing.expect(!dfa.isAccepting(0));
    try std.testing.expect(dfa.isAccepting(1));

    try std.testing.expectEqual(@as(Dfa.State, 1), dfa.next(0, 1));
    try std.testing.expectEqual(@as(Dfa.State, 0), dfa.next(1, 0));

    const accept_input = [_]Dfa.Symbol{ 0, 1, 1 };
    try std.testing.expect(dfa.process(&accept_input));

    const single_accept = [_]Dfa.Symbol{1};
    try std.testing.expect(dfa.process(&single_accept));

    const reject_input = [_]Dfa.Symbol{ 1, 0, 1, 0 };
    try std.testing.expect(!dfa.process(&reject_input));

    const trivial_reject = [_]Dfa.Symbol{};
    try std.testing.expect(!dfa.process(&trivial_reject));

    try expectLanguageUpToLength(allocator, &dfa, 2, 8, endsInOne);
}

test "Dfa - L = {s in {0,1}* | # of 1s in s is a multiple of 3}" {
    const allocator = std.testing.allocator;

    const delta = [_]Dfa.State{
        0, 1,
        1, 2,
        2, 0,
    };

    var accepting = try std.DynamicBitSetUnmanaged.initEmpty(allocator, 3);
    defer accepting.deinit(allocator);
    accepting.set(0);

    const dfa = Dfa.init(3, 2, &delta, 0, accepting);

    const ones = [_]Dfa.Symbol{ 1, 1 };
    try std.testing.expectEqual(@as(Dfa.State, 0), dfa.processFromState(&ones, 1));

    const zeros = [_]Dfa.Symbol{0};
    try std.testing.expectEqual(@as(Dfa.State, 2), dfa.processFromState(&zeros, 2));

    const input_accept = [_]Dfa.Symbol{ 1, 0, 1, 0, 1 };
    try std.testing.expect(dfa.process(&input_accept));

    const input_accept_2 = [_]Dfa.Symbol{1} ** 2025;
    try std.testing.expect(dfa.process(&input_accept_2));

    const input_reject = [_]Dfa.Symbol{ 1, 0, 1 };
    try std.testing.expect(!dfa.process(&input_reject));

    const trivial_accept = [_]Dfa.Symbol{};
    try std.testing.expect(dfa.process(&trivial_accept));

    try expectLanguageUpToLength(allocator, &dfa, 2, 8, onesMultipleOf3);
}

test "Dfa - Single State Automaton" {
    const allocator = std.testing.allocator;

    const delta = [_]Dfa.State{ 0, 0, 0, 0 };

    var accepting = try std.DynamicBitSetUnmanaged.initEmpty(allocator, 1);
    defer accepting.deinit(allocator);
    accepting.set(0);

    const dfa = Dfa.init(1, 3, &delta, 0, accepting);

    const input = [_]Dfa.Symbol{ 2, 0, 1, 2, 2 };

    try std.testing.expectEqual(@as(Dfa.State, 0), dfa.processFromState(&input, 0));
    try std.testing.expect(dfa.process(&input));
    try expectLanguageUpToLength(allocator, &dfa, 3, 5, alwaysAccept);
}

test "Dfa - representation uses compact state and symbol indexes" {
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(Dfa.State));
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(Dfa.Symbol));
    try std.testing.expectEqual(@as(usize, 4), Dfa.paddedAlphabetSize(3));
    try std.testing.expectEqual(@as(usize, 256), Dfa.paddedAlphabetSize(256));
}

test "Dfa - padded rows support non-power-of-two alphabets" {
    const allocator = std.testing.allocator;

    const delta = [_]Dfa.State{
        1, 0, 2, 0,
        2, 1, 0, 0,
        0, 2, 1, 0,
    };

    var accepting = try std.DynamicBitSetUnmanaged.initEmpty(allocator, 3);
    defer accepting.deinit(allocator);
    accepting.set(2);

    const dfa = Dfa.init(3, 3, &delta, 0, accepting);

    try std.testing.expectEqual(@as(Dfa.State, 1), dfa.next(1, 1));

    const input = [_]Dfa.Symbol{ 0, 2, 2 };
    try std.testing.expectEqual(@as(Dfa.State, 2), dfa.processFromState(&input, 0));
    try std.testing.expect(dfa.process(&input));
    try expectLanguageUpToLength(allocator, &dfa, 3, 5, ternaryPaddedLanguage);
}

test "Dfa - isDfa recognizes well-formed and malformed representations" {
    const allocator = std.testing.allocator;

    const well_formed_delta = [_]Dfa.State{
        0, 1,
        0, 1,
    };

    var accepting = try std.DynamicBitSetUnmanaged.initEmpty(allocator, 2);
    defer accepting.deinit(allocator);
    accepting.set(1);

    const well_formed = Dfa.init(2, 2, &well_formed_delta, 0, accepting);
    try std.testing.expect(well_formed.isDfa());

    const bad_target_delta = [_]Dfa.State{
        0, 2,
        0, 1,
    };
    const bad_target = Dfa{
        .state_size = 2,
        .alphabet_size = 2,
        .delta = &bad_target_delta,
        .start_state = 0,
        .accepting = accepting,
        .alphabet_shift = 1,
    };
    try std.testing.expect(!bad_target.isDfa());

    const bad_shift = Dfa{
        .state_size = 2,
        .alphabet_size = 2,
        .delta = &well_formed_delta,
        .start_state = 0,
        .accepting = accepting,
        .alphabet_shift = 0,
    };
    try std.testing.expect(!bad_shift.isDfa());

    var wrong_size_accepting = try std.DynamicBitSetUnmanaged.initEmpty(allocator, 3);
    defer wrong_size_accepting.deinit(allocator);
    const bad_accepting_set = Dfa{
        .state_size = 2,
        .alphabet_size = 2,
        .delta = &well_formed_delta,
        .start_state = 0,
        .accepting = wrong_size_accepting,
        .alphabet_shift = 1,
    };
    try std.testing.expect(!bad_accepting_set.isDfa());
}

test "Dfa - union solves language union over binary alphabets" {
    const allocator = std.testing.allocator;

    const ends_in_one_delta = [_]Dfa.State{
        0, 1,
        0, 1,
    };
    var ends_in_one_accepting = try std.DynamicBitSetUnmanaged.initEmpty(allocator, 2);
    defer ends_in_one_accepting.deinit(allocator);
    ends_in_one_accepting.set(1);
    const ends_in_one_dfa = Dfa.init(2, 2, &ends_in_one_delta, 0, ends_in_one_accepting);

    const ones_mod_3_delta = [_]Dfa.State{
        0, 1,
        1, 2,
        2, 0,
    };
    var ones_mod_3_accepting = try std.DynamicBitSetUnmanaged.initEmpty(allocator, 3);
    defer ones_mod_3_accepting.deinit(allocator);
    ones_mod_3_accepting.set(0);
    const ones_mod_3_dfa = Dfa.init(3, 2, &ones_mod_3_delta, 0, ones_mod_3_accepting);

    var union_dfa = try ends_in_one_dfa.unionWith(allocator, &ones_mod_3_dfa);
    defer union_dfa.deinit(allocator);

    try std.testing.expect(union_dfa.dfa.isDfa());
    try expectLanguageUpToLength(allocator, &union_dfa.dfa, 2, 8, endsInOneOrOnesMultipleOf3);
}

test "Dfa - intersect solves language intersection over binary alphabets" {
    const allocator = std.testing.allocator;

    const ends_in_one_delta = [_]Dfa.State{
        0, 1,
        0, 1,
    };
    var ends_in_one_accepting = try std.DynamicBitSetUnmanaged.initEmpty(allocator, 2);
    defer ends_in_one_accepting.deinit(allocator);
    ends_in_one_accepting.set(1);
    const ends_in_one_dfa = Dfa.init(2, 2, &ends_in_one_delta, 0, ends_in_one_accepting);

    const ones_mod_3_delta = [_]Dfa.State{
        0, 1,
        1, 2,
        2, 0,
    };
    var ones_mod_3_accepting = try std.DynamicBitSetUnmanaged.initEmpty(allocator, 3);
    defer ones_mod_3_accepting.deinit(allocator);
    ones_mod_3_accepting.set(0);
    const ones_mod_3_dfa = Dfa.init(3, 2, &ones_mod_3_delta, 0, ones_mod_3_accepting);

    var intersection = try ends_in_one_dfa.intersectWith(allocator, &ones_mod_3_dfa);
    defer intersection.deinit(allocator);

    try std.testing.expect(intersection.dfa.isDfa());
    try expectLanguageUpToLength(allocator, &intersection.dfa, 2, 8, endsInOneAndOnesMultipleOf3);
}

test "Dfa - union and intersect solve ternary languages with padded rows" {
    const allocator = std.testing.allocator;

    const ends_in_two_delta = [_]Dfa.State{
        0, 0, 1, 0,
        0, 0, 1, 0,
    };
    var ends_in_two_accepting = try std.DynamicBitSetUnmanaged.initEmpty(allocator, 2);
    defer ends_in_two_accepting.deinit(allocator);
    ends_in_two_accepting.set(1);
    const ends_in_two_dfa = Dfa.init(2, 3, &ends_in_two_delta, 0, ends_in_two_accepting);

    const contains_one_delta = [_]Dfa.State{
        0, 1, 0, 0,
        1, 1, 1, 0,
    };
    var contains_one_accepting = try std.DynamicBitSetUnmanaged.initEmpty(allocator, 2);
    defer contains_one_accepting.deinit(allocator);
    contains_one_accepting.set(1);
    const contains_one_dfa = Dfa.init(2, 3, &contains_one_delta, 0, contains_one_accepting);

    var union_dfa = try ends_in_two_dfa.unionWith(allocator, &contains_one_dfa);
    defer union_dfa.deinit(allocator);

    var intersection = try ends_in_two_dfa.intersectWith(allocator, &contains_one_dfa);
    defer intersection.deinit(allocator);

    try std.testing.expect(union_dfa.dfa.isDfa());
    try std.testing.expect(intersection.dfa.isDfa());
    try expectLanguageUpToLength(allocator, &union_dfa.dfa, 3, 5, endsInTwoOrContainsOne);
    try expectLanguageUpToLength(allocator, &intersection.dfa, 3, 5, endsInTwoAndContainsOne);
}

test "Dfa - product operations reject mismatched alphabets" {
    const allocator = std.testing.allocator;

    const binary_delta = [_]Dfa.State{ 0, 0 };
    var binary_accepting = try std.DynamicBitSetUnmanaged.initEmpty(allocator, 1);
    defer binary_accepting.deinit(allocator);
    binary_accepting.set(0);
    const binary_dfa = Dfa.init(1, 2, &binary_delta, 0, binary_accepting);

    const ternary_delta = [_]Dfa.State{ 0, 0, 0, 0 };
    var ternary_accepting = try std.DynamicBitSetUnmanaged.initEmpty(allocator, 1);
    defer ternary_accepting.deinit(allocator);
    ternary_accepting.set(0);
    const ternary_dfa = Dfa.init(1, 3, &ternary_delta, 0, ternary_accepting);

    try std.testing.expectError(error.IncompatibleAlphabets, binary_dfa.unionWith(allocator, &ternary_dfa));
    try std.testing.expectError(error.IncompatibleAlphabets, binary_dfa.intersectWith(allocator, &ternary_dfa));
}
