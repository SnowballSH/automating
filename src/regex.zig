//! Regular expression matcher built directly on the Nfa and Dfa modules.
//!
//! Grammar (only regular-language features):
//!   regex   = alt
//!   alt     = concat ('|' concat)*
//!   concat  = atom*
//!   atom    = primary ('*' | '+' | '?')?
//!   primary = literal | '(' alt ')' | '\\' literal
//!
//! Metacharacters: `( ) | * + ? \`. Any other byte is a literal. A backslash
//! escapes the following byte (which is treated as a literal). The empty
//! pattern matches only the empty string.
//!
//! Compilation is Thompson's construction: each subexpression is built into a
//! fragment with one start and one accept state, glued together with epsilon
//! transitions. The resulting NFA can be used directly for matching, or
//! determinized via `Nfa.toDfa` for repeated matches against the same regex.

const std = @import("std");
const nfa_mod = @import("nfa.zig");
pub const Nfa = nfa_mod.Nfa;
pub const Dfa = nfa_mod.Dfa;

const State = Nfa.State;
const Symbol = Nfa.Symbol;
const Word = Nfa.Word;

/// Number of distinct symbols the matcher recognizes (one per byte value).
pub const alphabet_size: usize = 256;

pub const ParseError = error{
    UnexpectedEnd,
    UnexpectedChar,
    UnclosedGroup,
    DanglingQuantifier,
    InvalidEscape,
    PatternTooLarge,
};

pub const CompileError = ParseError || std.mem.Allocator.Error;

const Frag = struct { start: State, accept: State };

const Edge = struct { from: State, sym: Symbol, to: State };
const EpsEdge = struct { from: State, to: State };

/// Compiles a regex pattern into the Nfa Thompson fragments. Owns no
/// allocations after `build` succeeds; `deinit` releases scratch storage.
const Builder = struct {
    allocator: std.mem.Allocator,
    state_count: usize = 0,
    edges: std.ArrayList(Edge) = .empty,
    eps_edges: std.ArrayList(EpsEdge) = .empty,

    fn deinit(self: *Builder) void {
        self.edges.deinit(self.allocator);
        self.eps_edges.deinit(self.allocator);
    }

    fn newState(self: *Builder) CompileError!State {
        if (self.state_count >= std.math.maxInt(State)) return error.PatternTooLarge;
        const s: State = @intCast(self.state_count);
        self.state_count += 1;
        return s;
    }

    fn addEdge(self: *Builder, from: State, sym: Symbol, to: State) CompileError!void {
        try self.edges.append(self.allocator, .{ .from = from, .sym = sym, .to = to });
    }

    fn addEps(self: *Builder, from: State, to: State) CompileError!void {
        try self.eps_edges.append(self.allocator, .{ .from = from, .to = to });
    }

    fn empty(self: *Builder) CompileError!Frag {
        const s = try self.newState();
        return .{ .start = s, .accept = s };
    }

    fn literal(self: *Builder, sym: Symbol) CompileError!Frag {
        const s = try self.newState();
        const e = try self.newState();
        try self.addEdge(s, sym, e);
        return .{ .start = s, .accept = e };
    }

    fn concat(self: *Builder, a: Frag, b: Frag) CompileError!Frag {
        try self.addEps(a.accept, b.start);
        return .{ .start = a.start, .accept = b.accept };
    }

    fn alt(self: *Builder, a: Frag, b: Frag) CompileError!Frag {
        const s = try self.newState();
        const e = try self.newState();
        try self.addEps(s, a.start);
        try self.addEps(s, b.start);
        try self.addEps(a.accept, e);
        try self.addEps(b.accept, e);
        return .{ .start = s, .accept = e };
    }

    fn star(self: *Builder, a: Frag) CompileError!Frag {
        const s = try self.newState();
        const e = try self.newState();
        try self.addEps(s, a.start);
        try self.addEps(s, e);
        try self.addEps(a.accept, a.start);
        try self.addEps(a.accept, e);
        return .{ .start = s, .accept = e };
    }

    fn plus(self: *Builder, a: Frag) CompileError!Frag {
        const e = try self.newState();
        try self.addEps(a.accept, a.start);
        try self.addEps(a.accept, e);
        return .{ .start = a.start, .accept = e };
    }

    fn optional(self: *Builder, a: Frag) CompileError!Frag {
        const s = try self.newState();
        const e = try self.newState();
        try self.addEps(s, a.start);
        try self.addEps(s, e);
        try self.addEps(a.accept, e);
        return .{ .start = s, .accept = e };
    }

    /// Materializes the bit-packed NFA. The returned `Nfa.Owned` takes
    /// ownership of `delta`, `epsilon`, and `accepting`.
    fn build(self: *Builder, start: State, accept: State) CompileError!Nfa.Owned {
        std.debug.assert(self.state_count > 0);
        std.debug.assert(start < self.state_count);
        std.debug.assert(accept < self.state_count);

        const sw = Nfa.stateWords(self.state_count);
        const padded = Nfa.paddedAlphabetSize(alphabet_size);

        const delta = try self.allocator.alloc(Word, self.state_count * padded * sw);
        errdefer self.allocator.free(delta);
        @memset(delta, 0);

        const epsilon = try self.allocator.alloc(Word, self.state_count * sw);
        errdefer self.allocator.free(epsilon);
        @memset(epsilon, 0);

        for (self.edges.items) |edge| {
            const base = (@as(usize, edge.from) * padded + @as(usize, edge.sym)) * sw;
            Nfa.setBit(delta[base .. base + sw], edge.to);
        }
        for (self.eps_edges.items) |edge| {
            const base = @as(usize, edge.from) * sw;
            Nfa.setBit(epsilon[base .. base + sw], edge.to);
        }

        var accepting = try std.DynamicBitSetUnmanaged.initEmpty(self.allocator, self.state_count);
        errdefer accepting.deinit(self.allocator);
        accepting.set(accept);

        return .{
            .nfa = Nfa.init(self.state_count, alphabet_size, delta, epsilon, start, accepting),
            .delta = delta,
            .epsilon = epsilon,
        };
    }
};

const Parser = struct {
    src: []const u8,
    pos: usize = 0,
    builder: *Builder,

    fn peek(self: *const Parser) ?u8 {
        return if (self.pos < self.src.len) self.src[self.pos] else null;
    }

    fn advance(self: *Parser) u8 {
        const c = self.src[self.pos];
        self.pos += 1;
        return c;
    }

    fn atConcatEnd(self: *const Parser) bool {
        const c = self.peek() orelse return true;
        return c == '|' or c == ')';
    }

    fn parseAlt(self: *Parser) CompileError!Frag {
        var left = try self.parseConcat();
        while (true) {
            const c = self.peek() orelse break;
            if (c != '|') break;
            _ = self.advance();
            const right = try self.parseConcat();
            left = try self.builder.alt(left, right);
        }
        return left;
    }

    fn parseConcat(self: *Parser) CompileError!Frag {
        if (self.atConcatEnd()) return self.builder.empty();
        var left = try self.parseAtom();
        while (!self.atConcatEnd()) {
            const right = try self.parseAtom();
            left = try self.builder.concat(left, right);
        }
        return left;
    }

    fn parseAtom(self: *Parser) CompileError!Frag {
        const prim = try self.parsePrimary();
        const c = self.peek() orelse return prim;
        switch (c) {
            '*' => {
                _ = self.advance();
                return self.builder.star(prim);
            },
            '+' => {
                _ = self.advance();
                return self.builder.plus(prim);
            },
            '?' => {
                _ = self.advance();
                return self.builder.optional(prim);
            },
            else => return prim,
        }
    }

    fn parsePrimary(self: *Parser) CompileError!Frag {
        const c = self.peek() orelse return error.UnexpectedEnd;
        switch (c) {
            '(' => {
                _ = self.advance();
                const inner = try self.parseAlt();
                const closing = self.peek() orelse return error.UnclosedGroup;
                if (closing != ')') return error.UnclosedGroup;
                _ = self.advance();
                return inner;
            },
            ')', '|' => return error.UnexpectedChar,
            '*', '+', '?' => return error.DanglingQuantifier,
            '\\' => {
                _ = self.advance();
                const escaped = self.peek() orelse return error.InvalidEscape;
                _ = self.advance();
                return self.builder.literal(@intCast(escaped));
            },
            else => {
                _ = self.advance();
                return self.builder.literal(@intCast(c));
            },
        }
    }
};

/// A compiled regular expression. Backed by an Nfa whose states and
/// transitions encode Thompson's construction of the source pattern.
pub const Regex = struct {
    owned: Nfa.Owned,

    /// Compiles `pattern` into a Regex.
    ///
    /// REQUIRES:
    /// - `allocator` can serve the resulting Nfa storage and small
    ///   per-fragment scratch buffers.
    ///
    /// ENSURES:
    /// - On success, returns a Regex `R` such that for every byte string `s`,
    ///   `R.match(s)` is true iff `s` is in the language denoted by `pattern`
    ///   under the grammar above.
    /// - On parse failure, returns the corresponding `ParseError`.
    /// - On allocation failure, returns `error.OutOfMemory`.
    /// - On overflow of the `Nfa.State` index, returns `error.PatternTooLarge`.
    /// - The caller owns the returned Regex storage and must call `deinit`.
    pub fn compile(allocator: std.mem.Allocator, pattern: []const u8) CompileError!Regex {
        var builder = Builder{ .allocator = allocator };
        defer builder.deinit();

        var parser = Parser{ .src = pattern, .builder = &builder };
        const frag = try parser.parseAlt();
        if (parser.peek() != null) return error.UnexpectedChar;

        const owned = try builder.build(frag.start, frag.accept);
        return .{ .owned = owned };
    }

    pub fn deinit(self: *Regex, allocator: std.mem.Allocator) void {
        self.owned.deinit(allocator);
        self.* = undefined;
    }

    /// Returns whether `input` is a full match of this regex.
    ///
    /// REQUIRES:
    /// - `allocator` can serve a `state_words`-sized scratch buffer (twice).
    ///
    /// ENSURES:
    /// - On success, returns `true` iff `input` is in the language of this regex.
    /// - On allocation failure, returns `error.OutOfMemory`.
    pub fn match(
        self: *const Regex,
        allocator: std.mem.Allocator,
        input: []const u8,
    ) std.mem.Allocator.Error!bool {
        const symbols = try allocator.alloc(Symbol, input.len);
        defer allocator.free(symbols);
        for (input, 0..) |b, i| symbols[i] = b;
        return self.owned.nfa.process(allocator, symbols);
    }

    /// Builds an equivalent Dfa via the subset construction. The returned
    /// `Dfa.Owned` is independent of this Regex; the caller must `deinit` it.
    pub fn toDfa(self: *const Regex, allocator: std.mem.Allocator) Nfa.ToDfaError!Dfa.Owned {
        return self.owned.nfa.toDfa(allocator);
    }
};

fn expectMatch(re: *const Regex, input: []const u8) !void {
    try std.testing.expect(try re.match(std.testing.allocator, input));
}

fn expectNoMatch(re: *const Regex, input: []const u8) !void {
    try std.testing.expect(!try re.match(std.testing.allocator, input));
}

test "Regex - empty pattern matches only empty string" {
    var re = try Regex.compile(std.testing.allocator, "");
    defer re.deinit(std.testing.allocator);

    try expectMatch(&re, "");
    try expectNoMatch(&re, "a");
    try expectNoMatch(&re, "abc");
}

test "Regex - single literal" {
    var re = try Regex.compile(std.testing.allocator, "a");
    defer re.deinit(std.testing.allocator);

    try expectMatch(&re, "a");
    try expectNoMatch(&re, "");
    try expectNoMatch(&re, "b");
    try expectNoMatch(&re, "aa");
    try expectNoMatch(&re, "ab");
}

test "Regex - concatenation" {
    var re = try Regex.compile(std.testing.allocator, "abc");
    defer re.deinit(std.testing.allocator);

    try expectMatch(&re, "abc");
    try expectNoMatch(&re, "");
    try expectNoMatch(&re, "ab");
    try expectNoMatch(&re, "abcd");
    try expectNoMatch(&re, "abx");
}

test "Regex - alternation" {
    var re = try Regex.compile(std.testing.allocator, "a|b|cd");
    defer re.deinit(std.testing.allocator);

    try expectMatch(&re, "a");
    try expectMatch(&re, "b");
    try expectMatch(&re, "cd");
    try expectNoMatch(&re, "");
    try expectNoMatch(&re, "c");
    try expectNoMatch(&re, "ab");
    try expectNoMatch(&re, "cda");
}

test "Regex - alternation with empty alternative" {
    var re = try Regex.compile(std.testing.allocator, "a|");
    defer re.deinit(std.testing.allocator);

    try expectMatch(&re, "");
    try expectMatch(&re, "a");
    try expectNoMatch(&re, "b");
    try expectNoMatch(&re, "aa");
}

test "Regex - kleene star" {
    var re = try Regex.compile(std.testing.allocator, "a*");
    defer re.deinit(std.testing.allocator);

    try expectMatch(&re, "");
    try expectMatch(&re, "a");
    try expectMatch(&re, "aaaaaa");
    try expectNoMatch(&re, "b");
    try expectNoMatch(&re, "aab");
}

test "Regex - plus quantifier" {
    var re = try Regex.compile(std.testing.allocator, "a+");
    defer re.deinit(std.testing.allocator);

    try expectNoMatch(&re, "");
    try expectMatch(&re, "a");
    try expectMatch(&re, "aaaa");
    try expectNoMatch(&re, "ab");
}

test "Regex - optional quantifier" {
    var re = try Regex.compile(std.testing.allocator, "a?b");
    defer re.deinit(std.testing.allocator);

    try expectMatch(&re, "b");
    try expectMatch(&re, "ab");
    try expectNoMatch(&re, "");
    try expectNoMatch(&re, "a");
    try expectNoMatch(&re, "aab");
}

test "Regex - grouping with quantifier" {
    var re = try Regex.compile(std.testing.allocator, "(ab)+c");
    defer re.deinit(std.testing.allocator);

    try expectMatch(&re, "abc");
    try expectMatch(&re, "ababc");
    try expectMatch(&re, "ababababc");
    try expectNoMatch(&re, "c");
    try expectNoMatch(&re, "abab");
    try expectNoMatch(&re, "abbc");
}

test "Regex - mixed alternation, grouping, and stars" {
    var re = try Regex.compile(std.testing.allocator, "a(b|c)*d");
    defer re.deinit(std.testing.allocator);

    try expectMatch(&re, "ad");
    try expectMatch(&re, "abd");
    try expectMatch(&re, "acd");
    try expectMatch(&re, "abcbcbd");
    try expectMatch(&re, "abbbcccd");
    try expectNoMatch(&re, "");
    try expectNoMatch(&re, "a");
    try expectNoMatch(&re, "abc");
    try expectNoMatch(&re, "axd");
}

test "Regex - escape sequences" {
    var re = try Regex.compile(std.testing.allocator, "a\\*b\\(c");
    defer re.deinit(std.testing.allocator);

    try expectMatch(&re, "a*b(c");
    try expectNoMatch(&re, "ab(c");
    try expectNoMatch(&re, "aab(c");
    try expectNoMatch(&re, "a*bc");
}

test "Regex - escape backslash itself" {
    var re = try Regex.compile(std.testing.allocator, "\\\\");
    defer re.deinit(std.testing.allocator);

    try expectMatch(&re, "\\");
    try expectNoMatch(&re, "");
    try expectNoMatch(&re, "\\\\");
}

test "Regex - star of group with alternation" {
    var re = try Regex.compile(std.testing.allocator, "(a|bc)*");
    defer re.deinit(std.testing.allocator);

    try expectMatch(&re, "");
    try expectMatch(&re, "a");
    try expectMatch(&re, "bc");
    try expectMatch(&re, "abc");
    try expectMatch(&re, "abcabca");
    try expectNoMatch(&re, "b");
    try expectNoMatch(&re, "ac");
}

test "Regex - rejects unbalanced parentheses" {
    try std.testing.expectError(error.UnclosedGroup, Regex.compile(std.testing.allocator, "(ab"));
    try std.testing.expectError(error.UnclosedGroup, Regex.compile(std.testing.allocator, "((a)"));
    try std.testing.expectError(error.UnexpectedChar, Regex.compile(std.testing.allocator, "ab)"));
}

test "Regex - rejects dangling quantifiers" {
    try std.testing.expectError(error.DanglingQuantifier, Regex.compile(std.testing.allocator, "*"));
    try std.testing.expectError(error.DanglingQuantifier, Regex.compile(std.testing.allocator, "+a"));
    try std.testing.expectError(error.DanglingQuantifier, Regex.compile(std.testing.allocator, "(?)"));
}

test "Regex - rejects trailing escape" {
    try std.testing.expectError(error.InvalidEscape, Regex.compile(std.testing.allocator, "a\\"));
}

test "Regex - toDfa accepts the same language" {
    var re = try Regex.compile(std.testing.allocator, "a(b|c)*d");
    defer re.deinit(std.testing.allocator);

    var dfa_owned = try re.toDfa(std.testing.allocator);
    defer dfa_owned.deinit(std.testing.allocator);

    const cases = [_]struct { s: []const u8, accept: bool }{
        .{ .s = "ad", .accept = true },
        .{ .s = "abd", .accept = true },
        .{ .s = "acd", .accept = true },
        .{ .s = "abcbcbd", .accept = true },
        .{ .s = "abbbcccd", .accept = true },
        .{ .s = "", .accept = false },
        .{ .s = "a", .accept = false },
        .{ .s = "abc", .accept = false },
        .{ .s = "axd", .accept = false },
    };

    for (cases) |c| {
        const buf = try std.testing.allocator.alloc(Dfa.Symbol, c.s.len);
        defer std.testing.allocator.free(buf);
        for (c.s, 0..) |b, i| buf[i] = b;
        try std.testing.expectEqual(c.accept, dfa_owned.dfa.process(buf));
    }
}

test "Regex - matches across full ASCII byte alphabet" {
    var re = try Regex.compile(std.testing.allocator, "(a|b|0|9| |!)+");
    defer re.deinit(std.testing.allocator);

    try expectMatch(&re, "a");
    try expectMatch(&re, "ab09 !");
    try expectMatch(&re, "9!ba");
    try expectMatch(&re, " ");
    try expectNoMatch(&re, "");
    try expectNoMatch(&re, "ax");
    try expectNoMatch(&re, "ab2");
}

test "Regex - star of empty alternative is benign" {
    // `(|a)*` reduces to `a*` once redundant epsilon paths are taken.
    var re = try Regex.compile(std.testing.allocator, "(|a)*");
    defer re.deinit(std.testing.allocator);

    try expectMatch(&re, "");
    try expectMatch(&re, "a");
    try expectMatch(&re, "aaaaa");
    try expectNoMatch(&re, "b");
    try expectNoMatch(&re, "ab");
}
