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
