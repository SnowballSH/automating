const std = @import("std");
pub const dfa_tools = @import("dfa.zig");

test {
    std.testing.refAllDecls(@This());
}
