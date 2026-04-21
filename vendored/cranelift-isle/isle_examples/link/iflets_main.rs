// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0


struct Context;
impl iflets::Context for Context {
    fn A(&mut self, a: u32, b: u32) -> Option<u32> {
        Some(a + b)
    }

    fn B(&mut self, value: u32) -> Option<(u32, u32)> {
        Some((value, value + 1))
    }
}

fn main() {
    iflets::constructor_C(&mut Context, 1, 2, 3, 4);
}
