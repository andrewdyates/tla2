// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

extern crate target_lexicon;

use target_lexicon::HOST;

fn main() {
    println!(
        "{}",
        HOST.pointer_width()
            .expect("architecture should be known")
            .bytes()
    );
}
