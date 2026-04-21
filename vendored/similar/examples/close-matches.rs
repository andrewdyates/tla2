// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use similar::get_close_matches;

fn main() {
    let words = vec![
        "apple",
        "appu",
        "appal",
        "apparitor",
        "beer",
        "beeb",
        "beeline",
    ];
    println!("{:?}", get_close_matches("app", &words, 3, 0.7));
    println!("{:?}", get_close_matches("bee", &words, 3, 0.7));
}
