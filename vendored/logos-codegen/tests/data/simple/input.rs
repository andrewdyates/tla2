// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[derive(Logos, Debug, Clone, Copy, PartialEq)]
enum Token {
    #[regex("a-z")]
    Letter,
}
