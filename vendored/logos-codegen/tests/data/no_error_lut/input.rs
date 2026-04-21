// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[derive(Logos)]
#[logos(source = [u8])]
enum Token {
    #[token("\n")]
    Newline,
    #[regex(".")]
    AnyUnicode,
    #[regex(b".", priority = 0)]
    Any,
}
