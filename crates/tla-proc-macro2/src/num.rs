// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

// TODO: use NonZero<char> in Rust 1.89+
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct NonZeroChar(char);

impl NonZeroChar {
    pub fn new(ch: char) -> Option<Self> {
        if ch == '\0' {
            None
        } else {
            Some(NonZeroChar(ch))
        }
    }

    pub fn get(self) -> char {
        self.0
    }
}
