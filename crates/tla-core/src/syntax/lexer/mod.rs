// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TLA+ lexer using logos.

mod block_comment;
mod token;

pub(crate) use token::Token;

#[cfg(test)]
mod tests;
