#![allow(clippy::module_inception)]
// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0


#[allow(dead_code, clippy::redundant_static_lifetimes, clippy::unreadable_literal)]
#[rustfmt::skip]
mod trie;

pub(crate) use self::trie::*;
