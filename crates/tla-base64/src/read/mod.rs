// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

//! Implementations of `io::Read` to transparently decode base64.
mod decoder;
pub use self::decoder::DecoderReader;

#[cfg(test)]
mod decoder_tests;
